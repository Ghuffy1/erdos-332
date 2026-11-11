#!/usr/bin/env python3
"""Reproduce the pinned build, statement bridges, axiom audit and kernel replay."""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time


ROOT = Path(__file__).resolve().parents[1]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def git(*arguments: str, directory: Path = ROOT) -> str:
    return subprocess.check_output(
        ["git", "-C", str(directory), *arguments], text=True, encoding="utf-8"
    ).strip()


def run(arguments: list[str], log: Path) -> dict:
    started = time.monotonic()
    print("Running " + " ".join(arguments), flush=True)
    with log.open("w", encoding="utf-8", newline="\n") as output:
        process = subprocess.run(
            arguments, cwd=ROOT, stdout=output, stderr=subprocess.STDOUT, check=False
        )
    result = {
        "command": arguments,
        "exit_code": process.returncode,
        "elapsed_seconds": round(time.monotonic() - started, 3),
        "log": log.name,
    }
    for line in log.read_text(encoding="utf-8", errors="replace").splitlines()[-18:]:
        print(line, flush=True)
    if process.returncode:
        raise RuntimeError(f"Command failed with exit {process.returncode}: {arguments}")
    return result


def audit_records(text: str) -> dict[str, list[str]]:
    records = {}
    pattern = r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)"
    for name, value in re.findall(pattern, text, flags=re.MULTILINE):
        records[name] = [part.strip() for part in value.split(",") if part.strip()]
    return records


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--kernel-replay", action="store_true")
    parser.add_argument("--out", default=".verification-run")
    options = parser.parse_args()
    destination = Path(options.out)
    if not destination.is_absolute():
        destination = ROOT / destination
    destination.mkdir(parents=True, exist_ok=True)
    result = {
        "started_at_utc": datetime.now(timezone.utc).isoformat(),
        "source_commit": git("rev-parse", "HEAD"),
        "branch": git("branch", "--show-current"),
        "lean_toolchain": (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip(),
        "commands": [],
        "kernel_replay": "not requested",
        "independent_checker": "not run",
        "verdict": "in progress",
    }
    try:
        tracked_changes = git("status", "--porcelain", "--untracked-files=no")
        if tracked_changes:
            raise RuntimeError("Tracked changes prevent verification of an exact committed source.")
        result["source_files"] = {}
        for name in (
            "Erdos332.lean", "verification/Audit.lean", "verification/Challenge.lean",
            "lakefile.toml", "lake-manifest.json", "lean-toolchain",
            "paper/recurring_differences.tex", "paper/recurring_differences.pdf",
        ):
            data = (ROOT / name).read_bytes()
            committed = subprocess.check_output(
                ["git", "show", f"{result['source_commit']}:{name}"], cwd=ROOT
            )
            if data != committed:
                raise RuntimeError(f"Working file differs from the selected commit: {name}")
            result["source_files"][name] = {
                "bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()
            }
        source = (ROOT / "Erdos332.lean").read_text(encoding="utf-8")
        suspicious = re.search(
            r"\b(?:sorry|admit|axiom|unsafe|native_decide)\b|debug\.skipKernelTC|implemented_by",
            source,
        )
        if suspicious:
            raise RuntimeError(f"Source requires manual trust review: {suspicious.group(0)}")
        expected = {
            "Erdos332." + name
            for name in re.findall(r"^(?:theorem|lemma)\s+([\w.]+)", source, re.MULTILINE)
        }
        challenge_source = (ROOT / "verification" / "Challenge.lean").read_text(encoding="utf-8")
        expected.update(
            "Erdos332SubmissionCheck." + name
            for name in re.findall(
                r"^theorem\s+([\w.]+)", challenge_source, re.MULTILINE
            )
        )
        result["commands"].append(run(["lake", "build", "Erdos332"], destination / "build.log"))
        result["commands"].append(run(
            ["lake", "env", "lean", "verification/Audit.lean"], destination / "axioms.log"
        ))
        result["commands"].append(run(
            ["lake", "env", "lean", "verification/Challenge.lean"], destination / "challenge.log"
        ))
        records = audit_records((destination / "axioms.log").read_text(encoding="utf-8"))
        records.update(audit_records((destination / "challenge.log").read_text(encoding="utf-8")))
        missing = expected - records.keys()
        if missing:
            raise RuntimeError("Missing axiom output for " + ", ".join(sorted(missing)))
        axioms = {axiom for values in records.values() for axiom in values}
        if not axioms <= ALLOWED_AXIOMS:
            raise RuntimeError("Additional axioms: " + ", ".join(sorted(axioms - ALLOWED_AXIOMS)))
        result["theorems_audited"] = len(expected)
        result["axiom_union"] = sorted(axioms)
        result["axiom_records"] = records
        manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
        dependencies = []
        for package in manifest["packages"]:
            directory = ROOT / ".lake" / "packages" / package["name"]
            actual = git("rev-parse", "HEAD", directory=directory)
            dirty = git("status", "--porcelain", "--untracked-files=no", directory=directory)
            if actual != package["rev"] or dirty:
                raise RuntimeError("Dependency revision or tracked source mismatch: " + package["name"])
            dependencies.append({"name": package["name"], "commit": actual, "tracked_changes": []})
        result["dependencies"] = dependencies
        if options.kernel_replay:
            result["commands"].append(run(
                ["lake", "env", "leanchecker", "--fresh", "--verbose", "Erdos332"],
                destination / "kernel-replay.log",
            ))
            result["kernel_replay"] = "passed"
        result["verdict"] = "PASS for declared formal targets"
        return_code = 0
    except Exception as error:
        result["verdict"] = "FAILED or incomplete"
        result["error"] = str(error)
        print(str(error), file=sys.stderr, flush=True)
        return_code = 1
    result["completed_at_utc"] = datetime.now(timezone.utc).isoformat()
    (destination / "results.json").write_text(
        json.dumps(result, indent=2) + "\n", encoding="utf-8"
    )
    print(result["verdict"], flush=True)
    return return_code


if __name__ == "__main__":
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    sys.stderr.reconfigure(encoding="utf-8", errors="replace")
    sys.exit(main())
