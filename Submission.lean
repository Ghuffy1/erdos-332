import Erdos332

set_option autoImplicit false

open Set Filter

namespace Erdos332Submission

/-- The signed infinitely recurring differences in the original question. -/
def recurrentDifferences (A : Set ℕ) : Set ℤ :=
  {d : ℤ | Set.Infinite {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ A ∧ (p.1 : ℤ) - p.2 = d}}

/-- A positive natural-number gap bound, with all integer starting points. -/
def HasBoundedGaps (S : Set ℤ) : Prop :=
  ∃ M : ℕ, 0 < M ∧ ∀ z : ℤ, ∃ d ∈ S, z ≤ d ∧ d < z + (M : ℤ)

def regularModels (A : Set ℕ) (g C : ℤ) (B : ℕ → Erdos332.Block) : Prop :=
  0 < g ∧ 0 ≤ C ∧
  (∀ n, 0 < (B n).p) ∧ (∀ n, 0 < (B n).q) ∧
  (∀ n, IsCoprime (B n).p (B n).q) ∧
  (∀ n, 0 ≤ (B n).L) ∧ (∀ n, 0 ≤ (B n).R) ∧
  Tendsto (fun n => (B n).p) atTop atTop ∧
  Tendsto (fun n => (B n).q) atTop atTop ∧
  Tendsto (fun n => min (B n).a (B n).b) atTop atTop ∧
  Erdos332.approximates A g C B

/-- Either of the two progression conditions supplied in the manuscript. -/
def sufficientCondition (A : Set ℕ) : Prop :=
  ∃ (g C : ℤ) (B : ℕ → Erdos332.Block), regularModels A g C B ∧
    ((∃ (K : ℤ) (δ : ℝ), 0 < δ ∧ ∃ᶠ n in atTop,
        δ ≤ Erdos332.hullOverlap g (B n) / ((g : ℝ) * (B n).p * (B n).q) ∧
          ∃ r : ℤ, |r| ≤ K ∧ Erdos332.cross g (B n) r) ∨
      (∃ H : ℕ, 0 < H ∧ ∃ᶠ n in atTop, Erdos332.finiteHullTest g H (B n)))

theorem recurrentDifferences_eq (A : Set ℕ) :
    recurrentDifferences A = Erdos332.differences A := by
  ext d
  exact (Erdos332.recurring_iff_infinite_pairs A d).symm

theorem natural_gap_bound {S : Set ℤ} (h : Erdos332.syndetic S) : HasBoundedGaps S := by
  obtain ⟨M, hM, hbound⟩ := h
  have hcast : (M.toNat : ℤ) = M := Int.toNat_of_nonneg (le_of_lt hM)
  refine ⟨M.toNat, by omega, ?_⟩
  simpa only [hcast] using hbound

/-- The original open-ended implication, with the proposed condition explicit. -/
theorem erdos_332 (A : Set ℕ) (h : sufficientCondition A) :
    HasBoundedGaps (recurrentDifferences A) := by
  obtain ⟨g, C, B, ⟨hg, hC, hp, hq, hcop, _hL, _hR, hpinf, hqinf, hbases, ha⟩,
    hcriterion⟩ := h
  apply natural_gap_bound
  rw [recurrentDifferences_eq]
  rcases hcriterion with hcontact | hfinite
  · obtain ⟨K, δ, hδ, hgood⟩ := hcontact
    exact Erdos332.main_bounded_contact hg hC hδ hp hq hcop hpinf hqinf hbases ha hgood
  · obtain ⟨H, hH, hgood⟩ := hfinite
    exact ⟨2 * g * H + 4 * C,
      Erdos332.main_finite_test hg hC hH hp hq hpinf hqinf hbases ha hgood⟩

end Erdos332Submission
