import Submission

set_option autoImplicit false

open Set Filter

namespace Erdos332SubmissionCheck

def InfiniteRepresentations (A : Set ℕ) (d : ℤ) : Prop :=
  Set.Infinite {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ A ∧ (p.1 : ℤ) - p.2 = d}

def BoundedGaps (S : Set ℤ) : Prop :=
  ∃ M : ℕ, 0 < M ∧ ∀ z : ℤ, ∃ d ∈ S, z ≤ d ∧ d < z + (M : ℤ)

theorem representation_bridge (A : Set ℕ) :
    {d | InfiniteRepresentations A d} = Erdos332.differences A := by
  ext d
  exact (Erdos332.recurring_iff_infinite_pairs A d).symm

theorem bounded_contact_challenge {A : Set ℕ} {g C K : ℤ} {δ : ℝ}
    {B : ℕ → Erdos332.Block}
    (hg : 0 < g) (hC : 0 ≤ C) (hδ : 0 < δ)
    (hp : ∀ n, 0 < (B n).p) (hq : ∀ n, 0 < (B n).q)
    (hcop : ∀ n, IsCoprime (B n).p (B n).q)
    (hpinf : Tendsto (fun n => (B n).p) atTop atTop)
    (hqinf : Tendsto (fun n => (B n).q) atTop atTop)
    (hbases : Tendsto (fun n => min (B n).a (B n).b) atTop atTop)
    (ha : Erdos332.approximates A g C B)
    (hgood : ∃ᶠ n in atTop,
      δ ≤ Erdos332.hullOverlap g (B n) / ((g : ℝ) * (B n).p * (B n).q) ∧
        ∃ r : ℤ, |r| ≤ K ∧ Erdos332.cross g (B n) r) :
    BoundedGaps {d | InfiniteRepresentations A d} := by
  rw [representation_bridge]
  exact Erdos332Submission.natural_gap_bound
    (Erdos332.main_bounded_contact hg hC hδ hp hq hcop hpinf hqinf hbases ha hgood)

theorem finite_gap_challenge {A : Set ℕ} {g C : ℤ} {H : ℕ}
    {B : ℕ → Erdos332.Block}
    (hg : 0 < g) (hC : 0 ≤ C) (hH : 0 < H)
    (hp : ∀ n, 0 < (B n).p) (hq : ∀ n, 0 < (B n).q)
    (hpinf : Tendsto (fun n => (B n).p) atTop atTop)
    (hqinf : Tendsto (fun n => (B n).q) atTop atTop)
    (hbases : Tendsto (fun n => min (B n).a (B n).b) atTop atTop)
    (ha : Erdos332.approximates A g C B)
    (hgood : ∃ᶠ n in atTop, Erdos332.finiteHullTest g H (B n)) :
    0 < 2 * g * H + 4 * C ∧ ∀ z : ℤ, ∃ d : ℤ,
      InfiniteRepresentations A d ∧ z ≤ d ∧ d < z + (2 * g * H + 4 * C) := by
  have h := Erdos332.main_finite_test hg hC hH hp hq hpinf hqinf hbases ha hgood
  refine ⟨h.1, fun z => ?_⟩
  obtain ⟨d, hd, hlo, hhi⟩ := h.2 z
  exact ⟨d, (Erdos332.recurring_iff_infinite_pairs A d).mp hd, hlo, hhi⟩

#check bounded_contact_challenge
#check finite_gap_challenge
#print axioms representation_bridge
#print axioms bounded_contact_challenge
#print axioms finite_gap_challenge

end Erdos332SubmissionCheck
