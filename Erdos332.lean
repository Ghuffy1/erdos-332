import Mathlib.Data.Int.ModEq
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

set_option autoImplicit false

/-!
Private formalization of the progression sufficient conditions for Erdős 332.
The hypotheses describe explicit finite arithmetic progressions and bounded
approximation by a subset of the natural numbers.
-/

open Set Filter

namespace Erdos332

noncomputable section

/-- Signed differences with witnesses arbitrarily far out in `A`. -/
def recurring (A : Set ℕ) (d : ℤ) : Prop :=
  ∀ N : ℕ, ∃ a ∈ A, ∃ b ∈ A, N ≤ a ∧ (a : ℤ) - b = d

def differences (A : Set ℕ) : Set ℤ := {d | recurring A d}

/-- Every half-open integer interval of length `N` meets `S`. -/
def gapBound (S : Set ℤ) (N : ℤ) : Prop :=
  0 < N ∧ ∀ z : ℤ, ∃ s ∈ S, z ≤ s ∧ s < z + N

def syndetic (S : Set ℤ) : Prop := ∃ N : ℤ, gapBound S N

structure Block where
  a : ℤ
  b : ℤ
  p : ℤ
  q : ℤ
  L : ℤ
  R : ℤ

def points (g : ℤ) (B : Block) : Set ℤ :=
  {t | (∃ i : ℤ, 0 ≤ i ∧ i ≤ B.L ∧ t = B.a + g * B.p * i) ∨
       (∃ j : ℤ, 0 ≤ j ∧ j ≤ B.R ∧ t = B.b + g * B.q * j)}

def cross (g : ℤ) (B : Block) (d : ℤ) : Prop :=
  ∃ i j : ℤ, 0 ≤ i ∧ i ≤ B.L ∧ 0 ≤ j ∧ j ≤ B.R ∧
    (B.a + g * B.p * i) - (B.b + g * B.q * j) = d

/-- Integer formulation of the largest circular gap of the first `H`
residues `0,v,...,(H-1)v` modulo `q`. A gap bound `G` means that every
`G` consecutive integers contains one of these residues. -/
def gapCertificate (v q : ℤ) (H : ℕ) (G : ℤ) : Prop :=
  0 < G ∧ ∀ t : ℤ, ∃ j : ℕ, j < H ∧ ∃ z : ℤ,
    t ≤ v * j + q * z ∧ v * j + q * z < t + G

def lower (B : Block) (x : ℤ) : ℝ := max 0 ((x : ℝ) / B.p)
def upper (B : Block) (x : ℤ) : ℝ :=
  min (B.L : ℝ) (((x : ℝ) + B.q * B.R) / B.p)

lemma cross_of_index {g r x k : ℤ} {B : Block} (hbase : g * x = B.b - B.a + r)
    (hp : 0 < B.p) (hq : 0 < B.q) {i : ℤ}
    (hi : 0 ≤ i) (hiL : i ≤ B.L)
    (hlo : (x : ℝ) + k ≤ B.p * i)
    (hhi : (B.p : ℝ) * i ≤ (x : ℝ) + k + B.q * B.R)
    (hdiv : B.q ∣ B.p * i - (x + k)) : cross g B (r + g * k) := by
  obtain ⟨j, hj⟩ := hdiv
  have heq : B.p * i - (x + k) = B.q * j := hj
  have hqR : (0 : ℝ) < B.q := by exact_mod_cast hq
  have hj0 : (0 : ℝ) ≤ j := by
    have heqR : (B.p : ℝ) * i - ((x : ℝ) + k) = B.q * j := by exact_mod_cast heq
    nlinarith
  have hjR : (j : ℝ) ≤ B.R := by
    have heqR : (B.p : ℝ) * i - ((x : ℝ) + k) = B.q * j := by exact_mod_cast heq
    nlinarith
  refine ⟨i, j, hi, hiL, ?_, ?_, ?_⟩
  · exact_mod_cast hj0
  · exact_mod_cast hjR
  · linear_combination g * heq + hbase

lemma cross_of_common_interval {g r x k : ℤ} {B : Block}
    (hbase : g * x = B.b - B.a + r) (hp : 0 < B.p) (hq : 0 < B.q)
    {E : ℝ} (hE : 0 ≤ E) (hk : |(k : ℝ)| ≤ B.p * E) {i : ℤ}
    (hil : lower B x + E ≤ i) (hiu : (i : ℝ) ≤ upper B x - E)
    (hdiv : B.q ∣ B.p * i - (x + k)) : cross g B (r + g * k) := by
  have hpR : (0 : ℝ) < B.p := by exact_mod_cast hp
  have hl0 : 0 ≤ lower B x := le_max_left _ _
  have hlx : (x : ℝ) ≤ B.p * lower B x := by
    have h := le_max_right (0 : ℝ) ((x : ℝ) / B.p)
    simpa [lower, mul_comm] using (div_le_iff₀ hpR).mp h
  have huL : upper B x ≤ B.L := min_le_left _ _
  have hux : (B.p : ℝ) * upper B x ≤ (x : ℝ) + B.q * B.R := by
    have h := min_le_right (B.L : ℝ) (((x : ℝ) + B.q * B.R) / B.p)
    simpa [upper, mul_comm] using (le_div_iff₀ hpR).mp h
  have hmulL := mul_le_mul_of_nonneg_left hil (le_of_lt hpR)
  have hmulU := mul_le_mul_of_nonneg_left hiu (le_of_lt hpR)
  have hka := (abs_le.mp hk).1
  have hkb := (abs_le.mp hk).2
  apply cross_of_index hbase hp hq
  · have : (0 : ℝ) ≤ i := by linarith
    exact_mod_cast this
  · have : (i : ℝ) ≤ B.L := by linarith
    exact_mod_cast this
  · nlinarith
  · nlinarith
  · exact hdiv

lemma gapCertificate.window {v q G : ℤ} {H : ℕ}
    (hc : gapCertificate v q H G) (start x m : ℤ) :
    ∃ k i : ℤ, start ≤ k ∧ k < start + H ∧ m ≤ i ∧ i < m + G ∧
      q ∣ i - v * (x + k) := by
  obtain ⟨j, hj, z, hlo, hhi⟩ := hc.2 (m - v * (x + start))
  refine ⟨start + j, v * (x + start + j) + q * z, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · exact_mod_cast (by omega : (start + (j : ℤ)) < start + (H : ℤ))
  · nlinarith
  · nlinarith
  · refine ⟨z, ?_⟩
    ring

lemma inverse_transfer {p q v x k i : ℤ} (hinv : q ∣ p * v - 1)
    (hi : q ∣ i - v * (x + k)) : q ∣ p * i - (x + k) := by
  obtain ⟨s, hs⟩ := hinv
  obtain ⟨t, ht⟩ := hi
  refine ⟨s * (x + k) + p * t, ?_⟩
  linear_combination (x + k) * hs + p * ht

/-- Finite, exact endpoint version of the two-window argument. -/
theorem finite_gap_window {g r x v G : ℤ} {H : ℕ} {B : Block}
    (hH : 0 < H) (hbase : g * x = B.b - B.a + r)
    (hp : 0 < B.p) (hq : 0 < B.q)
    (hinv : B.q ∣ B.p * v - 1) (hc : gapCertificate v B.q H G)
    (hwidth : (G : ℝ) ≤ upper B x - lower B x)
    (start : ℤ) (hpbig : 2 * (|start| + 2 * H) < B.p)
    (hqbig : 2 * (H : ℤ) < B.q) :
    ∃ k : ℤ, start ≤ k ∧ k < start + 2 * H ∧ cross g B (r + g * k) := by
  let M : ℤ := |start| + 2 * H
  let E : ℝ := (M : ℝ) / B.p
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hpR : (0 : ℝ) < B.p := by exact_mod_cast hp
  have hE : 0 ≤ E := div_nonneg (by exact_mod_cast hM) (le_of_lt hpR)
  have hEhalf : 2 * E < 1 := by
    have hbig : 2 * (M : ℝ) < B.p := by exact_mod_cast hpbig
    have hd : E < 1 / 2 := by
      apply (div_lt_iff₀ hpR).2
      linarith
    linarith
  let m : ℤ := ⌊lower B x + E⌋ + 1
  have hmlo : lower B x + E < m := by
    simpa [m] using Int.lt_floor_add_one (lower B x + E)
  have hmhi : (m : ℝ) ≤ lower B x + E + 1 := by
    dsimp [m]
    push_cast
    linarith [Int.floor_le (lower B x + E)]
  have hkgood : ∀ k : ℤ, start ≤ k → k < start + 2 * H →
      |(k : ℝ)| ≤ B.p * E := by
    intro k hklo hkhi
    have hkM : |k| ≤ M := by
      have hs := (abs_le.mp (le_refl |start|))
      rw [abs_le]
      dsimp [M]
      omega
    have hcM : |(k : ℝ)| ≤ (M : ℝ) := by exact_mod_cast hkM
    simpa [E, mul_div_cancel₀ _ (ne_of_gt hpR)] using hcM
  have hinside : ∀ k i : ℤ, start ≤ k → k < start + 2 * H →
      m ≤ i → i ≤ m + G - 2 → B.q ∣ B.p * i - (x + k) →
      cross g B (r + g * k) := by
    intro k i hklo hkhi hilo hihi hdiv
    apply cross_of_common_interval hbase hp hq hE (hkgood k hklo hkhi) _ _ hdiv
    · have : (m : ℝ) ≤ i := by exact_mod_cast hilo
      linarith
    · have : (i : ℝ) ≤ (m : ℝ) + G - 2 := by exact_mod_cast hihi
      linarith
  obtain ⟨k₁, i₁, hk₁lo, hk₁hi, hi₁lo, hi₁hi, hdiv₁⟩ :=
    hc.window start x m
  obtain ⟨k₂, i₂, hk₂lo, hk₂hi, hi₂lo, hi₂hi, hdiv₂⟩ :=
    hc.window (start + H) x m
  have hd₁ := inverse_transfer hinv hdiv₁
  have hd₂ := inverse_transfer hinv hdiv₂
  by_cases hi₁ : i₁ ≤ m + G - 2
  · exact ⟨k₁, hk₁lo, by omega, hinside _ _ hk₁lo (by omega) hi₁lo hi₁ hd₁⟩
  by_cases hi₂ : i₂ ≤ m + G - 2
  · exact ⟨k₂, by omega, by omega, hinside _ _ (by omega) (by omega) hi₂lo hi₂ hd₂⟩
  have heq : i₁ = i₂ := by omega
  have hd : B.q ∣ k₂ - k₁ := by
    obtain ⟨s, hs⟩ := hd₁
    obtain ⟨t, ht⟩ := hd₂
    refine ⟨s - t, ?_⟩
    rw [heq] at hs
    linear_combination hs - ht
  have hpos : 0 < k₂ - k₁ := by omega
  have hsmall : k₂ - k₁ < B.q := by omega
  have he := Int.emod_eq_of_lt (le_of_lt hpos) hsmall
  rw [Int.emod_eq_zero_of_dvd hd] at he
  omega

theorem recurring_iff_infinite_pairs (A : Set ℕ) (d : ℤ) :
    recurring A d ↔ {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ A ∧ (p.1 : ℤ) - p.2 = d}.Infinite := by
  let S : Set (ℕ × ℕ) := {p | p.1 ∈ A ∧ p.2 ∈ A ∧ (p.1 : ℤ) - p.2 = d}
  constructor
  · intro h hfin
    obtain ⟨N, hN⟩ := (hfin.image Prod.fst).bddAbove
    obtain ⟨a, ha, b, hb, hNa, hab⟩ := h (N + 1)
    have habS : (a, b) ∈ S := ⟨ha, hb, hab⟩
    have := hN (Set.mem_image_of_mem Prod.fst habS)
    omega
  · intro h N
    have hinj : Set.InjOn Prod.fst S := by
      intro a ha b hb heq
      have hd₁ := ha.2.2
      have hd₂ := hb.2.2
      apply Prod.ext heq
      omega
    have hi : (Prod.fst '' S).Infinite := h.image hinj
    obtain ⟨a, ⟨⟨u, v⟩, huv, rfl⟩, hNa⟩ := hi.exists_gt N
    exact ⟨u, huv.1, v, huv.2.1, le_of_lt hNa, huv.2.2⟩

def modelRecurring (g : ℤ) (B : ℕ → Block) (d : ℤ) : Prop :=
  ∃ᶠ n in atTop, ∃ u ∈ points g (B n), ∃ v ∈ points g (B n), u - v = d

def approximates (A : Set ℕ) (g C : ℤ) (B : ℕ → Block) : Prop :=
  ∀ n, ∀ u ∈ points g (B n), ∃ a ∈ A, |(a : ℤ) - u| ≤ C

def escapes (g : ℤ) (B : ℕ → Block) : Prop :=
  ∀ K : ℤ, ∀ᶠ n in atTop, ∀ u ∈ points g (B n), K ≤ u

theorem transfer_recurring {A : Set ℕ} {g C : ℤ} {B : ℕ → Block}
    (ha : approximates A g C B) (he : escapes g B) {d : ℤ}
    (hd : modelRecurring g B d) :
    ∃ e ∈ differences A, |e - d| ≤ 2 * C := by
  have hw : ∀ N : ℕ, ∃ e ∈ Set.Icc (d - 2 * C) (d + 2 * C),
      ∃ a ∈ A, ∃ b ∈ A, N ≤ a ∧ (a : ℤ) - b = e := by
    intro N
    obtain ⟨n, hn, u, hu, v, hv, huv⟩ := ((he ((N : ℤ) + C)).and_frequently hd).exists
    obtain ⟨a, haA, hau⟩ := ha n u hu
    obtain ⟨b, hbA, hbv⟩ := ha n v hv
    have hNa : N ≤ a := by
      have hnu := hn u hu
      rw [abs_le] at hau
      omega
    have hdiff : |((a : ℤ) - b) - d| ≤ 2 * C := by
      rw [abs_le] at hau hbv ⊢
      omega
    refine ⟨(a : ℤ) - b, ?_, a, haA, b, hbA, hNa, rfl⟩
    rw [abs_le] at hdiff
    exact ⟨by omega, by omega⟩
  have hf : ∃ᶠ N : ℕ in atTop, ∃ e ∈ Set.Icc (d - 2 * C) (d + 2 * C),
      ∃ a ∈ A, ∃ b ∈ A, N ≤ a ∧ (a : ℤ) - b = e :=
    (Filter.Eventually.of_forall hw).frequently
  obtain ⟨e, heI, heF⟩ := (Set.finite_Icc _ _).frequently_exists.mp hf
  refine ⟨e, ?_, ?_⟩
  · intro N
    obtain ⟨M, hNM, a, haA, b, hbA, hMa, hab⟩ := heF.forall_exists_of_atTop N
    exact ⟨a, haA, b, hbA, le_trans hNM hMa, hab⟩
  · rw [abs_le]
    rcases heI with ⟨hl, hu⟩
    exact ⟨by omega, by omega⟩

theorem transfer_gapBound {A : Set ℕ} {g C N : ℤ} {B : ℕ → Block}
    (hC : 0 ≤ C) (ha : approximates A g C B) (he : escapes g B)
    (hS : gapBound {d | modelRecurring g B d} N) :
    gapBound (differences A) (N + 4 * C) := by
  have hN := hS.1
  refine ⟨by omega, fun z => ?_⟩
  obtain ⟨d, hd, hdl, hdu⟩ := hS.2 (z + 2 * C)
  obtain ⟨e, heA, hed⟩ := transfer_recurring ha he hd
  rw [abs_le] at hed
  exact ⟨e, heA, by omega, by omega⟩

theorem escapes_of_bases {g : ℤ} {B : ℕ → Block} (hg : 0 < g)
    (hp : ∀ n, 0 ≤ (B n).p) (hq : ∀ n, 0 ≤ (B n).q)
    (ha : Tendsto (fun n => (B n).a) atTop atTop)
    (hb : Tendsto (fun n => (B n).b) atTop atTop) : escapes g B := by
  intro K
  filter_upwards [(tendsto_atTop.1 ha) K, (tendsto_atTop.1 hb) K] with n han hbn
  intro u hu
  rcases hu with ⟨i, hi, _, rfl⟩ | ⟨j, hj, _, rfl⟩
  · have := mul_nonneg (mul_nonneg (le_of_lt hg) (hp n)) hi
    omega
  · have := mul_nonneg (mul_nonneg (le_of_lt hg) (hq n)) hj
    omega

lemma integer_grid_interval {g : ℤ} (hg : 0 < g) (r z : ℤ) :
    ∃ k : ℤ, z ≤ r + g * k ∧ r + g * k < z + g := by
  have he := Int.ediv_mul_add_emod (z - r - 1) g
  have h0 := Int.emod_nonneg (z - r - 1) (ne_of_gt hg)
  have hlt := Int.emod_lt_of_pos (z - r - 1) hg
  refine ⟨(z - r - 1) / g + 1, ?_, ?_⟩
  · nlinarith
  · nlinarith

lemma cross_occurs {g d : ℤ} {B : Block} (h : cross g B d) :
    ∃ u ∈ points g B, ∃ v ∈ points g B, u - v = d := by
  obtain ⟨i, j, hi, hiL, hj, hjR, heq⟩ := h
  exact ⟨B.a + g * B.p * i, Or.inl ⟨i, hi, hiL, rfl⟩,
    B.b + g * B.q * j, Or.inr ⟨j, hj, hjR, rfl⟩, heq⟩

theorem model_gap_of_finite_test {g r : ℤ} {H : ℕ} {B : ℕ → Block}
    (hg : 0 < g) (hH : 0 < H)
    (hp : ∀ n, 0 < (B n).p) (hq : ∀ n, 0 < (B n).q)
    (hpinf : Tendsto (fun n => (B n).p) atTop atTop)
    (hqinf : Tendsto (fun n => (B n).q) atTop atTop)
    (hgood : ∃ᶠ n in atTop, ∃ x v G : ℤ,
      g * x = (B n).b - (B n).a + r ∧
      (B n).q ∣ (B n).p * v - 1 ∧ gapCertificate v (B n).q H G ∧
      (G : ℝ) ≤ upper (B n) x - lower (B n) x) :
    gapBound {d | modelRecurring g B d} (2 * g * H) := by
  refine ⟨by positivity, fun z => ?_⟩
  obtain ⟨start, hstartlo, hstarthi⟩ := integer_grid_interval hg r z
  have hpbig : ∀ᶠ n in atTop, 2 * (|start| + 2 * H) < (B n).p :=
    hpinf.eventually (eventually_gt_atTop _)
  have hqbig : ∀ᶠ n in atTop, 2 * (H : ℤ) < (B n).q :=
    hqinf.eventually (eventually_gt_atTop _)
  have hwindow : ∃ᶠ n in atTop, ∃ k ∈ Set.Ico start (start + 2 * H),
      cross g (B n) (r + g * k) := by
    apply (((hpbig.and hqbig).and_frequently hgood).mono)
    rintro n ⟨⟨hpB, hqB⟩, x, v, G, hx, hv, hc, hw⟩
    obtain ⟨k, hkl, hku, hk⟩ := finite_gap_window hH hx (hp n) (hq n) hv hc hw start hpB hqB
    exact ⟨k, ⟨hkl, hku⟩, hk⟩
  obtain ⟨k, hkI, hkF⟩ := (Set.finite_Ico _ _).frequently_exists.mp hwindow
  refine ⟨r + g * k, hkF.mono (fun _ h => cross_occurs h), ?_, ?_⟩
  · nlinarith [hkI.1]
  · have hkupper := hkI.2
    have hki : k ≤ start + 2 * H - 1 := by omega
    nlinarith

/-- The original finite test, expressed with its integer circular-gap
certificate. The residue and the translated overlap are both explicit. -/
def finiteGapCondition (g : ℤ) (H : ℕ) (B : Block) : Prop :=
  ∃ r x v G : ℤ, 0 ≤ r ∧ r < g ∧ g * x = B.b - B.a + r ∧
    B.q ∣ B.p * v - 1 ∧ gapCertificate v B.q H G ∧
    (G : ℝ) ≤ upper B x - lower B x

/-- Quantitative sufficient condition, with bounded perturbations and the
closed endpoint of the finite circular-gap test included. -/
theorem finite_test {A : Set ℕ} {g C : ℤ} {H : ℕ} {B : ℕ → Block}
    (hg : 0 < g) (hC : 0 ≤ C) (hH : 0 < H)
    (hp : ∀ n, 0 < (B n).p) (hq : ∀ n, 0 < (B n).q)
    (hpinf : Tendsto (fun n => (B n).p) atTop atTop)
    (hqinf : Tendsto (fun n => (B n).q) atTop atTop)
    (ha : approximates A g C B) (he : escapes g B)
    (hgood : ∃ᶠ n in atTop, finiteGapCondition g H (B n)) :
    gapBound (differences A) (2 * g * H + 4 * C) := by
  have hr : ∃ᶠ n in atTop, ∃ r ∈ Set.Ico (0 : ℤ) g, ∃ x v G : ℤ,
      g * x = (B n).b - (B n).a + r ∧
      (B n).q ∣ (B n).p * v - 1 ∧ gapCertificate v (B n).q H G ∧
      (G : ℝ) ≤ upper (B n) x - lower (B n) x := by
    apply hgood.mono
    rintro n ⟨r, x, v, G, hr0, hrg, hx, hv, hc, hw⟩
    exact ⟨r, ⟨hr0, hrg⟩, x, v, G, hx, hv, hc, hw⟩
  obtain ⟨r, _, hrF⟩ := (Set.finite_Ico _ _).frequently_exists.mp hr
  exact transfer_gapBound hC ha he (model_gap_of_finite_test hg hH hp hq hpinf hqinf hrF)

lemma gapBound_nearby {S T : Set ℤ} {N C : ℤ} (hC : 0 ≤ C)
    (hT : gapBound T N) (hnear : ∀ t ∈ T, ∃ s ∈ S, |s - t| ≤ C) :
    gapBound S (N + 2 * C) := by
  have hN := hT.1
  refine ⟨by omega, fun z => ?_⟩
  obtain ⟨t, ht, htl, htu⟩ := hT.2 (z + C)
  obtain ⟨s, hs, hst⟩ := hnear t ht
  rw [abs_le] at hst
  exact ⟨s, hs, by omega, by omega⟩

lemma gapBound_scale {S : Set ℤ} {N g : ℤ} (hg : 0 < g) (hS : gapBound S N) :
    gapBound ((fun k : ℤ => g * k) '' S) (g * N) := by
  refine ⟨mul_pos hg hS.1, fun z => ?_⟩
  obtain ⟨k, hkl, hku⟩ := integer_grid_interval hg 0 z
  obtain ⟨s, hs, hsl, hsu⟩ := hS.2 k
  refine ⟨g * s, ⟨s, hs, rfl⟩, ?_, ?_⟩
  · nlinarith
  · have : s ≤ k + N - 1 := by omega
    nlinarith

lemma modelRecurring_neg {g d : ℤ} {B : ℕ → Block} (h : modelRecurring g B d) :
    modelRecurring g B (-d) := by
  apply h.mono
  rintro n ⟨u, hu, v, hv, huv⟩
  exact ⟨v, hv, u, hu, by omega⟩

/-- Return times to a neighborhood of zero in a compact normed group have
bounded gaps. This also applies to a finite product of circles. -/
theorem bohr_syndetic {X : Type*} [NormedAddCommGroup X] [CompactSpace X]
    (a : X) {ε : ℝ} (hε : 0 < ε) :
    syndetic {k : ℤ | ‖k • a‖ < ε} := by
  classical
  let orbit : ℤ → X := fun k => k • a
  have ht : TotallyBounded (Set.range orbit) :=
    (isCompact_univ.totallyBounded).subset (Set.subset_univ _)
  obtain ⟨t, htsub, htfin, htcov⟩ := Metric.finite_approx_of_totallyBounded ht ε hε
  let f : X → ℤ := fun x => if hx : x ∈ Set.range orbit then Classical.choose hx else 0
  have hf : ∀ x ∈ t, (f x) • a = x := by
    intro x hx
    have hr := htsub hx
    simpa only [f, dif_pos hr, orbit] using Classical.choose_spec hr
  obtain ⟨B, hB⟩ := (htfin.image (fun x => |f x|)).bddAbove
  let M : ℤ := max B 0
  have hM : 0 ≤ M := le_max_right _ _
  refine ⟨2 * M + 1, by omega, fun z => ?_⟩
  have hor : orbit (z + M) ∈ Set.range orbit := Set.mem_range_self _
  have hc := htcov hor
  simp only [Set.mem_iUnion] at hc
  obtain ⟨x, hx, hdist⟩ := hc
  have hfx : |f x| ≤ M := le_trans (hB ⟨x, hx, rfl⟩) (le_max_left _ _)
  have hnorm : ‖(z + M - f x) • a‖ < ε := by
    calc
      ‖(z + M - f x) • a‖ = ‖(z + M) • a - (f x) • a‖ := by
        rw [sub_zsmul]
        simp only [sub_eq_add_neg]
      _ = ‖orbit (z + M) - x‖ := by simp only [orbit, hf x hx]
      _ < ε := by simpa only [Metric.mem_ball, dist_eq_norm] using hdist
  refine ⟨z + M - f x, hnorm, ?_, ?_⟩
  · have := (abs_le.mp hfx).2
    omega
  · have := (abs_le.mp hfx).1
    omega

lemma gapCertificate_full_period {v q : ℤ} {H : ℕ} (hq : 0 < q) (hH : 0 < H) :
    gapCertificate v q H q := by
  refine ⟨hq, fun t => ?_⟩
  obtain ⟨z, hzlo, hzhi⟩ := integer_grid_interval hq 0 t
  exact ⟨0, hH, z, by simpa using hzlo, by simpa using hzhi⟩

/-- The exact integer numerator of the largest circular gap. -/
def maxGapNumerator (v q : ℤ) (H : ℕ) : ℕ := by
  classical
  exact if h : ∃ G : ℕ, gapCertificate v q H G then Nat.find h else 0

lemma maxGapNumerator_spec {v q : ℤ} {H : ℕ} (hq : 0 < q) (hH : 0 < H) :
    gapCertificate v q H (maxGapNumerator v q H) := by
  classical
  have hex : ∃ G : ℕ, gapCertificate v q H G :=
    ⟨q.toNat, by simpa [Int.toNat_of_nonneg (le_of_lt hq)] using
      gapCertificate_full_period (v := v) hq hH⟩
  simpa [maxGapNumerator, dif_pos hex] using Nat.find_spec hex

lemma maxGapNumerator_min {v q : ℤ} {H G : ℕ} (h : gapCertificate v q H G) :
    maxGapNumerator v q H ≤ G := by
  classical
  have hex : ∃ K : ℕ, gapCertificate v q H K := ⟨G, h⟩
  simpa [maxGapNumerator, dif_pos hex] using Nat.find_min' hex h

def circularGap (v q : ℤ) (H : ℕ) : ℝ := (maxGapNumerator v q H : ℝ) / q

/-- A discrete gap certificate is equivalent to covering every closed real
interval of the same length by the periodically repeated phase points. -/
lemma gapCertificate_iff_real_cover {v q G : ℤ} {H : ℕ} :
    gapCertificate v q H G ↔ 0 < G ∧ ∀ t : ℝ, ∃ j : ℕ, j < H ∧ ∃ z : ℤ,
      t ≤ ((v * j + q * z : ℤ) : ℝ) ∧ ((v * j + q * z : ℤ) : ℝ) ≤ t + G := by
  constructor
  · rintro ⟨hG, hc⟩
    refine ⟨hG, fun t => ?_⟩
    obtain ⟨j, hj, z, hlo, hhi⟩ := hc ⌈t⌉
    refine ⟨j, hj, z, ?_, ?_⟩
    · exact le_trans (Int.le_ceil t) (by exact_mod_cast hlo)
    · have hi : ((v * j + q * z : ℤ) : ℝ) ≤ (⌈t⌉ : ℝ) + G - 1 := by
        exact_mod_cast (by omega : v * j + q * z ≤ ⌈t⌉ + G - 1)
      linarith [Int.ceil_lt_add_one t]
  · rintro ⟨hG, hc⟩
    refine ⟨hG, fun t => ?_⟩
    obtain ⟨j, hj, z, hlo, hhi⟩ := hc ((t : ℝ) - 1 / 2)
    refine ⟨j, hj, z, ?_, ?_⟩
    · by_contra h
      have hn : v * j + q * z ≤ t - 1 := by omega
      have hr : ((v * j + q * z : ℤ) : ℝ) ≤ (t : ℝ) - 1 := by exact_mod_cast hn
      linarith
    · by_contra h
      have hn : t + G ≤ v * j + q * z := by omega
      have hr : (t : ℝ) + G ≤ ((v * j + q * z : ℤ) : ℝ) := by exact_mod_cast hn
      linarith

def residue (g : ℤ) (B : Block) : ℤ := (B.a - B.b) % g
def offset (g : ℤ) (B : Block) : ℤ := -((B.a - B.b) / g)

lemma offset_identity (g : ℤ) (B : Block) : g * offset g B = B.b - B.a + residue g B := by
  have h := Int.ediv_mul_add_emod (B.a - B.b) g
  dsimp [offset, residue]
  nlinarith

/-- Canonical form of the finite circular-gap hypothesis, with the least
positive gap and the unique residue modulo the common step factor. -/
def canonicalFiniteTest (g : ℤ) (H : ℕ) (B : Block) : Prop :=
  ∃ v : ℤ, B.q ∣ B.p * v - 1 ∧
    circularGap v B.q H ≤
      (upper B (offset g B) - lower B (offset g B)) / B.q

theorem canonicalFiniteTest_implies {g : ℤ} {H : ℕ} {B : Block}
    (hg : 0 < g) (hq : 0 < B.q) (hH : 0 < H) (h : canonicalFiniteTest g H B) :
    finiteGapCondition g H B := by
  obtain ⟨v, hv, hgap⟩ := h
  refine ⟨residue g B, offset g B, v, maxGapNumerator v B.q H,
    Int.emod_nonneg _ (ne_of_gt hg), Int.emod_lt_of_pos _ hg,
    offset_identity g B, hv, maxGapNumerator_spec hq hH, ?_⟩
  have hqR : (0 : ℝ) < B.q := by exact_mod_cast hq
  exact (div_le_div_iff_of_pos_right hqR).mp hgap

def slope (v q : ℤ) : AddCircle (1 : ℝ) := ((v : ℝ) / q : ℝ)

def centeredResidue (v q h : ℤ) : ℤ :=
  v * h - q * round (((v * h : ℤ) : ℝ) / q)

lemma centeredResidue_mod (v q h : ℤ) : q ∣ centeredResidue v q h - v * h := by
  refine ⟨-round (((v * h : ℤ) : ℝ) / q), ?_⟩
  simp only [centeredResidue]
  ring

lemma centeredResidue_norm {v q h : ℤ} (hq : 0 < q) :
    ‖h • slope v q‖ = |((centeredResidue v q h : ℤ) : ℝ)| / q := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hr : (h : ℝ) * ((v : ℝ) / q) = ((v * h : ℤ) : ℝ) / q := by push_cast; ring
  unfold slope
  rw [← AddCircle.coe_zsmul, zsmul_eq_mul, hr, AddCircle.norm_eq]
  simp only [inv_one, one_mul, mul_one]
  have ht : ((centeredResidue v q h : ℤ) : ℝ) =
      (q : ℝ) * ((((v * h : ℤ) : ℝ) / q) - round (((v * h : ℤ) : ℝ) / q)) := by
    simp only [centeredResidue, Int.cast_sub, Int.cast_mul]
    field_simp
  rw [ht, abs_mul, abs_of_pos hqR]
  field_simp

lemma int_eq_zero_of_dvd_abs_lt {q h : ℤ} (hq : 0 < q) (hd : q ∣ h)
    (hs : |h| < q) : h = 0 := by
  have hda : q ∣ |h| := (dvd_abs q h).2 hd
  have he := Int.emod_eq_of_lt (abs_nonneg h) hs
  rw [Int.emod_eq_zero_of_dvd hda] at he
  exact abs_eq_zero.mp he.symm

lemma anchor_interval {g r x : ℤ} {B : Block} (hg : 0 < g)
    (hp : 0 < B.p) (hq : 0 < B.q) (hbase : g * x = B.b - B.a + r)
    (hc : cross g B r) : ∃ i : ℤ,
      lower B x ≤ i ∧ (i : ℝ) ≤ upper B x ∧ B.q ∣ B.p * i - x := by
  obtain ⟨i, j, hi, hiL, hj, hjR, heq⟩ := hc
  have hmul : g * (B.p * i - B.q * j - x) = 0 := by
    linear_combination heq - hbase
  have hij : B.p * i - B.q * j - x = 0 :=
    (mul_eq_zero.mp hmul).resolve_left (ne_of_gt hg)
  have hpR : (0 : ℝ) < B.p := by exact_mod_cast hp
  have hqR : (0 : ℝ) < B.q := by exact_mod_cast hq
  have hiR : (0 : ℝ) ≤ i := by exact_mod_cast hi
  have hiLR : (i : ℝ) ≤ B.L := by exact_mod_cast hiL
  have hj0R : (0 : ℝ) ≤ j := by exact_mod_cast hj
  have hjRR : (j : ℝ) ≤ B.R := by exact_mod_cast hjR
  have hijR : (B.p : ℝ) * i - B.q * j - x = 0 := by exact_mod_cast hij
  refine ⟨i, max_le hiR ?_, le_min hiLR ?_, j, ?_⟩
  · apply (div_le_iff₀ hpR).2
    nlinarith
  · apply (le_div_iff₀ hpR).2
    nlinarith
  · linarith

lemma move_inside {l u a t E : ℝ} (ha : l ≤ a) (hau : a ≤ u)
    (hm : E ≤ |t|) (hs : |t| + E ≤ (u - l) / 2) :
    (l + E ≤ a + t ∧ a + t ≤ u - E) ∨
      (l + E ≤ a - t ∧ a - t ≤ u - E) := by
  by_cases ham : a ≤ (l + u) / 2 <;> by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht] at hm hs
    exact Or.inl ⟨by linarith, by linarith⟩
  · rw [abs_of_neg (lt_of_not_ge ht)] at hm hs
    exact Or.inr ⟨by linarith, by linarith⟩
  · rw [abs_of_nonneg ht] at hm hs
    exact Or.inr ⟨by linarith, by linarith⟩
  · rw [abs_of_neg (lt_of_not_ge ht)] at hm hs
    exact Or.inl ⟨by linarith, by linarith⟩

/-- A small nonzero modular shift can be directed toward the interior of
the overlap. The resulting signed difference may use either orientation. -/
lemma cross_small_shift {g r x v h : ℤ} {B : Block}
    (hg : 0 < g) (hp : 0 < B.p) (hq : 0 < B.q)
    (hbase : g * x = B.b - B.a + r) (hc : cross g B r)
    (hinv : B.q ∣ B.p * v - 1) (hne : h ≠ 0)
    (hpbig : |h| < B.p) (hqbig : |h| < B.q)
    (hsmall : |((centeredResidue v B.q h : ℤ) : ℝ)| + |(h : ℝ)| / B.p ≤
      (upper B x - lower B x) / 2) :
    cross g B (r + g * h) ∨ cross g B (r - g * h) := by
  let t := centeredResidue v B.q h
  let E : ℝ := |(h : ℝ)| / B.p
  have htdiv : B.q ∣ B.p * t - h := by
    simpa using inverse_transfer (x := 0) (k := h) hinv
      (by simpa using centeredResidue_mod v B.q h)
  have htne : t ≠ 0 := by
    intro he
    have hh : B.q ∣ h := by simpa [he] using htdiv
    exact hne (int_eq_zero_of_dvd_abs_lt hq hh hqbig)
  have htone : (1 : ℝ) ≤ |(t : ℝ)| := by
    have htpos : (0 : ℤ) < |t| := abs_pos.mpr htne
    have : (1 : ℤ) ≤ |t| := by omega
    exact_mod_cast this
  have hpR : (0 : ℝ) < B.p := by exact_mod_cast hp
  have hE0 : 0 ≤ E := div_nonneg (abs_nonneg _) (le_of_lt hpR)
  have hElt : E < 1 := by
    apply (div_lt_iff₀ hpR).2
    simpa using (show |(h : ℝ)| < (B.p : ℝ) by exact_mod_cast hpbig)
  obtain ⟨i, hil, hiu, hidiv⟩ := anchor_interval hg hp hq hbase hc
  obtain hin | hin := move_inside hil hiu (by linarith : E ≤ |(t : ℝ)|) hsmall
  · left
    have hd : B.q ∣ B.p * (i + t) - (x + h) := by
      convert hidiv.add htdiv using 1 <;> ring
    apply cross_of_common_interval hbase hp hq hE0
      (le_of_eq (by dsimp [E]; field_simp)) _ _ hd
    · simpa using hin.1
    · simpa using hin.2
  · right
    have hd : B.q ∣ B.p * (i - t) - (x + -h) := by
      convert hidiv.sub htdiv using 1 <;> ring
    have hr := cross_of_common_interval (k := -h) hbase hp hq hE0
      (le_of_eq (by dsimp [E]; rw [Int.cast_neg, abs_neg]; field_simp))
      (by simpa using hin.1) (by simpa using hin.2) hd
    simpa only [mul_neg, sub_eq_add_neg] using hr

lemma modelRecurring_subsequence {g d : ℤ} {B : ℕ → Block} {f : ℕ → ℕ}
    (hf : Tendsto f atTop atTop) (hd : modelRecurring g (B ∘ f) d) :
    modelRecurring g B d := by
  apply frequently_atTop.2
  intro N
  obtain ⟨m, hfm, hm⟩ := ((hf.eventually (eventually_ge_atTop N)).and_frequently hd).exists
  exact ⟨f m, hfm, hm⟩

lemma gapBound_mono {S T : Set ℤ} {N : ℤ} (hst : S ⊆ T) (h : gapBound S N) :
    gapBound T N := by
  refine ⟨h.1, fun z => ?_⟩
  obtain ⟨s, hs, hsl, hsu⟩ := h.2 z
  exact ⟨s, hst hs, hsl, hsu⟩

theorem anchored_convergent_near_bohr {g r : ℤ} {δ : ℝ}
    {B : ℕ → Block} {x v : ℕ → ℤ} {α : AddCircle (1 : ℝ)}
    (hg : 0 < g) (hδ : 0 < δ)
    (hp : ∀ n, 0 < (B n).p) (hq : ∀ n, 0 < (B n).q)
    (hpinf : Tendsto (fun n => (B n).p) atTop atTop)
    (hqinf : Tendsto (fun n => (B n).q) atTop atTop)
    (hbase : ∀ n, g * x n = (B n).b - (B n).a + r)
    (hanchor : ∀ n, cross g (B n) r)
    (hinv : ∀ n, (B n).q ∣ (B n).p * v n - 1)
    (hwidth : ∀ᶠ n in atTop, δ * (B n).q ≤ upper (B n) (x n) - lower (B n) (x n))
    (hconv : Tendsto (fun n => slope (v n) (B n).q) atTop (nhds α)) :
    ∀ h : ℤ, ‖h • α‖ < δ / 16 → ∃ s,
      modelRecurring g B s ∧ |s - g * h| ≤ |r| := by
  intro h hh
  by_cases hh0 : h = 0
  · subst h
    refine ⟨r, (Filter.Eventually.of_forall (fun n => cross_occurs (hanchor n))).frequently, ?_⟩
    simp
  have hnf : ∀ᶠ n in atTop, ‖h • slope (v n) (B n).q‖ < δ / 8 :=
    (hconv.zsmul h).norm.eventually (gt_mem_nhds (by linarith))
  obtain ⟨M, hM⟩ := exists_int_gt (8 / δ)
  have hMδ : 8 < (M : ℝ) * δ := (div_lt_iff₀ hδ).mp hM
  have hpf : ∀ᶠ n in atTop, |h| < (B n).p := hpinf.eventually (eventually_gt_atTop _)
  have hqf : ∀ᶠ n in atTop, |h| < (B n).q := hqinf.eventually (eventually_gt_atTop _)
  have hMf : ∀ᶠ n in atTop, M ≤ (B n).q := hqinf.eventually (eventually_ge_atTop _)
  have hcF : ∃ᶠ n in atTop, cross g (B n) (r + g * h) ∨ cross g (B n) (r - g * h) := by
    apply Filter.Eventually.frequently
    filter_upwards [hnf, hpf, hqf, hMf, hwidth] with n hn hpn hqn hMn hwn
    apply cross_small_shift hg (hp n) (hq n) (hbase n) (hanchor n) (hinv n) hh0 hpn hqn
    have hpR : (0 : ℝ) < (B n).p := by exact_mod_cast hp n
    have hqR : (0 : ℝ) < (B n).q := by exact_mod_cast hq n
    rw [centeredResidue_norm (hq n)] at hn
    have ht := (div_lt_iff₀ hqR).mp hn
    have hE : |(h : ℝ)| / (B n).p < 1 := by
      apply (div_lt_iff₀ hpR).2
      simpa using (show |(h : ℝ)| < (B n).p by exact_mod_cast hpn)
    have hMQ : (M : ℝ) ≤ (B n).q := by exact_mod_cast hMn
    have hQ : 8 < δ * (B n).q := by nlinarith
    nlinarith
  rcases frequently_or_distrib.mp hcF with hc | hc
  · refine ⟨r + g * h, hc.mono (fun _ hn => cross_occurs hn), ?_⟩
    simp
  · refine ⟨-(r - g * h), modelRecurring_neg (hc.mono (fun _ hn => cross_occurs hn)), ?_⟩
    have he : -(r - g * h) - g * h = -r := by ring
    rw [he, abs_neg]

theorem anchored_model_syndetic {g r : ℤ} {δ : ℝ}
    {B : ℕ → Block} {x v : ℕ → ℤ}
    (hg : 0 < g) (hδ : 0 < δ)
    (hp : ∀ n, 0 < (B n).p) (hq : ∀ n, 0 < (B n).q)
    (hpinf : Tendsto (fun n => (B n).p) atTop atTop)
    (hqinf : Tendsto (fun n => (B n).q) atTop atTop)
    (hbase : ∀ n, g * x n = (B n).b - (B n).a + r)
    (hanchor : ∀ n, cross g (B n) r)
    (hinv : ∀ n, (B n).q ∣ (B n).p * v n - 1)
    (hwidth : ∀ᶠ n in atTop, δ * (B n).q ≤ upper (B n) (x n) - lower (B n) (x n)) :
    syndetic {s | modelRecurring g B s} := by
  obtain ⟨α, _, f, hf, hconv⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set (AddCircle (1 : ℝ)))).tendsto_subseq
      (fun n => Set.mem_univ (slope (v n) (B n).q))
  have hnear := anchored_convergent_near_bohr (B := B ∘ f) (x := x ∘ f) (v := v ∘ f)
    hg hδ (fun n => hp (f n)) (fun n => hq (f n))
    (hpinf.comp hf.tendsto_atTop) (hqinf.comp hf.tendsto_atTop)
    (fun n => hbase (f n)) (fun n => hanchor (f n))
    (fun n => hinv (f n)) (hf.tendsto_atTop.eventually hwidth) hconv
  obtain ⟨N, hN⟩ := bohr_syndetic α (by positivity : 0 < δ / 16)
  have hscale := gapBound_scale hg hN
  have hresult : gapBound {s | modelRecurring g (B ∘ f) s} (g * N + 2 * |r|) := by
    apply gapBound_nearby (abs_nonneg r) hscale
    rintro _ ⟨h, hh, rfl⟩
    exact hnear h hh
  exact ⟨_, gapBound_mono (fun _ hs => modelRecurring_subsequence hf.tendsto_atTop hs) hresult⟩

def windowWidth (B : Block) (s : ℝ) : ℝ :=
  min (B.L : ℝ) (s + (B.q : ℝ) * B.R / B.p) - max 0 s

def originalWidth (g : ℤ) (B : Block) : ℝ :=
  windowWidth B (((B.b : ℝ) - B.a) / ((g : ℝ) * B.p))

lemma width_eq_window (B : Block) (x : ℤ) :
    upper B x - lower B x = windowWidth B ((x : ℝ) / B.p) := by
  simp only [upper, lower, windowWidth, add_div]

lemma windowWidth_shift (B : Block) (s t : ℝ) :
    windowWidth B s - 2 * |t| ≤ windowWidth B (s + t) := by
  have hl : max 0 (s + t) ≤ max 0 s + |t| := by
    apply max_le
    · linarith [le_max_left (0 : ℝ) s, abs_nonneg t]
    · linarith [le_max_right (0 : ℝ) s, le_abs_self t]
  have hu : min (B.L : ℝ) (s + B.q * B.R / B.p) - |t| ≤
      min (B.L : ℝ) (s + t + B.q * B.R / B.p) := by
    apply le_min
    · linarith [min_le_left (B.L : ℝ) (s + B.q * B.R / B.p), abs_nonneg t]
    · linarith [min_le_right (B.L : ℝ) (s + B.q * B.R / B.p), neg_abs_le t]
  dsimp [windowWidth]
  linarith

lemma anchored_width_lower {g r x : ℤ} {B : Block}
    (hg : 0 < g) (hp : 0 < B.p) (hbase : g * x = B.b - B.a + r) :
    originalWidth g B - 2 * |(r : ℝ)| / ((g : ℝ) * B.p) ≤
      upper B x - lower B x := by
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hpR : (0 : ℝ) < B.p := by exact_mod_cast hp
  have heq : (x : ℝ) / B.p =
      ((B.b : ℝ) - B.a) / ((g : ℝ) * B.p) + (r : ℝ) / ((g : ℝ) * B.p) := by
    have hbaseR : (g : ℝ) * x = (B.b : ℝ) - B.a + r := by exact_mod_cast hbase
    field_simp
    nlinarith
  rw [width_eq_window, heq]
  have hw := windowWidth_shift B (((B.b : ℝ) - B.a) / ((g : ℝ) * B.p))
    ((r : ℝ) / ((g : ℝ) * B.p))
  simpa only [originalWidth, abs_div, abs_of_pos (mul_pos hgR hpR), mul_div_assoc] using hw

lemma cross_base {g r : ℤ} {B : Block} (hc : cross g B r) :
    ∃ x : ℤ, g * x = B.b - B.a + r := by
  obtain ⟨i, j, _, _, _, _, hij⟩ := hc
  refine ⟨B.p * i - B.q * j, ?_⟩
  linear_combination hij

lemma eventual_anchored_width {g r : ℤ} {δ : ℝ} {B : ℕ → Block} {x : ℕ → ℤ}
    (hg : 0 < g) (hδ : 0 < δ)
    (hp : ∀ n, 0 < (B n).p) (hq : ∀ n, 0 < (B n).q)
    (hpinf : Tendsto (fun n => (B n).p) atTop atTop)
    (hx : ∀ n, g * x n = (B n).b - (B n).a + r)
    (hw : ∀ n, δ * (B n).q ≤ originalWidth g (B n)) :
    ∀ᶠ n in atTop, δ / 2 * (B n).q ≤ upper (B n) (x n) - lower (B n) (x n) := by
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  obtain ⟨M, hM⟩ := exists_int_gt (4 * |(r : ℝ)| / (δ * g))
  have hMd : 4 * |(r : ℝ)| < (M : ℝ) * (δ * g) :=
    (div_lt_iff₀ (mul_pos hδ hgR)).mp hM
  filter_upwards [hpinf.eventually (eventually_ge_atTop M)] with n hn
  have hpR : (0 : ℝ) < (B n).p := by exact_mod_cast hp n
  have hMn : (M : ℝ) ≤ (B n).p := by exact_mod_cast hn
  have hQ : (1 : ℝ) ≤ (B n).q := by exact_mod_cast (show (1 : ℤ) ≤ (B n).q by have := hq n; omega)
  have hcorr : 2 * |(r : ℝ)| / ((g : ℝ) * (B n).p) ≤ δ / 2 := by
    apply (div_le_iff₀ (mul_pos hgR hpR)).2
    have hmul := mul_le_mul_of_nonneg_right hMn (le_of_lt (mul_pos hδ hgR))
    nlinarith
  have ha := anchored_width_lower hg (hp n) (hx n)
  have hwn := hw n
  nlinarith

/-- Bounded contact and a positive normalized overlap force recurrent
modeled differences to have bounded gaps. -/
theorem bounded_contact_model {g K : ℤ} {δ : ℝ} {B : ℕ → Block} {v : ℕ → ℤ}
    (hg : 0 < g) (hδ : 0 < δ)
    (hp : ∀ n, 0 < (B n).p) (hq : ∀ n, 0 < (B n).q)
    (hpinf : Tendsto (fun n => (B n).p) atTop atTop)
    (hqinf : Tendsto (fun n => (B n).q) atTop atTop)
    (hinv : ∀ n, (B n).q ∣ (B n).p * v n - 1)
    (hgood : ∃ᶠ n in atTop, δ * (B n).q ≤ originalWidth g (B n) ∧
      ∃ r : ℤ, |r| ≤ K ∧ cross g (B n) r) :
    syndetic {s | modelRecurring g B s} := by
  classical
  have hr : ∃ᶠ n in atTop, ∃ r ∈ Set.Icc (-K) K,
      δ * (B n).q ≤ originalWidth g (B n) ∧ cross g (B n) r := by
    apply hgood.mono
    rintro n ⟨hw, r, hr, hc⟩
    exact ⟨r, abs_le.mp hr, hw, hc⟩
  obtain ⟨r, _, hrF⟩ := (Set.finite_Icc _ _).frequently_exists.mp hr
  obtain ⟨f, hf, hfall⟩ := Filter.subseq_forall_of_frequently
    (p := fun n => δ * (B n).q ≤ originalWidth g (B n) ∧ cross g (B n) r)
    tendsto_id hrF
  choose x hx using (fun n => cross_base (hfall n).2)
  have hws := eventual_anchored_width (B := B ∘ f) hg hδ
    (fun n => hp (f n)) (fun n => hq (f n)) (hpinf.comp hf) hx (fun n => (hfall n).1)
  obtain ⟨N, hN⟩ := anchored_model_syndetic (B := B ∘ f) (v := v ∘ f)
    hg (by positivity : 0 < δ / 2) (fun n => hp (f n)) (fun n => hq (f n))
    (hpinf.comp hf) (hqinf.comp hf) hx (fun n => (hfall n).2) (fun n => hinv (f n)) hws
  exact ⟨N, gapBound_mono (fun _ hs => modelRecurring_subsequence hf hs) hN⟩

theorem bounded_contact {A : Set ℕ} {g C K : ℤ} {δ : ℝ}
    {B : ℕ → Block} {v : ℕ → ℤ}
    (hg : 0 < g) (hC : 0 ≤ C) (hδ : 0 < δ)
    (hp : ∀ n, 0 < (B n).p) (hq : ∀ n, 0 < (B n).q)
    (hpinf : Tendsto (fun n => (B n).p) atTop atTop)
    (hqinf : Tendsto (fun n => (B n).q) atTop atTop)
    (hinv : ∀ n, (B n).q ∣ (B n).p * v n - 1)
    (ha : approximates A g C B) (he : escapes g B)
    (hgood : ∃ᶠ n in atTop, δ * (B n).q ≤ originalWidth g (B n) ∧
      ∃ r : ℤ, |r| ≤ K ∧ cross g (B n) r) : syndetic (differences A) := by
  obtain ⟨N, hN⟩ := bounded_contact_model hg hδ hp hq hpinf hqinf hinv hgood
  exact ⟨N + 4 * C, transfer_gapBound hC ha he hN⟩

/-- With an exact common point, the recurrent differences contain a
neighborhood of zero in a rotation, after multiplication by `g`. -/
theorem common_point_bohr_subset {A : Set ℕ} {g : ℤ} {δ : ℝ}
    {B : ℕ → Block} {v : ℕ → ℤ}
    (hg : 0 < g) (hδ : 0 < δ)
    (hp : ∀ n, 0 < (B n).p) (hq : ∀ n, 0 < (B n).q)
    (hpinf : Tendsto (fun n => (B n).p) atTop atTop)
    (hqinf : Tendsto (fun n => (B n).q) atTop atTop)
    (hinv : ∀ n, (B n).q ∣ (B n).p * v n - 1)
    (ha : approximates A g 0 B) (he : escapes g B)
    (hanchor : ∀ n, cross g (B n) 0)
    (hw : ∀ n, δ * (B n).q ≤ originalWidth g (B n)) :
    ∃ α : AddCircle (1 : ℝ), ∀ h : ℤ, ‖h • α‖ < δ / 16 → recurring A (g * h) := by
  classical
  choose x hx using (fun n => cross_base (hanchor n))
  have hwidth : ∀ᶠ n in atTop, δ * (B n).q ≤ upper (B n) (x n) - lower (B n) (x n) := by
    apply Filter.Eventually.of_forall
    intro n
    have hlow := anchored_width_lower hg (hp n) (hx n)
    simp only [Int.cast_zero, abs_zero, mul_zero, zero_div, sub_zero] at hlow
    exact le_trans (hw n) hlow
  obtain ⟨α, _, f, hf, hconv⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set (AddCircle (1 : ℝ)))).tendsto_subseq
      (fun n => Set.mem_univ (slope (v n) (B n).q))
  have hnear := anchored_convergent_near_bohr (B := B ∘ f) (x := x ∘ f) (v := v ∘ f)
    hg hδ (fun n => hp (f n)) (fun n => hq (f n))
    (hpinf.comp hf.tendsto_atTop) (hqinf.comp hf.tendsto_atTop)
    (fun n => hx (f n)) (fun n => hanchor (f n))
    (fun n => hinv (f n)) (hf.tendsto_atTop.eventually hwidth) hconv
  refine ⟨α, fun h hh => ?_⟩
  obtain ⟨s, hs, hsd⟩ := hnear h hh
  have hsg : s = g * h := sub_eq_zero.mp (by simpa using hsd)
  obtain ⟨d, hd, hds⟩ := transfer_recurring ha he (modelRecurring_subsequence hf.tendsto_atTop hs)
  have hdeq : d = s := sub_eq_zero.mp (by simpa using hds)
  simpa [differences, hdeq, hsg] using hd

lemma finite_positive_lower {ι : Type*} [Fintype ι] (d : ι → ℝ) (hd : ∀ i, 0 < d i) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, ε ≤ d i := by
  classical
  have hf : ∀ s : Finset ι, ∃ ε : ℝ, 0 < ε ∧ ∀ i ∈ s, ε ≤ d i := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by norm_num, by simp⟩
    | @insert a s ha ih =>
      obtain ⟨ε, hε, hle⟩ := ih
      refine ⟨min (d a) ε, lt_min (hd a) hε, ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact min_le_left _ _
      · exact le_trans (min_le_right _ _) (hle i hi)
  obtain ⟨ε, hε, hle⟩ := hf Finset.univ
  exact ⟨ε, hε, fun i => hle i (Finset.mem_univ i)⟩

/-- Simultaneous recurrence for a finite family of exact common-point
progression pairs. Centered progression pairs satisfy these hypotheses. -/
theorem finite_common_point_intersection {ι : Type*} [Fintype ι]
    {A : ι → Set ℕ} {g : ι → ℤ} {δ : ι → ℝ}
    {B : ι → ℕ → Block} {v : ι → ℕ → ℤ}
    (hg : ∀ i, 0 < g i) (hδ : ∀ i, 0 < δ i)
    (hp : ∀ i n, 0 < (B i n).p) (hq : ∀ i n, 0 < (B i n).q)
    (hpinf : ∀ i, Tendsto (fun n => (B i n).p) atTop atTop)
    (hqinf : ∀ i, Tendsto (fun n => (B i n).q) atTop atTop)
    (hinv : ∀ i n, (B i n).q ∣ (B i n).p * v i n - 1)
    (ha : ∀ i, approximates (A i) (g i) 0 (B i)) (he : ∀ i, escapes (g i) (B i))
    (hanchor : ∀ i n, cross (g i) (B i n) 0)
    (hw : ∀ i n, δ i * (B i n).q ≤ originalWidth (g i) (B i n)) :
    syndetic (⋂ i, differences (A i)) := by
  classical
  choose α hα using (fun i => common_point_bohr_subset (hg i) (hδ i) (hp i) (hq i)
    (hpinf i) (hqinf i) (hinv i) (ha i) (he i) (hanchor i) (hw i))
  obtain ⟨ε, hε, hεle⟩ := finite_positive_lower (fun i => δ i / 16)
    (by intro i; exact div_pos (hδ i) (by norm_num))
  let G : ℤ := ∏ i, g i
  have hG : 0 < G := Finset.prod_pos (fun i _ => hg i)
  have hdiv : ∀ i, g i ∣ G := by
    intro i
    exact Finset.dvd_prod_of_mem g (Finset.mem_univ i)
  choose e heq using hdiv
  let γ : ι → AddCircle (1 : ℝ) := fun i => e i • α i
  obtain ⟨N, hN⟩ := bohr_syndetic γ hε
  refine ⟨G * N, gapBound_mono ?_ (gapBound_scale hG hN)⟩
  rintro _ ⟨k, hk, rfl⟩
  simp only [Set.mem_iInter]
  intro i
  have hi : ‖(e i * k) • α i‖ < δ i / 16 := by
    have hcomp : ‖(k • γ) i‖ ≤ ‖k • γ‖ := norm_le_pi_norm (k • γ) i
    have hb := lt_of_le_of_lt hcomp hk
    have he : (k • γ) i = (e i * k) • α i := by
      simp only [Pi.smul_apply, γ, smul_smul, mul_comm]
    rw [he] at hb
    exact lt_of_lt_of_le hb (hεle i)
  have hmem := hα i (e i * k) hi
  have he : G * k = g i * (e i * k) := by rw [heq i]; ring
  change recurring (A i) (G * k)
  simpa [he] using hmem

def hullOverlap (g : ℤ) (B : Block) (r : ℤ := 0) : ℝ :=
  max 0 (min ((B.a : ℝ) + g * B.p * B.L) ((B.b : ℝ) + r + g * B.q * B.R) -
    max (B.a : ℝ) ((B.b : ℝ) + r))

lemma affine_min {a c x y : ℝ} (hc : 0 < c) :
    min (a + c * x) (a + c * y) = a + c * min x y := by
  by_cases h : x ≤ y
  · rw [min_eq_left h, min_eq_left (by nlinarith)]
  · rw [min_eq_right (le_of_not_ge h), min_eq_right (by nlinarith)]

lemma affine_max {a c x y : ℝ} (hc : 0 < c) :
    max (a + c * x) (a + c * y) = a + c * max x y := by
  by_cases h : x ≤ y
  · rw [max_eq_right h, max_eq_right (by nlinarith)]
  · rw [max_eq_left (le_of_not_ge h), max_eq_left (by nlinarith)]

lemma hullOverlap_eq_window {g : ℤ} {B : Block} (hg : 0 < g) (hp : 0 < B.p) (r : ℤ) :
    hullOverlap g B r = (g : ℝ) * B.p *
      max 0 (windowWidth B (((B.b : ℝ) + r - B.a) / ((g : ℝ) * B.p))) := by
  let c : ℝ := (g : ℝ) * B.p
  let s : ℝ := ((B.b : ℝ) + r - B.a) / c
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hpR : (0 : ℝ) < B.p := by exact_mod_cast hp
  have hc : 0 < c := mul_pos hgR hpR
  have hs : c * s = (B.b : ℝ) + r - B.a := by dsimp [s]; field_simp
  have hb : (B.b : ℝ) + r = B.a + c * s := by linarith
  have he : (B.b : ℝ) + r + (g : ℝ) * B.q * B.R =
      B.a + c * (s + (B.q : ℝ) * B.R / B.p) := by
    rw [hb]
    dsimp [c]
    field_simp
    ring
  have hm : min ((B.a : ℝ) + g * B.p * B.L) ((B.b : ℝ) + r + g * B.q * B.R) =
      B.a + c * min (B.L : ℝ) (s + (B.q : ℝ) * B.R / B.p) := by
    rw [he]
    exact affine_min hc
  have hM : max (B.a : ℝ) ((B.b : ℝ) + r) = B.a + c * max 0 s := by
    rw [hb]
    simpa using (affine_max (a := (B.a : ℝ)) (x := 0) (y := s) hc)
  have hd : min ((B.a : ℝ) + g * B.p * B.L) ((B.b : ℝ) + r + g * B.q * B.R) -
      max (B.a : ℝ) ((B.b : ℝ) + r) = c * windowWidth B s := by
    rw [hm, hM]
    dsimp [windowWidth]
    ring
  unfold hullOverlap
  rw [hd]
  simpa [c, s] using (affine_max (a := 0) (x := 0) (y := windowWidth B s) hc)

theorem overlap_implies_originalWidth {g : ℤ} {B : Block} {δ : ℝ}
    (hg : 0 < g) (hp : 0 < B.p) (hq : 0 < B.q) (hδ : 0 < δ)
    (h : δ ≤ hullOverlap g B / ((g : ℝ) * B.p * B.q)) :
    δ * B.q ≤ originalWidth g B := by
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hpR : (0 : ℝ) < B.p := by exact_mod_cast hp
  have hqR : (0 : ℝ) < B.q := by exact_mod_cast hq
  have he : hullOverlap g B / ((g : ℝ) * B.p * B.q) = max 0 (originalWidth g B) / B.q := by
    rw [hullOverlap_eq_window hg hp 0]
    dsimp [originalWidth]
    simp only [Int.cast_zero, add_zero]
    field_simp
  rw [he] at h
  have hmul := (le_div_iff₀ hqR).mp h
  by_cases hw : 0 ≤ originalWidth g B
  · simpa only [max_eq_right hw] using hmul
  · rw [max_eq_left (le_of_not_ge hw)] at hmul
    nlinarith

/-- Bounded-contact sufficient condition using literal hull lengths. -/
theorem bounded_contact_hulls {A : Set ℕ} {g C K : ℤ} {δ : ℝ}
    {B : ℕ → Block} {v : ℕ → ℤ}
    (hg : 0 < g) (hC : 0 ≤ C) (hδ : 0 < δ)
    (hp : ∀ n, 0 < (B n).p) (hq : ∀ n, 0 < (B n).q)
    (hpinf : Tendsto (fun n => (B n).p) atTop atTop)
    (hqinf : Tendsto (fun n => (B n).q) atTop atTop)
    (hinv : ∀ n, (B n).q ∣ (B n).p * v n - 1)
    (ha : approximates A g C B) (he : escapes g B)
    (hgood : ∃ᶠ n in atTop,
      δ ≤ hullOverlap g (B n) / ((g : ℝ) * (B n).p * (B n).q) ∧
        ∃ r : ℤ, |r| ≤ K ∧ cross g (B n) r) : syndetic (differences A) := by
  apply bounded_contact hg hC hδ hp hq hpinf hqinf hinv ha he
  exact hgood.mono (fun n hn =>
    ⟨overlap_implies_originalWidth hg (hp n) (hq n) hδ hn.1, hn.2⟩)

lemma translated_overlap_implies_width {g r x : ℤ} {B : Block} {δ : ℝ}
    (hg : 0 < g) (hp : 0 < B.p) (hq : 0 < B.q) (hδ : 0 < δ)
    (hx : g * x = B.b - B.a + r)
    (h : δ ≤ hullOverlap g B r / ((g : ℝ) * B.p * B.q)) :
    δ * B.q ≤ upper B x - lower B x := by
  let B' : Block := {B with b := B.b + r}
  have h' : δ ≤ hullOverlap g B' / ((g : ℝ) * B'.p * B'.q) := by
    simpa [B', hullOverlap] using h
  have hw := overlap_implies_originalWidth (B := B') hg hp hq hδ h'
  have hx' : g * x = B'.b - B'.a + 0 := by dsimp [B']; linarith
  have hb := anchored_width_lower (B := B') hg hp hx'
  simp only [Int.cast_zero, abs_zero, mul_zero, zero_div, sub_zero] at hb
  exact le_trans hw hb

def finiteHullTest (g : ℤ) (H : ℕ) (B : Block) : Prop :=
  ∃ v : ℤ, B.q ∣ B.p * v - 1 ∧
    circularGap v B.q H ≤ hullOverlap g B (residue g B) / ((g : ℝ) * B.p * B.q)

lemma finiteHullTest_implies {g : ℤ} {H : ℕ} {B : Block}
    (hg : 0 < g) (hp : 0 < B.p) (hq : 0 < B.q) (hH : 0 < H)
    (h : finiteHullTest g H B) : finiteGapCondition g H B := by
  obtain ⟨v, hv, hgap⟩ := h
  apply canonicalFiniteTest_implies hg hq hH
  refine ⟨v, hv, ?_⟩
  have hnum := (maxGapNumerator_spec (v := v) hq hH).1
  have hnumR : (0 : ℝ) < (maxGapNumerator v B.q H : ℝ) := by exact_mod_cast hnum
  have hqR : (0 : ℝ) < B.q := by exact_mod_cast hq
  have hpos : 0 < circularGap v B.q H := div_pos hnumR hqR
  have hwidth := translated_overlap_implies_width hg hp hq hpos (offset_identity g B) hgap
  exact (le_div_iff₀ hqR).2 (by simpa [mul_comm] using hwidth)

/-- The quantitative theorem in terms of real hull overlap and the largest
circular gap of the normalized modular inverse. -/
theorem finite_test_hulls {A : Set ℕ} {g C : ℤ} {H : ℕ} {B : ℕ → Block}
    (hg : 0 < g) (hC : 0 ≤ C) (hH : 0 < H)
    (hp : ∀ n, 0 < (B n).p) (hq : ∀ n, 0 < (B n).q)
    (hpinf : Tendsto (fun n => (B n).p) atTop atTop)
    (hqinf : Tendsto (fun n => (B n).q) atTop atTop)
    (ha : approximates A g C B) (he : escapes g B)
    (hgood : ∃ᶠ n in atTop, finiteHullTest g H (B n)) :
    gapBound (differences A) (2 * g * H + 4 * C) := by
  exact finite_test hg hC hH hp hq hpinf hqinf ha he
    (hgood.mono (fun n hn => finiteHullTest_implies hg (hp n) (hq n) hH hn))

lemma inverse_of_coprime {p q : ℤ} (h : IsCoprime p q) : ∃ v : ℤ, q ∣ p * v - 1 := by
  obtain ⟨v, w, h⟩ := h
  refine ⟨v, -w, ?_⟩
  linear_combination h

lemma escapes_of_min_bases {g : ℤ} {B : ℕ → Block} (hg : 0 < g)
    (hp : ∀ n, 0 ≤ (B n).p) (hq : ∀ n, 0 ≤ (B n).q)
    (hm : Tendsto (fun n => min (B n).a (B n).b) atTop atTop) : escapes g B := by
  intro K
  filter_upwards [hm.eventually (eventually_ge_atTop K)] with n hn
  intro u hu
  have ha : K ≤ (B n).a := le_trans hn (min_le_left _ _)
  have hb : K ≤ (B n).b := le_trans hn (min_le_right _ _)
  rcases hu with ⟨i, hi, _, rfl⟩ | ⟨j, hj, _, rfl⟩
  · have := mul_nonneg (mul_nonneg (le_of_lt hg) (hp n)) hi
    omega
  · have := mul_nonneg (mul_nonneg (le_of_lt hg) (hq n)) hj
    omega

/-- The bounded-contact theorem with coprimality and the original escaping
base condition, without a supplied modular-inverse sequence. -/
theorem main_bounded_contact {A : Set ℕ} {g C K : ℤ} {δ : ℝ} {B : ℕ → Block}
    (hg : 0 < g) (hC : 0 ≤ C) (hδ : 0 < δ)
    (hp : ∀ n, 0 < (B n).p) (hq : ∀ n, 0 < (B n).q)
    (hcop : ∀ n, IsCoprime (B n).p (B n).q)
    (hpinf : Tendsto (fun n => (B n).p) atTop atTop)
    (hqinf : Tendsto (fun n => (B n).q) atTop atTop)
    (hbases : Tendsto (fun n => min (B n).a (B n).b) atTop atTop)
    (ha : approximates A g C B)
    (hgood : ∃ᶠ n in atTop,
      δ ≤ hullOverlap g (B n) / ((g : ℝ) * (B n).p * (B n).q) ∧
        ∃ r : ℤ, |r| ≤ K ∧ cross g (B n) r) : syndetic (differences A) := by
  choose v hv using (fun n => inverse_of_coprime (hcop n))
  exact bounded_contact_hulls hg hC hδ hp hq hpinf hqinf hv ha
    (escapes_of_min_bases hg (fun n => le_of_lt (hp n)) (fun n => le_of_lt (hq n)) hbases) hgood

/-- The finite-test theorem with the original escaping base condition. -/
theorem main_finite_test {A : Set ℕ} {g C : ℤ} {H : ℕ} {B : ℕ → Block}
    (hg : 0 < g) (hC : 0 ≤ C) (hH : 0 < H)
    (hp : ∀ n, 0 < (B n).p) (hq : ∀ n, 0 < (B n).q)
    (hpinf : Tendsto (fun n => (B n).p) atTop atTop)
    (hqinf : Tendsto (fun n => (B n).q) atTop atTop)
    (hbases : Tendsto (fun n => min (B n).a (B n).b) atTop atTop)
    (ha : approximates A g C B)
    (hgood : ∃ᶠ n in atTop, finiteHullTest g H (B n)) :
    gapBound (differences A) (2 * g * H + 4 * C) := by
  exact finite_test_hulls hg hC hH hp hq hpinf hqinf ha
    (escapes_of_min_bases hg (fun n => le_of_lt (hp n)) (fun n => le_of_lt (hq n)) hbases) hgood

def centeredBlock (g c p q L R : ℤ) : Block where
  a := c - g * p * L
  b := c - g * q * R
  p := p
  q := q
  L := 2 * L
  R := 2 * R

lemma centeredBlock_cross (g c p q L R : ℤ) (hL : 0 ≤ L) (hR : 0 ≤ R) :
    cross g (centeredBlock g c p q L R) 0 := by
  refine ⟨L, R, hL, by dsimp [centeredBlock]; omega,
    hR, by dsimp [centeredBlock]; omega, ?_⟩
  dsimp [centeredBlock]
  ring

lemma centeredBlock_width {g c p q L R : ℤ} {δ : ℝ}
    (hg : 0 < g) (hp : 0 < p) (hq : 0 < q) (hδ : 0 < δ)
    (hL : δ * q ≤ (L : ℝ)) (hR : δ * p ≤ (R : ℝ)) :
    δ * q ≤ originalWidth g (centeredBlock g c p q L R) := by
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hratio : δ * q ≤ (q : ℝ) * R / p := by
    apply (le_div_iff₀ hpR).2
    nlinarith [mul_le_mul_of_nonneg_left hR (le_of_lt hqR)]
  have hnorm : (((c - g * q * R : ℤ) : ℝ) - ((c - g * p * L : ℤ) : ℝ)) /
      ((g : ℝ) * p) = (L : ℝ) - (q : ℝ) * R / p := by
    push_cast
    field_simp
    ring
  unfold originalWidth
  change δ * q ≤ windowWidth (centeredBlock g c p q L R)
    ((((c - g * q * R : ℤ) : ℝ) - ((c - g * p * L : ℤ) : ℝ)) / ((g : ℝ) * p))
  rw [hnorm]
  dsimp [windowWidth, centeredBlock]
  push_cast
  have hu : (L : ℝ) + δ * q ≤ min (2 * (L : ℝ))
      ((L : ℝ) - (q : ℝ) * R / p + q * (2 * (R : ℝ)) / p) := by
    apply le_min
    · linarith
    · have hid : (q : ℝ) * (2 * (R : ℝ)) / p = 2 * ((q : ℝ) * R / p) := by ring
      rw [hid]
      linarith
  have hl : max 0 ((L : ℝ) - (q : ℝ) * R / p) ≤ (L : ℝ) - δ * q := by
    apply max_le <;> linarith
  nlinarith

/-- The centered finite-family theorem stated directly for the two
progressions about each specified center. -/
theorem centered_finite_intersection {ι : Type*} [Fintype ι]
    {A : ι → Set ℕ} {g : ι → ℤ} {δ : ι → ℝ}
    {c p q L R : ι → ℕ → ℤ}
    (hg : ∀ i, 0 < g i) (hδ : ∀ i, 0 < δ i)
    (hp : ∀ i n, 0 < p i n) (hq : ∀ i n, 0 < q i n)
    (hcop : ∀ i n, IsCoprime (p i n) (q i n))
    (hpinf : ∀ i, Tendsto (p i) atTop atTop) (hqinf : ∀ i, Tendsto (q i) atTop atTop)
    (hL0 : ∀ i n, 0 ≤ L i n) (hR0 : ∀ i n, 0 ≤ R i n)
    (hL : ∀ i n, δ i * q i n ≤ (L i n : ℝ))
    (hR : ∀ i n, δ i * p i n ≤ (R i n : ℝ))
    (ha : ∀ i, approximates (A i) (g i) 0
      (fun n => centeredBlock (g i) (c i n) (p i n) (q i n) (L i n) (R i n)))
    (he : ∀ i, escapes (g i)
      (fun n => centeredBlock (g i) (c i n) (p i n) (q i n) (L i n) (R i n))) :
    syndetic (⋂ i, differences (A i)) := by
  classical
  choose v hv using (fun i n => inverse_of_coprime (hcop i n))
  exact finite_common_point_intersection hg hδ hp hq hpinf hqinf hv ha he
    (fun i n => centeredBlock_cross _ _ _ _ _ _ (hL0 i n) (hR0 i n))
    (fun i n => centeredBlock_width (hg i) (hp i n) (hq i n) (hδ i) (hL i n) (hR i n))

end
end Erdos332
