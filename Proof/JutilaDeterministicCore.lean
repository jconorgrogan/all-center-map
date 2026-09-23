import Mathlib

/-!
# Deterministic core of Jutila's Theorem 1 proof

This staging module formalizes the finite Hilbert-space inequality underlying
Jutila, *On Linnik's constant* (1977), Lemma 7, and the exact exponent
arithmetic for the parameters chosen on journal page 52.

It does not assert a zero-density theorem, a detector lower bound, a local
zero-count estimate, or Graham's sieve asymptotic.
-/

namespace MAPJutilaDeterministicCore

open scoped BigOperators ComplexConjugate

noncomputable section

/-! ## The binning and parity compression before Lemma 6 -/

/-- If every occupied character/height box contains at most `H` zeros, the
full finite zero set is at most `H` times the number of occupied boxes.  This
is the multiplicity-aware finite core of the reduction using Jutila's Lemma 8
after equation (3.1). -/
theorem card_le_fiberCap_mul_occupied
    {Z B : Type*} [DecidableEq Z] [DecidableEq B]
    (zeros : Finset Z) (box : Z → B) (H : ℕ)
    (hcap : ∀ b ∈ zeros.image box,
      (zeros.filter fun z => box z = b).card ≤ H) :
    zeros.card ≤ H * (zeros.image box).card := by
  rw [Finset.card_eq_sum_card_fiberwise
    (t := zeros.image box) (f := box)
    (fun z hz => Finset.mem_image_of_mem box hz)]
  calc
    (∑ b ∈ zeros.image box,
        (zeros.filter fun z => box z = b).card) ≤
        ∑ _b ∈ zeros.image box, H := by
      apply Finset.sum_le_sum
      intro b hb
      exact hcap b hb
    _ = H * (zeros.image box).card := by
      simp [mul_comm]

/-- Splitting the occupied boxes by parity (or any decidable two-coloring)
leaves one color containing at least half of them. -/
theorem occupied_le_two_mul_larger_color
    {B : Type*} [DecidableEq B]
    (occupied : Finset B) (color : B → Prop)
    [DecidablePred color] [∀ b, Decidable (¬ color b)] :
    occupied.card ≤ 2 * max (occupied.filter color).card
      (occupied.filter fun b => ¬ color b).card := by
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := occupied) color
  have hleft : (occupied.filter color).card ≤
      max (occupied.filter color).card
        (occupied.filter fun b => ¬ color b).card := Nat.le_max_left _ _
  have hright : (occupied.filter fun b => ¬ color b).card ≤
      max (occupied.filter color).card
        (occupied.filter fun b => ¬ color b).card := Nat.le_max_right _ _
  omega

/-- Combined source reduction: a local Lemma-8 cap and the even/odd split
cost only `2*H` relative to the larger well-spaced box system. -/
theorem card_le_two_mul_fiberCap_mul_larger_color
    {Z B : Type*} [DecidableEq Z] [DecidableEq B]
    (zeros : Finset Z) (box : Z → B) (H : ℕ)
    (color : B → Prop) [DecidablePred color]
    [∀ b, Decidable (¬ color b)]
    (hcap : ∀ b ∈ zeros.image box,
      (zeros.filter fun z => box z = b).card ≤ H) :
    zeros.card ≤ 2 * H *
      max ((zeros.image box).filter color).card
        ((zeros.image box).filter fun b => ¬ color b).card := by
  have hfiber := card_le_fiberCap_mul_occupied zeros box H hcap
  have hcolor := occupied_le_two_mul_larger_color (zeros.image box) color
  nlinarith

/-- Multiplicity-aware version of the source-box compression.  This is the
form needed when the zero divisor is represented by its finite support plus
analytic multiplicity rather than by a list with repeated points. -/
theorem multiplicitySum_le_fiberCap_mul_occupied
    {Z B : Type*} [DecidableEq Z] [DecidableEq B]
    (zeros : Finset Z) (multiplicity : Z → ℕ) (box : Z → B) (H : ℕ)
    (hcap : ∀ b ∈ zeros.image box,
      ∑ z ∈ zeros with box z = b, multiplicity z ≤ H) :
    ∑ z ∈ zeros, multiplicity z ≤ H * (zeros.image box).card := by
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := zeros) (t := zeros.image box) (g := box)
    (fun z hz => Finset.mem_image_of_mem box hz) multiplicity]
  calc
    (∑ b ∈ zeros.image box,
        ∑ z ∈ zeros with box z = b, multiplicity z) ≤
        ∑ _b ∈ zeros.image box, H := by
      apply Finset.sum_le_sum
      intro b hb
      exact hcap b hb
    _ = H * (zeros.image box).card := by simp [mul_comm]

/-- Appendix-A.5-compatible multiplicity compression followed by Jutila's
even/odd source-box split. -/
theorem multiplicitySum_le_two_mul_fiberCap_mul_larger_color
    {Z B : Type*} [DecidableEq Z] [DecidableEq B]
    (zeros : Finset Z) (multiplicity : Z → ℕ) (box : Z → B) (H : ℕ)
    (color : B → Prop) [DecidablePred color]
    [∀ b, Decidable (¬ color b)]
    (hcap : ∀ b ∈ zeros.image box,
      ∑ z ∈ zeros with box z = b, multiplicity z ≤ H) :
    ∑ z ∈ zeros, multiplicity z ≤ 2 * H *
      max ((zeros.image box).filter color).card
        ((zeros.image box).filter fun b => ¬ color b).card := by
  have hfiber := multiplicitySum_le_fiberCap_mul_occupied
    zeros multiplicity box H hcap
  have hcolor := occupied_le_two_mul_larger_color (zeros.image box) color
  nlinarith

/-! ## The phase alignment used in Halasz's inequality -/

def alignPhase (z : ℂ) : ℂ :=
  if z = 0 then 1 else conj z / (‖z‖ : ℂ)

theorem norm_alignPhase (z : ℂ) : ‖alignPhase z‖ = 1 := by
  by_cases hz : z = 0
  · simp [alignPhase, hz]
  · rw [alignPhase, if_neg hz, norm_div, Complex.norm_conj, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z), div_self]
    exact norm_ne_zero_iff.mpr hz

theorem alignPhase_mul (z : ℂ) : alignPhase z * z = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · simp [alignPhase, hz]
  · rw [alignPhase, if_neg hz]
    have hn : (‖z‖ : ℂ) ≠ 0 := by
      exact_mod_cast (norm_ne_zero_iff.mpr hz)
    field_simp [hn]
    change conj z * z = (‖z‖ : ℂ) ^ 2
    rw [mul_comm, Complex.mul_conj, ← Complex.sq_norm]
    norm_cast

/-! ## A finite weighted Cauchy inequality -/

theorem weighted_norm_sum_sq_le
    {K : Type*} [DecidableEq K]
    (s : Finset K) (a u : K → ℂ) (b : K → ℝ)
    (hb : ∀ k ∈ s, 0 < b k) :
    ‖∑ k ∈ s, a k * u k‖ ^ 2 ≤
      (∑ k ∈ s, ‖a k‖ ^ 2 / b k) *
        ∑ k ∈ s, b k * ‖u k‖ ^ 2 := by
  have htriangle : ‖∑ k ∈ s, a k * u k‖ ≤
      ∑ k ∈ s, ‖a k‖ * ‖u k‖ := by
    calc
      ‖∑ k ∈ s, a k * u k‖ ≤ ∑ k ∈ s, ‖a k * u k‖ := norm_sum_le _ _
      _ = ∑ k ∈ s, ‖a k‖ * ‖u k‖ := by
        apply Finset.sum_congr rfl
        intro k hk
        exact norm_mul _ _
  have hsum_nonneg : 0 ≤ ∑ k ∈ s, ‖a k‖ * ‖u k‖ := by positivity
  have hsquare := pow_le_pow_left₀ (norm_nonneg _) htriangle 2
  refine hsquare.trans ?_
  let f : K → ℝ := fun k => ‖a k‖ / Real.sqrt (b k)
  let g : K → ℝ := fun k => Real.sqrt (b k) * ‖u k‖
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq s f g
  have hprod : (∑ k ∈ s, f k * g k) =
      ∑ k ∈ s, ‖a k‖ * ‖u k‖ := by
    apply Finset.sum_congr rfl
    intro k hk
    have hbpos := hb k hk
    have hsqrt : Real.sqrt (b k) ≠ 0 := (Real.sqrt_pos.2 hbpos).ne'
    dsimp [f, g]
    field_simp [hsqrt]
  have hf : (∑ k ∈ s, f k ^ 2) =
      ∑ k ∈ s, ‖a k‖ ^ 2 / b k := by
    apply Finset.sum_congr rfl
    intro k hk
    have hbpos := hb k hk
    have hsqrt : Real.sqrt (b k) ≠ 0 := (Real.sqrt_pos.2 hbpos).ne'
    have hsqrt_sq : (Real.sqrt (b k)) ^ 2 = b k := Real.sq_sqrt hbpos.le
    dsimp [f]
    field_simp [hsqrt, hbpos.ne']
    nlinarith
  have hg : (∑ k ∈ s, g k ^ 2) =
      ∑ k ∈ s, b k * ‖u k‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro k hk
    have hbpos := hb k hk
    have hsqrt_sq : (Real.sqrt (b k)) ^ 2 = b k := Real.sq_sqrt hbpos.le
    dsimp [g]
    nlinarith
  rw [hprod, hf, hg] at hCS
  exact hCS

/-! ## Source-form finite Halasz inequality (Jutila Lemma 7) -/

def finitePolynomial
    {I K : Type*} [DecidableEq K]
    (s : Finset K) (a : K → ℂ) (v : I → K → ℂ) (i : I) : ℂ :=
  ∑ k ∈ s, a k * v i k

def correlationEnergy
    {I K : Type*} [DecidableEq I] [DecidableEq K]
    (rows : Finset I) (cols : Finset K) (b : K → ℝ)
    (eta : I → ℂ) (v : I → K → ℂ) : ℝ :=
  ∑ k ∈ cols, b k * ‖∑ i ∈ rows, eta i * v i k‖ ^ 2

/-- Jutila's Lemma 7 before the final expansion into the correlation series
`B`.  The functions `v i k` stand for `chi_i(k) k^{-s_i}`. -/
theorem finite_halasz_inequality
    {I K : Type*} [DecidableEq I] [DecidableEq K]
    (rows : Finset I) (cols : Finset K)
    (a : K → ℂ) (b : K → ℝ) (v : I → K → ℂ)
    (hb : ∀ k ∈ cols, 0 < b k) :
    ∃ eta : I → ℂ,
      (∀ i ∈ rows, ‖eta i‖ = 1) ∧
      (∑ i ∈ rows, ‖finitePolynomial cols a v i‖) ^ 2 ≤
        (∑ k ∈ cols, ‖a k‖ ^ 2 / b k) *
          correlationEnergy rows cols b eta v := by
  let F : I → ℂ := finitePolynomial cols a v
  let eta : I → ℂ := fun i => alignPhase (F i)
  refine ⟨eta, ?_, ?_⟩
  · intro i hi
    exact norm_alignPhase (F i)
  · have halign : ((∑ i ∈ rows, ‖F i‖ : ℝ) : ℂ) =
        ∑ i ∈ rows, eta i * F i := by
      push_cast
      apply Finset.sum_congr rfl
      intro i hi
      exact (alignPhase_mul (F i)).symm
    have hinterchange : (∑ i ∈ rows, eta i * F i) =
        ∑ k ∈ cols, a k * (∑ i ∈ rows, eta i * v i k) := by
      dsimp [F, finitePolynomial]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro i hi
      ring
    have hweighted := weighted_norm_sum_sq_le cols a
      (fun k => ∑ i ∈ rows, eta i * v i k) b hb
    rw [← hinterchange, ← halign] at hweighted
    have hsum_nonneg : 0 ≤ ∑ i ∈ rows, ‖F i‖ := by positivity
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsum_nonneg] at hweighted
    simpa [correlationEnergy, F] using hweighted

/-- The real correlation energy is exactly the double correlation sum which
appears on the right of Jutila's printed Lemma 7. -/
theorem correlationEnergy_eq_doubleSum
    {I K : Type*} [DecidableEq I] [DecidableEq K]
    (rows : Finset I) (cols : Finset K) (b : K → ℝ)
    (eta : I → ℂ) (v : I → K → ℂ) :
    (correlationEnergy rows cols b eta v : ℂ) =
      ∑ i ∈ rows, ∑ j ∈ rows,
        conj (eta i) * eta j *
          (∑ k ∈ cols, (b k : ℂ) * conj (v i k) * v j k) := by
  unfold correlationEnergy
  push_cast
  calc
    (∑ k ∈ cols,
        (b k : ℂ) * (‖∑ i ∈ rows, eta i * v i k‖ : ℂ) ^ 2) =
        ∑ k ∈ cols, ∑ j ∈ rows, ∑ i ∈ rows,
          conj (eta j) * eta i *
            ((b k : ℂ) * conj (v j k) * v i k) := by
      apply Finset.sum_congr rfl
      intro k hk
      let S : ℂ := ∑ i ∈ rows, eta i * v i k
      have hnorm : ((‖S‖ : ℝ) : ℂ) ^ 2 = S * conj S := by
        rw [Complex.mul_conj, ← Complex.sq_norm]
        norm_cast
      rw [show (∑ i ∈ rows, eta i * v i k) = S by rfl, hnorm]
      dsimp [S]
      simp_rw [map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = ∑ i ∈ rows, ∑ j ∈ rows,
        conj (eta i) * eta j *
          (∑ k ∈ cols, (b k : ℂ) * conj (v i k) * v j k) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]

/-! ## Exact source parameter arithmetic on journal page 52 -/

/-- For `0 < epsilon <= 1/21` and `alpha >= 1-epsilon`, Jutila's choices
`R=D^epsilon`, `z2=D^(1/2+8epsilon)`, `X=D^(1+12epsilon)` satisfy the exponent
condition behind (2.8). -/
theorem detector_parameter_exponent
    {epsilon alpha : ℝ}
    (hepsilon : 0 ≤ epsilon) (hepsilon_small : epsilon ≤ 1 / 21)
    (halpha : 1 - epsilon ≤ alpha) :
    (1 + epsilon) * (1 / 2 + epsilon + (1 / 2 + 8 * epsilon)) ≤
      alpha * (1 + 12 * epsilon) := by
  have hfactor : 0 ≤ 1 + 12 * epsilon := by linarith
  have hmul := mul_le_mul_of_nonneg_right halpha hfactor
  nlinarith [mul_nonneg hepsilon (sub_nonneg.mpr hepsilon_small)]

theorem detector_parameter_rpow
    {D epsilon alpha : ℝ}
    (hD : 1 ≤ D) (hepsilon : 0 ≤ epsilon)
    (hepsilon_small : epsilon ≤ 1 / 21)
    (halpha : 1 - epsilon ≤ alpha) :
    Real.rpow D ((1 + epsilon) *
        (1 / 2 + epsilon + (1 / 2 + 8 * epsilon))) ≤
      Real.rpow D (alpha * (1 + 12 * epsilon)) := by
  exact Real.rpow_le_rpow_of_exponent_le hD
    (detector_parameter_exponent hepsilon hepsilon_small halpha)

/-! ## The epsilon relabeling hidden after the p. 53 conclusion -/

/-- The factor from `X = D^(1+12*delta)` in
`x^(2-2*alpha)`, before the `log^2 D` in `x` is absorbed. -/
def directDensityCoefficient (delta : ℝ) : ℝ :=
  2 * (1 + 12 * delta)

/-- If `log D <= D^kappa`, the factor `(log D)^(4(1-alpha))`
costs an additional `4*kappa` in the density coefficient. -/
def logBudgetedDensityCoefficient (delta kappa : ℝ) : ℝ :=
  directDensityCoefficient delta + 4 * kappa

theorem directDensityCoefficient_eq (delta : ℝ) :
    directDensityCoefficient delta = 2 + 24 * delta := by
  simp [directDensityCoefficient]
  ring

/-- Death test for the proposed `20/21` collar: Jutila's literal p. 52
parameters with `delta=1/21` already cost `22/7`, strictly worse than `2.1`,
even before the logarithmic factor in `x` is paid. -/
theorem oneTwentyFirst_direct_coefficient_gt_twoPointOne :
    (21 / 10 : ℝ) < directDensityCoefficient (1 / 21) := by
  norm_num [directDensityCoefficient]

/-- A clean source-faithful allocation for the final coefficient `2.1`:
`delta=kappa=1/280` pays `24 delta` for `X` and `4 kappa` for `log^2 D`. -/
theorem oneTwoEightieth_budget_exact :
    logBudgetedDensityCoefficient (1 / 280) (1 / 280) = (21 / 10 : ℝ) := by
  norm_num [logBudgetedDensityCoefficient, directDensityCoefficient]

theorem oneTwoEightieth_detector_parameter
    {alpha : ℝ} (halpha : (279 / 280 : ℝ) ≤ alpha) :
    (1 + (1 / 280 : ℝ)) *
        (1 / 2 + (1 / 280 : ℝ) + (1 / 2 + 8 * (1 / 280 : ℝ))) ≤
      alpha * (1 + 12 * (1 / 280 : ℝ)) := by
  apply detector_parameter_exponent (by norm_num) (by norm_num)
  norm_num at halpha ⊢
  exact halpha

/-! ## The last quadratic absorption on journal page 53 -/

/-- If the diagonal term carries a strict coefficient saving, the final
quadratic inequality gives a linear bound for `J`.  This is the exact
deterministic shape of the last sentence before (1.7). -/
theorem quadratic_density_absorption
    {A J W C E : ℝ}
    (hJ : 0 ≤ J) (hW : 0 ≤ W) (hC : 0 ≤ C)
    (hmain : A * J ^ 2 ≤ C * J * W + E * J ^ 2) (hEA : E < A - C) :
    J ≤ C * W / (A - C - E) := by
  have hden : 0 < A - C - E := by linarith
  by_cases hJ0 : J = 0
  · subst J
    positivity
  · have hJpos : 0 < J := lt_of_le_of_ne hJ (Ne.symm hJ0)
    have hraw : (A - C - E) * J ^ 2 ≤ C * J * W := by
      nlinarith
    have hcancel : (A - C - E) * J ≤ C * W := by
      nlinarith [mul_pos hden hJpos]
    exact (le_div_iff₀ hden).2 (by nlinarith)

end

end MAPJutilaDeterministicCore

#print axioms MAPJutilaDeterministicCore.finite_halasz_inequality
#print axioms MAPJutilaDeterministicCore.card_le_two_mul_fiberCap_mul_larger_color
#print axioms MAPJutilaDeterministicCore.multiplicitySum_le_fiberCap_mul_occupied
#print axioms MAPJutilaDeterministicCore.multiplicitySum_le_two_mul_fiberCap_mul_larger_color
#print axioms MAPJutilaDeterministicCore.correlationEnergy_eq_doubleSum
#print axioms MAPJutilaDeterministicCore.detector_parameter_rpow
#print axioms MAPJutilaDeterministicCore.oneTwentyFirst_direct_coefficient_gt_twoPointOne
#print axioms MAPJutilaDeterministicCore.oneTwoEightieth_budget_exact
#print axioms MAPJutilaDeterministicCore.oneTwoEightieth_detector_parameter
#print axioms MAPJutilaDeterministicCore.quadratic_density_absorption
