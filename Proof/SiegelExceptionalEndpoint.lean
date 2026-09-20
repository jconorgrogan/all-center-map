import ExceptionalZeroWeight
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Source-faithful Siegel input and the exceptional-weight endpoint

The external statement isolated here is Koukoulopoulos, *The Distribution of
Prime Numbers*, Theorem 12.10: for every positive `epsilon`, all real
nonprincipal Dirichlet characters modulo `q` have no real zero to the right of
`1 - c(epsilon) q^(-epsilon)`.  The constant is positive and ineffective.

This is strictly cheaper than importing a lower bound for `L(1, chi)` and then
recovering a zero gap through a derivative estimate.  No inhabitant of the
source proposition is asserted in this file.
-/

namespace MAPSiegelExceptionalEndpoint

open Filter Asymptotics

noncomputable section

/-- Koukoulopoulos, Theorem 12.10, in the exact real-axis form used by the
exceptional-zero branch.  The condition `chi ^ 2 = 1` is the finite-character
encoding of real-valuedness.  The published theorem does not require
primitivity. -/
def PublishedSiegelRealZeroFreeRegion : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ c : ℝ, 0 < c ∧
      ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q),
        chi ≠ 1 → chi ^ 2 = 1 →
          ∀ sigma : ℝ,
            1 - c * Real.rpow (q : ℝ) (-epsilon) < sigma →
              DirichletCharacter.LFunction chi sigma ≠ 0

/-- A zero of a character covered by the published zero-free region has the
literal Siegel gap. -/
theorem PublishedSiegelRealZeroFreeRegion.zero_gap
    (hSiegel : PublishedSiegelRealZeroFreeRegion)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q),
        chi ≠ 1 → chi ^ 2 = 1 →
          ∀ beta : ℝ, DirichletCharacter.LFunction chi beta = 0 →
            c * Real.rpow (q : ℝ) (-epsilon) ≤ 1 - beta := by
  rcases hSiegel epsilon hepsilon with ⟨c, hc, hregion⟩
  refine ⟨c, hc, ?_⟩
  intro q _ chi hchi hreal beta hzero
  have hnot : ¬ (1 - c * Real.rpow (q : ℝ) (-epsilon) < beta) := by
    intro hbeta
    exact (hregion q chi hchi hreal beta hbeta) hzero
  linarith

/-- `log (log X)` is eventually dominated by every positive power of
`log X`, with the exact coefficient arrangement consumed by
`exceptionalWeight_le_logSaving_of_gap`. -/
theorem eventually_exceptional_trade
    {A c theta : ℝ} (hA : 0 < A) (hc : 0 < c) (htheta : 0 < theta) :
    ∀ᶠ X : ℝ in atTop,
      A * Real.log (Real.log X) ≤
        2 * c * Real.rpow (Real.log X) theta := by
  let D : ℝ := A / (2 * c)
  have hD : 0 < D := div_pos hA (mul_pos (by norm_num) hc)
  have hsmall0 :=
    ((isLittleO_log_rpow_rpow_atTop (1 : ℝ) htheta).const_mul_left D).eventuallyLE
  have hsmall : ∀ᶠ L : ℝ in atTop,
      A * Real.log L ≤ 2 * c * Real.rpow L theta := by
    filter_upwards [hsmall0, eventually_gt_atTop (1 : ℝ)] with L hbound hL
    have hlog0 : 0 ≤ Real.log L := Real.log_nonneg hL.le
    have hDlog0 : 0 ≤ D * Real.log L := mul_nonneg hD.le hlog0
    have hrpow0 : 0 ≤ Real.rpow L theta :=
      Real.rpow_nonneg (zero_lt_one.trans hL).le theta
    have hbound' : D * Real.log L ≤ Real.rpow L theta := by
      have hrpowOne : Real.rpow (Real.log L) (1 : ℝ) = Real.log L :=
        Real.rpow_one (Real.log L)
      rw [← Real.rpow_eq_pow, ← Real.rpow_eq_pow] at hbound
      rw [hrpowOne, Real.norm_of_nonneg hDlog0,
        Real.norm_of_nonneg hrpow0] at hbound
      exact hbound
    have hidentity : (2 * c) * D = A := by
      dsimp [D]
      field_simp
    have hscaled := mul_le_mul_of_nonneg_left hbound'
      (show 0 ≤ 2 * c by positivity)
    nlinarith
  exact Real.tendsto_log_atTop.eventually hsmall

/-- The direct source route closes the pointwise exceptional-real-zero
endpoint, including an arbitrary fixed polylogarithmic prefactor.  Choosing
`nu = 1/(4K)` leaves the stretched-exponential power `3/4` in the logarithmic
coordinate. -/
theorem PublishedSiegelRealZeroFreeRegion.eventually_prefactor_mul_weight_le
    (hSiegel : PublishedSiegelRealZeroFreeRegion)
    {K A P : ℝ} (hK : 0 < K) (hA : 0 < A) (hP : 0 ≤ P) :
    ∀ᶠ X : ℝ in atTop,
      ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q) (beta : ℝ),
        (q : ℝ) ≤ Real.rpow (Real.log X) K →
        chi ≠ 1 → chi ^ 2 = 1 →
        DirichletCharacter.LFunction chi beta = 0 →
          Real.rpow (Real.log X) P *
              Real.rpow X (2 * (beta - 1)) ≤
            Real.rpow (Real.log X) (-A) := by
  let nu : ℝ := 1 / (4 * K)
  have hnu : 0 < nu := by
    dsimp [nu]
    positivity
  have hKnu : K * nu = 1 / 4 := by
    dsimp [nu]
    field_simp
  have htheta : 0 < 1 - K * nu := by
    rw [hKnu]
    norm_num
  rcases hSiegel.zero_gap hnu with ⟨c, hc, hgap⟩
  have htrade := eventually_exceptional_trade
    (A := A + P) (c := c) (theta := 1 - K * nu)
    (add_pos_of_pos_of_nonneg hA hP) hc htheta
  filter_upwards [htrade, eventually_ge_atTop (Real.exp 1)] with X htradeX hX
  intro q _ chi beta hq hchi hreal hzero
  have hpoint :=
    MAPZeroFreeSiegelSpine.exceptionalWeight_le_logSaving_of_gap
      (A := A + P) (K := K) (ε := nu) (c := c)
      (X := X) (β := beta) hX hnu.le hc hq
      (hgap q chi hchi hreal beta hzero) htradeX
  have hlogpos : 0 < Real.log X := by
    have hXpos : 0 < X := (Real.exp_pos 1).trans_le hX
    have hlogone : 1 ≤ Real.log X := by
      rw [Real.le_log_iff_exp_le hXpos]
      exact hX
    exact zero_lt_one.trans_le hlogone
  calc
    Real.rpow (Real.log X) P * Real.rpow X (2 * (beta - 1)) ≤
        Real.rpow (Real.log X) P *
          Real.rpow (Real.log X) (-(A + P)) :=
      mul_le_mul_of_nonneg_left hpoint
        (Real.rpow_nonneg hlogpos.le P)
    _ = Real.rpow (Real.log X) (P + -(A + P)) :=
      (Real.rpow_add hlogpos P (-(A + P))).symm
    _ = Real.rpow (Real.log X) (-A) := by ring_nf

/-- Threshold form of the preceding eventual theorem, matching the outer
quantifier shape of `APWeightedZeroMassLogSaving`. -/
theorem PublishedSiegelRealZeroFreeRegion.exists_prefactor_mul_weight_le
    (hSiegel : PublishedSiegelRealZeroFreeRegion)
    {K A P : ℝ} (hK : 0 < K) (hA : 0 < A) (hP : 0 ≤ P) :
    ∃ X0 : ℝ, 2 ≤ X0 ∧
      ∀ X : ℝ, X0 ≤ X →
        ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q) (beta : ℝ),
          (q : ℝ) ≤ Real.rpow (Real.log X) K →
          chi ≠ 1 → chi ^ 2 = 1 →
          DirichletCharacter.LFunction chi beta = 0 →
            Real.rpow (Real.log X) P *
                Real.rpow X (2 * (beta - 1)) ≤
              Real.rpow (Real.log X) (-A) := by
  rcases (eventually_atTop.1
      (hSiegel.eventually_prefactor_mul_weight_le hK hA hP)) with
    ⟨X1, hX1⟩
  refine ⟨max 2 X1, le_max_left _ _, ?_⟩
  intro X hX
  exact hX1 X ((le_max_right 2 X1).trans hX)

/-- The specialization used in the manuscript audit: the crude total number
of ambient character slots costs at most `(log X)^(2K)`. -/
theorem PublishedSiegelRealZeroFreeRegion.exists_twoK_prefactor_mul_weight_le
    (hSiegel : PublishedSiegelRealZeroFreeRegion)
    {K A : ℝ} (hK : 0 < K) (hA : 0 < A) :
    ∃ X0 : ℝ, 2 ≤ X0 ∧
      ∀ X : ℝ, X0 ≤ X →
        ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q) (beta : ℝ),
          (q : ℝ) ≤ Real.rpow (Real.log X) K →
          chi ≠ 1 → chi ^ 2 = 1 →
          DirichletCharacter.LFunction chi beta = 0 →
            Real.rpow (Real.log X) (2 * K) *
                Real.rpow X (2 * (beta - 1)) ≤
              Real.rpow (Real.log X) (-A) := by
  exact hSiegel.exists_prefactor_mul_weight_le hK hA
    (mul_nonneg (by norm_num) hK.le)

/-- Finite weighted endpoint bookkeeping.  If the total multiplicity/cardinal
budget is at most `(log X)^P` and every exceptional atom has the pointwise
saving `(log X)^(-(A+P))`, then the whole exceptional contribution has the
requested saving `(log X)^(-A)`. -/
theorem exceptionalWeightedEndpoint_of_pointwise
    {iota : Type*} {S : Finset iota} {mass weight : iota → ℝ}
    {L A P : ℝ} (hL : 0 < L)
    (hmass : ∀ i ∈ S, 0 ≤ mass i)
    (hmassTotal : ∑ i ∈ S, mass i ≤ Real.rpow L P)
    (hweight : ∀ i ∈ S, weight i ≤ Real.rpow L (-(A + P))) :
    ∑ i ∈ S, mass i * weight i ≤ Real.rpow L (-A) := by
  calc
    ∑ i ∈ S, mass i * weight i ≤
        ∑ i ∈ S, mass i * Real.rpow L (-(A + P)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hweight i hi) (hmass i hi)
    _ = (∑ i ∈ S, mass i) * Real.rpow L (-(A + P)) := by
      rw [Finset.sum_mul]
    _ ≤ Real.rpow L P * Real.rpow L (-(A + P)) := by
      exact mul_le_mul_of_nonneg_right hmassTotal
        (Real.rpow_nonneg hL.le _)
    _ = Real.rpow L (P + -(A + P)) :=
      (Real.rpow_add hL P (-(A + P))).symm
    _ = Real.rpow L (-A) := by ring_nf

/-- Simple-atom version of the weighted endpoint.  This is the exact final
step after exceptional-zero simplicity and a cardinality budget. -/
theorem exceptionalSimpleEndpoint_of_pointwise
    {iota : Type*} {S : Finset iota} {weight : iota → ℝ}
    {L A P : ℝ} (hL : 0 < L)
    (hcard : (S.card : ℝ) ≤ Real.rpow L P)
    (hweight : ∀ i ∈ S, weight i ≤ Real.rpow L (-(A + P))) :
    ∑ i ∈ S, weight i ≤ Real.rpow L (-A) := by
  have hmassTotal : ∑ _i ∈ S, (1 : ℝ) ≤ Real.rpow L P := by
    simpa using hcard
  simpa using exceptionalWeightedEndpoint_of_pointwise
    (S := S) (mass := fun _ => (1 : ℝ)) (weight := weight)
    hL (by simp) hmassTotal hweight

end
end MAPSiegelExceptionalEndpoint

#print axioms MAPSiegelExceptionalEndpoint.PublishedSiegelRealZeroFreeRegion.zero_gap
#print axioms MAPSiegelExceptionalEndpoint.eventually_exceptional_trade
#print axioms MAPSiegelExceptionalEndpoint.PublishedSiegelRealZeroFreeRegion.eventually_prefactor_mul_weight_le
#print axioms MAPSiegelExceptionalEndpoint.PublishedSiegelRealZeroFreeRegion.exists_prefactor_mul_weight_le
#print axioms MAPSiegelExceptionalEndpoint.PublishedSiegelRealZeroFreeRegion.exists_twoK_prefactor_mul_weight_le
#print axioms MAPSiegelExceptionalEndpoint.exceptionalWeightedEndpoint_of_pointwise
#print axioms MAPSiegelExceptionalEndpoint.exceptionalSimpleEndpoint_of_pointwise
