import KTwoPrimeArithmeticLogBudgetLargeScale
import KTwoDyadicPrimeReciprocalFromChebyshev
import PrimitiveTwistedMangoldtCertified
import PrimitiveExplicitFormulaSpine
import Mathlib.NumberTheory.Chebyshev

/-!
# Dyadic reciprocal-prime mass from the certified conductor-one psi theorem

This file replaces the remaining prime input in Jutila--Heath--Brown (29.32)
by a specialization of the already-certified conductor-one twisted Mangoldt
estimate.  The first lemmas identify that specialization with Mathlib's
Chebyshev `psi` and turn it into a dyadic lower bound.
-/

namespace KTwoDyadicPrimeReciprocalFromCertifiedPsi

open Filter Set
open scoped BigOperators ArithmeticFunction

noncomputable section

local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩

/-- At conductor one the twisted Mangoldt prefix is exactly Chebyshev's
`psi`, including the real-floor endpoint convention. -/
theorem twistedMangoldtSum_one_eq_psi (t : ℝ) :
    APFoundation.twistedMangoldtSum
        (1 : DirichletCharacter ℂ 1) (Finset.Icc 1 ⌊t⌋₊) =
      (Chebyshev.psi t : ℂ) := by
  unfold APFoundation.twistedMangoldtSum Chebyshev.psi
  push_cast
  apply Finset.sum_congr
  · ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  · intro n hn
    have hunit : IsUnit (n : ZMod 1) := by
      rw [show (n : ZMod 1) = 1 from Subsingleton.elim _ _]
      exact isUnit_one
    change (1 : DirichletCharacter ℂ 1) (n : ZMod 1) *
      (ArithmeticFunction.vonMangoldt n : ℂ) = _
    rw [MulChar.one_apply hunit, one_mul]

/-- The certified conductor-one theorem gives the ordinary psi estimate on
every point of the source dyadic interval. -/
theorem exists_eventually_psi_close_on_dyadic :
    ∃ C X₀ : ℝ, 0 < C ∧ 2 ≤ X₀ ∧
      ∀ X : ℝ, X₀ ≤ X → ∀ t : ℝ, t ∈ Set.Icc X (2 * X) →
        |Chebyshev.psi t - t| ≤ C * X / (Real.log X) ^ 2 := by
  obtain ⟨C, X₀, hC, hX₀, hbound⟩ :=
    MAPPrimitiveTwistedMangoldtCertified.primitiveTwistedMangoldtPsi 2 0
  refine ⟨C, X₀, hC, hX₀, ?_⟩
  intro X hX t ht
  have hcomplex := hbound X hX 1 (by norm_num) (by norm_num)
    (1 : DirichletCharacter ℂ 1) (by
      rw [DirichletCharacter.isPrimitive_def,
        DirichletCharacter.conductor_one]) t ht
  rw [twistedMangoldtSum_one_eq_psi] at hcomplex
  simp [MAPSiegelWalfiszCharacterReduction.characterMain] at hcomplex
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hcomplex
  exact hcomplex

/-- The dyadic Mangoldt mass is eventually a fixed positive proportion of
the interval length. -/
theorem exists_eventually_psi_dyadic_increment_lower :
    ∃ X₀ : ℝ, 2 ≤ X₀ ∧
      ∀ X : ℝ, X₀ ≤ X →
        X / 2 ≤ Chebyshev.psi (2 * X) - Chebyshev.psi X := by
  obtain ⟨C, X₀, hC, hX₀, hpsi⟩ := exists_eventually_psi_close_on_dyadic
  have hlogEventually : ∀ᶠ X : ℝ in atTop,
      Real.sqrt (4 * C) ≤ Real.log X := by
    exact Real.tendsto_log_atTop.eventually (eventually_ge_atTop _)
  obtain ⟨Y, hY⟩ := (eventually_atTop.1 hlogEventually)
  let Z : ℝ := max X₀ (max Y (Real.exp 1))
  have hZ2 : 2 ≤ Z := le_trans hX₀ (le_max_left _ _)
  refine ⟨Z, hZ2, ?_⟩
  intro X hZX
  have hX₀X : X₀ ≤ X := (le_max_left X₀ (max Y (Real.exp 1))).trans hZX
  have hYX : Y ≤ X :=
    (le_trans (le_max_left Y (Real.exp 1)) (le_max_right X₀ _)).trans hZX
  have hExpX : Real.exp 1 ≤ X :=
    (le_trans (le_max_right Y (Real.exp 1)) (le_max_right X₀ _)).trans hZX
  have hXpos : 0 < X := (Real.exp_pos 1).trans_le hExpX
  have hlogPos : 0 < Real.log X := by
    rw [Real.log_pos_iff hXpos.le]
    exact (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).trans_le hExpX
  have hlogLower := hY X hYX
  have hCsqrt : 0 ≤ Real.sqrt (4 * C) := Real.sqrt_nonneg _
  have hlogSq : 4 * C ≤ (Real.log X) ^ 2 := by
    have hsquare := pow_le_pow_left₀ hCsqrt hlogLower 2
    rw [Real.sq_sqrt (by positivity : 0 ≤ 4 * C)] at hsquare
    exact hsquare
  have herror : C * X / (Real.log X) ^ 2 ≤ X / 4 := by
    apply (div_le_iff₀ (sq_pos_of_pos hlogPos)).2
    have hX0 : 0 ≤ X := hXpos.le
    nlinarith
  have hAtX := hpsi X hX₀X X (by constructor <;> linarith)
  have hAtTwoX := hpsi X hX₀X (2 * X) (by constructor <;> linarith)
  have hlowerTwo : 2 * X - C * X / (Real.log X) ^ 2 ≤
      Chebyshev.psi (2 * X) := by
    nlinarith [neg_abs_le (Chebyshev.psi (2 * X) - 2 * X)]
  have hupperOne : Chebyshev.psi X ≤ X + C * X / (Real.log X) ^ 2 := by
    nlinarith [le_abs_self (Chebyshev.psi X - X)]
  linarith

/-- The elementary prime-power correction at the upper dyadic endpoint is
eventually at most one quarter of the interval length. -/
theorem eventually_primePowerCorrection_upper :
    ∀ᶠ X : ℝ in atTop,
      2 * Real.sqrt (2 * X) * Real.log (2 * X) ≤ X / 4 := by
  have hsmall :=
    (isLittleO_log_rpow_rpow_atTop (1 : ℝ)
      (by norm_num : (0 : ℝ) < 1 / 2)).bound
        (by norm_num : (0 : ℝ) < 1 / 32)
  filter_upwards [hsmall, eventually_ge_atTop (2 : ℝ)] with X hlog hX2
  have hXpos : 0 < X := by linarith
  have hlog0 : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hsqrt0 : 0 ≤ Real.sqrt X := Real.sqrt_nonneg X
  have hlogSmall : Real.log X ≤ (1 / 32 : ℝ) * Real.sqrt X := by
    have hXpow0 : 0 ≤ Real.rpow X (1 / 2 : ℝ) :=
      Real.rpow_nonneg hXpos.le _
    have hraw : Real.rpow (Real.log X) 1 ≤
        (1 / 32 : ℝ) * Real.rpow X (1 / 2 : ℝ) := by
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)] at hlog
      simpa only [] using! hlog
    simpa [Real.rpow_one, Real.sqrt_eq_rpow] using hraw
  have hsqrtTwo : Real.sqrt (2 * X) ≤ 2 * Real.sqrt X := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hrootTwo : Real.sqrt (2 : ℝ) ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
        Real.sqrt_nonneg (2 : ℝ)]
    exact mul_le_mul_of_nonneg_right hrootTwo hsqrt0
  have hlogTwoX : Real.log (2 * X) ≤ 2 * Real.log X := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hXpos.ne']
    have hlogTwoLe : Real.log 2 ≤ Real.log X :=
      Real.log_le_log (by norm_num) hX2
    linarith
  have hlogTwoX0 : 0 ≤ Real.log (2 * X) :=
    Real.log_nonneg (by nlinarith)
  have hfirst :
      2 * Real.sqrt (2 * X) * Real.log (2 * X) ≤
        8 * Real.sqrt X * Real.log X := by
    nlinarith [mul_le_mul hsqrtTwo hlogTwoX hlogTwoX0
      (show 0 ≤ 2 * Real.sqrt X by positivity)]
  have hsqrtSq : (Real.sqrt X) ^ 2 = X := Real.sq_sqrt hXpos.le
  calc
    2 * Real.sqrt (2 * X) * Real.log (2 * X) ≤
        8 * Real.sqrt X * Real.log X := hfirst
    _ ≤ 8 * Real.sqrt X * ((1 / 32 : ℝ) * Real.sqrt X) := by
      exact mul_le_mul_of_nonneg_left hlogSmall (by positivity)
    _ = (1 / 4 : ℝ) * (Real.sqrt X) ^ 2 := by ring
    _ = X / 4 := by rw [hsqrtSq]; ring

theorem exists_eventually_primePowerCorrection_upper :
    ∃ X₀ : ℝ, 2 ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
      2 * Real.sqrt (2 * X) * Real.log (2 * X) ≤ X / 4 := by
  obtain ⟨Y, hY⟩ := eventually_atTop.1 eventually_primePowerCorrection_upper
  refine ⟨max 2 Y, le_max_left _ _, ?_⟩
  intro X hX
  exact hY X ((le_max_right _ _).trans hX)

/-- Consequently the dyadic Chebyshev-theta mass is eventually at least
`X/4`; this is the prime-only content needed for (29.32). -/
theorem exists_eventually_theta_dyadic_increment_lower :
    ∃ X₀ : ℝ, 2 ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
      X / 4 ≤ Chebyshev.theta (2 * X) - Chebyshev.theta X := by
  obtain ⟨X₁, hX₁, hpsi⟩ := exists_eventually_psi_dyadic_increment_lower
  obtain ⟨X₂, hX₂, hpower⟩ := exists_eventually_primePowerCorrection_upper
  refine ⟨max X₁ X₂, le_max_of_le_left hX₁, ?_⟩
  intro X hX
  have hX1 : X₁ ≤ X := (le_max_left _ _).trans hX
  have hX2 : X₂ ≤ X := (le_max_right _ _).trans hX
  have hXlarge : 2 ≤ X := hX₁.trans hX1
  have hpsiNow := hpsi X hX1
  have hpowerNow := hpower X hX2
  have hcheb := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log
    (show 1 ≤ 2 * X by linarith)
  have hupper : Chebyshev.psi (2 * X) - Chebyshev.theta (2 * X) ≤ X / 4 :=
    (le_abs_self _).trans (hcheb.trans hpowerNow)
  have hthetaPsi := Chebyshev.theta_le_psi X
  linarith

/-- Premise-free inhabitant of the exact native theta-increment leaf used by
the finite Chebyshev-to-reciprocal bridge. -/
theorem dyadicChebyshevThetaIncrementLower_certified :
    GuthMaynardJutilaLemma29NineKTwo.DyadicChebyshevThetaIncrementLower := by
  obtain ⟨X₀, hX₀, htheta⟩ := exists_eventually_theta_dyadic_increment_lower
  refine ⟨1 / 4, X₀, by norm_num, hX₀, ?_⟩
  intro X hX
  simpa [div_eq_mul_inv, mul_comm] using htheta X hX

/-- The source estimate (29.32), now discharged from the already-certified
conductor-one prime theorem rather than retained as a fresh analytic premise. -/
theorem dyadicPrimeReciprocalLower29_32_certified :
    GuthMaynardJutilaLemma29NineKTwo.DyadicPrimeReciprocalLower29_32 :=
  GuthMaynardJutilaLemma29NineKTwo.dyadicPrimeReciprocalLower29_32_of_thetaIncrement
    dyadicChebyshevThetaIncrementLower_certified

theorem dyadicPrimeReciprocalInverseLogBound_certified :
    GuthMaynardJutilaLemma29NineKTwo.DyadicPrimeReciprocalInverseLogBound :=
  GuthMaynardJutilaLemma29NineKTwo.dyadicPrimeReciprocalInverseLogBound_of_29_32
    dyadicPrimeReciprocalLower29_32_certified

theorem kTwoPrimeArithmeticLogBudgetLargeScale_certified :
    GuthMaynardJutilaLemma29NineKTwo.KTwoPrimeArithmeticLogBudgetLargeScale :=
  GuthMaynardJutilaLemma29NineKTwo.kTwoPrimeArithmeticLogBudgetLargeScale_of_dyadicPrimeReciprocal
    dyadicPrimeReciprocalInverseLogBound_certified

#print axioms twistedMangoldtSum_one_eq_psi
#print axioms exists_eventually_psi_close_on_dyadic
#print axioms exists_eventually_psi_dyadic_increment_lower
#print axioms exists_eventually_primePowerCorrection_upper
#print axioms exists_eventually_theta_dyadic_increment_lower
#print axioms dyadicChebyshevThetaIncrementLower_certified
#print axioms dyadicPrimeReciprocalLower29_32_certified
#print axioms dyadicPrimeReciprocalInverseLogBound_certified
#print axioms kTwoPrimeArithmeticLogBudgetLargeScale_certified

end

end KTwoDyadicPrimeReciprocalFromCertifiedPsi
