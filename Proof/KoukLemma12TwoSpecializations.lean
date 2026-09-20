import KoukLemma12TwoEulerAdapter

/-!
# Source-facing specializations of Koukoulopoulos Lemma 12.2

Only the two forms used by the `3-4-1` proof are developed here: the empty
selected-zero list for an arbitrary character, and isolation of a supported
zero for a primitive nonprincipal character.
-/

namespace MAPKoukLemma12TwoSpecializations

open Complex Filter Topology Set
open DirichletZeros MAPLocalZeroWindow MAPZeroFreeSiegelSpine
open PrimitiveEulerZeroTransport MAPKoukLemma12TwoEulerAdapter
open MAPPrimitiveLogDerivativeRemainderUnconditional
open MAPPrincipalLogDerivativeRemainderUnconditional
open scoped BigOperators

noncomputable section

theorem primitiveCharacter_eq_one_iff
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) :
    chi.primitiveCharacter = 1 ↔ chi = 1 := by
  constructor
  · intro h
    rw [← chi.changeLevel_primitiveCharacter]
    rw [h]
    simp
  · intro h
    subst chi
    exact DirichletCharacter.primitiveCharacter_one

theorem log_arithmeticScale_conductor_le_level
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (t : ℝ) :
    Real.log (arithmeticScale chi.conductor t) ≤
      Real.log (arithmeticScale q t) := by
  have hcond : chi.conductor ≤ q :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) chi.conductor_dvd_level
  have hcast : (chi.conductor : ℝ) ≤ q := by exact_mod_cast hcond
  have hpos : 0 < arithmeticScale chi.conductor t := by
    unfold arithmeticScale
    exact mul_pos (by exact_mod_cast chi.conductor_ne_zero |> Nat.pos_of_ne_zero)
      (by linarith [abs_nonneg t])
  apply Real.log_le_log hpos
  unfold arithmeticScale
  exact mul_le_mul_of_nonneg_right hcast (by positivity)

theorem log_level_le_log_arithmeticScale
    {q : ℕ} [NeZero q] (t : ℝ) :
    Real.log q ≤ Real.log (arithmeticScale q t) := by
  have hqpos : (0 : ℝ) < q := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  apply Real.log_le_log hqpos
  unfold arithmeticScale
  have hqnonneg : (0 : ℝ) ≤ q := hqpos.le
  nlinarith [mul_le_mul_of_nonneg_left
    (show (1 : ℝ) ≤ |t| + 2 by linarith [abs_nonneg t]) hqnonneg]

theorem re_centeredZeroPoleSum_nonneg
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {u t : ℝ} (hu : 1 ≤ u) :
    0 ≤ (centeredZeroPoleSum chi t ((u : ℂ) + Complex.I * t)).re := by
  unfold centeredZeroPoleSum
  rw [Complex.re_sum]
  exact Finset.sum_nonneg fun rho hrho =>
    re_centeredZeroPoleTerm_nonneg chi hu hrho

/-- Quantitative logarithmic-derivative change of level at `Re s > 1`. -/
theorem logDeriv_LFunction_eq_primitive_add_correction
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    [NeZero chi.conductor] {s : ℂ} (hs : 1 < s.re) :
    logDeriv (DirichletCharacter.LFunction chi) s =
      logDeriv (DirichletCharacter.LFunction chi.primitiveCharacter) s +
        logDeriv (eulerCorrection chi) s := by
  have hs1 : s ≠ 1 := by
    intro h
    subst s
    norm_num at hs
  have hprimNe : DirichletCharacter.LFunction chi.primitiveCharacter s ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re chi.primitiveCharacter
      (Or.inr hs1) hs.le
  have hcorrNe : eulerCorrection chi s ≠ 0 :=
    eulerCorrection_ne_zero chi (by linarith)
  have hprimDiff : DifferentiableAt ℂ
      (DirichletCharacter.LFunction chi.primitiveCharacter) s :=
    DirichletCharacter.differentiableAt_LFunction chi.primitiveCharacter s
      (Or.inl hs1)
  have hcorrDiff : DifferentiableAt ℂ (eulerCorrection chi) s :=
    (analyticAt_eulerCorrection chi s).differentiableAt
  have hmul := logDeriv_mul s hprimNe hcorrNe hprimDiff hcorrDiff
  have hevent : Filter.EventuallyEq (nhds s)
      (DirichletCharacter.LFunction chi)
      (fun z => DirichletCharacter.LFunction chi.primitiveCharacter z *
        eulerCorrection chi z) := by
    filter_upwards [eventually_ne_nhds hs1] with z hz
    exact LFunction_eq_primitive_mul_eulerCorrection chi (Or.inr hz)
  calc
    logDeriv (DirichletCharacter.LFunction chi) s =
        logDeriv (fun z => DirichletCharacter.LFunction chi.primitiveCharacter z *
          eulerCorrection chi z) s := by
      rw [logDeriv_apply, logDeriv_apply, hevent.deriv_eq,
        hevent.self_of_nhds]
    _ = _ := hmul

/-- Empty-selected-list half of Lemma 12.2, in the precise uniform form
needed for the `chi^2` term. -/
theorem logDeriv_LFunction_re_ge_empty
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {u t : ℝ} (hu : 1 < u) (hu2 : u ≤ 2) :
    (logDeriv (DirichletCharacter.LFunction chi)
        ((u : ℂ) + Complex.I * t)).re ≥
      -(if chi = 1 then
          (1 / (((u : ℂ) + Complex.I * t) - 1)).re else 0) -
        102002 * Real.log (arithmeticScale q t) := by
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  let psi := chi.primitiveCharacter
  let s : ℂ := (u : ℂ) + Complex.I * t
  have hchange := logDeriv_LFunction_eq_primitive_add_correction chi
    (s := s) (by dsimp [s]; simpa using hu)
  have hcorr := norm_logDeriv_eulerCorrection_le chi
    (s := s) (by dsimp [s]; simpa using hu)
  have hcorrLower : -(2 * Real.log q) ≤
      (logDeriv (eulerCorrection chi) s).re := by
    have hneg := (abs_le.mp
      (Complex.abs_re_le_norm (logDeriv (eulerCorrection chi) s))).1
    exact (neg_le_neg hcorr).trans hneg
  have hscaleCond := log_arithmeticScale_conductor_le_level chi t
  have hscaleQ := log_level_le_log_arithmeticScale (q := q) t
  have hlogQ0 : 0 ≤ Real.log (arithmeticScale q t) :=
    Real.log_nonneg (MAPPrimitiveLFixedStrip.one_le_arithmeticScale t)
  by_cases hpsi : psi = 1
  · have hchi : chi = 1 := (primitiveCharacter_eq_one_iff chi).mp hpsi
    have hprincipal := principalLogDerivativeRemainder_le (t := t) hu hu2
    have hformula :=
      neg_logDeriv_riemannZeta_eq_pole_sub_centered_add_remainder (t := t) hu
    have hpoles := re_centeredZeroPoleSum_nonneg
      (1 : DirichletCharacter ℂ 1) hu.le (t := t)
    have hzetaLower :
        -(1 / (s - 1)).re -
            100000 * Real.log (arithmeticScale 1 t) ≤
          (logDeriv riemannZeta s).re := by
      dsimp [s] at hformula ⊢
      have hremUpper :
          (primitiveLogDerivativeRemainder
              (1 : DirichletCharacter ℂ 1) u t).re ≤
            100000 * Real.log (arithmeticScale 1 t) :=
        (Complex.re_le_norm _).trans hprincipal
      have hreFormula := congrArg Complex.re hformula
      simp only [Complex.neg_re, Complex.add_re, Complex.sub_re] at hreFormula
      linarith
    have hs1 : s ≠ 1 := by
      intro heq
      have hre := congrArg Complex.re heq
      dsimp [s] at hre
      simp at hre
      linarith
    have hcond : chi.conductor = 1 := by
      rw [hchi, DirichletCharacter.conductor_one]
    have hpf : chi.conductor.primeFactors = ∅ := by rw [hcond]; simp
    have heventPsi : Filter.EventuallyEq (nhds s)
        (DirichletCharacter.LFunction psi) riemannZeta := by
      filter_upwards [eventually_ne_nhds hs1] with z hz
      rw [hpsi]
      have hztriv := @DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta
        chi.conductor inferInstance z hz
      rw [hpf] at hztriv
      simpa using hztriv
    have hpsiLog :
        logDeriv (DirichletCharacter.LFunction psi) s =
          logDeriv riemannZeta s := by
      rw [logDeriv_apply, logDeriv_apply, heventPsi.deriv_eq,
        heventPsi.self_of_nhds]
    have hprimLower :
        -(1 / (s - 1)).re -
            100000 * Real.log (arithmeticScale 1 t) ≤
          (logDeriv (DirichletCharacter.LFunction psi) s).re := by
      rw [hpsiLog]
      exact hzetaLower
    have hscaleOne : Real.log (arithmeticScale 1 t) ≤
        Real.log (arithmeticScale q t) := by
      have hq1 : (1 : ℝ) ≤ q := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
      have hpos : 0 < arithmeticScale 1 t := by
        unfold arithmeticScale
        positivity
      apply Real.log_le_log hpos
      unfold arithmeticScale
      calc
        ((1 : ℕ) : ℝ) * (|t| + 2) = |t| + 2 := by norm_num
        _ ≤ (q : ℝ) * (|t| + 2) := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hq1
            (show 0 ≤ |t| + 2 by positivity)
    rw [hchange, Complex.add_re, if_pos hchi]
    dsimp [psi] at hprimLower
    dsimp [s] at hprimLower ⊢
    nlinarith
  · have hchi : chi ≠ 1 := by
      intro h
      apply hpsi
      exact (primitiveCharacter_eq_one_iff chi).mpr h
    have hrem := primitiveLogDerivativeRemainder_le psi
      chi.primitiveCharacter_isPrimitive hpsi (t := t) hu hu2
    have hformula := neg_logDeriv_LFunction_eq_centeredZeroSum_add_remainder
      psi hpsi hu.le t
    have hpoles := re_centeredZeroPoleSum_nonneg psi hu.le (t := t)
    have hprimLower :
        -(17000 * Real.log (arithmeticScale chi.conductor t)) ≤
          (logDeriv (DirichletCharacter.LFunction psi) s).re := by
      dsimp [s] at hformula ⊢
      have hremUpper :
          (primitiveLogDerivativeRemainder psi u t).re ≤
            17000 * Real.log (arithmeticScale chi.conductor t) :=
        (Complex.re_le_norm _).trans hrem
      rw [Complex.ext_iff] at hformula
      have hreFormula := hformula.1
      simp only [Complex.neg_re, Complex.add_re] at hreFormula
      linarith
    rw [hchange, Complex.add_re, if_neg hchi]
    nlinarith

/-- The selected-zero form for a primitive nonprincipal character. -/
theorem logDeriv_LFunction_re_ge_selected_same_height
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive) (hchi : chi ≠ 1)
    {u t : ℝ} (hu : 1 < u) (hu2 : u ≤ 2)
    {rho : ℂ} (hrho : rho ∈ centeredUnitWindowSupport chi (1 / 2) t)
    (him : rho.im = t) :
    (zeroMultiplicity chi (1 / 2)
        (windowHeight (t - 1 / 2)) rho : ℝ) / (u - rho.re) -
        17000 * Real.log (arithmeticScale q t) ≤
      (logDeriv (DirichletCharacter.LFunction chi)
        ((u : ℂ) + Complex.I * t)).re := by
  have hrem := primitiveLogDerivativeRemainder_le chi hprim hchi (t := t) hu hu2
  have hupper := neg_logDeriv_re_le_logScale_sub_zeroPole
    chi hchi hu hrho him hrem
  have hneg := neg_le_neg hupper
  simp only [Complex.neg_re] at hneg
  linarith

end

end MAPKoukLemma12TwoSpecializations

#print axioms MAPKoukLemma12TwoSpecializations.logDeriv_LFunction_re_ge_empty
#print axioms MAPKoukLemma12TwoSpecializations.logDeriv_LFunction_re_ge_selected_same_height
