import KoukTheorem12ThreePrimitive
import DirichletLFunctionConjugationGeneral

/-!
# A principal Koukoulopoulos 12.3 collar

The conductor-one principal branch has no Siegel atom.  This file applies the
same `3-4-1` logarithmic-derivative argument used for primitive nonprincipal
characters directly to zeta.  The pole at one is retained in all three
terms.  A selected zeta zero then contradicts positivity in the standard
reciprocal-logarithmic collar.

This provides a possible route around the Ford--Khale weak-VK input for the
principal Siegel--Walfisz endpoint.
-/

namespace MAPPrincipalKoukTheorem12Three

set_option maxHeartbeats 800000

open Complex Set Filter Topology DirichletZeros
open MAPLocalZeroWindow MAPMellinDetectorLeaf MAPZeroFreeSiegelSpine
open MAPPrincipalLogDerivativeRemainderUnconditional
open MAPPrimitiveLogDerivativeRemainderUnconditional
open MAPKoukTheorem12ThreePrimitive
open MAPKoukLemma12TwoSpecializations PrimitiveExplicitFormulaSpine
open scoped ComplexConjugate

noncomputable section

local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩

private abbrev chi₁ : DirichletCharacter ℂ 1 := 1

theorem principalOne_LFunction_eq_riemannZeta
    {s : ℂ} (hs : 1 < s.re) :
    DirichletCharacter.LFunction chi₁ s = riemannZeta s := by
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have h := @DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta
    1 inferInstance s hs1
  simpa [chi₁, DirichletCharacter.LFunctionTrivChar] using h

theorem logDeriv_principalOne_eq_riemannZeta
    {s : ℂ} (hs : 1 < s.re) :
    logDeriv (DirichletCharacter.LFunction chi₁) s =
      logDeriv riemannZeta s := by
  have hopen : IsOpen {z : ℂ | 1 < z.re} :=
    isOpen_lt continuous_const continuous_re
  have hevent : DirichletCharacter.LFunction chi₁ =ᶠ[nhds s]
      riemannZeta := by
    apply eventually_of_mem (hopen.mem_nhds hs)
    intro z hz
    exact principalOne_LFunction_eq_riemannZeta hz
  rw [logDeriv_apply, logDeriv_apply, hevent.deriv_eq, hevent.self_of_nhds]

/-- Empty selected list: retain zeta's pole at one explicitly. -/
theorem neg_logDeriv_riemannZeta_re_le_general
    {u t : ℝ} (hu : 1 < u) (hu2 : u ≤ 2) :
    (-logDeriv riemannZeta ((u : ℂ) + Complex.I * t)).re ≤
      (1 / (((u : ℂ) + Complex.I * t) - 1)).re +
        100000 * Real.log (arithmeticScale 1 t) := by
  have hformula :=
    neg_logDeriv_riemannZeta_eq_pole_sub_centered_add_remainder
      (u := u) (t := t) hu
  have hpoles := re_centeredZeroPoleSum_nonneg chi₁ hu.le (t := t)
  have hrem := principalLogDerivativeRemainder_le (t := t) hu hu2
  have hremRe :
      (primitiveLogDerivativeRemainder chi₁ u t).re ≤
        100000 * Real.log (arithmeticScale 1 t) :=
    (Complex.re_le_norm _).trans hrem
  dsimp only [chi₁] at hpoles hremRe
  rw [hformula, Complex.add_re, Complex.sub_re]
  linarith

/-- A selected zeta zero contributes its exact reciprocal pole. -/
theorem neg_logDeriv_riemannZeta_re_le_selected
    {u t : ℝ} (hu : 1 < u) (hu2 : u ≤ 2)
    {rho : ℂ}
    (hrho : rho ∈ centeredUnitWindowSupport chi₁ (1 / 2) t)
    (him : rho.im = t) :
    (-logDeriv riemannZeta ((u : ℂ) + Complex.I * t)).re ≤
      (1 / (((u : ℂ) + Complex.I * t) - 1)).re +
        100000 * Real.log (arithmeticScale 1 t) -
          (zeroMultiplicity chi₁ (1 / 2)
            (windowHeight (t - 1 / 2)) rho : ℝ) / (u - rho.re) := by
  have hformula :=
    neg_logDeriv_riemannZeta_eq_pole_sub_centered_add_remainder
      (u := u) (t := t) hu
  have hreRho := re_lt_one_of_mem_zeroSupport chi₁
    (mem_zeroSupport_of_mem_centeredUnitWindowSupport chi₁ hrho)
  have hterm := re_centeredZeroPoleTerm_le_re_centeredZeroPoleSum
    chi₁ hu.le hrho
  rw [re_centeredZeroPoleTerm_eq_reciprocal_of_im_eq
    chi₁ (hreRho.trans hu) him] at hterm
  have hrem := principalLogDerivativeRemainder_le (t := t) hu hu2
  have hremRe :
      (primitiveLogDerivativeRemainder chi₁ u t).re ≤
        100000 * Real.log (arithmeticScale 1 t) :=
    (Complex.re_le_norm _).trans hrem
  dsimp only [chi₁] at hterm hremRe
  dsimp only [chi₁]
  rw [hformula, Complex.add_re, Complex.sub_re]
  linarith

/-- The selected zero and its conjugate both contribute in the short-height
case. -/
theorem neg_logDeriv_riemannZeta_re_le_pair
    {u : ℝ} {rho : ℂ} (hu : 1 < u) (hu2 : u ≤ 2)
    (hrho : rho ∈ centeredUnitWindowSupport chi₁ (1 / 2) rho.im)
    (hconj : conj rho ∈ centeredUnitWindowSupport chi₁ (1 / 2) rho.im)
    (hne : rho ≠ conj rho) :
    (-logDeriv riemannZeta
        ((u : ℂ) + Complex.I * rho.im)).re ≤
      (1 / (((u : ℂ) + Complex.I * rho.im) - 1)).re +
        100000 * Real.log (arithmeticScale 1 rho.im) -
          (1 / (u - rho.re) +
            (u - rho.re) /
              ((u - rho.re) ^ 2 + (2 * rho.im) ^ 2)) := by
  have hformula :=
    neg_logDeriv_riemannZeta_eq_pole_sub_centered_add_remainder
      (u := u) (t := rho.im) hu
  have hpairs := re_centeredZeroPoleSum_ge_pair chi₁ hu.le
    hrho hconj hne
  have hrem := principalLogDerivativeRemainder_le
    (t := rho.im) hu hu2
  have hremRe :
      (primitiveLogDerivativeRemainder chi₁ u rho.im).re ≤
        100000 * Real.log (arithmeticScale 1 rho.im) :=
    (Complex.re_le_norm _).trans hrem
  dsimp only [chi₁] at hpairs hremRe
  rw [hformula, Complex.add_re, Complex.sub_re]
  linarith

/-- Conjugation symmetry for the conductor-one regularized divisor. -/
theorem conj_mem_centeredUnitWindowSupport_principal
    {rho : ℂ}
    (hrho : rho ∈ centeredUnitWindowSupport chi₁ (1 / 2) rho.im)
    (him : |rho.im| ≤ 1 / 4) :
    conj rho ∈ centeredUnitWindowSupport chi₁ (1 / 2) rho.im := by
  rw [centeredUnitWindowSupport, closedUnitWindowSupport, Finset.mem_filter]
    at hrho ⊢
  have hrect := PrimitiveExplicitFormulaSpine.mem_zeroRectangle_of_mem_zeroSupport
    chi₁ _ _ hrho.1
  have hrectConj : conj rho ∈ zeroRectangle (1 / 2)
      (windowHeight (rho.im - 1 / 2)) := by
    rw [zeroRectangle, Complex.mem_reProdIm] at hrect ⊢
    refine ⟨hrect.1, ?_⟩
    constructor <;> simp only [Complex.conj_im] <;>
      linarith [hrect.2.1, hrect.2.2]
  have hzeroReg := regularizedLFunction_eq_zero_of_mem_zeroSupport
    chi₁ _ _ hrho.1
  have hreRho := re_lt_one_of_mem_zeroSupport chi₁ hrho.1
  have hrho1 : rho ≠ 1 := by
    intro h
    subst rho
    norm_num at hreRho
  have hzeta : riemannZeta rho = 0 := by
    rw [MAPPrincipalZetaTransport.regularized_principal_eq,
      MAPPrincipalZetaFixedStrip.principalRegularized_apply_of_ne_one hrho1]
      at hzeroReg
    exact (mul_eq_zero.mp hzeroReg).resolve_left (sub_ne_zero.mpr hrho1)
  have hLzero : DirichletCharacter.LFunction chi₁ rho = 0 := by
    have h := @DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta
      1 inferInstance rho hrho1
    simpa [chi₁, DirichletCharacter.LFunctionTrivChar, hzeta] using h
  have hconj1 : conj rho ≠ 1 := by
    intro h
    apply hrho1
    have := congrArg conj h
    simpa using this
  have hLconj :=
    MAPDirichletLFunctionConjugationGeneral.LFunction_inv_conj_of_ne_one
      chi₁ rho hrho1
  have hLzeroConj : DirichletCharacter.LFunction chi₁ (conj rho) = 0 := by
    simpa [chi₁, hLzero] using hLconj
  have hzetaConj : riemannZeta (conj rho) = 0 := by
    have h := @DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta
      1 inferInstance (conj rho) hconj1
    simpa [chi₁, DirichletCharacter.LFunctionTrivChar] using
      (show DirichletCharacter.LFunction chi₁ (conj rho) = 0 from hLzeroConj)
  have hzeroRegConj : regularizedLFunction chi₁ (conj rho) = 0 := by
    rw [MAPPrincipalZetaTransport.regularized_principal_eq,
      MAPPrincipalZetaFixedStrip.principalRegularized_apply_of_ne_one hconj1,
      hzetaConj, mul_zero]
  refine ⟨(MAPAPZeroDensityCert.mem_zeroSupport_iff_eq_zero chi₁ _ _ hrectConj).mpr
      hzeroRegConj, ?_⟩
  simp only [Complex.conj_im]
  rcases abs_le.mp him with ⟨himLower, himUpper⟩
  constructor <;> linarith

/-- Above the fixed compact range, a principal zeta zero cannot lie in the
Koukoulopoulos reciprocal-logarithmic collar.  This is the principal `3-4-1`
argument: the pole at the middle and doubled ordinates is `O(delta)` once
`|Im rho| > 1/4`, while the selected zero costs `1/(u-Re rho)`. -/
theorem high_principal_nearOne_zero_absent
    {rho : ℂ}
    (hrho : rho ∈ centeredUnitWindowSupport chi₁ (1 / 2) rho.im)
    (hheight : 1 / 4 < |rho.im|)
    (hnear : 1 - rho.re <
      1 / (100000000000 * Real.log (arithmeticScale 1 rho.im))) :
    False := by
  let L := Real.log (arithmeticScale 1 rho.im)
  let delta := 1 / (1000000000 * L)
  let u := 1 + delta
  let gap := 1 - rho.re
  let a := u - rho.re
  have hscaleTwo := two_le_arithmeticScale (q := 1) rho.im
  have hlogTwoLe : Real.log 2 ≤ L := by
    dsimp [L]
    exact Real.log_le_log (by norm_num) hscaleTwo
  have hL : 1 / 2 < L := by
    nlinarith [Real.log_two_gt_d9]
  have hdelta : 0 < delta := by
    dsimp [delta]
    positivity
  have hdeltaInv : 1 / delta = 1000000000 * L := by
    dsimp [delta]
    field_simp
  have hu : 1 < u := by dsimp [u]; linarith
  have hu2 : u ≤ 2 := by
    have hden : 1 ≤ 1000000000 * L := by nlinarith
    have hdle : delta ≤ 1 := by
      dsimp [delta]
      exact (div_le_one (by positivity)).2 hden
    dsimp [u]
    linarith
  have hrelt := re_lt_one_of_mem_zeroSupport chi₁
    (mem_zeroSupport_of_mem_centeredUnitWindowSupport chi₁ hrho)
  have hgap : 0 < gap := by dsimp [gap]; linarith
  have hnear' : gap < delta / 100 := by
    dsimp [gap, delta, L] at hnear ⊢
    convert hnear using 1 <;> ring
  have haeq : a = delta + gap := by dsimp [a, u, gap]; ring
  have ha : 0 < a := by rw [haeq]; linarith
  have haUpper : a < (101 / 100 : ℝ) * delta := by
    rw [haeq]
    linarith
  have hrecip : 39 / (10 * delta) < 4 / a := by
    rw [div_lt_div_iff₀ (by positivity : 0 < 10 * delta) ha]
    nlinarith
  have hrecipL : 3900000000 * L < 4 / a := by
    calc
      3900000000 * L = 39 / (10 * delta) := by
        rw [show 39 / (10 * delta) = (39 / 10) * (1 / delta) by field_simp]
        rw [hdeltaInv]
        ring
      _ < 4 / a := hrecip
  have hdeltaLeL : delta ≤ L := by
    have hsq : 1 ≤ 1000000000 * L ^ 2 := by nlinarith
    dsimp [delta]
    rw [div_le_iff₀ (by positivity : 0 < 1000000000 * L)]
    nlinarith
  have hmult : (1 : ℝ) ≤
      (zeroMultiplicity chi₁ (1 / 2)
        (windowHeight (rho.im - 1 / 2)) rho : ℝ) := by
    exact_mod_cast (show 1 ≤ zeroMultiplicity chi₁ (1 / 2)
      (windowHeight (rho.im - 1 / 2)) rho by
        have hp := zeroMultiplicity_pos_of_mem chi₁ _ _
          (mem_zeroSupport_of_mem_centeredUnitWindowSupport chi₁ hrho)
        omega)
  have hzeta0' := neg_logDeriv_riemannZeta_re_le_general
    (u := u) (t := 0) hu hu2
  have hpole0 :
      (1 / (((u : ℂ) + Complex.I * (0 : ℝ)) - 1)).re = 1 / delta := by
    dsimp [u]
    norm_num
  have hzeta0 : (-logDeriv riemannZeta (u : ℂ)).re ≤
      1 / delta + 100000 * L := by
    rw [hpole0] at hzeta0'
    norm_num [arithmeticScale] at hzeta0'
    have hzeta0Base : (-logDeriv riemannZeta (u : ℂ)).re ≤
        1 / delta + 100000 * Real.log 2 := by
      simpa only [one_div] using hzeta0'
    have hmul : 100000 * Real.log 2 ≤ 100000 * L :=
      mul_le_mul_of_nonneg_left hlogTwoLe (by norm_num)
    exact hzeta0Base.trans (by
      simpa [add_comm] using add_le_add_left hmul (1 / delta))
  have hselected' := neg_logDeriv_riemannZeta_re_le_selected
    (u := u) hu hu2 hrho rfl
  have hpoleT :
      (1 / (((u : ℂ) + Complex.I * rho.im) - 1)).re =
        delta / (delta ^ 2 + rho.im ^ 2) := by
    rw [Complex.div_re, Complex.normSq_apply]
    simp [u]
    ring
  have htSq : (1 / 16 : ℝ) < rho.im ^ 2 := by
    have hs : (1 / 4 : ℝ) ^ 2 < rho.im ^ 2 :=
      (sq_lt_sq).2 (by
        simpa only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)]
          using hheight)
    norm_num at hs ⊢
    exact hs
  have hdenT : 0 < delta ^ 2 + rho.im ^ 2 := by positivity
  have hpoleTLe : delta / (delta ^ 2 + rho.im ^ 2) ≤ 16 * delta := by
    apply (div_le_iff₀ hdenT).2
    nlinarith [sq_nonneg delta]
  have hselected :
      (-logDeriv riemannZeta
        ((u : ℂ) + Complex.I * rho.im)).re ≤
        16 * delta + 100000 * L - 1 / a := by
    rw [hpoleT] at hselected'
    have hmultDiv : 1 / a ≤
        (zeroMultiplicity chi₁ (1 / 2)
          (windowHeight (rho.im - 1 / 2)) rho : ℝ) / a :=
      (div_le_div_iff_of_pos_right ha).2 hmult
    exact hselected'.trans (by linarith)
  have hzeta2' := neg_logDeriv_riemannZeta_re_le_general
    (u := u) (t := 2 * rho.im) hu hu2
  have hpole2 :
      (1 / (((u : ℂ) + Complex.I * (2 * rho.im)) - 1)).re =
        delta / (delta ^ 2 + (2 * rho.im) ^ 2) := by
    dsimp [u]
    exact re_vertical_pole
  have hpole2Le :
      delta / (delta ^ 2 + (2 * rho.im) ^ 2) ≤ 4 * delta :=
    vertical_pole_le_four_delta hdelta hheight
  have hscale2 := log_arithmeticScale_double_le_two_mul
    (q := 1) rho.im
  have hzeta2 :
      (-logDeriv riemannZeta
        ((u : ℂ) + Complex.I * (2 * rho.im))).re ≤
        4 * delta + 200000 * L := by
    have hpole2' :
        (1 / (((u : ℂ) + Complex.I * ((2 * rho.im : ℝ) : ℂ)) - 1)).re =
          delta / (delta ^ 2 + (2 * rho.im) ^ 2) := by
      convert hpole2 using 1 <;> push_cast <;> ring
    rw [hpole2'] at hzeta2'
    have hrhs :
        delta / (delta ^ 2 + (2 * rho.im) ^ 2) +
            100000 * Real.log (arithmeticScale 1 (2 * rho.im)) ≤
          4 * delta + 200000 * L := by
      calc
        _ ≤ 4 * delta + 100000 * (2 * L) :=
          add_le_add hpole2Le
            (mul_le_mul_of_nonneg_left (by simpa only [L] using hscale2)
              (by norm_num))
        _ = 4 * delta + 200000 * L := by ring
    have hzeta2Cast := hzeta2'.trans hrhs
    convert hzeta2Cast using 1 <;> push_cast <;> ring
  have hpos := threeCharacter_neg_logDeriv_re_nonneg chi₁ hu rho.im
  have hlog0 := logDeriv_principalOne_eq_riemannZeta
    (s := (u : ℂ)) (by simpa using hu)
  have hlogT := logDeriv_principalOne_eq_riemannZeta
    (s := (u : ℂ) + Complex.I * rho.im) (by simpa using hu)
  have hlog2T := logDeriv_principalOne_eq_riemannZeta
    (s := (u : ℂ) + Complex.I * (2 * rho.im)) (by simpa using hu)
  simp only [one_pow] at hpos
  have hlogT' :
      logDeriv (DirichletCharacter.LFunction
        (1 : DirichletCharacter ℂ 1))
          ((u : ℂ) + Complex.I * rho.im) =
        logDeriv riemannZeta ((u : ℂ) + Complex.I * rho.im) := by
    simpa only [chi₁] using hlogT
  have hlog2T' :
      logDeriv (DirichletCharacter.LFunction
        (1 : DirichletCharacter ℂ 1))
          ((u : ℂ) + Complex.I * (2 * rho.im)) =
        logDeriv riemannZeta ((u : ℂ) + Complex.I * (2 * rho.im)) := by
    simpa only [chi₁] using hlog2T
  rw [hlogT', hlog2T'] at hpos
  have hup : 0 ≤
      3 * (1 / delta + 100000 * L) +
      4 * (16 * delta + 100000 * L - 1 / a) +
      (4 * delta + 200000 * L) := by
    linarith
  rw [hdeltaInv] at hup
  let R : ℝ := 1 / a
  have hrecipL' : 3900000000 * L < 4 * R := by
    simpa only [R, div_eq_mul_inv, one_mul] using hrecipL
  change 0 ≤
      3 * (1000000000 * L + 100000 * L) +
      4 * (16 * delta + 100000 * L - R) +
      (4 * delta + 200000 * L) at hup
  nlinarith

end
end MAPPrincipalKoukTheorem12Three

#print axioms MAPPrincipalKoukTheorem12Three.neg_logDeriv_riemannZeta_re_le_general
#print axioms MAPPrincipalKoukTheorem12Three.neg_logDeriv_riemannZeta_re_le_selected
#print axioms MAPPrincipalKoukTheorem12Three.neg_logDeriv_riemannZeta_re_le_pair
#print axioms MAPPrincipalKoukTheorem12Three.conj_mem_centeredUnitWindowSupport_principal
#print axioms MAPPrincipalKoukTheorem12Three.high_principal_nearOne_zero_absent
