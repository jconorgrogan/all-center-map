import RealCharacterLFunctionConjugation

/-!
# Primitive-character zero-free alternative (Koukoulopoulos, Theorem 12.3)

This file instantiates the `3-4-1` inequality with the unconditional forms of
Lemma 12.2.  It keeps the square-character pole explicit and uses conjugation
symmetry only in the short-ordinate real-character case.
-/

namespace MAPKoukTheorem12ThreePrimitive

set_option maxHeartbeats 800000

open Complex Set DirichletZeros MAPMellinDetectorLeaf MAPLocalZeroWindow MAPZeroFreeSiegelSpine
open MAPPrimitiveLogDerivativeRemainderUnconditional
open MAPPrincipalLogDerivativeRemainderUnconditional
open MAPKoukLemma12TwoSpecializations
open MAPRealCharacterLFunctionConjugation
open scoped BigOperators ComplexConjugate

noncomputable section

/-- Doubling the ordinate costs at most a factor two in the arithmetic scale. -/
theorem arithmeticScale_double_le_two_mul {q : ℕ} [NeZero q] (t : ℝ) :
    arithmeticScale q (2 * t) ≤ 2 * arithmeticScale q t := by
  have hq0 : (0 : ℝ) ≤ q := by positivity
  unfold arithmeticScale
  rw [abs_mul]
  norm_num
  nlinarith [abs_nonneg t]

/-- The doubled-height logarithm is absorbed by twice the original one. -/
theorem log_arithmeticScale_double_le_two_mul {q : ℕ} [NeZero q] (t : ℝ) :
    Real.log (arithmeticScale q (2 * t)) ≤
      2 * Real.log (arithmeticScale q t) := by
  let S := arithmeticScale q t
  have hS2 : 2 ≤ S := two_le_arithmeticScale t
  have hdouble := arithmeticScale_double_le_two_mul (q := q) t
  have hpos : 0 < arithmeticScale q (2 * t) := by
    linarith [two_le_arithmeticScale (q := q) (2 * t)]
  have hpow : 2 * S ≤ S ^ (2 : ℕ) := by nlinarith
  calc
    Real.log (arithmeticScale q (2 * t)) ≤ Real.log (S ^ (2 : ℕ)) :=
      Real.log_le_log hpos (hdouble.trans hpow)
    _ = 2 * Real.log S := by rw [Real.log_pow]; norm_num

/-- The zeta term in `3-4-1`, with its pole and the certified principal
remainder retained separately. -/
theorem neg_logDeriv_riemannZeta_re_le
    {u : ℝ} (hu : 1 < u) (hu2 : u ≤ 2) :
    (-logDeriv riemannZeta (u : ℂ)).re ≤
      1 / (u - 1) + 100000 * Real.log 2 := by
  have hformula :=
    neg_logDeriv_riemannZeta_eq_pole_sub_centered_add_remainder
      (u := u) (t := 0) hu
  have hpoles := re_centeredZeroPoleSum_nonneg
    (1 : DirichletCharacter ℂ 1) hu.le (t := 0)
  have hrem := principalLogDerivativeRemainder_le (t := 0) hu hu2
  have hremRe :
      (primitiveLogDerivativeRemainder
        (1 : DirichletCharacter ℂ 1) u 0).re ≤
        100000 * Real.log 2 := by
    have := (Complex.re_le_norm _).trans hrem
    simpa [arithmeticScale] using this
  have hre := congrArg Complex.re hformula
  simp only [Complex.neg_re, Complex.add_re, Complex.sub_re] at hre
  norm_num at hformula hpoles hre ⊢
  have hgap : u - 1 ≠ 0 := by linarith
  have hnorm : Complex.normSq ((u : ℂ) - 1) = (u - 1) ^ 2 := by
    rw [Complex.normSq_apply]
    simp
    ring
  rw [hnorm] at hre
  have hrecip : (u - 1) / (u - 1) ^ 2 = 1 / (u - 1) := by
    field_simp
  rw [hrecip] at hre
  simp only [one_div] at hre ⊢
  linarith

/-- Empty-selected-list Lemma 12.2, converted to the upper bound for the
negative logarithmic derivative used in `3-4-1`. -/
theorem neg_logDeriv_square_re_le
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {u t : ℝ} (hu : 1 < u) (hu2 : u ≤ 2) :
    (-logDeriv (DirichletCharacter.LFunction (chi ^ 2))
        ((u : ℂ) + Complex.I * (2 * t))).re ≤
      (if chi ^ 2 = 1 then
          (1 / (((u : ℂ) + Complex.I * (2 * t)) - 1)).re else 0) +
        204004 * Real.log (arithmeticScale q t) := by
  have h := logDeriv_LFunction_re_ge_empty (chi ^ 2)
    (u := u) (t := 2 * t) hu hu2
  have hscale := log_arithmeticScale_double_le_two_mul (q := q) t
  simp only [Complex.neg_re]
  push_cast at h ⊢
  by_cases hsq : chi ^ 2 = 1
  · rw [if_pos hsq] at h ⊢
    nlinarith
  · rw [if_neg hsq] at h ⊢
    nlinarith

/-- Selected-zero Lemma 12.2 as an upper bound for `-L'/L`. -/
theorem neg_logDeriv_selected_re_le
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive) (hchi : chi ≠ 1)
    {u t : ℝ} (hu : 1 < u) (hu2 : u ≤ 2)
    {rho : ℂ} (hrho : rho ∈ centeredUnitWindowSupport chi (1 / 2) t)
    (him : rho.im = t) :
    (-logDeriv (DirichletCharacter.LFunction chi)
        ((u : ℂ) + Complex.I * t)).re ≤
      17000 * Real.log (arithmeticScale q t) -
        (zeroMultiplicity chi (1 / 2)
          (windowHeight (t - 1 / 2)) rho : ℝ) / (u - rho.re) := by
  have h := logDeriv_LFunction_re_ge_selected_same_height
    chi hprim hchi hu hu2 hrho him
  simp only [Complex.neg_re]
  linarith

/-- For a real character and `|Im rho| <= 1/4`, the conjugate zero lies in
the same centered half-width window. -/
theorem conj_mem_centeredUnitWindowSupport_of_abs_im_le_quarter
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hchi : chi ≠ 1) (hsq : chi ^ 2 = 1)
    {rho : ℂ} (hrho : rho ∈ centeredUnitWindowSupport chi (1 / 2) rho.im)
    (him : |rho.im| ≤ 1 / 4) :
    conj rho ∈ centeredUnitWindowSupport chi (1 / 2) rho.im := by
  rw [centeredUnitWindowSupport, closedUnitWindowSupport, Finset.mem_filter]
    at hrho ⊢
  have hbase := conj_mem_zeroSupport_of_sq_eq_one chi hchi hsq hrho.1
  refine ⟨hbase, ?_⟩
  simp only [Complex.conj_im]
  constructor <;> linarith [le_abs_self rho.im, neg_abs_le rho.im]

/-- Real part of the conjugate zero's reciprocal pole contribution. -/
theorem re_conj_zeroPoleTerm
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {u : ℝ} {rho : ℂ} :
    (((zeroMultiplicity chi (1 / 2)
        (windowHeight (rho.im - 1 / 2)) (conj rho) : ℂ) /
      ((u : ℂ) + Complex.I * rho.im - conj rho)).re) =
      (zeroMultiplicity chi (1 / 2)
        (windowHeight (rho.im - 1 / 2)) (conj rho) : ℝ) *
        (u - rho.re) /
          ((u - rho.re) ^ 2 + (2 * rho.im) ^ 2) := by
  rw [Complex.div_re, Complex.normSq_apply]
  simp
  ring

/-- The centered pole sum contains both a nonreal zero and its conjugate.
Only positivity of their analytic multiplicities is used. -/
theorem re_centeredZeroPoleSum_ge_pair
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {u : ℝ} {rho : ℂ}
    (hu : 1 ≤ u)
    (hrho : rho ∈ centeredUnitWindowSupport chi (1 / 2) rho.im)
    (hconj : conj rho ∈ centeredUnitWindowSupport chi (1 / 2) rho.im)
    (hne : rho ≠ conj rho) :
    1 / (u - rho.re) +
        (u - rho.re) / ((u - rho.re) ^ 2 + (2 * rho.im) ^ 2) ≤
      (centeredZeroPoleSum chi rho.im
        ((u : ℂ) + Complex.I * rho.im)).re := by
  let S := centeredUnitWindowSupport chi (1 / 2) rho.im
  let w : ℂ → ℝ := fun z =>
    (((zeroMultiplicity chi (1 / 2)
        (windowHeight (rho.im - 1 / 2)) z : ℂ) /
      ((u : ℂ) + Complex.I * rho.im - z)).re)
  have hsub : ({rho, conj rho} : Finset ℂ) ⊆ S := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hrho
    · exact hconj
  have hw_nonneg : ∀ z ∈ S, 0 ≤ w z := by
    intro z hz
    exact re_centeredZeroPoleTerm_nonneg chi hu hz
  have hsum : ∑ z ∈ ({rho, conj rho} : Finset ℂ), w z ≤ ∑ z ∈ S, w z :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun z _ _ => hw_nonneg z ‹z ∈ S›)
  have hmrho : 1 ≤ zeroMultiplicity chi (1 / 2)
      (windowHeight (rho.im - 1 / 2)) rho := by
    have hp := zeroMultiplicity_pos_of_mem chi _ _
      (mem_zeroSupport_of_mem_centeredUnitWindowSupport chi hrho)
    omega
  have hmconj : 1 ≤ zeroMultiplicity chi (1 / 2)
      (windowHeight (rho.im - 1 / 2)) (conj rho) := by
    have hp := zeroMultiplicity_pos_of_mem chi _ _
      (mem_zeroSupport_of_mem_centeredUnitWindowSupport chi hconj)
    omega
  have hgap : 0 < u - rho.re := by
    have hre := re_lt_one_of_mem_zeroSupport chi
      (mem_zeroSupport_of_mem_centeredUnitWindowSupport chi hrho)
    linarith
  have hden : 0 < (u - rho.re) ^ 2 + (2 * rho.im) ^ 2 := by positivity
  have hw_rho : 1 / (u - rho.re) ≤ w rho := by
    have heq := re_centeredZeroPoleTerm_eq_reciprocal_of_im_eq
      chi (by linarith : rho.re < u) (ρ := rho) (t := rho.im) rfl
    dsimp [w]
    rw [heq]
    exact (div_le_div_iff_of_pos_right hgap).2 (by exact_mod_cast hmrho)
  have hw_conj :
      (u - rho.re) / ((u - rho.re) ^ 2 + (2 * rho.im) ^ 2) ≤
        w (conj rho) := by
    dsimp [w]
    rw [re_conj_zeroPoleTerm]
    apply (div_le_div_iff_of_pos_right hden).2
    nlinarith [show (1 : ℝ) ≤
      (zeroMultiplicity chi (1 / 2)
        (windowHeight (rho.im - 1 / 2)) (conj rho) : ℝ) by exact_mod_cast hmconj]
  rw [Finset.sum_insert (by simpa using hne), Finset.sum_singleton] at hsum
  have hsum' : w rho + w (conj rho) ≤
      (centeredZeroPoleSum chi rho.im
        ((u : ℂ) + Complex.I * rho.im)).re := by
    rw [centeredZeroPoleSum, Complex.re_sum]
    change w rho + w (conj rho) ≤ ∑ z ∈ S, w z
    exact hsum
  exact add_le_add hw_rho hw_conj |>.trans hsum' 

/-- Pair-selected version of Lemma 12.2 for the small nonzero real-character
case. -/
theorem neg_logDeriv_pair_re_le
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive) (hchi : chi ≠ 1)
    {u : ℝ} {rho : ℂ} (hu : 1 < u) (hu2 : u ≤ 2)
    (hrho : rho ∈ centeredUnitWindowSupport chi (1 / 2) rho.im)
    (hconj : conj rho ∈ centeredUnitWindowSupport chi (1 / 2) rho.im)
    (hne : rho ≠ conj rho) :
    (-logDeriv (DirichletCharacter.LFunction chi)
        ((u : ℂ) + Complex.I * rho.im)).re ≤
      17000 * Real.log (arithmeticScale q rho.im) -
        (1 / (u - rho.re) +
          (u - rho.re) / ((u - rho.re) ^ 2 + (2 * rho.im) ^ 2)) := by
  have hformula := neg_logDeriv_LFunction_eq_centeredZeroSum_add_remainder
    chi hchi hu.le rho.im
  have hpairs := re_centeredZeroPoleSum_ge_pair chi hu.le hrho hconj hne
  have hrem := primitiveLogDerivativeRemainder_le chi hprim hchi
    (t := rho.im) hu hu2
  have hremRe :
      (primitiveLogDerivativeRemainder chi u rho.im).re ≤
        17000 * Real.log (arithmeticScale q rho.im) :=
    (Complex.re_le_norm _).trans hrem
  have hre := congrArg Complex.re hformula
  simp only [Complex.neg_re, Complex.add_re] at hre ⊢
  linarith

/-- Real part of the vertical principal pole. -/
theorem re_vertical_pole {delta t : ℝ} :
    (1 / (((1 + delta : ℝ) : ℂ) + Complex.I * (2 * t) - 1)).re =
      delta / (delta ^ 2 + (2 * t) ^ 2) := by
  rw [Complex.div_re, Complex.normSq_apply]
  simp
  ring

/-- At ordinate larger than `1/4`, the principal square-character pole is
small compared with its horizontal displacement. -/
theorem vertical_pole_le_four_delta
    {delta t : ℝ} (hdelta : 0 < delta) (ht : 1 / 4 < |t|) :
    delta / (delta ^ 2 + (2 * t) ^ 2) ≤ 4 * delta := by
  have ht2 : (1 / 4 : ℝ) < (2 * t) ^ 2 := by
    have hs : (1 / 4 : ℝ) ^ 2 < t ^ 2 := sq_lt_sq.mpr (by simpa using ht)
    norm_num at hs ⊢
    nlinarith
  have hden : 0 < delta ^ 2 + (2 * t) ^ 2 := by positivity
  apply (div_le_iff₀ hden).2
  nlinarith [sq_nonneg delta]

/-- The factor four on the conjugate pole dominates the principal square
pole when the horizontal distances differ only by the zero gap. -/
theorem vertical_pole_le_four_conjugate_pole
    {delta a c : ℝ} (hdelta : 0 < delta) (hda : delta ≤ a)
    (ha2 : a ≤ 2 * delta) (hc : 0 ≤ c) :
    delta / (delta ^ 2 + c) ≤ 4 * (a / (a ^ 2 + c)) := by
  have ha : 0 < a := hdelta.trans_le hda
  have hd0 : 0 < delta ^ 2 + c := by positivity
  have ha0 : 0 < a ^ 2 + c := by positivity
  rw [show 4 * (a / (a ^ 2 + c)) = (4 * a) / (a ^ 2 + c) by ring]
  rw [div_le_div_iff₀ hd0 ha0]
  have h1 : 0 ≤ delta * a * (4 * delta - a) := by
    have hfour : 0 ≤ 4 * delta - a := by linarith
    exact mul_nonneg (mul_nonneg hdelta.le ha.le) hfour
  have h2 : 0 ≤ c * (4 * a - delta) := by
    have : 0 ≤ 4 * a - delta := by linarith
    positivity
  nlinarith

/-- Source-shaped primitive part of Theorem 12.3.  A zero in the near-one
collar is necessarily a simple real zero of a real character.  The explicit
constant is intentionally large; only its absolute and uniform nature is
used downstream. -/
theorem primitive_nearOne_zero_is_exceptional
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive) (hchi : chi ≠ 1)
    {rho : ℂ}
    (hrho : rho ∈ centeredUnitWindowSupport chi (1 / 2) rho.im)
    (hnear : 1 - rho.re <
      1 / (100000000000 * Real.log (arithmeticScale q rho.im))) :
    chi ^ 2 = 1 ∧ rho.im = 0 ∧
      zeroMultiplicity chi (1 / 2)
        (windowHeight (rho.im - 1 / 2)) rho = 1 := by
  let L := Real.log (arithmeticScale q rho.im)
  let delta := 1 / (1000000000 * L)
  let u := 1 + delta
  have hS2 := two_le_arithmeticScale (q := q) rho.im
  have hlog2le : Real.log 2 ≤ L := by
    dsimp [L]
    exact Real.log_le_log (by norm_num) hS2
  have hL : 1 / 2 < L := by
    nlinarith [Real.log_two_gt_d9]
  have hdelta : 0 < delta := by
    dsimp [delta]
    positivity
  have hdelta_inv : 1 / delta = 1000000000 * L := by
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
  have hrelt := re_lt_one_of_mem_zeroSupport chi
    (mem_zeroSupport_of_mem_centeredUnitWindowSupport chi hrho)
  let gap := 1 - rho.re
  let a := u - rho.re
  have hgap0 : 0 < gap := by dsimp [gap]; linarith
  have hnear' : gap < delta / 100 := by
    dsimp [gap, delta, L] at hnear ⊢
    convert hnear using 1 <;> ring
  have haeq : a = delta + gap := by dsimp [a, u, gap]; ring
  have ha : 0 < a := by rw [haeq]; linarith
  have hada : delta ≤ a := by rw [haeq]; linarith
  have ha101 : a < (101 / 100 : ℝ) * delta := by
    rw [haeq]
    linarith
  have ha2 : a ≤ 2 * delta := by linarith
  have hrecip : 39 / (10 * delta) < 4 / a := by
    rw [div_lt_div_iff₀ (by positivity : 0 < 10 * delta) ha]
    nlinarith
  have hdelta_le_L : delta ≤ L := by
    have hLsq : 1 ≤ 1000000000 * L ^ 2 := by nlinarith
    dsimp [delta]
    rw [div_le_iff₀ (by positivity : 0 < 1000000000 * L)]
    nlinarith
  have hmultPos := zeroMultiplicity_pos_of_mem chi _ _
    (mem_zeroSupport_of_mem_centeredUnitWindowSupport chi hrho)
  have hm1 : (1 : ℝ) ≤
      (zeroMultiplicity chi (1 / 2)
        (windowHeight (rho.im - 1 / 2)) rho : ℝ) := by
    exact_mod_cast (show 1 ≤ zeroMultiplicity chi (1 / 2)
      (windowHeight (rho.im - 1 / 2)) rho by omega)
  have hzeta0 := neg_logDeriv_riemannZeta_re_le hu hu2
  have hzeta : (-logDeriv riemannZeta (u : ℂ)).re ≤
      1 / delta + 100000 * L := by
    dsimp [u] at hzeta0 ⊢
    have hgapu : (1 + delta - 1) = delta := by ring
    rw [hgapu] at hzeta0
    exact hzeta0.trans (by nlinarith)
  have hrecipL : 3900000000 * L < 4 / a := by
    calc
      3900000000 * L = 39 / (10 * delta) := by
        rw [show 39 / (10 * delta) = (39 / 10) * (1 / delta) by field_simp]
        rw [hdelta_inv]
        ring
      _ < 4 / a := hrecip
  have hchi0 := neg_logDeriv_selected_re_le chi hprim hchi hu hu2 hrho rfl
  have hchiBound :
      (-logDeriv (DirichletCharacter.LFunction chi)
        ((u : ℂ) + Complex.I * rho.im)).re ≤
      17000 * L - 1 / a := by
    dsimp [L, a]
    exact hchi0.trans (by
      have := (div_le_div_iff_of_pos_right ha).2 hm1
      linarith)
  have hsquare := neg_logDeriv_square_re_le chi hu hu2 (t := rho.im)
  dsimp [L] at hsquare
  have hpos := threeCharacter_neg_logDeriv_re_nonneg chi hu rho.im
  by_cases hsq : chi ^ 2 = 1
  · by_cases him : rho.im = 0
    · by_cases hone : zeroMultiplicity chi (1 / 2)
          (windowHeight (rho.im - 1 / 2)) rho = 1
      · exact ⟨hsq, him, hone⟩
      have hm2 : (2 : ℝ) ≤
          (zeroMultiplicity chi (1 / 2)
            (windowHeight (rho.im - 1 / 2)) rho : ℝ) := by
        have hm2nat : 2 ≤ zeroMultiplicity chi (1 / 2)
            (windowHeight (rho.im - 1 / 2)) rho := by omega
        exact_mod_cast hm2nat
      have hchi2 :
          (-logDeriv (DirichletCharacter.LFunction chi)
            ((u : ℂ) + Complex.I * rho.im)).re ≤
          17000 * L - 2 / a := by
        exact hchi0.trans (by
          dsimp [L, a]
          have := (div_le_div_iff_of_pos_right ha).2 hm2
          linarith)
      have hpole :
          (1 / (((u : ℂ) + Complex.I * (2 * rho.im)) - 1)).re =
            1 / delta := by
        rw [him]
        dsimp [u]
        norm_num
      rw [if_pos hsq, hpole] at hsquare
      have hsquareBound :
          (-logDeriv (DirichletCharacter.LFunction (chi ^ 2))
            ((u : ℂ) + Complex.I * (2 * rho.im))).re ≤
          1 / delta + 204004 * L := by
        simpa only [Complex.neg_re] using hsquare
      have hup : 0 ≤
          3 * (1 / delta + 100000 * L) +
          4 * (17000 * L - 2 / a) +
          (1 / delta + 204004 * L) := by
        linarith [hpos, hzeta, hchi2, hsquareBound]
      rw [hdelta_inv] at hup
      simp only [div_eq_mul_inv] at hrecipL hup
      linarith
    · by_cases hsmall : |rho.im| ≤ 1 / 4
      · have hconj :=
          conj_mem_centeredUnitWindowSupport_of_abs_im_le_quarter
            chi hchi hsq hrho hsmall
        have hne : rho ≠ conj rho := by
          intro heq
          have := congrArg Complex.im heq
          simp only [Complex.conj_im] at this
          apply him
          linarith
        have hpair := neg_logDeriv_pair_re_le chi hprim hchi hu hu2 hrho hconj hne
        let e := a / (a ^ 2 + (2 * rho.im) ^ 2)
        let p := delta / (delta ^ 2 + (2 * rho.im) ^ 2)
        have hpair' :
            (-logDeriv (DirichletCharacter.LFunction chi)
              ((u : ℂ) + Complex.I * rho.im)).re ≤
            17000 * L - (1 / a + e) := by
          simpa [L, a, e] using hpair
        have hpole :
            (1 / (((u : ℂ) + Complex.I * (2 * rho.im)) - 1)).re = p := by
          dsimp [u, p]
          exact re_vertical_pole
        rw [if_pos hsq, hpole] at hsquare
        have hc : 0 ≤ (2 * rho.im) ^ 2 := sq_nonneg _
        have hpe : p ≤ 4 * e := by
          dsimp [p, e]
          exact vertical_pole_le_four_conjugate_pole hdelta hada ha2 hc
        have hsquareBound :
            (-logDeriv (DirichletCharacter.LFunction (chi ^ 2))
              ((u : ℂ) + Complex.I * (2 * rho.im))).re ≤
            p + 204004 * L := by
          simpa only [Complex.neg_re] using hsquare
        have hup : 0 ≤
            3 * (1 / delta + 100000 * L) +
            4 * (17000 * L - (1 / a + e)) +
            (p + 204004 * L) := by
          linarith [hpos, hzeta, hpair', hsquareBound]
        rw [hdelta_inv] at hup
        simp only [div_eq_mul_inv] at hrecipL hup
        linarith
      · have hlarge : 1 / 4 < |rho.im| := lt_of_not_ge hsmall
        let p := delta / (delta ^ 2 + (2 * rho.im) ^ 2)
        have hpole :
            (1 / (((u : ℂ) + Complex.I * (2 * rho.im)) - 1)).re = p := by
          dsimp [u, p]
          exact re_vertical_pole
        rw [if_pos hsq, hpole] at hsquare
        have hp : p ≤ 4 * delta := by
          dsimp [p]
          exact vertical_pole_le_four_delta hdelta hlarge
        have hsquareBound :
            (-logDeriv (DirichletCharacter.LFunction (chi ^ 2))
              ((u : ℂ) + Complex.I * (2 * rho.im))).re ≤
            p + 204004 * L := by
          simpa only [Complex.neg_re] using hsquare
        have hup : 0 ≤
            3 * (1 / delta + 100000 * L) +
            4 * (17000 * L - 1 / a) +
            (p + 204004 * L) := by
          linarith [hpos, hzeta, hchiBound, hsquareBound]
        rw [hdelta_inv] at hup
        simp only [div_eq_mul_inv] at hrecipL hup
        linarith
  · rw [if_neg hsq] at hsquare
    have hsquareBound :
        (-logDeriv (DirichletCharacter.LFunction (chi ^ 2))
          ((u : ℂ) + Complex.I * (2 * rho.im))).re ≤
        204004 * L := by
      simpa only [Complex.neg_re, zero_add] using hsquare
    have hup : 0 ≤
        3 * (1 / delta + 100000 * L) +
        4 * (17000 * L - 1 / a) +
        204004 * L := by
      linarith [hpos, hzeta, hchiBound, hsquareBound]
    rw [hdelta_inv] at hup
    simp only [div_eq_mul_inv] at hrecipL hup
    linarith

#print axioms MAPKoukTheorem12ThreePrimitive.neg_logDeriv_riemannZeta_re_le
#print axioms MAPKoukTheorem12ThreePrimitive.neg_logDeriv_square_re_le
#print axioms MAPKoukTheorem12ThreePrimitive.neg_logDeriv_pair_re_le
#print axioms MAPKoukTheorem12ThreePrimitive.primitive_nearOne_zero_is_exceptional

end

end MAPKoukTheorem12ThreePrimitive
