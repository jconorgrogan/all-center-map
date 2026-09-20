import RamachandraPrincipalResidueContinuity
import RamachandraPrincipalLowRange
import RamachandraShiftedDirectShellAbsorption
import KoukGaussDigammaSeries

/-!
# Explicit second-moment budget for the conductor-one residue

The translated zeta pole appears only at conductor one.  Its coefficient has
the closed formula certified in `RamachandraPrincipalResidueContinuity`.  This
module bounds that formula directly from Gamma decay and the certified Gauss
digamma estimate; it never feeds a fourth moment back into the remainder.
-/

namespace RamachandraPrincipalRemainderBudget

open Complex MeasureTheory Set Filter Topology
open scoped Interval Topology BigOperators
open RamachandraPrincipalHighContourIdentity
open RamachandraPrincipalHighSourceIdentity
open RamachandraPrincipalResidueContinuity
open RamachandraPrimitiveShiftedContourReduction
open RamachandraTheorem6SourceProofChain
open RamachandraPrincipalHighContourTails

noncomputable section

set_option maxHeartbeats 800000

/-- Log convexity between the two unit values gives the elementary bound
`Gamma(x) ≤ 1` on `[1,2]`. -/
theorem Real.Gamma_Icc_one_two_le_one {x : ℝ}
    (hx1 : 1 ≤ x) (hx2 : x ≤ 2) : Real.Gamma x ≤ 1 := by
  rcases hx1.eq_or_lt with rfl | hx1lt
  · simp
  rcases hx2.eq_or_lt with rfl | hx2lt
  · simp
  let a : ℝ := 2 - x
  let b : ℝ := x - 1
  have ha : 0 < a := by dsimp [a]; linarith
  have hb : 0 < b := by dsimp [b]; linarith
  have hab : a + b = 1 := by dsimp [a, b]; ring
  have hconv := Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma
    (s := (1 : ℝ)) (t := 2) (a := a) (b := b)
    (by norm_num) (by norm_num) ha hb hab
  have harg : a * (1 : ℝ) + b * 2 = x := by
    dsimp [a, b]
    ring
  rw [harg, Real.Gamma_one, Real.Gamma_two,
    Real.one_rpow, Real.one_rpow, mul_one] at hconv
  exact hconv

/-- A uniform Gamma envelope on `1 ≤ Re z ≤ 2`, including the compact
ordinates omitted by the large-height contour estimate. -/
theorem norm_Gamma_one_two_le_expEnvelope
    {a t : ℝ} (ha1 : 1 ≤ a) (ha2 : a ≤ 2) :
    ‖Complex.Gamma ((a : ℂ) + t * I)‖ ≤
      36 * (1 + |t|) ^ 2 * Real.exp (-|t|) := by
  by_cases ht : 1 ≤ |t|
  · exact (RamachandraShiftedGammaPoleContour.norm_Gamma_ramachandraHorizontalStrip_le_exp
      (a := a) (t := t) (by linarith) ha2 ht).trans (by gcongr <;> norm_num)
  · have htlt : |t| < 1 := lt_of_not_ge ht
    have hGamma := MAPMellinDetectorLeaf.norm_Gamma_le_realGamma_re
      (s := (a : ℂ) + t * I) (by simp; linarith)
    have hreal : Real.Gamma a ≤ 1 := Real.Gamma_Icc_one_two_le_one ha1 ha2
    have hexple : 1 ≤ 3 * Real.exp (-|t|) := by
      have he : Real.exp |t| ≤ 3 :=
        (Real.exp_le_exp.mpr htlt.le).trans Real.exp_one_lt_three.le
      have hm := mul_le_mul_of_nonneg_right he (Real.exp_pos (-|t|)).le
      rw [← Real.exp_add] at hm
      norm_num at hm
      exact hm
    calc
      ‖Complex.Gamma ((a : ℂ) + t * I)‖ ≤ Real.Gamma a := by simpa using hGamma
      _ ≤ 1 := hreal
      _ ≤ 3 * Real.exp (-|t|) := hexple
      _ ≤ 36 * (1 + |t|) ^ 2 * Real.exp (-|t|) := by
        have hb : 1 ≤ (1 + |t|) ^ 2 := by nlinarith [abs_nonneg t]
        nlinarith [Real.exp_pos (-|t|)]

/-- The derivative form of the digamma identity away from Gamma's (absent)
zeros. -/
theorem deriv_Gamma_eq_digamma_mul_Gamma {z : ℂ}
    (hz : ∀ m : ℕ, z ≠ -(m : ℂ)) :
    deriv Complex.Gamma z = Complex.digamma z * Complex.Gamma z := by
  rw [Complex.digamma_def, logDeriv_apply]
  field_simp [Complex.Gamma_ne_zero hz]

/-- Joint Gamma/Gamma-derivative exponential decay in the exact strip used by
the principal residue.  The constant is existential only because the already
certified Gauss digamma theorem exposes its absolute constant existentially. -/
theorem exists_gamma_deriv_one_two_expEnvelope :
    ∃ Cg : ℝ, 0 < Cg ∧ ∀ (a t : ℝ), 1 ≤ a → a ≤ 2 →
      ‖Complex.Gamma ((a : ℂ) + t * I)‖ +
          ‖deriv Complex.Gamma ((a : ℂ) + t * I)‖ ≤
        Cg * (1 + |t|) ^ 3 * Real.exp (-|t|) := by
  obtain ⟨Cd, hCd, hdig⟩ := KoukGaussDigammaSeries.rightHalfPlaneDigammaLogBound
  refine ⟨36 + 108 * Cd, by positivity, ?_⟩
  intro a t ha1 ha2
  let z : ℂ := (a : ℂ) + t * I
  have hzre : z.re = a := by simp [z]
  have hG := norm_Gamma_one_two_le_expEnvelope ha1 ha2 (t := t)
  have hDg := hdig z (by simpa [hzre] using ha1)
  have hznorm : ‖z‖ ≤ 2 + |t| := by
    calc
      ‖z‖ ≤ ‖(a : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
      _ = |a| + |t| := by simp
      _ ≤ 2 + |t| := by
        rw [abs_of_nonneg (by linarith)]
        linarith
  have hlogpos : 0 < ‖z‖ + 2 := by positivity
  have hlog : Real.log (‖z‖ + 2) ≤ 3 * (1 + |t|) := by
    have hraw := Real.log_le_sub_one_of_pos hlogpos
    nlinarith [abs_nonneg t]
  have hDg' : ‖Complex.digamma z‖ ≤ Cd * (3 * (1 + |t|)) := by
    exact hDg.trans (mul_le_mul_of_nonneg_left hlog hCd.le)
  have hzPole : ∀ m : ℕ, z ≠ -(m : ℂ) := by
    intro m hm
    have hre := congrArg Complex.re hm
    simp [z] at hre
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hderivEq := deriv_Gamma_eq_digamma_mul_Gamma hzPole
  have hD : ‖deriv Complex.Gamma z‖ ≤
      108 * Cd * (1 + |t|) ^ 3 * Real.exp (-|t|) := by
    rw [hderivEq, norm_mul]
    calc
      ‖Complex.digamma z‖ * ‖Complex.Gamma z‖ ≤
          (Cd * (3 * (1 + |t|))) *
            (36 * (1 + |t|) ^ 2 * Real.exp (-|t|)) := by gcongr
      _ = 108 * Cd * (1 + |t|) ^ 3 * Real.exp (-|t|) := by ring
  calc
    ‖Complex.Gamma z‖ + ‖deriv Complex.Gamma z‖ ≤
        36 * (1 + |t|) ^ 2 * Real.exp (-|t|) +
          108 * Cd * (1 + |t|) ^ 3 * Real.exp (-|t|) := add_le_add hG hD
    _ ≤ (36 + 108 * Cd) * (1 + |t|) ^ 3 * Real.exp (-|t|) := by
      have hb : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
      have hp : (1 + |t|) ^ 2 ≤ (1 + |t|) ^ 3 :=
        pow_le_pow_right₀ hb (by norm_num)
      nlinarith [Real.exp_pos (-|t|), hCd]

/-- Pointwise residue envelope in the full coarse source strip.  All moving
arithmetic has disappeared; the only scale factor is `T^(1-sigma)`. -/
theorem norm_principalTranslatedResidueClosedForm_le
    {Cg T sigma t : ℝ} (hCg : 0 < Cg) (hT : 3 ≤ T)
    (hsigma0 : 0 ≤ sigma) (hsigma1 : sigma ≤ 3 / 4)
    (hGD : ‖Complex.Gamma
          (principalTranslatedPole (ramachandraShiftedPoint sigma t) + 1)‖ +
        ‖deriv Complex.Gamma
          (principalTranslatedPole (ramachandraShiftedPoint sigma t) + 1)‖ ≤
      Cg * (1 + |t|) ^ 3 * Real.exp (-|t|)) :
    ‖principalTranslatedResidueClosedForm T
        (principalTranslatedPole (ramachandraShiftedPoint sigma t))‖ ≤
      (64 * (1 + ‖MAPPrincipalZetaFixedStrip.principalRegularized 1‖) ^ 2 *
          (1 + ‖deriv MAPPrincipalZetaFixedStrip.principalRegularized 1‖) * Cg) *
        T ^ (1 - sigma) * (1 + Real.log T) *
          (1 + |t|) ^ 3 * Real.exp (-|t|) := by
  let p : ℂ := principalTranslatedPole (ramachandraShiftedPoint sigma t)
  let F : ℂ := MAPPrincipalZetaFixedStrip.principalRegularized 1
  let D : ℂ := deriv MAPPrincipalZetaFixedStrip.principalRegularized 1
  let B : ℝ := (1 + |t|) ^ 3 * Real.exp (-|t|)
  have hTpos : 0 < T := by linarith
  have hpRe : p.re = 1 - sigma := by
    simp [p, principalTranslatedPole, ramachandraShiftedPoint]
  have hpNorm : (1 / 4 : ℝ) ≤ ‖p‖ := by
    have hre := Complex.abs_re_le_norm p
    rw [hpRe] at hre
    have : (0 : ℝ) ≤ 1 - sigma := by linarith
    rw [abs_of_nonneg this] at hre
    linarith
  have hp : p ≠ 0 := by
    intro h
    rw [h, norm_zero] at hpNorm
    norm_num at hpNorm
  have hinv : ‖p⁻¹‖ ≤ 4 := by
    rw [norm_inv]
    exact (inv_le_comm₀ (norm_pos_iff.mpr hp) (by norm_num)).2 (by nlinarith)
  have hinv2 : ‖(p ^ 2)⁻¹‖ ≤ 16 := by
    rw [norm_inv, norm_pow]
    have hp2 : (1 / 16 : ℝ) ≤ ‖p‖ ^ 2 := by nlinarith [sq_nonneg ‖p‖]
    exact (inv_le_comm₀ (sq_pos_of_pos (norm_pos_iff.mpr hp)) (by norm_num)).2
      (by nlinarith)
  have hpow : ‖(T : ℂ) ^ p‖ = T ^ (1 - sigma) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hTpos, hpRe]
  have hlogpos : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hlog : ‖Complex.log (T : ℂ)‖ = Real.log T := by
    rw [← Complex.ofReal_log hTpos.le, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hlogpos]
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hG : ‖Complex.Gamma (p + 1)‖ ≤ Cg * B := by
    dsimp [p, B]
    nlinarith [norm_nonneg
      (deriv Complex.Gamma
        (principalTranslatedPole (ramachandraShiftedPoint sigma t) + 1))]
  have hDG : ‖deriv Complex.Gamma (p + 1)‖ ≤ Cg * B := by
    dsimp [p, B]
    nlinarith [norm_nonneg
      (Complex.Gamma
        (principalTranslatedPole (ramachandraShiftedPoint sigma t) + 1))]
  have hF0 : 0 ≤ ‖F‖ := norm_nonneg _
  have hD0 : 0 ≤ ‖D‖ := norm_nonneg _
  have hL : 1 ≤ 1 + Real.log T := by linarith
  have hP : 0 ≤ T ^ (1 - sigma) := Real.rpow_nonneg hTpos.le _
  have hbase0 : 0 ≤
      (1 + ‖F‖) ^ 2 * (1 + ‖D‖) * Cg *
        T ^ (1 - sigma) * (1 + Real.log T) * B := by positivity
  have hN1 :
      ‖2 * F * D * Complex.Gamma (p + 1) * (T : ℂ) ^ p‖ ≤
        2 * ((1 + ‖F‖) ^ 2 * (1 + ‖D‖) * Cg *
          T ^ (1 - sigma) * (1 + Real.log T) * B) := by
    simp only [norm_mul]
    rw [hpow]
    rw [show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
    have hFle : ‖F‖ ≤ (1 + ‖F‖) ^ 2 := by nlinarith [sq_nonneg (1 + ‖F‖)]
    have hDle : ‖D‖ ≤ 1 + ‖D‖ := by linarith
    calc
      2 * ‖F‖ * ‖D‖ * ‖Complex.Gamma (p + 1)‖ * T ^ (1 - sigma) ≤
          2 * (1 + ‖F‖) ^ 2 * (1 + ‖D‖) * (Cg * B) *
            T ^ (1 - sigma) := by gcongr
      _ ≤ 2 * ((1 + ‖F‖) ^ 2 * (1 + ‖D‖) * Cg *
          T ^ (1 - sigma) * (1 + Real.log T) * B) := by
        rw [show 2 * ((1 + ‖F‖) ^ 2 * (1 + ‖D‖) * Cg *
          T ^ (1 - sigma) * (1 + Real.log T) * B) =
            (2 * (1 + ‖F‖) ^ 2 * (1 + ‖D‖) * (Cg * B) *
              T ^ (1 - sigma)) * (1 + Real.log T) by ring]
        exact le_mul_of_one_le_right (by positivity) hL
  have hN2 :
      ‖F ^ 2 * deriv Complex.Gamma (p + 1) * (T : ℂ) ^ p‖ ≤
        (1 + ‖F‖) ^ 2 * (1 + ‖D‖) * Cg *
          T ^ (1 - sigma) * (1 + Real.log T) * B := by
    rw [norm_mul, norm_mul, norm_pow, hpow]
    have hFpow : ‖F‖ ^ 2 ≤ (1 + ‖F‖) ^ 2 := by nlinarith
    calc
      ‖F‖ ^ 2 * ‖deriv Complex.Gamma (p + 1)‖ * T ^ (1 - sigma) ≤
          (1 + ‖F‖) ^ 2 * (Cg * B) * T ^ (1 - sigma) := by gcongr
      _ ≤ (1 + ‖F‖) ^ 2 * (1 + ‖D‖) * Cg *
          T ^ (1 - sigma) * (1 + Real.log T) * B := by
        rw [show (1 + ‖F‖) ^ 2 * (1 + ‖D‖) * Cg *
          T ^ (1 - sigma) * (1 + Real.log T) * B =
            ((1 + ‖F‖) ^ 2 * (Cg * B) * T ^ (1 - sigma)) *
              ((1 + ‖D‖) * (1 + Real.log T)) by ring]
        exact le_mul_of_one_le_right (by positivity)
          (one_le_mul_of_one_le_of_one_le (by linarith) hL)
  have hN3 :
      ‖F ^ 2 * Complex.Gamma (p + 1) *
          ((T : ℂ) ^ p * Complex.log (T : ℂ))‖ ≤
        (1 + ‖F‖) ^ 2 * (1 + ‖D‖) * Cg *
          T ^ (1 - sigma) * (1 + Real.log T) * B := by
    rw [norm_mul, norm_mul, norm_mul, norm_pow, hpow, hlog]
    have hFpow : ‖F‖ ^ 2 ≤ (1 + ‖F‖) ^ 2 := by nlinarith
    have hlogle : Real.log T ≤ 1 + Real.log T := by linarith
    calc
      ‖F‖ ^ 2 * ‖Complex.Gamma (p + 1)‖ *
          (T ^ (1 - sigma) * Real.log T) ≤
          (1 + ‖F‖) ^ 2 * (Cg * B) *
            (T ^ (1 - sigma) * Real.log T) := by gcongr
      _ ≤ (1 + ‖F‖) ^ 2 * (1 + ‖D‖) * Cg *
          T ^ (1 - sigma) * (1 + Real.log T) * B := by
        calc
          _ ≤ (1 + ‖F‖) ^ 2 * (Cg * B) *
              (T ^ (1 - sigma) * (1 + Real.log T)) := by gcongr
          _ ≤ (1 + ‖F‖) ^ 2 * (1 + ‖D‖) * Cg *
              T ^ (1 - sigma) * (1 + Real.log T) * B := by
            have hfac : 1 ≤ 1 + ‖D‖ := by linarith
            nlinarith [mul_le_mul_of_nonneg_left hfac (by positivity :
              0 ≤ (1 + ‖F‖) ^ 2 * (Cg * B) *
                (T ^ (1 - sigma) * (1 + Real.log T)))]
  unfold principalTranslatedResidueClosedForm
  change ‖((2 * F * D * Complex.Gamma (p + 1) * (T : ℂ) ^ p) +
      (F ^ 2 * deriv Complex.Gamma (p + 1) * (T : ℂ) ^ p) +
      (F ^ 2 * Complex.Gamma (p + 1) *
        ((T : ℂ) ^ p * Complex.log (T : ℂ)))) / p -
      (F ^ 2 * Complex.Gamma (p + 1) * (T : ℂ) ^ p) / p ^ 2‖ ≤ _
  have hcorr :
      ‖F ^ 2 * Complex.Gamma (p + 1) * (T : ℂ) ^ p‖ ≤
        (1 + ‖F‖) ^ 2 * (1 + ‖D‖) * Cg *
          T ^ (1 - sigma) * (1 + Real.log T) * B := by
    rw [norm_mul, norm_mul, norm_pow, hpow]
    have hFpow : ‖F‖ ^ 2 ≤ (1 + ‖F‖) ^ 2 := by nlinarith
    calc
      ‖F‖ ^ 2 * ‖Complex.Gamma (p + 1)‖ * T ^ (1 - sigma) ≤
          (1 + ‖F‖) ^ 2 * (Cg * B) * T ^ (1 - sigma) := by gcongr
      _ ≤ (1 + ‖F‖) ^ 2 * (1 + ‖D‖) * Cg *
          T ^ (1 - sigma) * (1 + Real.log T) * B := by
        rw [show (1 + ‖F‖) ^ 2 * (1 + ‖D‖) * Cg *
          T ^ (1 - sigma) * (1 + Real.log T) * B =
            ((1 + ‖F‖) ^ 2 * (Cg * B) * T ^ (1 - sigma)) *
              ((1 + ‖D‖) * (1 + Real.log T)) by ring]
        exact le_mul_of_one_le_right (by positivity)
          (one_le_mul_of_one_le_of_one_le (by linarith) hL)
  have hsum :
      ‖(2 * F * D * Complex.Gamma (p + 1) * (T : ℂ) ^ p) +
          (F ^ 2 * deriv Complex.Gamma (p + 1) * (T : ℂ) ^ p) +
          (F ^ 2 * Complex.Gamma (p + 1) *
            ((T : ℂ) ^ p * Complex.log (T : ℂ)))‖ ≤
        ‖2 * F * D * Complex.Gamma (p + 1) * (T : ℂ) ^ p‖ +
          ‖F ^ 2 * deriv Complex.Gamma (p + 1) * (T : ℂ) ^ p‖ +
          ‖F ^ 2 * Complex.Gamma (p + 1) *
            ((T : ℂ) ^ p * Complex.log (T : ℂ))‖ := by
    exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  calc
    _ ≤ ‖((2 * F * D * Complex.Gamma (p + 1) * (T : ℂ) ^ p) +
          (F ^ 2 * deriv Complex.Gamma (p + 1) * (T : ℂ) ^ p) +
          (F ^ 2 * Complex.Gamma (p + 1) *
            ((T : ℂ) ^ p * Complex.log (T : ℂ)))) / p‖ +
        ‖(F ^ 2 * Complex.Gamma (p + 1) * (T : ℂ) ^ p) / p ^ 2‖ :=
      norm_sub_le _ _
    _ = ‖(2 * F * D * Complex.Gamma (p + 1) * (T : ℂ) ^ p) +
          (F ^ 2 * deriv Complex.Gamma (p + 1) * (T : ℂ) ^ p) +
          (F ^ 2 * Complex.Gamma (p + 1) *
            ((T : ℂ) ^ p * Complex.log (T : ℂ)))‖ * ‖p⁻¹‖ +
        ‖F ^ 2 * Complex.Gamma (p + 1) * (T : ℂ) ^ p‖ * ‖(p ^ 2)⁻¹‖ := by
      simp only [div_eq_mul_inv, norm_mul]
    _ ≤ (‖2 * F * D * Complex.Gamma (p + 1) * (T : ℂ) ^ p‖ +
          ‖F ^ 2 * deriv Complex.Gamma (p + 1) * (T : ℂ) ^ p‖ +
          ‖F ^ 2 * Complex.Gamma (p + 1) *
            ((T : ℂ) ^ p * Complex.log (T : ℂ))‖) * ‖p⁻¹‖ +
        ‖F ^ 2 * Complex.Gamma (p + 1) * (T : ℂ) ^ p‖ * ‖(p ^ 2)⁻¹‖ := by
      exact add_le_add (mul_le_mul_of_nonneg_right hsum (norm_nonneg _)) le_rfl
    _ ≤ (64 * (1 + ‖F‖) ^ 2 * (1 + ‖D‖) * Cg) *
          T ^ (1 - sigma) * (1 + Real.log T) * B := by
      calc
        _ ≤ ((2 * ((1 + ‖F‖) ^ 2 * (1 + ‖D‖) * Cg *
                T ^ (1 - sigma) * (1 + Real.log T) * B) +
              ((1 + ‖F‖) ^ 2 * (1 + ‖D‖) * Cg *
                T ^ (1 - sigma) * (1 + Real.log T) * B) +
              ((1 + ‖F‖) ^ 2 * (1 + ‖D‖) * Cg *
                T ^ (1 - sigma) * (1 + Real.log T) * B)) * 4 +
            ((1 + ‖F‖) ^ 2 * (1 + ‖D‖) * Cg *
              T ^ (1 - sigma) * (1 + Real.log T) * B) * 16) := by
          gcongr
        _ ≤ (64 * (1 + ‖F‖) ^ 2 * (1 + ‖D‖) * Cg) *
              T ^ (1 - sigma) * (1 + Real.log T) * B := by
          nlinarith
    _ = _ := by dsimp [F, D, B]; ring

/-- Uniform pointwise envelope for the literal conductor-one source
remainder throughout Ramachandra's stated strip. -/
theorem exists_principalShiftedSourceRemainder_pointwiseEnvelope :
    ∃ Cr : ℝ, 0 < Cr ∧ ∀ (T sigma t : ℝ), 3 ≤ T →
      0 ≤ sigma → sigma ≤ 3 / 4 →
      ‖principalShiftedSourceRemainder T sigma t‖ ≤
        Cr * T ^ (1 - sigma) * (1 + Real.log T) *
          (1 + |t|) ^ 3 * Real.exp (-|t|) := by
  obtain ⟨Cg, hCg, hGDall⟩ := exists_gamma_deriv_one_two_expEnvelope
  let Cr : ℝ :=
    64 * (1 + ‖MAPPrincipalZetaFixedStrip.principalRegularized 1‖) ^ 2 *
      (1 + ‖deriv MAPPrincipalZetaFixedStrip.principalRegularized 1‖) * Cg
  refine ⟨Cr, by dsimp [Cr]; positivity, ?_⟩
  intro T sigma t hT hsigma0 hsigma1
  have hTpos : 0 < T := by linarith
  have hsigmaLt : sigma < 1 := by linarith
  rw [principalShiftedSourceRemainder_eq_neg_closedForm hTpos hsigmaLt,
    norm_neg]
  apply norm_principalTranslatedResidueClosedForm_le hCg hT hsigma0 hsigma1
  have hGD := hGDall (2 - sigma) (-t) (by linarith) (by linarith)
  convert hGD using 1 <;>
    simp [principalTranslatedPole, ramachandraShiftedPoint, Cr,
      abs_neg, add_comm, add_left_comm, add_assoc] <;> ring

/-- The fixed integrable mass used to turn the pointwise residue envelope
into a second moment. -/
def principalResidueEnvelopeMass : ℝ :=
  ∫ t : ℝ, (1 + |t|) ^ 14 * Real.exp (-|t|)

theorem principalResidueEnvelopeMass_nonneg :
    0 ≤ principalResidueEnvelopeMass := by
  unfold principalResidueEnvelopeMass
  exact integral_nonneg fun t => by positivity

theorem principalResidueEnvelopeMass_lt_top :
    Integrable (fun t : ℝ => (1 + |t|) ^ 14 * Real.exp (-|t|)) :=
  integrable_one_add_abs_pow_fourteen_mul_exp_neg_abs

theorem intervalIntegral_le_fullIntegral_of_nonneg
    {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : Integrable f) (hnonneg : ∀ y, 0 ≤ f y) :
    (∫ y in a..b, f y) ≤ ∫ y : ℝ, f y := by
  rw [intervalIntegral.integral_of_le hab]
  exact integral_mono_measure Measure.restrict_le_self
    (Filter.Eventually.of_forall hnonneg) hf

/-- Squaring and integrating the pointwise residue envelope costs only the
fixed degree-fourteen exponential mass. -/
theorem principalShiftedSourceRemainder_secondMoment_le
    {Cr T sigma : ℝ} (hCr : 0 < Cr) (hT : 3 ≤ T)
    (hsigma0 : 0 ≤ sigma) (hsigma1 : sigma ≤ 3 / 4)
    (hpoint : ∀ t : ℝ,
      ‖principalShiftedSourceRemainder T sigma t‖ ≤
        Cr * T ^ (1 - sigma) * (1 + Real.log T) *
          (1 + |t|) ^ 3 * Real.exp (-|t|)) :
    (∫ t in (-T)..T, ‖principalShiftedSourceRemainder T sigma t‖ ^ 2) ≤
      (Cr * T ^ (1 - sigma) * (1 + Real.log T)) ^ 2 *
        principalResidueEnvelopeMass := by
  let A : ℝ := Cr * T ^ (1 - sigma) * (1 + Real.log T)
  let M : ℝ → ℝ := fun t =>
    (1 + |t|) ^ 14 * Real.exp (-|t|)
  have hTpos : 0 < T := by linarith
  have hlog : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hM0 : ∀ t, 0 ≤ M t := by intro t; dsimp [M]; positivity
  have hsmall (t : ℝ) :
      ((1 + |t|) ^ 3 * Real.exp (-|t|)) ^ 2 ≤ M t := by
    let r : ℝ := 1 + |t|
    let e : ℝ := Real.exp (-|t|)
    have hr : 1 ≤ r := by dsimp [r]; linarith [abs_nonneg t]
    have he0 : 0 ≤ e := (Real.exp_pos _).le
    have he1 : e ≤ 1 := by
      dsimp [e]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg t))
    have hp : r ^ 6 ≤ r ^ 14 := pow_le_pow_right₀ hr (by norm_num)
    have he : e ^ 2 ≤ e := by nlinarith
    dsimp [M, r, e]
    calc
      ((1 + |t|) ^ 3 * Real.exp (-|t|)) ^ 2 =
          (1 + |t|) ^ 6 * Real.exp (-|t|) ^ 2 := by ring
      _ ≤ (1 + |t|) ^ 14 * Real.exp (-|t|) := by
        exact mul_le_mul hp he (sq_nonneg _) (by positivity)
  have hpw (t : ℝ) :
      ‖principalShiftedSourceRemainder T sigma t‖ ^ 2 ≤ A ^ 2 * M t := by
    have ht := hpoint t
    have ht' : ‖principalShiftedSourceRemainder T sigma t‖ ≤
        A * ((1 + |t|) ^ 3 * Real.exp (-|t|)) := by
      simpa [A, mul_assoc] using ht
    calc
      ‖principalShiftedSourceRemainder T sigma t‖ ^ 2 ≤
          (A * ((1 + |t|) ^ 3 * Real.exp (-|t|))) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) ht' 2
      _ = A ^ 2 * (((1 + |t|) ^ 3 * Real.exp (-|t|)) ^ 2) := by ring
      _ ≤ A ^ 2 * M t :=
        mul_le_mul_of_nonneg_left (hsmall t) (sq_nonneg A)
  have hremCont := continuous_principalShiftedSourceRemainder_sq
    hTpos (by linarith : sigma < 1)
  have hMcont : Continuous M := by
    dsimp [M]
    fun_prop
  calc
    (∫ t in (-T)..T, ‖principalShiftedSourceRemainder T sigma t‖ ^ 2) ≤
        ∫ t in (-T)..T, A ^ 2 * M t := by
      apply intervalIntegral.integral_mono_on (by linarith)
      · exact hremCont.intervalIntegrable _ _
      · exact (continuous_const.mul hMcont).intervalIntegrable _ _
      · intro t ht
        exact hpw t
    _ = A ^ 2 * ∫ t in (-T)..T, M t := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ A ^ 2 * principalResidueEnvelopeMass := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg A)
      exact intervalIntegral_le_fullIntegral_of_nonneg (by linarith)
        (by simpa [M] using principalResidueEnvelopeMass_lt_top) hM0
    _ = _ := by rfl

/-- The exact Theorem 6 strip turns the scale factor from the residue into at
most `3T`. -/
theorem sourceStrip_rpow_two_one_sub_sigma_le_three_mul
    (q : ℕ) [NeZero q] {T sigma : ℝ} (hT : 3 ≤ T)
    (hstrip : |sigma - (1 / 2 : ℝ)| ≤
      (100 * Real.log ((q : ℝ) * T))⁻¹) :
    T ^ (2 * (1 - sigma)) ≤ 3 * T := by
  let R : ℝ := (q : ℝ) * T
  let delta : ℝ := (100 * Real.log R)⁻¹
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hTpos : 0 < T := by linarith
  have hR3 : 3 ≤ R := by dsimp [R]; nlinarith
  have hRpos : 0 < R := by linarith
  have hlogR : 0 < Real.log R := Real.log_pos (by linarith)
  have hdelta : 0 ≤ delta := by dsimp [delta]; positivity
  have hTleR : T ≤ R := by dsimp [R]; nlinarith
  have hlogTR : Real.log T ≤ Real.log R :=
    Real.log_le_log hTpos hTleR
  have hsigmaLow : 1 / 2 - delta ≤ sigma := by
    have h := (abs_le.mp hstrip).1
    simpa [delta, R] using (show 1 / 2 - delta ≤ sigma by linarith)
  have hexponent : 2 * (1 - sigma) ≤ 1 + 2 * delta := by linarith
  have hrpow := Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ T) hexponent
  have hprod : 2 * delta * Real.log T ≤ 2 / 100 := by
    calc
      2 * delta * Real.log T ≤ 2 * delta * Real.log R := by gcongr
      _ = 2 / 100 := by
        dsimp [delta]
        field_simp
  have hexp : Real.exp (2 * delta * Real.log T) ≤ 3 := by
    calc
      Real.exp (2 * delta * Real.log T) ≤ Real.exp 1 :=
        Real.exp_le_exp.mpr (hprod.trans (by norm_num))
      _ ≤ 3 := Real.exp_one_lt_three.le
  calc
    T ^ (2 * (1 - sigma)) ≤ T ^ (1 + 2 * delta) := hrpow
    _ = T * Real.exp (2 * delta * Real.log T) := by
      rw [Real.rpow_add hTpos, Real.rpow_one,
        Real.rpow_def_of_pos hTpos]
      congr 1
      ring
    _ ≤ T * 3 := mul_le_mul_of_nonneg_left hexp hTpos.le
    _ = 3 * T := by ring

/-- Premise-free source-shaped conductor-one residue budget. -/
theorem exists_principalShiftedSourceRemainder_sourceStripBudget :
    ∃ Crem : ℝ, 0 < Crem ∧ ∀ (q : ℕ) [NeZero q]
      (T sigma : ℝ), 3 ≤ T →
      |sigma - (1 / 2 : ℝ)| ≤
          (100 * Real.log ((q : ℝ) * T))⁻¹ →
      (∫ t in (-T)..T, ‖principalShiftedSourceRemainder T sigma t‖ ^ 2) ≤
        Crem * T * Real.log T ^ 200 := by
  obtain ⟨Cr, hCr, hpoint⟩ :=
    exists_principalShiftedSourceRemainder_pointwiseEnvelope
  let J : ℝ := principalResidueEnvelopeMass
  let Crem : ℝ := 12 * Cr ^ 2 * (1 + J)
  have hJ : 0 ≤ J := by
    simpa [J] using principalResidueEnvelopeMass_nonneg
  refine ⟨Crem, by dsimp [Crem]; positivity, ?_⟩
  intro q _instq T sigma hT hstrip
  obtain ⟨hsigma0, hsigma1⟩ :=
    RamachandraPrincipalLowRange.sigma_mem_zero_threequarters_of_ramachandraStrip
      hT hstrip
  have hraw := principalShiftedSourceRemainder_secondMoment_le
    hCr hT hsigma0 hsigma1 (fun t => hpoint T sigma t hT hsigma0 hsigma1)
  have hscale := sourceStrip_rpow_two_one_sub_sigma_le_three_mul
    q hT hstrip
  have hlog1 : 1 ≤ Real.log T :=
    (RamachandraShiftedDirectParameters.one_lt_log_of_three_le hT).le
  have hlogsq : (1 + Real.log T) ^ 2 ≤ 4 * Real.log T ^ 200 := by
    have htwo : 1 + Real.log T ≤ 2 * Real.log T := by linarith
    have hsquare : (1 + Real.log T) ^ 2 ≤ (2 * Real.log T) ^ 2 := by
      gcongr
    have hp : Real.log T ^ 2 ≤ Real.log T ^ 200 :=
      pow_le_pow_right₀ hlog1 (by norm_num)
    nlinarith
  have hrewrite :
      (Cr * T ^ (1 - sigma) * (1 + Real.log T)) ^ 2 =
        Cr ^ 2 * T ^ (2 * (1 - sigma)) * (1 + Real.log T) ^ 2 := by
    have hrp : (T ^ (1 - sigma)) ^ 2 = T ^ (2 * (1 - sigma)) := by
      rw [← Real.rpow_mul_natCast (by linarith : 0 ≤ T)]
      congr 1
      ring
    rw [mul_pow, mul_pow, hrp]
  rw [hrewrite] at hraw
  calc
    (∫ t in (-T)..T, ‖principalShiftedSourceRemainder T sigma t‖ ^ 2) ≤
        Cr ^ 2 * T ^ (2 * (1 - sigma)) *
          (1 + Real.log T) ^ 2 * J := by simpa [J] using hraw
    _ ≤ Cr ^ 2 * (3 * T) * (4 * Real.log T ^ 200) * J := by
      gcongr
    _ ≤ (12 * Cr ^ 2 * (1 + J)) * T * Real.log T ^ 200 := by
      have hnonneg : 0 ≤ 12 * Cr ^ 2 * T * Real.log T ^ 200 := by positivity
      calc
        Cr ^ 2 * (3 * T) * (4 * Real.log T ^ 200) * J =
            (12 * Cr ^ 2 * T * Real.log T ^ 200) * J := by ring
        _ ≤ (12 * Cr ^ 2 * T * Real.log T ^ 200) * (1 + J) := by
          exact mul_le_mul_of_nonneg_left (by linarith) hnonneg
        _ = (12 * Cr ^ 2 * (1 + J)) * T * Real.log T ^ 200 := by ring
    _ = Crem * T * Real.log T ^ 200 := by rfl

/-- Final primitive-family remainder leaf.  It is the preceding residue
budget at conductor one and vanishes identically at every other conductor. -/
theorem exists_canonicalPrimitiveShiftedRemainder_sourceStripBudget :
    ∃ Crem : ℝ, 0 < Crem ∧ ∀ (q d : ℕ) [NeZero q] [NeZero d]
      (T sigma : ℝ), d ∣ q → 3 ≤ T →
      |sigma - (1 / 2 : ℝ)| ≤
          (100 * Real.log ((q : ℝ) * T))⁻¹ →
      primitiveFamilyRemainderSecondMoment d T
          (fun psi t => canonicalPrimitiveShiftedRemainder psi T sigma t) ≤
        Crem * ((d : ℝ) * T) * Real.log ((d : ℝ) * T) ^ 200 := by
  obtain ⟨Crem, hCrem, hprincipal⟩ :=
    exists_principalShiftedSourceRemainder_sourceStripBudget
  refine ⟨Crem, hCrem, ?_⟩
  intro q d _instq _instd T sigma hdq hT hstrip
  by_cases hd : d = 1
  · subst d
    have hmain := hprincipal q T sigma hT hstrip
    have hprim : (default : DirichletCharacter ℂ 1).IsPrimitive :=
      DirichletCharacter.isPrimitive_one_level_one
    simpa [primitiveFamilyRemainderSecondMoment,
      canonicalPrimitiveShiftedRemainder, hprim] using hmain
  · have hzero : primitiveFamilyRemainderSecondMoment d T
        (fun psi t => canonicalPrimitiveShiftedRemainder psi T sigma t) = 0 := by
      unfold primitiveFamilyRemainderSecondMoment
      simp [canonicalPrimitiveShiftedRemainder, hd]
    rw [hzero]
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast NeZero.pos d
    have hlog : 0 ≤ Real.log ((d : ℝ) * T) :=
      Real.log_nonneg (by nlinarith)
    positivity

end
end RamachandraPrincipalRemainderBudget

#print axioms RamachandraPrincipalRemainderBudget.norm_Gamma_one_two_le_expEnvelope
#print axioms RamachandraPrincipalRemainderBudget.exists_gamma_deriv_one_two_expEnvelope
#print axioms RamachandraPrincipalRemainderBudget.norm_principalTranslatedResidueClosedForm_le
#print axioms RamachandraPrincipalRemainderBudget.exists_canonicalPrimitiveShiftedRemainder_sourceStripBudget
