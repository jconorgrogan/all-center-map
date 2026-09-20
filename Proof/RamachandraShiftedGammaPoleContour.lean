import RamachandraShiftedRightLineIdentity
import FinitePoleRectangle
import GoldfeldFourfoldContour
import GammaCompactStrip
import PrimitiveLFixedStripGrowthCertified

/-!
# The Gamma-pole contour in shifted Ramachandra Lemma 3

This file removes the first complex-analytic ambiguity in the omitted
shifted proof on printed p. 88.  For a nonprincipal primitive character, the
integrand

`L(s+w,chi)^2 * Gamma(w) * X^w`

has exactly one pole in the strip `Re w > -1`, namely the Gamma pole at
`w = 0`.  We construct its holomorphic remainder and prove the exact finite
rectangle residue identity.  No limiting contour estimate or fourth-moment
bound is assumed here.
-/

namespace RamachandraShiftedGammaPoleContour

open Complex MeasureTheory Set Filter
open scoped Interval Topology
open FinitePoleRectangle
open MAPGoldfeldSiegel

noncomputable section

set_option maxHeartbeats 800000

/-! ## A Gamma envelope on the literal Lemma 3 horizontal strip -/

/-- The elementary recurrences extend the certified compact-strip Gamma
decay to the whole range crossed by the shifted Lemma 3 rectangle.  The
quadratic factor is intentionally generous and keeps the proof independent
of a complex Stirling theorem. -/
theorem norm_Gamma_ramachandraHorizontalStrip_le_exp
    {a t : ℝ} (haLo : -(3 / 2 : ℝ) ≤ a) (haHi : a ≤ 2)
    (ht : 1 ≤ |t|) :
    ‖Complex.Gamma ((a : ℂ) + t * I)‖ ≤
      12 * (1 + |t|) ^ 2 * Real.exp (-|t|) := by
  let z : ℂ := (a : ℂ) + t * I
  have ht0 : t ≠ 0 := by
    intro h
    subst t
    norm_num at ht
  have hz : z ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp [z, ht0] at him
  have hz1 : z + 1 ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp [z, ht0] at him
  by_cases haNeg : a < -(1 / 2 : ℝ)
  · have hshiftLo : (1 / 2 : ℝ) ≤ a + 2 := by linarith
    have hshiftHi : a + 2 ≤ 3 / 2 := by linarith
    have hG := GammaCompactStripScratch.norm_Gamma_positive_strip_le_exp
      hshiftLo hshiftHi (t := t)
    have hrec : Complex.Gamma (z + 2) =
        (z + 1) * z * Complex.Gamma z := by
      calc
        Complex.Gamma (z + 2) = Complex.Gamma ((z + 1) + 1) := by ring_nf
        _ = (z + 1) * Complex.Gamma (z + 1) :=
          Complex.Gamma_add_one (z + 1) hz1
        _ = (z + 1) * z * Complex.Gamma z := by
          rw [Complex.Gamma_add_one z hz]
          ring
    have hnorm : ‖Complex.Gamma (z + 2)‖ =
        ‖z + 1‖ * ‖z‖ * ‖Complex.Gamma z‖ := by
      rw [hrec, norm_mul, norm_mul]
    have hzT : 1 ≤ ‖z‖ := ht.trans (by
      simpa [z] using Complex.abs_im_le_norm z)
    have hz1T : 1 ≤ ‖z + 1‖ := ht.trans (by
      simpa [z] using Complex.abs_im_le_norm (z + 1))
    have hsmall : ‖Complex.Gamma z‖ ≤ ‖Complex.Gamma (z + 2)‖ := by
      rw [hnorm]
      calc
        ‖Complex.Gamma z‖ = 1 * (1 * ‖Complex.Gamma z‖) := by ring
        _ ≤ ‖z + 1‖ * (‖z‖ * ‖Complex.Gamma z‖) := by
          gcongr
        _ = ‖z + 1‖ * ‖z‖ * ‖Complex.Gamma z‖ := by ring
    calc
      ‖Complex.Gamma ((a : ℂ) + t * I)‖ =
          ‖Complex.Gamma z‖ := rfl
      _ ≤ ‖Complex.Gamma (z + 2)‖ := hsmall
      _ = ‖Complex.Gamma (((a + 2 : ℝ) : ℂ) + t * I)‖ := by
        congr 2
        apply Complex.ext <;> simp [z]
      _ ≤ 12 * (1 + |t|) * Real.exp (-|t|) := by
        simpa [GammaCompactStripScratch.stripPoint] using hG
      _ ≤ 12 * (1 + |t|) ^ 2 * Real.exp (-|t|) := by
        have hone : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
        have he : 0 ≤ Real.exp (-|t|) := Real.exp_pos _ |>.le
        have hfac : 1 + |t| ≤ (1 + |t|) ^ 2 := by
          nlinarith [abs_nonneg t]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hfac (by norm_num)) he
  · have haMidLo : -(1 / 2 : ℝ) ≤ a := le_of_not_gt haNeg
    by_cases haMidHi : a ≤ 1 / 2
    · have hG := GammaCompactStripScratch.norm_Gamma_compactStrip_le_exp
        haMidLo haMidHi ht
      have hone : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
      have he : 0 ≤ Real.exp (-|t|) := Real.exp_pos _ |>.le
      calc
        ‖Complex.Gamma ((a : ℂ) + t * I)‖ ≤
            12 * (1 + |t|) * Real.exp (-|t|) := by
          simpa [GammaCompactStripScratch.stripPoint] using hG
        _ ≤ 12 * (1 + |t|) ^ 2 * Real.exp (-|t|) := by
          have hfac : 1 + |t| ≤ (1 + |t|) ^ 2 := by
            nlinarith [abs_nonneg t]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hfac (by norm_num)) he
    · have haPosLo : (1 / 2 : ℝ) ≤ a := (lt_of_not_ge haMidHi).le
      by_cases haPosHi : a ≤ 3 / 2
      · have hG := GammaCompactStripScratch.norm_Gamma_positive_strip_le_exp
          haPosLo haPosHi (t := t)
        have hone : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
        have he : 0 ≤ Real.exp (-|t|) := Real.exp_pos _ |>.le
        calc
          ‖Complex.Gamma ((a : ℂ) + t * I)‖ ≤
              12 * (1 + |t|) * Real.exp (-|t|) := by
            simpa [GammaCompactStripScratch.stripPoint] using hG
          _ ≤ 12 * (1 + |t|) ^ 2 * Real.exp (-|t|) := by
            have hfac : 1 + |t| ≤ (1 + |t|) ^ 2 := by
              nlinarith [abs_nonneg t]
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hfac (by norm_num)) he
      · have hbaseLo : (1 / 2 : ℝ) ≤ a - 1 := by linarith
        have hbaseHi : a - 1 ≤ 3 / 2 := by linarith
        let y : ℂ := (((a - 1 : ℝ) : ℂ) + t * I)
        have hy : y ≠ 0 := by
          intro h
          have him := congrArg Complex.im h
          simp [y, ht0] at him
        have hrec : Complex.Gamma (y + 1) = y * Complex.Gamma y :=
          Complex.Gamma_add_one y hy
        have hG := GammaCompactStripScratch.norm_Gamma_positive_strip_le_exp
          hbaseLo hbaseHi (t := t)
        have hyNorm : ‖y‖ ≤ 1 + |t| := by
          calc
            ‖y‖ ≤ |y.re| + |y.im| := Complex.norm_le_abs_re_add_abs_im y
            _ = |a - 1| + |t| := by simp [y]
            _ ≤ 1 + |t| := by
              rw [abs_of_nonneg (by linarith : 0 ≤ a - 1)]
              linarith
        have hform : ((a : ℂ) + t * I) = y + 1 := by
          apply Complex.ext <;> simp [y]
        calc
          ‖Complex.Gamma ((a : ℂ) + t * I)‖ =
              ‖y‖ * ‖Complex.Gamma y‖ := by
            rw [hform, hrec, norm_mul]
          _ ≤ (1 + |t|) *
              (12 * (1 + |t|) * Real.exp (-|t|)) := by
            apply mul_le_mul hyNorm
            · simpa [y, GammaCompactStripScratch.stripPoint] using hG
            · exact norm_nonneg _
            · positivity
          _ = 12 * (1 + |t|) ^ 2 * Real.exp (-|t|) := by ring

/-- On a finite horizontal segment, the Mellin scale has no hidden
dependence on the height. -/
theorem norm_posReal_cpow_horizontal_le_max
    {X a b x t : ℝ} (hX : 0 < X) (hax : a ≤ x) (hxb : x ≤ b) :
    ‖(X : ℂ) ^ ((x : ℂ) + t * I)‖ ≤
      max (X ^ a) (X ^ b) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hX]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
    sub_zero, add_zero]
  by_cases hXone : 1 ≤ X
  · exact (Real.rpow_le_rpow_of_exponent_le hXone hxb).trans (le_max_right _ _)
  · have hXle : X ≤ 1 := le_of_not_ge hXone
    exact (Real.rpow_le_rpow_of_exponent_ge hX hXle hax).trans
      (le_max_left _ _)

/-- Literal Mellin integrand in Ramachandra Lemma 3. -/
def shiftedGammaRawIntegrand {d : ℕ} [NeZero d]
    (psi : DirichletCharacter ℂ d) (s : ℂ) (X : ℝ) (w : ℂ) : ℂ :=
  DirichletCharacter.LFunction psi (s + w) ^ 2 *
    Complex.Gamma w * (X : ℂ) ^ w

/-- Uniform pointwise envelope on a Ramachandra horizontal edge.  It uses
only the certified fixed-strip polynomial L-bound and the Gamma recurrence
bound above. -/
theorem norm_shiftedGammaRawIntegrand_horizontal_le
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d)
    (hpsi : psi ≠ 1) (s : ℂ)
    {X a b x t : ℝ} (hX : 0 < X)
    (haLo : -(3 / 2 : ℝ) ≤ a) (hbHi : b ≤ 2)
    (hax : a ≤ x) (hxb : x ≤ b)
    (hLLo : -1 ≤ s.re + a) (hLHi : s.re + b ≤ 2)
    (ht : 1 ≤ |t|) :
    ‖shiftedGammaRawIntegrand psi s X ((x : ℂ) + t * I)‖ ≤
      480000 * (d : ℝ) ^ 4 * (5 + |s.im| + |t|) ^ 4 *
        (1 + |t|) ^ 2 * Real.exp (-|t|) *
          max (X ^ a) (X ^ b) := by
  let z : ℂ := s + ((x : ℂ) + t * I)
  have hzRe : z.re = s.re + x := by simp [z]
  have hzIm : z.im = s.im + t := by simp [z]
  have hzLo : -1 ≤ z.re := by
    dsimp [z]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_zero, add_zero]
    linarith
  have hzHi : z.re ≤ 2 := by
    dsimp [z]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_zero, add_zero]
    linarith
  have hrePos : 0 ≤ (z + 3).re := by
    rw [Complex.add_re, hzRe]
    norm_num
    linarith
  have hreAbs : |(z + 3).re| ≤ 5 := by
    rw [abs_of_nonneg hrePos]
    rw [Complex.add_re, hzRe]
    norm_num
    linarith
  have himAbs : |(z + 3).im| ≤ |s.im| + |t| := by
    rw [Complex.add_im, hzIm]
    norm_num
    exact abs_add_le s.im t
  have hzNorm : ‖z + 3‖ ≤ 5 + |s.im| + |t| := by
    calc
      ‖z + 3‖ ≤ |(z + 3).re| + |(z + 3).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ ≤ 5 + (|s.im| + |t|) := add_le_add hreAbs himAbs
      _ = 5 + |s.im| + |t| := by ring
  have hL0 := PLInteriorGrowth.norm_LFunction_fixedStrip_le
    psi hpsi hzLo hzHi
  have hL : ‖DirichletCharacter.LFunction psi z‖ ≤
      200 * (d : ℝ) ^ 2 * (5 + |s.im| + |t|) ^ 2 := by
    exact hL0.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) hzNorm 2) (by positivity))
  have hG := norm_Gamma_ramachandraHorizontalStrip_le_exp
    (haLo.trans hax) (hxb.trans hbHi) ht
  have hP := norm_posReal_cpow_horizontal_le_max hX hax hxb (t := t)
  unfold shiftedGammaRawIntegrand
  rw [norm_mul, norm_mul, norm_pow]
  calc
    ‖DirichletCharacter.LFunction psi z‖ ^ 2 *
          ‖Complex.Gamma ((x : ℂ) + t * I)‖ *
          ‖(X : ℂ) ^ ((x : ℂ) + t * I)‖ ≤
        (200 * (d : ℝ) ^ 2 * (5 + |s.im| + |t|) ^ 2) ^ 2 *
          (12 * (1 + |t|) ^ 2 * Real.exp (-|t|)) *
            max (X ^ a) (X ^ b) := by
      gcongr
    _ = 480000 * (d : ℝ) ^ 4 * (5 + |s.im| + |t|) ^ 4 *
        (1 + |t|) ^ 2 * Real.exp (-|t|) *
          max (X ^ a) (X ^ b) := by ring

/-- Literal uniform envelope for either horizontal edge at positive height
`B`. -/
def shiftedGammaHorizontalEnvelope
    (d : ℕ) (s : ℂ) (X a b B : ℝ) : ℝ :=
  480000 * (d : ℝ) ^ 4 * (5 + |s.im| + B) ^ 4 *
    (1 + B) ^ 2 * Real.exp (-B) * max (X ^ a) (X ^ b)

/-- The universal degree-six exponential envelope used on all vertical and
horizontal tails. -/
theorem integrable_one_add_abs_pow_six_mul_exp_neg_abs :
    Integrable (fun t : ℝ => (1 + |t|) ^ 6 * Real.exp (-|t|)) := by
  let f : ℝ → ℝ := fun t => (1 + |t|) ^ 6 * Real.exp (-|t|)
  have hposRaw : IntegrableOn
      (fun t : ℝ => (1 + t) ^ 6 * Real.exp (-t)) (Set.Ioi 0) := by
    have h0 := integrableOn_exp_neg_Ioi 0
    have h6 : IntegrableOn
        (fun t : ℝ => Real.exp (-t) * t ^ 6) (Set.Ioi 0) := by
      have h := Real.GammaIntegral_convergent
        (s := (7 : ℝ)) (by norm_num)
      convert h using 1
      ext t
      norm_num [Real.rpow_natCast]
    have hmajor : IntegrableOn
        (fun t : ℝ =>
          32 * (Real.exp (-t) + Real.exp (-t) * t ^ 6)) (Set.Ioi 0) :=
      (h0.add h6).const_mul 32
    apply hmajor.mono'
    · exact (by fun_prop : Continuous
        (fun t : ℝ => (1 + t) ^ 6 * Real.exp (-t))).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 ≤ t := ht.le
      have hp := add_pow_le (by norm_num : (0 : ℝ) ≤ 1) ht0 6
      norm_num at hp
      rw [Real.norm_of_nonneg
        (mul_nonneg (by positivity) (Real.exp_pos _).le)]
      calc
        (1 + t) ^ 6 * Real.exp (-t) ≤
            (32 * (1 + t ^ 6)) * Real.exp (-t) :=
          mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
        _ = 32 * (Real.exp (-t) + Real.exp (-t) * t ^ 6) := by ring
  have hpos : IntegrableOn f (Set.Ioi 0) := by
    apply hposRaw.congr_fun
    · intro t ht
      have ht' : 0 < t := ht
      simp [f, abs_of_pos ht']
    · exact measurableSet_Ioi
  have hneg0 := hpos.comp_neg
  rw [Set.neg_Ioi, neg_zero] at hneg0
  have hneg : IntegrableOn f (Set.Iio 0) := by
    apply hneg0.congr_fun
    · intro t ht
      simp [f]
    · exact measurableSet_Iio
  have hzero : IntegrableOn f ({0} : Set ℝ) := by
    exact integrableOn_singleton (μ := volume) (f := f) (hx := by simp)
  have hnonneg : IntegrableOn f (Set.Ici 0) := by
    have h := hpos.union hzero
    convert h using 1
    ext t
    simp [le_iff_lt_or_eq, or_comm]
  have hall := hneg.union hnonneg
  rw [Set.Iio_union_Ici] at hall
  exact integrableOn_univ.mp hall

/-- Continuity of a vertical slice away from the sole Gamma pole at zero.
The interval `-1 < c` excludes every other Gamma pole. -/
theorem continuous_shiftedGammaRaw_vertical
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d)
    (hpsi : psi ≠ 1) (s : ℂ) {X c : ℝ}
    (hX : 0 < X) (hcLo : -1 < c) (hc0 : c ≠ 0) :
    Continuous (fun t : ℝ =>
      shiftedGammaRawIntegrand psi s X ((c : ℂ) + t * I)) := by
  rw [continuous_iff_continuousAt]
  intro t
  unfold shiftedGammaRawIntegrand
  have hinner : ContinuousAt (fun u : ℝ => (c : ℂ) + u * I) t := by
    fun_prop
  have hL : ContinuousAt (fun u : ℝ =>
      DirichletCharacter.LFunction psi (s + ((c : ℂ) + u * I))) t :=
    ((DirichletCharacter.differentiable_LFunction hpsi).continuous.comp
      (by fun_prop)).continuousAt
  have hGammaPoint (m : ℕ) : ((c : ℂ) + t * I) ≠ -(m : ℂ) := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_zero, Complex.neg_re, Complex.natCast_re] at hre
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hmLt : (m : ℝ) < 1 := by linarith
    have hmNat : m < 1 := by exact_mod_cast hmLt
    have hm0 : m = 0 := Nat.lt_one_iff.mp hmNat
    subst m
    norm_num at hre
    exact hc0 hre
  have hGammaComp : ContinuousAt
      (Complex.Gamma ∘ (fun u : ℝ => (c : ℂ) + u * I)) t :=
    ContinuousAt.comp
      (f := fun u : ℝ => (c : ℂ) + u * I)
      (g := Complex.Gamma)
      (Complex.continuousAt_Gamma _ hGammaPoint) hinner
  have hGamma : ContinuousAt (fun u : ℝ =>
      Complex.Gamma ((c : ℂ) + u * I)) t := by
    simpa [Function.comp_def] using hGammaComp
  have hpow : ContinuousAt (fun u : ℝ =>
      (X : ℂ) ^ ((c : ℂ) + u * I)) t := by
    letI : NeZero (X : ℂ) :=
      ⟨Complex.ofReal_ne_zero.mpr hX.ne'⟩
    have hcpow : Continuous (fun z : ℂ => (X : ℂ) ^ z) :=
      continuous_const_cpow (X : ℂ)
    have hcomp : ContinuousAt
        ((fun z : ℂ => (X : ℂ) ^ z) ∘
          (fun u : ℝ => (c : ℂ) + u * I)) t :=
      ContinuousAt.comp
        (f := fun u : ℝ => (c : ℂ) + u * I)
        (g := fun z : ℂ => (X : ℂ) ^ z)
        hcpow.continuousAt hinner
    simpa [Function.comp_def] using hcomp
  exact ((hL.pow 2).mul hGamma).mul hpow

/-- Both vertical slices in the shifted Lemma 3 rectangle are integrable.
This closes the last premise of the infinite contour-shift theorem using the
same fixed-strip L-growth and Gamma decay as the horizontal edges. -/
theorem integrable_shiftedGammaRaw_vertical
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d)
    (hpsi : psi ≠ 1) (s : ℂ) {X c : ℝ}
    (hX : 0 < X) (hcLo : -1 < c) (hcHi : c ≤ 2) (hc0 : c ≠ 0)
    (hLLo : -1 ≤ s.re + c) (hLHi : s.re + c ≤ 2) :
    Integrable (fun t : ℝ =>
      shiftedGammaRawIntegrand psi s X ((c : ℂ) + t * I)) := by
  let F : ℝ → ℂ := fun t =>
    shiftedGammaRawIntegrand psi s X ((c : ℂ) + t * I)
  let C : ℝ := 5 + |s.im|
  let K : ℝ := 480000 * (d : ℝ) ^ 4 * C ^ 4 * X ^ c
  let E : ℝ → ℝ := fun t =>
    K * ((1 + |t|) ^ 6 * Real.exp (-|t|))
  let S : Set ℝ := {t | 1 ≤ |t|}
  have hcont : Continuous F := by
    simpa [F] using continuous_shiftedGammaRaw_vertical
      psi hpsi s hX hcLo hc0
  have hE : Integrable E := by
    exact integrable_one_add_abs_pow_six_mul_exp_neg_abs.const_mul K
  have htail : IntegrableOn F S := by
    apply hE.integrableOn.mono'
    · exact hcont.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem (by
          dsimp [S]
          exact measurableSet_le measurable_const measurable_abs :
          MeasurableSet S)] with t ht
      have hraw := norm_shiftedGammaRawIntegrand_horizontal_le
        psi hpsi s hX (a := c) (b := c) (x := c) (t := t)
        (by linarith) hcHi le_rfl le_rfl hLLo hLHi ht
      have hC : 1 ≤ C := by dsimp [C]; linarith [abs_nonneg s.im]
      have hu : 0 ≤ |t| := abs_nonneg t
      have hCu : C + |t| ≤ C * (1 + |t|) := by
        nlinarith
      have hpow : (C + |t|) ^ 4 ≤ C ^ 4 * (1 + |t|) ^ 4 := by
        calc
          (C + |t|) ^ 4 ≤ (C * (1 + |t|)) ^ 4 :=
            pow_le_pow_left₀ (by positivity) hCu 4
          _ = C ^ 4 * (1 + |t|) ^ 4 := by ring
      have hK : 0 ≤ 480000 * (d : ℝ) ^ 4 := by positivity
      have htailNonneg : 0 ≤
          (1 + |t|) ^ 2 * Real.exp (-|t|) * X ^ c := by positivity
      calc
        ‖F t‖ ≤
            480000 * (d : ℝ) ^ 4 * (C + |t|) ^ 4 *
              (1 + |t|) ^ 2 * Real.exp (-|t|) * X ^ c := by
          simpa [F, C, max_self] using hraw
        _ ≤ 480000 * (d : ℝ) ^ 4 *
              (C ^ 4 * (1 + |t|) ^ 4) *
              (1 + |t|) ^ 2 * Real.exp (-|t|) * X ^ c := by
          gcongr
        _ = E t := by
          dsimp [E, K]
          ring
  have hcentral : IntegrableOn F (Set.Icc (-1) 1) :=
    hcont.continuousOn.integrableOn_compact isCompact_Icc
  have hcover : Set.Icc (-1 : ℝ) 1 ∪ S = Set.univ := by
    ext t
    simp only [Set.mem_union, Set.mem_Icc, Set.mem_setOf_eq, Set.mem_univ,
      iff_true]
    by_cases h : -1 ≤ t ∧ t ≤ 1
    · exact Or.inl h
    · right
      rw [not_and_or] at h
      rcases h with h | h
      · have ht : t < -1 := lt_of_not_ge h
        dsimp [S]
        rw [abs_of_neg (by linarith)]
        linarith
      · have ht : 1 < t := lt_of_not_ge h
        dsimp [S]
        rw [abs_of_pos (by linarith)]
        linarith
  have hall := hcentral.union htail
  rw [hcover] at hall
  exact integrableOn_univ.mp hall

/-- The explicit edge envelope vanishes exponentially. -/
theorem tendsto_shiftedGammaHorizontalEnvelope_zero
    (d : ℕ) (s : ℂ) {X : ℝ} (hX : 0 < X) (a b : ℝ) :
    Tendsto (shiftedGammaHorizontalEnvelope d s X a b) atTop (𝓝 0) := by
  let C : ℝ := 5 + |s.im|
  let K : ℝ := 480000 * (d : ℝ) ^ 4 * max (X ^ a) (X ^ b)
  let G : ℝ → ℝ := fun B =>
    K * Real.exp C * ((B + C) ^ 6 * Real.exp (-(B + C)))
  have hshift : Tendsto (fun B : ℝ => B + C) atTop atTop :=
    tendsto_atTop_add_const_right atTop C tendsto_id
  have hpoly : Tendsto (fun B : ℝ =>
      (B + C) ^ 6 * Real.exp (-(B + C))) atTop (𝓝 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 6).comp hshift
  have hG : Tendsto G atTop (𝓝 0) := by
    have h := hpoly.const_mul (K * Real.exp C)
    simpa [G] using h
  apply squeeze_zero' (g := G)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with B hB
    unfold shiftedGammaHorizontalEnvelope
    positivity
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with B hB
    have hC : 1 ≤ C := by dsimp [C]; linarith [abs_nonneg s.im]
    have hbase : 0 ≤ B + C := by linarith
    have hone : 1 + B ≤ B + C := by linarith
    have hpowTwo : (1 + B) ^ 2 ≤ (B + C) ^ 2 := by
      exact pow_le_pow_left₀ (by positivity) hone 2
    have hpowFour : (5 + |s.im| + B) ^ 4 = (B + C) ^ 4 := by
      congr 1
      dsimp [C]
      ring
    have hcombine : (5 + |s.im| + B) ^ 4 * (1 + B) ^ 2 ≤
        (B + C) ^ 6 := by
      rw [hpowFour]
      calc
        (B + C) ^ 4 * (1 + B) ^ 2 ≤
            (B + C) ^ 4 * (B + C) ^ 2 :=
          mul_le_mul_of_nonneg_left hpowTwo (by positivity)
        _ = (B + C) ^ 6 := by ring
    have hK : 0 ≤ K := by
      dsimp [K]
      positivity
    have hexp : 0 ≤ Real.exp (-B) := Real.exp_pos _ |>.le
    have hrewrite : Real.exp C * Real.exp (-(B + C)) =
        Real.exp (-B) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      shiftedGammaHorizontalEnvelope d s X a b B =
          K * ((5 + |s.im| + B) ^ 4 * (1 + B) ^ 2 *
            Real.exp (-B)) := by
        dsimp [shiftedGammaHorizontalEnvelope, K]
        ring
      _ ≤ K * ((B + C) ^ 6 * Real.exp (-B)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hcombine hexp) hK
      _ = G B := by
        rw [← hrewrite]
        dsimp [G]
        ring
  · exact hG

/-- The upper horizontal edge in the finite residue rectangle tends to zero.
This supplies the missing limiting step between the finite contour identity
and the infinite vertical-line formula. -/
theorem tendsto_shiftedGamma_upperHorizontal_zero
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d)
    (hpsi : psi ≠ 1) (s : ℂ)
    {X a b : ℝ} (hX : 0 < X)
    (hab : a ≤ b) (haLo : -(3 / 2 : ℝ) ≤ a) (hbHi : b ≤ 2)
    (hLLo : -1 ≤ s.re + a) (hLHi : s.re + b ≤ 2) :
    Tendsto (fun B : ℝ =>
      ∫ x : ℝ in a..b,
        shiftedGammaRawIntegrand psi s X ((x : ℂ) + B * I))
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have henv :=
    (tendsto_shiftedGammaHorizontalEnvelope_zero d s hX a b).mul_const
      |b - a|
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun B => norm_nonneg _
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with B hB
    apply MAPAppendixA4Detector.horizontal_segment_norm_le
      (shiftedGammaRawIntegrand psi s X)
      (B := B) (M := shiftedGammaHorizontalEnvelope d s X a b B)
    intro x hx
    have hx' : x ∈ Set.Ioc a b := by
      simpa [Set.uIoc_of_le hab] using hx
    simpa [shiftedGammaHorizontalEnvelope, abs_of_nonneg (le_trans zero_le_one hB)] using
      (norm_shiftedGammaRawIntegrand_horizontal_le psi hpsi s hX
        haLo hbHi hx'.1.le hx'.2 hLLo hLHi (t := B)
          (by simpa [abs_of_nonneg (le_trans zero_le_one hB)] using hB))
  · simpa using henv

/-- The lower horizontal edge tends to zero with the same envelope. -/
theorem tendsto_shiftedGamma_lowerHorizontal_zero
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d)
    (hpsi : psi ≠ 1) (s : ℂ)
    {X a b : ℝ} (hX : 0 < X)
    (hab : a ≤ b) (haLo : -(3 / 2 : ℝ) ≤ a) (hbHi : b ≤ 2)
    (hLLo : -1 ≤ s.re + a) (hLHi : s.re + b ≤ 2) :
    Tendsto (fun B : ℝ =>
      ∫ x : ℝ in a..b,
        shiftedGammaRawIntegrand psi s X ((x : ℂ) - B * I))
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have henv :=
    (tendsto_shiftedGammaHorizontalEnvelope_zero d s hX a b).mul_const
      |b - a|
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun B => norm_nonneg _
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with B hB
    simpa [sub_eq_add_neg, shiftedGammaHorizontalEnvelope,
      abs_of_nonneg (le_trans zero_le_one hB)] using
      (MAPAppendixA4Detector.horizontal_segment_norm_le
        (shiftedGammaRawIntegrand psi s X)
        (B := -B) (M := shiftedGammaHorizontalEnvelope d s X a b B)
        (fun x hx => by
          have hx' : x ∈ Set.Ioc a b := by
            simpa [Set.uIoc_of_le hab] using hx
          have hbound := norm_shiftedGammaRawIntegrand_horizontal_le
            psi hpsi s hX haLo hbHi hx'.1.le hx'.2 hLLo hLHi
              (t := -B) (by
                rw [abs_neg, abs_of_nonneg (le_trans zero_le_one hB)]
                exact hB)
          simpa [abs_neg, abs_of_nonneg (le_trans zero_le_one hB)] using hbound))
  · simpa using henv

/-- Multiplying the raw integrand by `w` and applying the Gamma recurrence
produces this analytic numerator. -/
def shiftedGammaNumerator {d : ℕ} [NeZero d]
    (psi : DirichletCharacter ℂ d) (s : ℂ) (X : ℝ) (w : ℂ) : ℂ :=
  DirichletCharacter.LFunction psi (s + w) ^ 2 *
    Complex.Gamma (w + 1) * (X : ℂ) ^ w

/-- Holomorphic remainder after subtracting the Gamma principal part. -/
def shiftedGammaRemainder {d : ℕ} [NeZero d]
    (psi : DirichletCharacter ℂ d) (s : ℂ) (X : ℝ) : ℂ → ℂ :=
  dslope (shiftedGammaNumerator psi s X) 0

theorem analyticAt_shiftedGammaNumerator
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d)
    (hpsi : psi ≠ 1) (s : ℂ) {X : ℝ} (hX : 0 < X)
    {w : ℂ} (hw : -1 < w.re) :
    AnalyticAt ℂ (shiftedGammaNumerator psi s X) w := by
  unfold shiftedGammaNumerator
  have hL : AnalyticAt ℂ
      (fun z : ℂ => DirichletCharacter.LFunction psi (s + z)) w :=
    ((DirichletCharacter.differentiable_LFunction hpsi).analyticAt _).comp
      (by fun_prop)
  have hGamma : AnalyticAt ℂ (fun z : ℂ => Complex.Gamma (z + 1)) w := by
    apply MAPAppendixA4Detector.analyticAt_Gamma_add_one_of_mem_contourStrip
    exact hw
  have hpow : AnalyticAt ℂ (fun z : ℂ => (X : ℂ) ^ z) w :=
    (differentiable_id.const_cpow
      (.inl (Complex.ofReal_ne_zero.mpr hX.ne'))).analyticAt w
  exact ((hL.pow 2).mul hGamma).mul hpow

theorem analyticAt_shiftedGammaRemainder
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d)
    (hpsi : psi ≠ 1) (s : ℂ) {X : ℝ} (hX : 0 < X)
    {w : ℂ} (hw : -1 < w.re) :
    AnalyticAt ℂ (shiftedGammaRemainder psi s X) w := by
  unfold shiftedGammaRemainder
  apply analyticAt_dslope_of_analyticAt
  · exact analyticAt_shiftedGammaNumerator psi hpsi s hX (by simp)
  · exact analyticAt_shiftedGammaNumerator psi hpsi s hX hw

@[simp] theorem shiftedGammaNumerator_zero
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d)
    (s : ℂ) (X : ℝ) :
    shiftedGammaNumerator psi s X 0 =
      DirichletCharacter.LFunction psi s ^ 2 := by
  simp [shiftedGammaNumerator]

/-- Away from zero, the literal integrand is the analytic remainder plus the
principal part with residue `L(s,psi)^2`. -/
theorem shiftedGammaRawIntegrand_eq_remainder_add_principal
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d)
    (s : ℂ) (X : ℝ) {w : ℂ} (hw : w ≠ 0) :
    shiftedGammaRawIntegrand psi s X w =
      shiftedGammaRemainder psi s X w +
        DirichletCharacter.LFunction psi s ^ 2 * w⁻¹ := by
  have hrec : Complex.Gamma (w + 1) = w * Complex.Gamma w :=
    Complex.Gamma_add_one w hw
  have hnum : shiftedGammaNumerator psi s X w =
      w * shiftedGammaRawIntegrand psi s X w := by
    unfold shiftedGammaNumerator shiftedGammaRawIntegrand
    rw [hrec]
    ring
  have hds : shiftedGammaRemainder psi s X w =
      (shiftedGammaNumerator psi s X w -
        shiftedGammaNumerator psi s X 0) / w := by
    rw [shiftedGammaRemainder, dslope_of_ne]
    · simp only [slope, vsub_eq_sub, sub_zero, div_eq_inv_mul]
      ring
    · exact hw
  rw [hds, shiftedGammaNumerator_zero, hnum]
  field_simp [hw]
  ring

/-- Exact finite rectangle shift across the Gamma pole.  This is the residue
step in the shifted analogue of Lemma 3 before any horizontal-edge or
vertical-tail estimate is taken. -/
theorem rectangleBoundaryIntegral_shiftedGammaRaw_eq_L_sq
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d)
    (hpsi : psi ≠ 1) (s : ℂ) {X a b u v r : ℝ}
    (hX : 0 < X) (hr : 0 < r)
    (haStrip : -1 < a) (ha : a < -r) (hb : r < b)
    (hu : u < -r) (hv : r < v) :
    rectangleBoundaryIntegral (shiftedGammaRawIntegrand psi s X)
        a b u v =
      (2 * Real.pi * I) * DirichletCharacter.LFunction psi s ^ 2 := by
  let p : Unit → ℂ := fun _ => 0
  let R : Unit → ℂ := fun _ => DirichletCharacter.LFunction psi s ^ 2
  let rad : Unit → ℝ := fun _ => r
  let g : ℂ → ℂ := shiftedGammaRemainder psi s X
  have hab : a ≤ b := by linarith
  have huv : u ≤ v := by linarith
  have hgdiff : DifferentiableOn ℂ g
      (Set.uIcc a b ×ℂ Set.uIcc u v) := by
    intro z hz
    have hzre : a ≤ z.re := by
      have h := hz.1.1
      rw [min_eq_left hab] at h
      exact h
    exact (analyticAt_shiftedGammaRemainder psi hpsi s hX
      (haStrip.trans_le hzre)).differentiableAt.differentiableWithinAt
  have hedge (z : ℂ) (hz : z ≠ 0) :
      shiftedGammaRawIntegrand psi s X z =
        g z + DirichletCharacter.LFunction psi s ^ 2 * (z - 0)⁻¹ := by
    simpa [g] using
      shiftedGammaRawIntegrand_eq_remainder_add_principal psi s X hz
  have hsum : (∑ i ∈ ({()} : Finset Unit), R i) =
      DirichletCharacter.LFunction psi s ^ 2 := by simp [R]
  rw [← hsum]
  apply rectangleBoundaryIntegral_eq_two_pi_I_mul_sum_residue
    ({()} : Finset Unit) p R rad
      (shiftedGammaRawIntegrand psi s X) g a b u v
  · intro i hi; simpa [rad] using hr
  · intro i hi; simpa [p, rad] using ha
  · intro i hi; simpa [p, rad] using hb
  · intro i hi; simpa [p, rad] using hu
  · intro i hi; simpa [p, rad] using hv
  · exact boundaryIntervalIntegrable_of_differentiableOn hgdiff
  · exact hgdiff
  · intro x
    have hz : (x : ℂ) + (u : ℂ) * I ≠ 0 := by
      intro h
      have him := congrArg Complex.im h
      simp at him
      linarith
    simpa [p, R, g] using hedge ((x : ℂ) + (u : ℂ) * I) hz
  · intro x
    have hz : (x : ℂ) + (v : ℂ) * I ≠ 0 := by
      intro h
      have him := congrArg Complex.im h
      simp at him
      linarith
    simpa [p, R, g] using hedge ((x : ℂ) + (v : ℂ) * I) hz
  · intro y
    have hz : (b : ℂ) + (y : ℂ) * I ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      simp at hre
      linarith
    simpa [p, R, g] using hedge ((b : ℂ) + (y : ℂ) * I) hz
  · intro y
    have hz : (a : ℂ) + (y : ℂ) * I ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      simp at hre
      linarith
    simpa [p, R, g] using hedge ((a : ℂ) + (y : ℂ) * I) hz

/-! ## Normalized finite vertical-line identity -/

/-- The standard `1/(2*pi)` normalization after `dw = i dv`. -/
def shiftedGammaVerticalLine {d : ℕ} [NeZero d]
    (psi : DirichletCharacter ℂ d) (s : ℂ) (X c u v : ℝ) : ℂ :=
  (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
    ∫ y in u..v, shiftedGammaRawIntegrand psi s X ((c : ℂ) + y * I)

/-- The two horizontal edges with their `1/(2*pi*i)` normalization. -/
def shiftedGammaHorizontalEdges {d : ℕ} [NeZero d]
    (psi : DirichletCharacter ℂ d) (s : ℂ)
    (X a b u v : ℝ) : ℂ :=
  ((((2 * Real.pi : ℝ) : ℂ) * I)⁻¹) *
    ((∫ x in a..b,
        shiftedGammaRawIntegrand psi s X ((x : ℂ) + (u : ℂ) * I)) -
      ∫ x in a..b,
        shiftedGammaRawIntegrand psi s X ((x : ℂ) + (v : ℂ) * I))

/-- Finite source-faithful contour displacement.  The starting line equals
the residue, the shifted line, and the two horizontal edges exactly. -/
theorem shiftedGammaVerticalLine_eq_residue_add_left_sub_horizontal
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d)
    (hpsi : psi ≠ 1) (s : ℂ) {X a b u v r : ℝ}
    (hX : 0 < X) (hr : 0 < r)
    (haStrip : -1 < a) (ha : a < -r) (hb : r < b)
    (hu : u < -r) (hv : r < v) :
    shiftedGammaVerticalLine psi s X b u v =
      DirichletCharacter.LFunction psi s ^ 2 +
        shiftedGammaVerticalLine psi s X a u v -
          shiftedGammaHorizontalEdges psi s X a b u v := by
  have hrect := rectangleBoundaryIntegral_shiftedGammaRaw_eq_L_sq
    psi hpsi s hX hr haStrip ha hb hu hv
  unfold rectangleBoundaryIntegral at hrect
  unfold shiftedGammaVerticalLine shiftedGammaHorizontalEdges
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hpiC : (((2 * Real.pi : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast hpi
  apply mul_left_cancel₀ (mul_ne_zero hpiC I_ne_zero)
  field_simp [hpiC, I_ne_zero] at hrect ⊢
  push_cast at hrect ⊢
  linear_combination hrect

/-- Infinite nonprincipal contour displacement with the horizontal limits
now discharged internally.  The only remaining inputs are integrability of
the two literal vertical slices. -/
theorem full_shiftedGamma_vertical_integral_eq_residue_add_left
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d)
    (hpsi : psi ≠ 1) (s : ℂ)
    {X a b r : ℝ} (hX : 0 < X) (hr : 0 < r)
    (haStrip : -1 < a) (ha : a < -r) (hb : r < b)
    (haLo : -(3 / 2 : ℝ) ≤ a) (hbHi : b ≤ 2)
    (hLLo : -1 ≤ s.re + a) (hLHi : s.re + b ≤ 2)
    (hleft : Integrable (fun t : ℝ =>
      shiftedGammaRawIntegrand psi s X ((a : ℂ) + t * I)))
    (hright : Integrable (fun t : ℝ =>
      shiftedGammaRawIntegrand psi s X ((b : ℂ) + t * I))) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ t : ℝ, shiftedGammaRawIntegrand psi s X ((b : ℂ) + t * I)) =
      DirichletCharacter.LFunction psi s ^ 2 +
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ t : ℝ,
            shiftedGammaRawIntegrand psi s X ((a : ℂ) + t * I)) := by
  let R : ℝ → ℂ := fun B => ∫ t : ℝ in -B..B,
    shiftedGammaRawIntegrand psi s X ((b : ℂ) + t * I)
  let L : ℝ → ℂ := fun B => ∫ t : ℝ in -B..B,
    shiftedGammaRawIntegrand psi s X ((a : ℂ) + t * I)
  let Hminus : ℝ → ℂ := fun B => ∫ x : ℝ in a..b,
    shiftedGammaRawIntegrand psi s X ((x : ℂ) - B * I)
  let Hplus : ℝ → ℂ := fun B => ∫ x : ℝ in a..b,
    shiftedGammaRawIntegrand psi s X ((x : ℂ) + B * I)
  have hab : a ≤ b := by linarith
  have hR : Tendsto R atTop
      (𝓝 (∫ t : ℝ,
        shiftedGammaRawIntegrand psi s X ((b : ℂ) + t * I))) := by
    exact MeasureTheory.intervalIntegral_tendsto_integral hright
      Filter.tendsto_neg_atTop_atBot tendsto_id
  have hL : Tendsto L atTop
      (𝓝 (∫ t : ℝ,
        shiftedGammaRawIntegrand psi s X ((a : ℂ) + t * I))) := by
    exact MeasureTheory.intervalIntegral_tendsto_integral hleft
      Filter.tendsto_neg_atTop_atBot tendsto_id
  have hminus : Tendsto Hminus atTop (𝓝 0) := by
    simpa [Hminus] using tendsto_shiftedGamma_lowerHorizontal_zero
      psi hpsi s hX hab haLo hbHi hLLo hLHi
  have hplus : Tendsto Hplus atTop (𝓝 0) := by
    simpa [Hplus] using tendsto_shiftedGamma_upperHorizontal_zero
      psi hpsi s hX hab haLo hbHi hLLo hLHi
  have hbalance : ∀ᶠ B : ℝ in atTop,
      I * (R B - L B) =
        (2 * Real.pi * I) * DirichletCharacter.LFunction psi s ^ 2 +
          (Hplus B - Hminus B) := by
    filter_upwards [eventually_gt_atTop r] with B hBr
    have hrect := rectangleBoundaryIntegral_shiftedGammaRaw_eq_L_sq
      psi hpsi s (u := -B) (v := B) hX hr haStrip ha hb (by linarith) hBr
    unfold rectangleBoundaryIntegral at hrect
    have hminusInt :
        (∫ x : ℝ in a..b,
          shiftedGammaRawIntegrand psi s X
            ((x : ℂ) + ((-B : ℝ) : ℂ) * I)) =
        ∫ x : ℝ in a..b,
          shiftedGammaRawIntegrand psi s X ((x : ℂ) - (B : ℂ) * I) := by
      apply intervalIntegral.integral_congr
      intro x hx
      apply congrArg (shiftedGammaRawIntegrand psi s X)
      push_cast
      ring
    rw [hminusInt] at hrect
    change Hminus B - Hplus B + I * R B - I * L B =
      (2 * Real.pi * I) * DirichletCharacter.LFunction psi s ^ 2 at hrect
    linear_combination hrect
  have hlhs : Tendsto (fun B => I * (R B - L B)) atTop
      (𝓝 (I * ((∫ t : ℝ,
          shiftedGammaRawIntegrand psi s X ((b : ℂ) + t * I)) -
        ∫ t : ℝ,
          shiftedGammaRawIntegrand psi s X ((a : ℂ) + t * I)))) :=
    tendsto_const_nhds.mul (hR.sub hL)
  have hrhs : Tendsto (fun B =>
      (2 * Real.pi * I) * DirichletCharacter.LFunction psi s ^ 2 +
        (Hplus B - Hminus B)) atTop
      (𝓝 ((2 * Real.pi * I) *
        DirichletCharacter.LFunction psi s ^ 2)) := by
    simpa using tendsto_const_nhds.add (hplus.sub hminus)
  have hlhs' : Tendsto (fun B => I * (R B - L B)) atTop
      (𝓝 ((2 * Real.pi * I) *
        DirichletCharacter.LFunction psi s ^ 2)) :=
    hrhs.congr' (hbalance.mono fun B hB => hB.symm)
  have heq := tendsto_nhds_unique hlhs hlhs'
  have hshift :
      (∫ t : ℝ,
          shiftedGammaRawIntegrand psi s X ((b : ℂ) + t * I)) -
        ∫ t : ℝ,
          shiftedGammaRawIntegrand psi s X ((a : ℂ) + t * I) =
        (2 : ℂ) * (Real.pi : ℂ) *
          DirichletCharacter.LFunction psi s ^ 2 := by
    apply mul_left_cancel₀ I_ne_zero
    linear_combination heq
  rw [show (∫ t : ℝ,
      shiftedGammaRawIntegrand psi s X ((b : ℂ) + t * I)) =
      (2 : ℂ) * (Real.pi : ℂ) *
          DirichletCharacter.LFunction psi s ^ 2 +
        ∫ t : ℝ,
          shiftedGammaRawIntegrand psi s X ((a : ℂ) + t * I) by
        linear_combination hshift]
  have hnorm : (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ((2 : ℂ) * (Real.pi : ℂ))) = 1 := by
    norm_cast
    field_simp [Real.pi_ne_zero]
  calc
    _ = ((((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ((2 : ℂ) * (Real.pi : ℂ))) *
            DirichletCharacter.LFunction psi s ^ 2) +
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ t : ℝ,
            shiftedGammaRawIntegrand psi s X ((a : ℂ) + t * I)) := by ring
    _ = _ := by rw [hnorm, one_mul]

/-- Premise-free nonprincipal infinite contour shift.  Vertical integrability,
the Gamma residue, and both horizontal limits are all discharged inside this
module. -/
theorem full_shiftedGamma_vertical_integral_eq_residue_add_left_unconditional
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d)
    (hpsi : psi ≠ 1) (s : ℂ)
    {X a b r : ℝ} (hX : 0 < X) (hr : 0 < r)
    (haStrip : -1 < a) (ha : a < -r) (hb : r < b)
    (haLo : -(3 / 2 : ℝ) ≤ a) (hbHi : b ≤ 2)
    (hLLo : -1 ≤ s.re + a) (hLHi : s.re + b ≤ 2) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ t : ℝ, shiftedGammaRawIntegrand psi s X ((b : ℂ) + t * I)) =
      DirichletCharacter.LFunction psi s ^ 2 +
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ t : ℝ,
            shiftedGammaRawIntegrand psi s X ((a : ℂ) + t * I)) := by
  have hab : a ≤ b := by linarith
  have ha0 : a ≠ 0 := by linarith
  have hb0 : b ≠ 0 := by linarith
  have haLHi : s.re + a ≤ 2 := by linarith
  have hbLLo : -1 ≤ s.re + b := by linarith
  have hbLo : -1 < b := by linarith
  have hleft := integrable_shiftedGammaRaw_vertical
    psi hpsi s hX haStrip (le_trans hab hbHi) ha0 hLLo haLHi
  have hright := integrable_shiftedGammaRaw_vertical
    psi hpsi s hX hbLo hbHi hb0 hbLLo hLHi
  exact full_shiftedGamma_vertical_integral_eq_residue_add_left
    psi hpsi s hX hr haStrip ha hb haLo hbHi hLLo hLHi hleft hright

end
end RamachandraShiftedGammaPoleContour

#print axioms RamachandraShiftedGammaPoleContour.shiftedGammaRawIntegrand_eq_remainder_add_principal
#print axioms RamachandraShiftedGammaPoleContour.norm_Gamma_ramachandraHorizontalStrip_le_exp
#print axioms RamachandraShiftedGammaPoleContour.norm_shiftedGammaRawIntegrand_horizontal_le
#print axioms RamachandraShiftedGammaPoleContour.tendsto_shiftedGamma_upperHorizontal_zero
#print axioms RamachandraShiftedGammaPoleContour.tendsto_shiftedGamma_lowerHorizontal_zero
#print axioms RamachandraShiftedGammaPoleContour.rectangleBoundaryIntegral_shiftedGammaRaw_eq_L_sq
#print axioms RamachandraShiftedGammaPoleContour.shiftedGammaVerticalLine_eq_residue_add_left_sub_horizontal
#print axioms RamachandraShiftedGammaPoleContour.full_shiftedGamma_vertical_integral_eq_residue_add_left
#print axioms RamachandraShiftedGammaPoleContour.integrable_shiftedGammaRaw_vertical
#print axioms RamachandraShiftedGammaPoleContour.full_shiftedGamma_vertical_integral_eq_residue_add_left_unconditional
