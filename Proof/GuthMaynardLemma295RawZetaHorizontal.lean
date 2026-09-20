import GuthMaynardLemma295HorizontalIntegral
import GoldfeldContourBounds
import GuthMaynardLemma295DeepLeftSplit

/-!
# Uniform raw-zeta bound on the first Lemma 29.5 rectangle
-/

namespace GuthMaynardLemma295RawZetaHorizontal

open Complex Real Set
open GuthMaynardLemma295CutoffAnalytic
open GuthMaynardLemma295DualTail
open GuthMaynardLemma295ThetaHorizontal
open MAPGoldfeldSiegel

noncomputable section

def rawZetaHorizontalRadius (n : ℕ) (u : ℝ) : ℝ :=
  6 + 4 * n + |u|

def rawZetaHorizontalDegree (n : ℕ) : ℕ := 2 * n + 6

private theorem rawRadius_one_le (n : ℕ) (u : ℝ) :
    1 ≤ rawZetaHorizontalRadius n u := by
  unfold rawZetaHorizontalRadius
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith [abs_nonneg u]

/-- On `-1 ≤ Re z ≤ 2`, remove the pole using the imaginary height and apply
the certified regularized principal-zeta strip bound. -/
theorem norm_riemannZeta_middleHorizontal_le
    {x u : ℝ} (hxlo : -1 ≤ x) (hxhi : x ≤ 2) (hu : 1 ≤ |u|) :
    ‖riemannZeta ((x : ℂ) + (u : ℂ) * I)‖ ≤
      (1600 * 5 ^ 6) * (1 + |u|) ^ 6 := by
  let z : ℂ := (x : ℂ) + (u : ℂ) * I
  have hune : u ≠ 0 := by
    intro h
    subst u
    norm_num at hu
  have hz1 : z ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    simp [z] at him
    exact hune him
  have hreg0 := MAPPrincipalZetaFixedStrip.norm_principalRegularized_fixedStrip_le
    (z := z) (by simpa [z] using hxlo) (by simpa [z] using hxhi)
  have hreg : ‖regularizedRiemannZeta z‖ ≤
      1600 * ‖z + 3‖ ^ 6 := by
    rw [regularizedRiemannZeta_eq_principalRegularized]
    exact hreg0
  have heq := regularizedRiemannZeta_eq_mul hz1
  have hden : 1 ≤ ‖z - 1‖ := by
    exact hu.trans (by simpa [z] using Complex.abs_im_le_norm (z - 1))
  have hzetaReg : ‖riemannZeta z‖ ≤ ‖regularizedRiemannZeta z‖ := by
    rw [heq, norm_mul]
    exact le_mul_of_one_le_left (norm_nonneg _) hden
  have hnorm : ‖z + 3‖ ≤ 5 * (1 + |u|) := by
    calc
      ‖z + 3‖ ≤ |(z + 3).re| + |(z + 3).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ = |x + 3| + |u| := by simp [z]
      _ ≤ 5 + |u| := by
        have : |x + 3| ≤ 5 := by rw [abs_le]; constructor <;> linarith
        linarith
      _ ≤ 5 * (1 + |u|) := by linarith [abs_nonneg u]
  calc
    ‖riemannZeta z‖ ≤ ‖regularizedRiemannZeta z‖ := hzetaReg
    _ ≤ 1600 * ‖z + 3‖ ^ 6 := hreg
    _ ≤ 1600 * (5 * (1 + |u|)) ^ 6 := by gcongr
    _ = (1600 * 5 ^ 6) * (1 + |u|) ^ 6 := by ring

/-- In the genuinely left half-plane, the exact functional equation and the
absolutely convergent dual zeta series give a uniform factor two. -/
theorem norm_riemannZeta_deepHorizontal_le
    (n : ℕ) {x u : ℝ}
    (hx : x ∈ Set.Icc (deepLeftSigma n) (1 / 2))
    (hxneg : x < -1) (hu : 2 ≤ |u|) :
    ‖riemannZeta ((x : ℂ) + (u : ℂ) * I)‖ ≤
      2304 * horizontalThetaRadius n u ^ (2 * n + 5) := by
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, abs_zero] at hu
    norm_num at hu
  let z : ℂ := (x : ℂ) + (u : ℂ) * I
  have hzre : z.re = x := by simp [z]
  have hzim : z.im = u := by simp [z]
  have hzneg : z.re < 0 := by linarith
  have hz0 : z ≠ 0 := ne_zero_of_re_ne_zero (ne_of_lt hzneg)
  have hdual0 : 1 - z ≠ 0 := by
    apply ne_zero_of_re_ne_zero
    simp
    linarith
  have hgamma : Complex.Gammaℝ z ≠ 0 := by
    intro hzero
    rw [Complex.Gammaℝ_eq_zero_iff] at hzero
    obtain ⟨m, hm⟩ := hzero
    have : z.im = 0 := by rw [hm]; simp
    rw [hzim] at this
    exact hu0 this
  have hgammaDual : Complex.Gammaℝ (1 - z) ≠ 0 := by
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    simp
    linarith
  have hFE := riemannZeta_eq_sourceZetaTheta_mul
    hz0 hdual0 hgamma hgammaDual
  have htheta := norm_sourceZetaTheta_horizontal_le
    n (B := u) (g := 0) hx (by simpa using hu)
  have htheta' : ‖sourceZetaTheta z‖ ≤
      1152 * horizontalThetaRadius n u ^ (2 * n + 5) := by
    simpa [z] using htheta
  have htail := norm_sourceDualTailNat_le hzneg 0
  have hdualEq : sourceDualTailNat 0 z = riemannZeta (1 - z) := by
    simp [sourceDualTailNat, sourceDualPartialNat]
  rw [hdualEq, hzre] at htail
  have hdual : ‖riemannZeta (1 - z)‖ ≤ 2 := by
    calc
      ‖riemannZeta (1 - z)‖ ≤
          (1 : ℝ) ^ (x - 1) + (1 : ℝ) ^ x / (-x) := by simpa using htail
      _ = 1 + 1 / (-x) := by simp
      _ ≤ 2 := by
        have hxpos : 1 < -x := by linarith
        have hx0 : 0 < -x := zero_lt_one.trans hxpos
        have : 1 / (-x) ≤ 1 := (div_le_one hx0).2 hxpos.le
        linarith
  change ‖riemannZeta z‖ ≤ _
  rw [hFE, norm_mul]
  calc
    ‖sourceZetaTheta z‖ * ‖riemannZeta (1 - z)‖ ≤
        (1152 * horizontalThetaRadius n u ^ (2 * n + 5)) * 2 := by
      exact mul_le_mul htheta' hdual (norm_nonneg _)
        ((norm_nonneg _).trans htheta')
    _ = 2304 * horizontalThetaRadius n u ^ (2 * n + 5) := by ring

/-- One polynomial envelope valid across the entire raw first rectangle. -/
theorem norm_riemannZeta_rawHorizontal_le
    (n : ℕ) {x u : ℝ}
    (hx : x ∈ Set.Icc (deepLeftSigma n) 2) (hu : 2 ≤ |u|) :
    ‖riemannZeta ((x : ℂ) + (u : ℂ) * I)‖ ≤
      (1600 * 5 ^ 6) * rawZetaHorizontalRadius n u ^
        rawZetaHorizontalDegree n := by
  by_cases hxmid : -1 ≤ x
  · have hmid := norm_riemannZeta_middleHorizontal_le hxmid hx.2
      (le_trans (by norm_num) hu)
    have hlow : 1 + |u| ≤ rawZetaHorizontalRadius n u := by
      unfold rawZetaHorizontalRadius
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hdegree : 6 ≤ rawZetaHorizontalDegree n := by
      unfold rawZetaHorizontalDegree
      omega
    have hr := rawRadius_one_le n u
    exact hmid.trans (mul_le_mul_of_nonneg_left
      ((pow_le_pow_left₀ (by positivity) hlow 6).trans
        (pow_le_pow_right₀ hr hdegree)) (by positivity))
  · have hxneg : x < -1 := lt_of_not_ge hxmid
    have hxhalf : x ∈ Set.Icc (deepLeftSigma n) (1 / 2) :=
      ⟨hx.1, by linarith⟩
    have hdeep := norm_riemannZeta_deepHorizontal_le n hxhalf hxneg hu
    have hrad : horizontalThetaRadius n u ≤ rawZetaHorizontalRadius n u := by
      unfold horizontalThetaRadius rawZetaHorizontalRadius
      linarith
    have hdeg : 2 * n + 5 ≤ rawZetaHorizontalDegree n := by
      unfold rawZetaHorizontalDegree
      omega
    have hr := rawRadius_one_le n u
    have hp : horizontalThetaRadius n u ^ (2 * n + 5) ≤
        rawZetaHorizontalRadius n u ^ rawZetaHorizontalDegree n :=
      (pow_le_pow_left₀ (by
          unfold horizontalThetaRadius
          positivity) hrad _).trans (pow_le_pow_right₀ hr hdeg)
    calc
      ‖riemannZeta ((x : ℂ) + (u : ℂ) * I)‖ ≤
          2304 * horizontalThetaRadius n u ^ (2 * n + 5) := hdeep
      _ ≤ 2304 * rawZetaHorizontalRadius n u ^ rawZetaHorizontalDegree n := by
        gcongr
      _ ≤ (1600 * 5 ^ 6) *
          rawZetaHorizontalRadius n u ^ rawZetaHorizontalDegree n := by
        gcongr
        norm_num

end
end GuthMaynardLemma295RawZetaHorizontal

#print axioms GuthMaynardLemma295RawZetaHorizontal.norm_riemannZeta_rawHorizontal_le
