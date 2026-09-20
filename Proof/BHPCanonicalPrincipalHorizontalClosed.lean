import BHPPrincipalNormalizedGaussian
import BHPCanonicalHorizontalScalar
import BHPCanonicalPrincipalPointwise

/-!
# Closing the principal BHP horizontal source

This file turns the pole-safe Gaussian interpolation into the exact horizontal
integral used by the principal Perron rectangle.  The comparison with the
already certified ambient endpoint numerator is deterministic: the new left
and right boundary bases are each bounded by one fixed scalar multiple of the
ambient bases, and their interpolation exponents add to one.
-/

namespace MAPBHPCanonicalPrincipalHorizontalClosed

open Complex MeasureTheory Set
open MAPBHPPrincipalNormalizedGaussian
open MAPBHPHorizontalEndpointInterpolation
open MAPBHPCanonicalHorizontalScalar
open MAPBHPCorrectedContourShift
open MAPBHPCanonicalPrincipalPointwise
open MAPBHPRademacherTitchmarshSources
open MAPZeroFreeSiegelSpine
open RamachandraTheorem6ShiftedStripSource

noncomputable section

def principalHorizontalScale : ℝ := 1024000000 * Real.exp 4

def principalHorizontalEndpointNumerator
    (q : ℕ) (x0 X u : ℝ) : ℝ :=
  let d := canonicalRamachandraOffset x0
  let r := (Real.log x0)⁻¹
  let W := 1 + r + d
  let c := 1 / 2 + r
  let A := principalLeftGaussianBound q x0 u
  let B := principalRightGaussianBound x0
  Real.rpow A ((c - d) / W) *
      Real.rpow B ((d + (W - c)) / W) * Real.rpow X d +
    Real.rpow B 1 * Real.rpow X c

private theorem principal_left_base_le_scaled_ambient
    {q : ℕ} (hq : 1 ≤ q) {x0 u : ℝ}
    (hx0 : 8 ≤ x0) :
    principalLeftGaussianBound q x0 u ≤
      principalHorizontalScale *
        (48 * (1 + (canonicalRamachandraOffset x0)⁻¹) *
          Real.rpow (2 * (q : ℝ) * (3 + |u|))
            (canonicalRamachandraOffset x0 + 1)) := by
  let d := canonicalRamachandraOffset x0
  let Q := 2 * (q : ℝ) * (3 + |u|)
  have hxOne : 1 < x0 := by linarith
  have hlog : 0 < Real.log x0 := Real.log_pos hxOne
  have hd0 : 0 < d := by dsimp [d, canonicalRamachandraOffset]; positivity
  have hdInv : d⁻¹ = 400 * Real.log x0 := by
    dsimp [d, canonicalRamachandraOffset]
    field_simp
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hsqrtq : Real.sqrt (q : ℝ) ≤ (q : ℝ) := by
    rw [Real.sqrt_le_iff]
    exact ⟨by positivity, by nlinarith [hqR]⟩
  have hlinear : 1 + |u| ≤ 3 + |u| := by linarith
  have hscale : Real.sqrt (q : ℝ) * (1 + |u|) ≤ Q := by
    dsimp [Q]
    calc
      Real.sqrt (q : ℝ) * (1 + |u|) ≤ (q : ℝ) * (3 + |u|) :=
        mul_le_mul hsqrtq hlinear (by positivity) (by positivity)
      _ ≤ 2 * (q : ℝ) * (3 + |u|) := by
        have hnonneg : 0 ≤ (q : ℝ) * (3 + |u|) := by positivity
        nlinarith
  have hQone : 1 ≤ Q := by dsimp [Q]; nlinarith [abs_nonneg u]
  have hQrpow : Q ≤ Real.rpow Q (d + 1) := by
    calc
      Q = Real.rpow Q 1 := by norm_num
      _ ≤ Real.rpow Q (d + 1) :=
        Real.rpow_le_rpow_of_exponent_le hQone (by linarith)
  unfold principalLeftGaussianBound principalHorizontalScale
  rw [← hdInv]
  dsimp [Q] at hscale hQrpow ⊢
  have hP0 : 0 ≤ 1 + d⁻¹ := by positivity
  have hmain := hscale.trans hQrpow
  calc
    1024000000 * (1 + d⁻¹) * Real.exp 4 *
        Real.sqrt (q : ℝ) * (1 + |u|) =
      (1024000000 * Real.exp 4) * (1 + d⁻¹) *
        (Real.sqrt (q : ℝ) * (1 + |u|)) := by ring
    _ ≤ (1024000000 * Real.exp 4) * (1 + d⁻¹) *
        Real.rpow (2 * (q : ℝ) * (3 + |u|)) (d + 1) :=
      mul_le_mul_of_nonneg_left hmain (by positivity)
    _ ≤ (1024000000 * Real.exp 4) *
        (48 * (1 + d⁻¹) *
          Real.rpow (2 * (q : ℝ) * (3 + |u|)) (d + 1)) := by
      have hrest : 0 ≤ (1 + d⁻¹) *
          Real.rpow (2 * (q : ℝ) * (3 + |u|)) (d + 1) := by
        exact mul_nonneg (by positivity)
          (Real.rpow_nonneg (by positivity) _)
      nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 1024000000 * Real.exp 4) hrest]

private theorem principal_right_base_le_scaled_ambient
    {x0 : ℝ} (hx0 : 8 ≤ x0) :
    principalRightGaussianBound x0 ≤
      principalHorizontalScale *
        (rightEdgePSeries (Real.log x0)⁻¹ *
          Real.exp ((1 + (Real.log x0)⁻¹) ^ 2)) := by
  let r := (Real.log x0)⁻¹
  have hxOne : 1 < x0 := by linarith
  have hlog : 0 < Real.log x0 := Real.log_pos hxOne
  have hr0 : 0 < r := by dsimp [r]; positivity
  have hlog8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  have hlog8le : Real.log 8 ≤ Real.log x0 := Real.log_le_log (by norm_num) hx0
  rw [hlog8] at hlog8le
  have hlogTwo : 2 ≤ Real.log x0 := by nlinarith [Real.log_two_gt_d9]
  have hrHalf : r ≤ (1 / 2 : ℝ) := by
    dsimp [r]
    have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hlogTwo
    simpa [one_div] using hi
  have hextra : Real.exp (2 * (1 + r) ^ 2) ≤ principalHorizontalScale := by
    unfold principalHorizontalScale
    have hpow : 2 * (1 + r) ^ 2 ≤ 5 := by nlinarith [sq_nonneg r]
    have he : Real.exp (2 * (1 + r) ^ 2) ≤ Real.exp 5 :=
      Real.exp_le_exp.mpr hpow
    have he5 : Real.exp 5 ≤ 1024000000 * Real.exp 4 := by
      rw [show (5 : ℝ) = 4 + 1 by norm_num, Real.exp_add]
      have := Real.exp_one_lt_three
      nlinarith [Real.exp_pos 4]
    exact he.trans he5
  unfold principalRightGaussianBound
  change rightEdgePSeries r * Real.exp (3 * (1 + r) ^ 2) ≤
    principalHorizontalScale *
      (rightEdgePSeries r * Real.exp ((1 + r) ^ 2))
  have hP0 : 0 ≤ rightEdgePSeries r :=
    zero_le_one.trans (one_le_rightEdgePSeries hr0)
  have hsplit : Real.exp (3 * (1 + r) ^ 2) =
      Real.exp ((1 + r) ^ 2) * Real.exp (2 * (1 + r) ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hsplit]
  nlinarith [mul_nonneg hP0 (Real.exp_pos ((1 + r) ^ 2)).le]

private theorem scaled_interp_product_le
    {K A B A₀ B₀ alpha beta : ℝ}
    (hK : 0 < K) (hA₀ : 0 < A₀) (hB₀ : 0 < B₀)
    (hA : A ≤ K * A₀) (hB : B ≤ K * B₀)
    (hApos : 0 ≤ A) (hBpos : 0 ≤ B)
    (ha : 0 ≤ alpha) (hb : 0 ≤ beta) (hsum : alpha + beta = 1) :
    Real.rpow A alpha * Real.rpow B beta ≤
      K * (Real.rpow A₀ alpha * Real.rpow B₀ beta) := by
  have hKA : 0 < K * A₀ := mul_pos hK hA₀
  have hKB : 0 < K * B₀ := mul_pos hK hB₀
  have hAr := Real.rpow_le_rpow hApos hA ha
  have hBr := Real.rpow_le_rpow hBpos hB hb
  calc
    Real.rpow A alpha * Real.rpow B beta ≤
      Real.rpow (K * A₀) alpha * Real.rpow (K * B₀) beta :=
        mul_le_mul hAr hBr (Real.rpow_nonneg hBpos _) (Real.rpow_nonneg hKA.le _)
    _ = (Real.rpow K alpha * Real.rpow A₀ alpha) *
        (Real.rpow K beta * Real.rpow B₀ beta) := by
      have hmulA : Real.rpow (K * A₀) alpha =
          Real.rpow K alpha * Real.rpow A₀ alpha :=
        Real.mul_rpow hK.le hA₀.le
      have hmulB : Real.rpow (K * B₀) beta =
          Real.rpow K beta * Real.rpow B₀ beta :=
        Real.mul_rpow hK.le hB₀.le
      rw [hmulA, hmulB]
    _ = (Real.rpow K alpha * Real.rpow K beta) *
        (Real.rpow A₀ alpha * Real.rpow B₀ beta) := by ring
    _ = K * (Real.rpow A₀ alpha * Real.rpow B₀ beta) := by
      have hcombine : Real.rpow K alpha * Real.rpow K beta = K := by
        calc
          Real.rpow K alpha * Real.rpow K beta =
              Real.rpow K (alpha + beta) := (Real.rpow_add hK alpha beta).symm
          _ = K := by rw [hsum]; norm_num
      rw [hcombine]

/-- If interpolation weight is transferred from the larger endpoint to the
smaller endpoint, the geometric interpolation product can only decrease. -/
private theorem rpow_product_le_of_weight_shift
    {A B alpha beta alpha₀ beta₀ : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hBA : B ≤ A)
    (hsum : alpha + beta = 1) (hsum₀ : alpha₀ + beta₀ = 1)
    (halpha : alpha ≤ alpha₀) :
    Real.rpow A alpha * Real.rpow B beta ≤
      Real.rpow A alpha₀ * Real.rpow B beta₀ := by
  let e := alpha₀ - alpha
  have he : 0 ≤ e := by dsimp [e]; linarith
  have hbeta : beta = beta₀ + e := by dsimp [e]; linarith
  have halpha₀ : alpha₀ = alpha + e := by dsimp [e]; ring
  have hpow : Real.rpow B e ≤ Real.rpow A e :=
    Real.rpow_le_rpow hB.le hBA he
  have hBsplit : Real.rpow B beta =
      Real.rpow B beta₀ * Real.rpow B e := by
    rw [hbeta]
    exact Real.rpow_add hB beta₀ e
  have hAsplit : Real.rpow A alpha₀ =
      Real.rpow A alpha * Real.rpow A e := by
    rw [halpha₀]
    exact Real.rpow_add hA alpha e
  rw [hBsplit, hAsplit]
  have hnonneg : 0 ≤ Real.rpow A alpha * Real.rpow B beta₀ :=
    mul_nonneg (Real.rpow_nonneg hA.le _) (Real.rpow_nonneg hB.le _)
  calc
    Real.rpow A alpha * (Real.rpow B beta₀ * Real.rpow B e) =
        (Real.rpow A alpha * Real.rpow B beta₀) * Real.rpow B e := by ring
    _ ≤ (Real.rpow A alpha * Real.rpow B beta₀) * Real.rpow A e :=
      mul_le_mul_of_nonneg_left hpow hnonneg
    _ = (Real.rpow A alpha * Real.rpow A e) * Real.rpow B beta₀ := by ring

theorem principalHorizontalEndpointNumerator_le_scaled_ambient
    {q : ℕ} (hq : 1 ≤ q) {x0 X u : ℝ}
    (hx0 : 8 ≤ x0) (hX : 0 < X) :
    principalHorizontalEndpointNumerator q x0 X u ≤
      principalHorizontalScale *
        ambientHorizontalGeneralEndpointNumerator q
          (canonicalRamachandraOffset x0) (Real.log x0)⁻¹
          (canonicalRamachandraOffset x0) X u := by
  let d := canonicalRamachandraOffset x0
  let r := (Real.log x0)⁻¹
  let W := 1 + r + d
  let c := 1 / 2 + r
  let A := principalLeftGaussianBound q x0 u
  let B := principalRightGaussianBound x0
  let A₀ := 48 * (1 + d⁻¹) *
    Real.rpow (2 * (q : ℝ) * (3 + |u|)) (d + 1)
  let B₀ := rightEdgePSeries r * Real.exp ((1 + r) ^ 2)
  let alpha := (c - d) / W
  let beta := (d + (W - c)) / W
  let alpha₀ := (c - d) / (1 + r)
  let beta₀ := (d + 1 / 2) / (1 + r)
  have hxOne : 1 < x0 := by linarith
  have hlog : 0 < Real.log x0 := Real.log_pos hxOne
  have hd0 : 0 < d := by dsimp [d, canonicalRamachandraOffset]; positivity
  have hr0 : 0 < r := by dsimp [r]; positivity
  have hW : 0 < W := by dsimp [W]; linarith
  have hdr : d ≤ r := by
    dsimp [d, r, canonicalRamachandraOffset]
    have hden : Real.log x0 ≤ 400 * Real.log x0 := by nlinarith
    have hi := one_div_le_one_div_of_le hlog hden
    simpa [one_div] using hi
  have hcgd : d ≤ c := by dsimp [c]; linarith
  have ha : 0 ≤ alpha := by
    dsimp [alpha]
    exact div_nonneg (sub_nonneg.mpr hcgd) hW.le
  have hb : 0 ≤ beta := by
    dsimp [beta]
    exact div_nonneg (by dsimp [W, c]; linarith) hW.le
  have hsum : alpha + beta = 1 := by
    dsimp [alpha, beta, W, c]
    field_simp [ne_of_gt hW]
    ring
  have hsum₀ : alpha₀ + beta₀ = 1 := by
    dsimp [alpha₀, beta₀, c]
    field_simp [ne_of_gt (by linarith : 0 < 1 + r)]
    ring
  have halpha : alpha ≤ alpha₀ := by
    dsimp [alpha, alpha₀, W]
    exact div_le_div_of_nonneg_left (sub_nonneg.mpr hcgd)
      (by linarith : 0 < 1 + r) (by linarith : 1 + r ≤ 1 + r + d)
  have hA₀ : 0 < A₀ := by dsimp [A₀]; positivity
  have hB₀ : 0 < B₀ := by
    dsimp [B₀]
    have := one_le_rightEdgePSeries hr0
    positivity
  have hB₀A₀ : B₀ ≤ A₀ := by
    have hlog8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      norm_num
    have hlog8le : Real.log 8 ≤ Real.log x0 :=
      Real.log_le_log (by norm_num) hx0
    rw [hlog8] at hlog8le
    have hlogTwo : 2 ≤ Real.log x0 := by
      nlinarith [Real.log_two_gt_d9]
    have hrHalf : r ≤ (1 / 2 : ℝ) := by
      dsimp [r]
      have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hlogTwo
      simpa [one_div] using hi
    have hPinv : rightEdgePSeries r ≤ 1 + Real.log x0 := by
      have hp := MAPRightEdgePSeriesExplicitBound.rightEdgePSeries_le_one_add_inv hr0
      have hrInv : 1 / r = Real.log x0 := by
        dsimp [r]
        field_simp
      rw [hrInv] at hp
      exact hp
    have hexp : Real.exp ((1 + r) ^ 2) ≤ Real.exp 4 := by
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg r]
    have hexp4 : Real.exp 4 < 81 := by
      rw [show (4 : ℝ) = (4 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      have hp := pow_lt_pow_left₀ Real.exp_one_lt_three
        (Real.exp_pos 1).le (by norm_num : (4 : ℕ) ≠ 0)
      norm_num at hp ⊢
      exact hp
    have hBcoarse : B₀ ≤ 81 * (1 + Real.log x0) := by
      dsimp [B₀]
      calc
        rightEdgePSeries r * Real.exp ((1 + r) ^ 2) ≤
            (1 + Real.log x0) * Real.exp 4 :=
          mul_le_mul hPinv hexp (Real.exp_pos _).le (by positivity)
        _ ≤ 81 * (1 + Real.log x0) := by
          have hL : 0 ≤ 1 + Real.log x0 := by positivity
          nlinarith [mul_nonneg hL (sub_nonneg.mpr hexp4.le)]
    have hQone : 1 ≤ 2 * (q : ℝ) * (3 + |u|) := by
      have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
      nlinarith [abs_nonneg u]
    have hQr : 1 ≤ Real.rpow (2 * (q : ℝ) * (3 + |u|)) (d + 1) :=
      Real.one_le_rpow hQone (by linarith)
    have hdInv : d⁻¹ = 400 * Real.log x0 := by
      dsimp [d, canonicalRamachandraOffset]
      field_simp
    have hscalar : 81 * (1 + Real.log x0) ≤ 48 * (1 + d⁻¹) := by
      rw [hdInv]
      nlinarith
    calc
      B₀ ≤ 81 * (1 + Real.log x0) := hBcoarse
      _ ≤ 48 * (1 + d⁻¹) := hscalar
      _ ≤ A₀ := by
        dsimp [A₀]
        have hp : 0 ≤ 48 * (1 + d⁻¹) := by positivity
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hQr hp
  have hK : 0 < principalHorizontalScale := by
    unfold principalHorizontalScale
    positivity
  have hA : A ≤ principalHorizontalScale * A₀ := by
    simpa [A, A₀, d] using
      (principal_left_base_le_scaled_ambient hq (x0 := x0) (u := u) hx0)
  have hB : B ≤ principalHorizontalScale * B₀ := by
    simpa [B, B₀, r] using
      (principal_right_base_le_scaled_ambient (x0 := x0) hx0)
  have hApos : 0 ≤ A := by unfold A principalLeftGaussianBound; positivity
  have hBpos : 0 ≤ B := by
    unfold B principalRightGaussianBound
    have := one_le_rightEdgePSeries hr0
    positivity
  have hfirst := scaled_interp_product_le hK hA₀ hB₀ hA hB hApos hBpos ha hb hsum
  have hambientWeights : Real.rpow A₀ alpha * Real.rpow B₀ beta ≤
      Real.rpow A₀ alpha₀ * Real.rpow B₀ beta₀ :=
    rpow_product_le_of_weight_shift hA₀ hB₀ hB₀A₀ hsum hsum₀ halpha
  have hfirstAmbient : Real.rpow A alpha * Real.rpow B beta ≤
      principalHorizontalScale *
        (Real.rpow A₀ alpha₀ * Real.rpow B₀ beta₀) :=
    hfirst.trans (mul_le_mul_of_nonneg_left hambientWeights hK.le)
  have hXpow : 0 ≤ Real.rpow X d := Real.rpow_nonneg hX.le _
  have hfirstX := mul_le_mul_of_nonneg_right hfirstAmbient hXpow
  have hfirstX' : Real.rpow A alpha * Real.rpow B beta * Real.rpow X d ≤
      principalHorizontalScale *
        (Real.rpow A₀ alpha₀ * Real.rpow B₀ beta₀ * Real.rpow X d) := by
    calc
      _ ≤ (principalHorizontalScale *
          (Real.rpow A₀ alpha₀ * Real.rpow B₀ beta₀)) * Real.rpow X d :=
        hfirstX
      _ = _ := by ring
  have hBright : Real.rpow B 1 * Real.rpow X c ≤
      principalHorizontalScale * (Real.rpow B₀ 1 * Real.rpow X c) := by
    norm_num
    calc
      B * Real.rpow X c ≤
          (principalHorizontalScale * B₀) * Real.rpow X c :=
        mul_le_mul_of_nonneg_right hB (Real.rpow_nonneg hX.le _)
      _ = principalHorizontalScale * (B₀ * Real.rpow X c) := by ring
  unfold principalHorizontalEndpointNumerator
  unfold ambientHorizontalGeneralEndpointNumerator
  change Real.rpow A alpha * Real.rpow B beta * Real.rpow X d +
      Real.rpow B 1 * Real.rpow X c ≤
    principalHorizontalScale *
      (Real.rpow A₀ alpha₀ * Real.rpow B₀ beta₀ * Real.rpow X d +
        Real.rpow B₀ 1 * Real.rpow X c)
  calc
    _ ≤ principalHorizontalScale *
          (Real.rpow A₀ alpha₀ *
            Real.rpow B₀ beta₀ * Real.rpow X d) +
        principalHorizontalScale *
          (Real.rpow B₀ 1 * Real.rpow X c) := add_le_add hfirstX' hBright
    _ = principalHorizontalScale *
        (Real.rpow A₀ alpha₀ *
            Real.rpow B₀ beta₀ * Real.rpow X d +
          Real.rpow B₀ 1 * Real.rpow X c) := by ring
    _ = _ := by rfl

/-- Literal `/w` estimate on either principal horizontal edge.  The high
imaginary part keeps the translated zeta pole away, while `principalAux`
removes it before three-lines interpolation. -/
theorem norm_bhpPerronIntegrand_principal_horizontal_le_endpoint
    {q : ℕ} [NeZero q] {x0 X t x v H : ℝ}
    (hx0 : 8 ≤ x0) (hqx : (q : ℝ) ≤ x0)
    (hX : 0 < X) (hH : 0 < H) (hv : |v| = H)
    (him : 1 ≤ |t + v|)
    (hxd : canonicalRamachandraOffset x0 ≤ x)
    (hxc : x ≤ 1 / 2 + (Real.log x0)⁻¹) :
    ‖bhpPerronIntegrand (1 : DirichletCharacter ℂ q) X t
        ((x : ℂ) + Complex.I * v)‖ ≤
      4 * principalHorizontalEndpointNumerator q x0 X (t + v) / H := by
  let d := canonicalRamachandraOffset x0
  let r := (Real.log x0)⁻¹
  let W := 1 + r + d
  let c := 1 / 2 + r
  let sigma := 1 / 2 + x
  let u := t + v
  let s : ℂ := (sigma : ℂ) + (u : ℂ) * I
  let A := principalLeftGaussianBound q x0 u
  let B := principalRightGaussianBound x0
  have hxOne : 1 < x0 := by linarith
  have hlog : 0 < Real.log x0 := Real.log_pos hxOne
  have hd0 : 0 < d := by dsimp [d, canonicalRamachandraOffset]; positivity
  have hr0 : 0 < r := by dsimp [r]; positivity
  have hW : 0 < W := by dsimp [W]; linarith
  have hc : c ≤ (1 : ℝ) := by
    have hlog8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      norm_num
    have hlog8le : Real.log 8 ≤ Real.log x0 :=
      Real.log_le_log (by norm_num) hx0
    rw [hlog8] at hlog8le
    have hlogTwo : 2 ≤ Real.log x0 := by
      nlinarith [Real.log_two_gt_d9]
    have hrHalf : r ≤ (1 / 2 : ℝ) := by
      dsimp [r]
      have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hlogTwo
      simpa [one_div] using hi
    dsimp [c]
    linarith
  have hsigmaLo : -d ≤ sigma := by dsimp [sigma]; linarith
  have hsigmaHi : sigma ≤ 1 + r := by dsimp [sigma, c] at hxc ⊢; linarith
  have hsre : s.re = sigma := by simp [s]
  have hsim : s.im = u := by simp [s]
  have hsreLo : 0 ≤ s.re := by rw [hsre]; dsimp [sigma]; linarith
  have hsreHi : s.re ≤ 2 := by rw [hsre]; linarith [hsigmaHi]
  have hsimHigh : 1 ≤ |s.im| := by simpa [hsim, u] using him
  have hs1 : s ≠ 1 := by
    intro heq
    have hi := congrArg Complex.im heq
    simp [hsim] at hi
    rw [hsim, hi, abs_zero] at hsimHigh
    norm_num at hsimHigh
  have hsneg1 : s + 1 ≠ 0 := by
    intro heq
    have hre := congrArg Complex.re heq
    simp [hsre] at hre
    linarith
  have hidentity :
      DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s =
        ((s + 1) / (s - 1)) * principalAux q s := by
    have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    rw [principalAux_eq_principalNormalized_of_ne_one hs1,
      principalNormalized_eq_ratio_mul_LFunction hs1]
    field_simp [hsub, hsneg1]
  have hratio := norm_add_div_sub_le_four_of_high hsreLo hsreHi hsimHigh
  have hL : ‖DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s‖ ≤
      4 * ‖principalAux q s‖ := by
    rw [hidentity, norm_mul]
    exact mul_le_mul_of_nonneg_right hratio (norm_nonneg _)
  have hAuxRaw := norm_principalAux_canonical_interp
    (q := q) (x0 := x0) (sigma := sigma) (u := u)
      hx0 hqx (by simpa [d] using hsigmaLo) (by simpa [r] using hsigmaHi)
  have hAux : ‖principalAux q s‖ ≤
      Real.rpow A ((c - x) / W) *
        Real.rpow B ((x + (W - c)) / W) := by
    have hleft : (1 + r - sigma) / W = (c - x) / W := by
      congr 1
      dsimp [sigma, c]
      ring
    have hright : (sigma + d) / W = (x + (W - c)) / W := by
      congr 1
      dsimp [sigma, W, c]
      ring
    rw [hleft, hright] at hAuxRaw
    simpa only [s, A, B, d, r, W, u] using hAuxRaw
  have hA : 0 < A := by
    unfold A principalLeftGaussianBound
    have hqpos : 0 < (q : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
    positivity
  have hB : 0 < B := by
    unfold B principalRightGaussianBound
    have := one_le_rightEdgePSeries hr0
    positivity
  have hend := weighted_strip_interpolation_le_endpoint_sum
    hA hB hX hW (by simpa [d] using hxd) (by simpa [c, r] using hxc)
      (d := d) (c := c) (W := W) (x := x)
  have hauxWeighted : ‖principalAux q s‖ * Real.rpow X x ≤
      principalHorizontalEndpointNumerator q x0 X u := by
    calc
      ‖principalAux q s‖ * Real.rpow X x ≤
          (Real.rpow A ((c - x) / W) *
            Real.rpow B ((x + (W - c)) / W)) * Real.rpow X x :=
        mul_le_mul_of_nonneg_right hAux (Real.rpow_nonneg hX.le _)
      _ ≤ principalHorizontalEndpointNumerator q x0 X u := by
        simpa [principalHorizontalEndpointNumerator, A, B, c, W, d, r] using hend
  have hpow :
      ‖Complex.exp ((((x : ℂ) + Complex.I * v) * Real.log X))‖ =
        Real.rpow X x := by
    rw [← PerronKernel.verticalPower_eq_exp hX x v]
    exact PerronKernel.norm_verticalPower hX x v
  have hden : H ≤ ‖(x : ℂ) + Complex.I * v‖ := by
    rw [← hv]
    calc
      |v| = |(((x : ℂ) + Complex.I * v).im)| := by simp
      _ ≤ ‖(x : ℂ) + Complex.I * v‖ := Complex.abs_im_le_norm _
  have hN0 : 0 ≤ principalHorizontalEndpointNumerator q x0 X u := by
    unfold principalHorizontalEndpointNumerator
    have hA0 : 0 ≤ principalLeftGaussianBound q x0 u := by
      unfold principalLeftGaussianBound; positivity
    have hB0 : 0 ≤ principalRightGaussianBound x0 := by
      unfold principalRightGaussianBound
      have := one_le_rightEdgePSeries hr0
      positivity
    exact add_nonneg
      (mul_nonneg (mul_nonneg (Real.rpow_nonneg hA0 _)
        (Real.rpow_nonneg hB0 _)) (Real.rpow_nonneg hX.le _))
      (mul_nonneg (Real.rpow_nonneg hB0 _) (Real.rpow_nonneg hX.le _))
  unfold bhpPerronIntegrand
  rw [norm_div, norm_mul, hpow]
  have harg :
      ((((1 / 2 : ℝ) : ℂ) + t * Complex.I) +
          ((x : ℂ) + Complex.I * v)) = s := by
    dsimp [s, sigma, u]
    push_cast
    ring
  rw [harg]
  calc
    ‖DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s‖ *
          Real.rpow X x / ‖(x : ℂ) + Complex.I * v‖ ≤
        (4 * ‖principalAux q s‖) * Real.rpow X x /
          ‖(x : ℂ) + Complex.I * v‖ := by
      apply div_le_div_of_nonneg_right _ (norm_nonneg _)
      exact mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg hX.le _)
    _ ≤ (4 * principalHorizontalEndpointNumerator q x0 X u) /
          ‖(x : ℂ) + Complex.I * v‖ := by
      apply div_le_div_of_nonneg_right _ (norm_nonneg _)
      nlinarith [hauxWeighted]
    _ ≤ (4 * principalHorizontalEndpointNumerator q x0 X u) / H := by
      exact div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hN0) hH hden
    _ = _ := by rfl

/-- Both principal horizontal edges with the pole-safe endpoint numerator and
the literal Perron division by the height. -/
theorem norm_bhpHorizontalBoundaryIntegral_principal_endpoints_le
    {q : ℕ} [NeZero q] {x0 X t T : ℝ}
    (hx0 : 8 ≤ x0) (hqx : (q : ℝ) ≤ x0)
    (hX : 0 < X) (hT : 1 ≤ T) (ht : |t| ≤ T) :
    ‖bhpHorizontalBoundaryIntegral (1 : DirichletCharacter ℂ q) X t
        (canonicalRamachandraOffset x0)
        (1 / 2 + (Real.log x0)⁻¹) (2 * T)‖ ≤
      ‖((((2 * Real.pi : ℝ) : ℂ)⁻¹) * Complex.I)‖ *
        (((4 * principalHorizontalEndpointNumerator q x0 X (t + 2 * T) /
              (2 * T)) +
          (4 * principalHorizontalEndpointNumerator q x0 X (t - 2 * T) /
              (2 * T))) *
            (1 / 2 + (Real.log x0)⁻¹ -
              canonicalRamachandraOffset x0)) := by
  let d := canonicalRamachandraOffset x0
  let c := 1 / 2 + (Real.log x0)⁻¹
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hH0 : 0 < 2 * T := by positivity
  have hxOne : 1 < x0 := by linarith
  have hlog : 0 < Real.log x0 := Real.log_pos hxOne
  have hd0 : 0 < d := by dsimp [d, canonicalRamachandraOffset]; positivity
  have hdc : d ≤ c := by
    dsimp [d, c, canonicalRamachandraOffset]
    have hden : Real.log x0 ≤ 400 * Real.log x0 := by nlinarith
    have hi := one_div_le_one_div_of_le hlog hden
    have : (400 * Real.log x0)⁻¹ ≤ (Real.log x0)⁻¹ := by
      simpa [one_div] using hi
    linarith
  have htopHigh : 1 ≤ |t + 2 * T| := by
    have htLower := (abs_le.mp ht).1
    have hnonneg : 0 ≤ t + 2 * T := by linarith
    rw [abs_of_nonneg hnonneg]
    linarith
  have hbottomHigh : 1 ≤ |t - 2 * T| := by
    have htUpper := (abs_le.mp ht).2
    have hnonpos : t - 2 * T ≤ 0 := by linarith
    rw [abs_of_nonpos hnonpos]
    linarith
  have hNtop0 : 0 ≤ principalHorizontalEndpointNumerator q x0 X
      (t + 2 * T) := by
    unfold principalHorizontalEndpointNumerator
    have hB : 0 ≤ principalRightGaussianBound x0 := by
      unfold principalRightGaussianBound
      have hp := one_le_rightEdgePSeries (inv_pos.mpr hlog)
      positivity
    have hA : 0 ≤ principalLeftGaussianBound q x0 (t + 2 * T) := by
      unfold principalLeftGaussianBound; positivity
    exact add_nonneg
      (mul_nonneg (mul_nonneg (Real.rpow_nonneg hA _)
        (Real.rpow_nonneg hB _)) (Real.rpow_nonneg hX.le _))
      (mul_nonneg (Real.rpow_nonneg hB _) (Real.rpow_nonneg hX.le _))
  have hNbottom0 : 0 ≤ principalHorizontalEndpointNumerator q x0 X
      (t - 2 * T) := by
    unfold principalHorizontalEndpointNumerator
    have hB : 0 ≤ principalRightGaussianBound x0 := by
      unfold principalRightGaussianBound
      have hp := one_le_rightEdgePSeries (inv_pos.mpr hlog)
      positivity
    have hA : 0 ≤ principalLeftGaussianBound q x0 (t - 2 * T) := by
      unfold principalLeftGaussianBound; positivity
    exact add_nonneg
      (mul_nonneg (mul_nonneg (Real.rpow_nonneg hA _)
        (Real.rpow_nonneg hB _)) (Real.rpow_nonneg hX.le _))
      (mul_nonneg (Real.rpow_nonneg hB _) (Real.rpow_nonneg hX.le _))
  have hraw := norm_bhpHorizontalBoundaryIntegral_le_of_pointwise
    (1 : DirichletCharacter ℂ q) (X := X) (t := t) (delta := d)
      (c := c) (H := 2 * T) hdc
      (div_nonneg (mul_nonneg (by norm_num) hNtop0) hH0.le)
      (div_nonneg (mul_nonneg (by norm_num) hNbottom0) hH0.le)
      (Mtop := 4 * principalHorizontalEndpointNumerator q x0 X (t + 2 * T) /
        (2 * T))
      (Mbottom := 4 * principalHorizontalEndpointNumerator q x0 X (t - 2 * T) /
        (2 * T))
  apply hraw
  · intro x hx
    have hx' : x ∈ Set.Ioc d c := by
      simpa [Set.uIoc_of_le hdc] using hx
    exact norm_bhpPerronIntegrand_principal_horizontal_le_endpoint
      hx0 hqx hX hH0 (by rw [abs_of_pos hH0]) htopHigh hx'.1.le hx'.2
  · intro x hx
    have hx' : x ∈ Set.Ioc d c := by
      simpa [Set.uIoc_of_le hdc] using hx
    have hpoint := norm_bhpPerronIntegrand_principal_horizontal_le_endpoint
      hx0 hqx hX hH0 (v := -(2 * T))
        (by rw [abs_neg, abs_of_pos hH0]) hbottomHigh hx'.1.le hx'.2
    simpa [sub_eq_add_neg] using hpoint

def principalHorizontalSourceConstant : ℝ :=
  320000 *
    ‖((((2 * Real.pi : ℝ) : ℂ)⁻¹) * Complex.I)‖ *
    principalHorizontalScale * Real.exp 9

theorem principalHorizontalSourceConstant_pos :
    0 < principalHorizontalSourceConstant := by
  unfold principalHorizontalSourceConstant principalHorizontalScale
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hcomplex : (((2 * Real.pi : ℝ) : ℂ) ≠ 0) := by
    exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  have hnorm : 0 < ‖((((2 * Real.pi : ℝ) : ℂ)⁻¹) * Complex.I)‖ := by
    rw [norm_pos_iff]
    exact mul_ne_zero (inv_ne_zero hcomplex) Complex.I_ne_zero
  exact mul_pos (mul_pos (mul_pos (by norm_num) hnorm) (by positivity)) (by positivity)

/-- The principal horizontal source is inhabited with a single global
constant.  No bundled fourth-moment or contour premise is used here. -/
theorem canonicalPrincipalHorizontalSource_proved :
    CanonicalPrincipalHorizontalSource := by
  refine ⟨principalHorizontalSourceConstant,
    principalHorizontalSourceConstant_pos, ?_⟩
  intro q X _ t T x0 hX hT hx0 hqx hXx hTx hTwoTx ht
  have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hXpos : 0 < (X : ℝ) := by positivity
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have h2T0 : 0 < 2 * T := by positivity
  have htopHeight : |t + 2 * T| ≤ 3 * T := by
    have h2Tabs : |2 * T| = 2 * T := abs_of_nonneg (by positivity)
    calc
      |t + 2 * T| ≤ |t| + |2 * T| := abs_add_le _ _
      _ = |t| + 2 * T := by rw [h2Tabs]
      _ ≤ 3 * T := by linarith
  have hbottomHeight : |t - 2 * T| ≤ 3 * T := by
    have hneg2Tabs : |-(2 * T)| = 2 * T := by
      rw [abs_neg, abs_of_nonneg (by positivity)]
    calc
      |t - 2 * T| ≤ |t| + |-(2 * T)| := by
        simpa only [sub_eq_add_neg] using abs_add_le t (-(2 * T))
      _ = |t| + 2 * T := by rw [hneg2Tabs]
      _ ≤ 3 * T := by linarith
  let S : ℝ := 20000 * (1 + Real.log x0) ^ 2 * Real.exp 9
  let M : ℝ := principalHorizontalScale * S *
    (4 * Real.sqrt (q : ℝ) * Real.sqrt T + Real.sqrt (X : ℝ))
  have hS0 : 0 ≤ S := by dsimp [S]; positivity
  have hM0 : 0 ≤ M := by dsimp [M, principalHorizontalScale]; positivity
  have htopCompare := principalHorizontalEndpointNumerator_le_scaled_ambient
    hq hx0 hXpos (u := t + 2 * T)
  have hbottomCompare := principalHorizontalEndpointNumerator_le_scaled_ambient
    hq hx0 hXpos (u := t - 2 * T)
  have htopAmbient := ambientHorizontalGeneralEndpointNumerator_canonical_le
    hq hx0 hXpos hXx hqx hT hTx htopHeight
      (u := t + 2 * T)
  have hbottomAmbient := ambientHorizontalGeneralEndpointNumerator_canonical_le
    hq hx0 hXpos hXx hqx hT hTx hbottomHeight
      (u := t - 2 * T)
  have htopSqrt := sqrt_edge_height_le hq hT htopHeight
  have hbottomSqrt := sqrt_edge_height_le hq hT hbottomHeight
  have htop : principalHorizontalEndpointNumerator q x0 (X : ℝ)
      (t + 2 * T) ≤ M := by
    refine htopCompare.trans ?_
    have hamb : ambientHorizontalGeneralEndpointNumerator q
        (canonicalRamachandraOffset x0) (Real.log x0)⁻¹
        (canonicalRamachandraOffset x0) (X : ℝ) (t + 2 * T) ≤
          S * (4 * Real.sqrt (q : ℝ) * Real.sqrt T + Real.sqrt (X : ℝ)) := by
      refine htopAmbient.trans ?_
      exact mul_le_mul_of_nonneg_left
        (add_le_add htopSqrt (le_refl (Real.sqrt (X : ℝ)))) hS0
    calc
      principalHorizontalScale *
          ambientHorizontalGeneralEndpointNumerator q
            (canonicalRamachandraOffset x0) (Real.log x0)⁻¹
            (canonicalRamachandraOffset x0) (X : ℝ) (t + 2 * T) ≤
        principalHorizontalScale *
          (S * (4 * Real.sqrt (q : ℝ) * Real.sqrt T + Real.sqrt (X : ℝ))) :=
        mul_le_mul_of_nonneg_left hamb
          (by unfold principalHorizontalScale; positivity)
      _ = M := by dsimp [M]; ring
  have hbottom : principalHorizontalEndpointNumerator q x0 (X : ℝ)
      (t - 2 * T) ≤ M := by
    refine hbottomCompare.trans ?_
    have hamb : ambientHorizontalGeneralEndpointNumerator q
        (canonicalRamachandraOffset x0) (Real.log x0)⁻¹
        (canonicalRamachandraOffset x0) (X : ℝ) (t - 2 * T) ≤
          S * (4 * Real.sqrt (q : ℝ) * Real.sqrt T + Real.sqrt (X : ℝ)) := by
      refine hbottomAmbient.trans ?_
      exact mul_le_mul_of_nonneg_left
        (add_le_add hbottomSqrt (le_refl (Real.sqrt (X : ℝ)))) hS0
    calc
      principalHorizontalScale *
          ambientHorizontalGeneralEndpointNumerator q
            (canonicalRamachandraOffset x0) (Real.log x0)⁻¹
            (canonicalRamachandraOffset x0) (X : ℝ) (t - 2 * T) ≤
        principalHorizontalScale *
          (S * (4 * Real.sqrt (q : ℝ) * Real.sqrt T + Real.sqrt (X : ℝ))) :=
        mul_le_mul_of_nonneg_left hamb
          (by unfold principalHorizontalScale; positivity)
      _ = M := by dsimp [M]; ring
  have hraw := norm_bhpHorizontalBoundaryIntegral_principal_endpoints_le
    hx0 hqx hXpos hT ht (q := q) (x0 := x0) (X := (X : ℝ))
      (t := t) (T := T)
  let Ntop := principalHorizontalEndpointNumerator q x0 (X : ℝ) (t + 2 * T)
  let Nbottom := principalHorizontalEndpointNumerator q x0 (X : ℝ) (t - 2 * T)
  let width : ℝ := 1 / 2 + (Real.log x0)⁻¹ - canonicalRamachandraOffset x0
  have hxOne : 1 < x0 := by linarith
  have hlog : 0 < Real.log x0 := Real.log_pos hxOne
  have hlog8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  have hlog8le : Real.log 8 ≤ Real.log x0 := Real.log_le_log (by norm_num) hx0
  rw [hlog8] at hlog8le
  have hlogTwo : 2 ≤ Real.log x0 := by nlinarith [Real.log_two_gt_d9]
  have hrHalf : (Real.log x0)⁻¹ ≤ (1 / 2 : ℝ) := by
    have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hlogTwo
    simpa [one_div] using hi
  have hwidth0 : 0 ≤ width := by
    dsimp [width, canonicalRamachandraOffset]
    have hden : Real.log x0 ≤ 400 * Real.log x0 := by nlinarith
    have hi := one_div_le_one_div_of_le hlog hden
    have : (400 * Real.log x0)⁻¹ ≤ (Real.log x0)⁻¹ := by
      simpa [one_div] using hi
    linarith
  have hwidthOne : width ≤ 1 := by
    dsimp [width]
    have hd0 : 0 ≤ canonicalRamachandraOffset x0 := by
      unfold canonicalRamachandraOffset; positivity
    linarith
  have hEndpoint0 (u : ℝ) :
      0 ≤ principalHorizontalEndpointNumerator q x0 (X : ℝ) u := by
    unfold principalHorizontalEndpointNumerator
    have hB : 0 ≤ principalRightGaussianBound x0 := by
      unfold principalRightGaussianBound
      have hp := one_le_rightEdgePSeries (inv_pos.mpr hlog)
      positivity
    have hA : 0 ≤ principalLeftGaussianBound q x0 u := by
      unfold principalLeftGaussianBound; positivity
    exact add_nonneg
      (mul_nonneg (mul_nonneg (Real.rpow_nonneg hA _)
        (Real.rpow_nonneg hB _)) (Real.rpow_nonneg hXpos.le _))
      (mul_nonneg (Real.rpow_nonneg hB _) (Real.rpow_nonneg hXpos.le _))
  have hNtop0 : 0 ≤ Ntop := by simpa [Ntop] using hEndpoint0 (t + 2 * T)
  have hNbottom0 : 0 ≤ Nbottom := by
    simpa [Nbottom] using hEndpoint0 (t - 2 * T)
  have htopDiv : 4 * Ntop / (2 * T) ≤ 4 * M / (2 * T) := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by simpa [Ntop] using htop) (by norm_num)) h2T0.le
  have hbottomDiv : 4 * Nbottom / (2 * T) ≤ 4 * M / (2 * T) := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by simpa [Nbottom] using hbottom) (by norm_num)) h2T0.le
  have hsum0 : 0 ≤ 4 * Ntop / (2 * T) + 4 * Nbottom / (2 * T) := by
    positivity
  have hsum : 4 * Ntop / (2 * T) + 4 * Nbottom / (2 * T) ≤ 4 * M / T := by
    have hs := add_le_add htopDiv hbottomDiv
    calc
      _ ≤ 4 * M / (2 * T) + 4 * M / (2 * T) := hs
      _ = 4 * M / T := by field_simp [hT0.ne']; ring
  have hweighted :
      (4 * Ntop / (2 * T) + 4 * Nbottom / (2 * T)) * width ≤
        4 * M / T := by
    calc
      _ ≤ (4 * Ntop / (2 * T) + 4 * Nbottom / (2 * T)) * 1 :=
        mul_le_mul_of_nonneg_left hwidthOne hsum0
      _ ≤ 4 * M / T := by simpa using hsum
  have hsqrtT : 0 < Real.sqrt T := Real.sqrt_pos.2 hT0
  have hsqrtDiv : Real.sqrt T / T = 1 / Real.sqrt T := by
    field_simp [hT0.ne', hsqrtT.ne']
    simpa [pow_two] using Real.sq_sqrt hT0.le
  let a : ℝ := Real.sqrt (q : ℝ) / Real.sqrt T
  let b : ℝ := Real.sqrt (X : ℝ) / T
  let Cbase : ℝ := principalHorizontalScale * (1 + Real.log x0) ^ 2 * Real.exp 9
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have hCbase0 : 0 ≤ Cbase := by
    dsimp [Cbase, principalHorizontalScale]; positivity
  have hcollapse : 4 * M / T ≤ 320000 * Cbase * (a + b) := by
    have hMrewrite : 4 * M / T = 80000 * Cbase * (4 * a + b) := by
      calc
        4 * M / T = 80000 * Cbase *
            (4 * Real.sqrt (q : ℝ) * (Real.sqrt T / T) +
              Real.sqrt (X : ℝ) / T) := by
          dsimp [M, S, Cbase]
          ring
        _ = 80000 * Cbase * (4 * a + b) := by
          rw [hsqrtDiv]
          dsimp [a, b]
          ring
    rw [hMrewrite]
    calc
      80000 * Cbase * (4 * a + b) ≤
          80000 * Cbase * (4 * (a + b)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
      _ = 320000 * Cbase * (a + b) := by ring
  calc
    ‖bhpHorizontalBoundaryIntegral (1 : DirichletCharacter ℂ q) (X : ℝ) t
        (canonicalRamachandraOffset x0)
        (1 / 2 + (Real.log x0)⁻¹) (2 * T)‖ ≤
      ‖((((2 * Real.pi : ℝ) : ℂ)⁻¹) * Complex.I)‖ *
        ((4 * Ntop / (2 * T) + 4 * Nbottom / (2 * T)) * width) := by
      simpa [Ntop, Nbottom, width] using hraw
    _ ≤ ‖((((2 * Real.pi : ℝ) : ℂ)⁻¹) * Complex.I)‖ *
        (4 * M / T) := mul_le_mul_of_nonneg_left hweighted (norm_nonneg _)
    _ ≤ principalHorizontalSourceConstant * (1 + Real.log x0) ^ 2 *
        (Real.sqrt (q : ℝ) / Real.sqrt T + Real.sqrt (X : ℝ) / T) := by
      have hc := mul_le_mul_of_nonneg_left hcollapse
        (norm_nonneg ((((2 * Real.pi : ℝ) : ℂ)⁻¹) * Complex.I))
      calc
        _ ≤ ‖((((2 * Real.pi : ℝ) : ℂ)⁻¹) * Complex.I)‖ *
            (320000 * Cbase * (a + b)) := hc
        _ = _ := by
          unfold principalHorizontalSourceConstant
          dsimp [Cbase, a, b]
          ring

end
end MAPBHPCanonicalPrincipalHorizontalClosed

#print axioms MAPBHPCanonicalPrincipalHorizontalClosed.principalHorizontalEndpointNumerator_le_scaled_ambient
#print axioms MAPBHPCanonicalPrincipalHorizontalClosed.norm_bhpPerronIntegrand_principal_horizontal_le_endpoint
#print axioms MAPBHPCanonicalPrincipalHorizontalClosed.norm_bhpHorizontalBoundaryIntegral_principal_endpoints_le
#print axioms MAPBHPCanonicalPrincipalHorizontalClosed.canonicalPrincipalHorizontalSource_proved
