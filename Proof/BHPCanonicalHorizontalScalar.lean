import BHPHorizontalEndpointInterpolation
import RamachandraTheorem6ShiftedStripSource

/-!
# Scalar specialization of the corrected BHP horizontal endpoints
-/

namespace MAPBHPCanonicalHorizontalScalar

open MAPBHPHorizontalEndpointInterpolation
open MAPBHPCorrectedContourShift
open MAPZeroFreeSiegelSpine
open RamachandraTheorem6ShiftedStripSource

noncomputable section

/-- The exact endpoint numerator is bounded by the two familiar square-root
scales.  This is the algebraic heart of the BHP horizontal estimate; the
remaining specialization only replaces `delta^-1` and bounds heights. -/
theorem ambientHorizontalEndpointNumerator_le_squareRootScales
    {q : ℕ} (hq : 1 ≤ q) {delta X u : ℝ}
    (hdelta : 0 < delta) (hX : 0 < X) :
    ambientHorizontalEndpointNumerator q delta X u ≤
      let C := 48 * (1 + delta⁻¹)
      let Q := 2 * (q : ℝ) * (3 + |u|)
      let B := rightEdgePSeries delta * Real.exp ((1 + delta) ^ 2)
      C * Real.sqrt Q * B * Real.rpow X delta +
        B * Real.sqrt X * Real.rpow X delta := by
  let C : ℝ := 48 * (1 + delta⁻¹)
  let Q : ℝ := 2 * (q : ℝ) * (3 + |u|)
  let B : ℝ := rightEdgePSeries delta * Real.exp ((1 + delta) ^ 2)
  let W : ℝ := 1 + delta
  let theta : ℝ := (1 / 2) / W
  let phi : ℝ := (1 / 2 + delta) / W
  have hqR : 0 < (q : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hq)
  have hC : 1 ≤ C := by
    dsimp [C]
    have : 0 ≤ delta⁻¹ := inv_nonneg.mpr hdelta.le
    nlinarith
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hB : 1 ≤ B := by
    dsimp [B]
    have hp := one_le_rightEdgePSeries hdelta
    have he : 1 ≤ Real.exp ((1 + delta) ^ 2) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (sq_nonneg _)
    nlinarith [mul_le_mul hp he (by positivity) (by positivity)]
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hW : 0 < W := by dsimp [W]; linarith
  have htheta0 : 0 ≤ theta := by dsimp [theta]; positivity
  have htheta1 : theta ≤ 1 := by
    dsimp [theta, W]
    rw [div_le_iff₀ hW]
    linarith
  have hphi0 : 0 ≤ phi := by dsimp [phi, W]; positivity
  have hphi1 : phi ≤ 1 := by
    dsimp [phi, W]
    rw [div_le_iff₀ hW]
    linarith
  have hCtheta : Real.rpow C theta ≤ C := by
    rw [Real.rpow_eq_pow]
    have := Real.rpow_le_rpow_of_exponent_le hC htheta1
    simpa using this
  have hBphi : Real.rpow B phi ≤ B := by
    rw [Real.rpow_eq_pow]
    have := Real.rpow_le_rpow_of_exponent_le hB hphi1
    simpa using this
  have hQpower :
      Real.rpow (Real.rpow Q W) theta = Real.sqrt Q := by
    rw [Real.rpow_eq_pow, Real.rpow_eq_pow]
    rw [← Real.rpow_mul hQ.le]
    have hmul : W * theta = (1 / 2 : ℝ) := by
      dsimp [theta]
      field_simp [ne_of_gt hW]
    rw [hmul, ← Real.sqrt_eq_rpow]
  have hAtheta :
      Real.rpow (C * Real.rpow Q W) theta ≤ C * Real.sqrt Q := by
    simp only [Real.rpow_eq_pow]
    rw [Real.mul_rpow hC0 (Real.rpow_nonneg hQ.le _)]
    have hright := hQpower
    simp only [Real.rpow_eq_pow] at hright
    have hleft := hCtheta
    rw [Real.rpow_eq_pow] at hleft
    rw [hright]
    exact mul_le_mul_of_nonneg_right hleft (Real.sqrt_nonneg _)
  have hXd0 : 0 ≤ Real.rpow X delta := Real.rpow_nonneg hX.le _
  have hsqrtQ0 : 0 ≤ Real.sqrt Q := Real.sqrt_nonneg _
  have hsqrtX0 : 0 ≤ Real.sqrt X := Real.sqrt_nonneg _
  unfold ambientHorizontalEndpointNumerator
  dsimp only [C, Q, B, W, theta, phi]
  have hexpA :
      (((1 / 2 + delta) - delta) / (1 + delta)) = theta := by
    dsimp [theta, W]
    congr 1
    ring
  have hexpB :
      (delta + ((1 + delta) - (1 / 2 + delta))) /
        (1 + delta) = phi := by
    dsimp [phi, W]
    congr 1
    ring
  have hAform :
      48 * (1 + delta⁻¹) *
          Real.rpow (2 * (q : ℝ) * (3 + |u|)) (delta + 1) =
        C * Real.rpow Q W := by
    dsimp [C, Q, W]
    congr 2
    ring
  rw [hexpA, hexpB, hAform]
  have hBone : Real.rpow B 1 = B := by
    rw [Real.rpow_eq_pow, Real.rpow_one]
  rw [hBone]
  have hXhalf : Real.rpow X (1 / 2 + delta) =
      Real.sqrt X * Real.rpow X delta := by
    rw [Real.rpow_eq_pow]
    rw [Real.rpow_add hX (1 / 2) delta, ← Real.sqrt_eq_rpow]
    rfl
  rw [hXhalf]
  apply add_le_add
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul hAtheta hBphi (Real.rpow_nonneg hB0 _)
        (mul_nonneg hC0 hsqrtQ0)) hXd0
  · dsimp [B]
    simpa only [mul_assoc] using le_refl
      (rightEdgePSeries delta * Real.exp ((1 + delta) ^ 2) *
        Real.sqrt X * (X ^ delta : ℝ))

/-- At the endpoint-safe Ramachandra offset every contour-kernel loss is an
explicit fixed power of the ambient logarithm.  This is deliberately stated
before estimating the height `u`: it can be reused for the upper and lower
horizontal edges without duplicating absolute-value algebra. -/
theorem ambientHorizontalEndpointNumerator_canonical_le
    {q : ℕ} (hq : 1 ≤ q) {X x0 u : ℝ}
    (hx0 : 2 ≤ x0) (hX : 0 < X) (hXx : X ≤ x0) :
    ambientHorizontalEndpointNumerator q
        (canonicalRamachandraOffset x0) X u ≤
      (48 * (1 + 400 * Real.log x0) *
          Real.sqrt (2 * (q : ℝ) * (3 + |u|)) + Real.sqrt X) *
        ((1 + 400 * Real.log x0) * Real.exp 4 *
          Real.exp (1 / 400 : ℝ)) := by
  let delta : ℝ := canonicalRamachandraOffset x0
  let P : ℝ := 1 + 400 * Real.log x0
  let Q : ℝ := 2 * (q : ℝ) * (3 + |u|)
  let B : ℝ := rightEdgePSeries delta * Real.exp ((1 + delta) ^ 2)
  have hx0one : 1 < x0 := by linarith
  have hlog : 0 < Real.log x0 := Real.log_pos hx0one
  have hdelta : 0 < delta := by
    dsimp [delta, canonicalRamachandraOffset]
    positivity
  have hdeltaOne : delta ≤ 1 := by
    dsimp [delta, canonicalRamachandraOffset]
    rw [inv_le_one₀ (by positivity : 0 < 400 * Real.log x0)]
    nlinarith [Real.log_two_gt_d9,
      Real.strictMonoOn_log.monotoneOn (by norm_num : (0 : ℝ) < 2)
        (by linarith : 0 < x0) hx0]
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    have hqR : 0 ≤ (q : ℝ) := by positivity
    positivity
  have hBinv : rightEdgePSeries delta ≤ 1 + delta⁻¹ := by
    simpa only [one_div] using
      MAPRightEdgePSeriesExplicitBound.rightEdgePSeries_le_one_add_inv hdelta
  have hPinv : 1 + delta⁻¹ = P := by
    dsimp [delta, P]
    rw [canonicalRamachandraOffset_inv]
  have hexp : Real.exp ((1 + delta) ^ 2) ≤ Real.exp 4 := by
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg delta]
  have hB : B ≤ P * Real.exp 4 := by
    dsimp [B]
    rw [hPinv] at hBinv
    exact mul_le_mul hBinv hexp (Real.exp_pos _).le hP
  have hB0 : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg
      (zero_le_one.trans (one_le_rightEdgePSeries hdelta))
      (Real.exp_pos _).le
  have hXd := rpow_canonicalRamachandraOffset_le hX hXx hx0one
  have hXd0 : 0 ≤ X ^ delta := by
    exact Real.rpow_nonneg hX.le _
  have hPX : B * X ^ delta ≤
      P * Real.exp 4 * Real.exp (1 / 400 : ℝ) := by
    exact mul_le_mul hB hXd hXd0
      (mul_nonneg hP (Real.exp_pos _).le)
  have hraw := ambientHorizontalEndpointNumerator_le_squareRootScales
    hq hdelta hX (u := u)
  dsimp only [delta, P, Q, B] at hraw hPX ⊢
  rw [canonicalRamachandraOffset_inv] at hraw
  have hsqrtQ : 0 ≤ Real.sqrt (2 * (q : ℝ) * (3 + |u|)) :=
    Real.sqrt_nonneg _
  have hsqrtX : 0 ≤ Real.sqrt X := Real.sqrt_nonneg _
  calc
    ambientHorizontalEndpointNumerator q
        (canonicalRamachandraOffset x0) X u ≤
      48 * (1 + 400 * Real.log x0) *
          Real.sqrt (2 * (q : ℝ) * (3 + |u|)) *
            (rightEdgePSeries (canonicalRamachandraOffset x0) *
              Real.exp ((1 + canonicalRamachandraOffset x0) ^ 2) *
              X ^ canonicalRamachandraOffset x0) +
        Real.sqrt X *
            (rightEdgePSeries (canonicalRamachandraOffset x0) *
              Real.exp ((1 + canonicalRamachandraOffset x0) ^ 2) *
              X ^ canonicalRamachandraOffset x0) := by
        calc
          _ ≤ 48 * (1 + 400 * Real.log x0) *
                Real.sqrt (2 * (q : ℝ) * (3 + |u|)) *
                (rightEdgePSeries (canonicalRamachandraOffset x0) *
                  Real.exp ((1 + canonicalRamachandraOffset x0) ^ 2)) *
                X ^ canonicalRamachandraOffset x0 +
              (rightEdgePSeries (canonicalRamachandraOffset x0) *
                  Real.exp ((1 + canonicalRamachandraOffset x0) ^ 2)) *
                Real.sqrt X * X ^ canonicalRamachandraOffset x0 := hraw
          _ = _ := by ring
    _ ≤ 48 * (1 + 400 * Real.log x0) *
          Real.sqrt (2 * (q : ℝ) * (3 + |u|)) *
            ((1 + 400 * Real.log x0) * Real.exp 4 *
              Real.exp (1 / 400 : ℝ)) +
        Real.sqrt X *
            ((1 + 400 * Real.log x0) * Real.exp 4 *
              Real.exp (1 / 400 : ℝ)) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hPX
            (mul_nonneg
              (mul_nonneg (by positivity)
                (by positivity : 0 ≤ 1 + 400 * Real.log x0)) hsqrtQ)
        · exact mul_le_mul_of_nonneg_left hPX hsqrtX
    _ = (48 * (1 + 400 * Real.log x0) *
          Real.sqrt (2 * (q : ℝ) * (3 + |u|)) + Real.sqrt X) *
        ((1 + 400 * Real.log x0) * Real.exp 4 *
          Real.exp (1 / 400 : ℝ)) := by ring

/-- Elementary height collapse used on both edges of the height-`2T`
rectangle. -/
theorem sqrt_edge_height_le
    {q : ℕ} (hq : 1 ≤ q) {T u : ℝ}
    (hT : 1 ≤ T) (hu : |u| ≤ 3 * T) :
    Real.sqrt (2 * (q : ℝ) * (3 + |u|)) ≤
      4 * Real.sqrt (q : ℝ) * Real.sqrt T := by
  have hq0 : 0 ≤ (q : ℝ) := by positivity
  have hT0 : 0 ≤ T := by linarith
  have hbase :
      2 * (q : ℝ) * (3 + |u|) ≤ 16 * ((q : ℝ) * T) := by
    have hthree : 3 + |u| ≤ 6 * T := by linarith
    nlinarith
  have hsqrt := Real.sqrt_le_sqrt hbase
  have hrewrite : Real.sqrt (16 * ((q : ℝ) * T)) =
      4 * Real.sqrt (q : ℝ) * Real.sqrt T := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16),
      Real.sqrt_mul hq0]
    norm_num
    ring
  rw [hrewrite] at hsqrt
  exact hsqrt

/-- The two translated horizontal heights `t` plus-or-minus `2T` have the same scalar
endpoint budget. -/
theorem ambientHorizontalEndpointNumerator_canonical_edge_le
    {q : ℕ} (hq : 1 ≤ q) {X x0 t T : ℝ}
    (hx0 : 2 ≤ x0) (hX : 0 < X) (hXx : X ≤ x0)
    (hT : 1 ≤ T) (ht : |t| ≤ T) (v : ℝ)
    (hv : v = 2 * T ∨ v = -(2 * T)) :
    ambientHorizontalEndpointNumerator q
        (canonicalRamachandraOffset x0) X (t + v) ≤
      (192 * (1 + 400 * Real.log x0) *
          Real.sqrt (q : ℝ) * Real.sqrt T + Real.sqrt X) *
        ((1 + 400 * Real.log x0) * Real.exp 4 *
          Real.exp (1 / 400 : ℝ)) := by
  have hT0 : 0 ≤ T := by linarith
  have hvabs : |v| = 2 * T := by
    rcases hv with rfl | rfl
    · rw [abs_of_nonneg (by positivity)]
    · rw [abs_neg, abs_of_nonneg (by positivity)]
  have huv : |t + v| ≤ 3 * T := by
    calc
      |t + v| ≤ |t| + |v| := abs_add_le t v
      _ = |t| + 2 * T := by rw [hvabs]
      _ ≤ 3 * T := by linarith
  have hsqrt := sqrt_edge_height_le hq hT huv
  have hraw := ambientHorizontalEndpointNumerator_canonical_le
    hq hx0 hX hXx (u := t + v)
  have hP0 : 0 ≤ 1 + 400 * Real.log x0 := by
    have : 0 ≤ Real.log x0 := Real.log_nonneg (by linarith)
    positivity
  have hE0 : 0 ≤ (1 + 400 * Real.log x0) * Real.exp 4 *
      Real.exp (1 / 400 : ℝ) := by positivity
  refine hraw.trans (mul_le_mul_of_nonneg_right ?_ hE0)
  have hscaled :
      48 * (1 + 400 * Real.log x0) *
          Real.sqrt (2 * (q : ℝ) * (3 + |t + v|)) ≤
        48 * (1 + 400 * Real.log x0) *
          (4 * Real.sqrt (q : ℝ) * Real.sqrt T) :=
    mul_le_mul_of_nonneg_left hsqrt
      (mul_nonneg (by norm_num) hP0)
  have hscaled' :
      48 * (1 + 400 * Real.log x0) *
          Real.sqrt (2 * (q : ℝ) * (3 + |t + v|)) ≤
        192 * (1 + 400 * Real.log x0) *
          Real.sqrt (q : ℝ) * Real.sqrt T := by
    convert hscaled using 1 <;> ring
  exact add_le_add hscaled' (le_refl (Real.sqrt X))

/-- Fully integrated top and bottom horizontal edges at height `2T`.  The
normalizing factor `1/(2*pi)` is retained exactly; the displayed division by
`2T` is the Perron `/w` saving. -/
theorem norm_bhpHorizontalBoundaryIntegral_canonical_le
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hchi : chi ≠ 1) {X x0 t T : ℝ}
    (hx0 : 2 ≤ x0) (hX : 0 < X) (hXx : X ≤ x0)
    (hT : 1 ≤ T) (ht : |t| ≤ T) :
    ‖bhpHorizontalBoundaryIntegral chi X t
        (canonicalRamachandraOffset x0)
        (1 / 2 + canonicalRamachandraOffset x0) (2 * T)‖ ≤
      ‖((((2 * Real.pi : ℝ) : ℂ)⁻¹) * Complex.I)‖ *
        (((192 * (1 + 400 * Real.log x0) *
            Real.sqrt (q : ℝ) * Real.sqrt T + Real.sqrt X) *
          ((1 + 400 * Real.log x0) * Real.exp 4 *
            Real.exp (1 / 400 : ℝ))) / (2 * T)) := by
  have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hx0one : 1 < x0 := by linarith
  have hlog : 0 < Real.log x0 := Real.log_pos hx0one
  have hdelta : 0 < canonicalRamachandraOffset x0 := by
    unfold canonicalRamachandraOffset
    positivity
  have hdeltaHalf : canonicalRamachandraOffset x0 ≤ (1 / 2 : ℝ) := by
    have hlog2le : Real.log 2 ≤ Real.log x0 :=
      Real.strictMonoOn_log.monotoneOn (by norm_num : (0 : ℝ) < 2)
        (by exact zero_lt_one.trans hx0one) hx0
    have hden : (2 : ℝ) ≤ 400 * Real.log x0 := by
      nlinarith [Real.log_two_gt_d9]
    have hinv := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hden
    simpa [canonicalRamachandraOffset, one_div] using hinv
  have h2T : 0 < 2 * T := by linarith
  let M : ℝ :=
    (192 * (1 + 400 * Real.log x0) *
        Real.sqrt (q : ℝ) * Real.sqrt T + Real.sqrt X) *
      ((1 + 400 * Real.log x0) * Real.exp 4 *
        Real.exp (1 / 400 : ℝ))
  have hM0 : 0 ≤ M := by
    dsimp [M]
    have hlog0 : 0 ≤ Real.log x0 := hlog.le
    positivity
  have htop :
      ambientHorizontalEndpointNumerator q
          (canonicalRamachandraOffset x0) X (t + 2 * T) ≤ M := by
    simpa only [M] using
      ambientHorizontalEndpointNumerator_canonical_edge_le
        hq hx0 hX hXx hT ht (2 * T) (Or.inl rfl)
  have hbottom :
      ambientHorizontalEndpointNumerator q
          (canonicalRamachandraOffset x0) X (t - 2 * T) ≤ M := by
    have h := ambientHorizontalEndpointNumerator_canonical_edge_le
      hq hx0 hX hXx hT ht (-(2 * T)) (Or.inr rfl)
    simpa only [M, sub_eq_add_neg] using h
  have htopDiv := div_le_div_of_nonneg_right htop h2T.le
  have hbottomDiv := div_le_div_of_nonneg_right hbottom h2T.le
  have havg :
      ((ambientHorizontalEndpointNumerator q
            (canonicalRamachandraOffset x0) X (t + 2 * T) / (2 * T) +
        ambientHorizontalEndpointNumerator q
            (canonicalRamachandraOffset x0) X (t - 2 * T) / (2 * T)) *
          (1 / 2)) ≤ M / (2 * T) := by
    nlinarith
  have hraw := norm_bhpHorizontalBoundaryIntegral_le_exact_endpoints
    chi hchi hdelta hdeltaHalf hX h2T
      (delta := canonicalRamachandraOffset x0) (X := X)
      (t := t) (H := 2 * T)
  calc
    ‖bhpHorizontalBoundaryIntegral chi X t
        (canonicalRamachandraOffset x0)
        (1 / 2 + canonicalRamachandraOffset x0) (2 * T)‖ ≤
      ‖((((2 * Real.pi : ℝ) : ℂ)⁻¹) * Complex.I)‖ *
        ((ambientHorizontalEndpointNumerator q
              (canonicalRamachandraOffset x0) X (t + 2 * T) / (2 * T) +
          ambientHorizontalEndpointNumerator q
              (canonicalRamachandraOffset x0) X (t - 2 * T) / (2 * T)) *
            (1 / 2)) := hraw
    _ ≤ ‖((((2 * Real.pi : ℝ) : ℂ)⁻¹) * Complex.I)‖ *
          (M / (2 * T)) :=
      mul_le_mul_of_nonneg_left havg (norm_nonneg _)
    _ = _ := by rfl

/-- Source-faithful canonical rectangle: the left offset is the
Ramachandra-safe `1/(400 log x0)`, while the independent right edge remains
Titchmarsh's literal `1/2 + 1/log x0`.  This theorem is the exact scalar
specialization to use in the pointwise weld; the equal-offset rectangle above
is useful locally but must not be substituted for Theorem 3.19's right edge. -/
theorem norm_bhpHorizontalBoundaryIntegral_titchmarshCanonical_le
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hchi : chi ≠ 1) {X x0 t T : ℝ}
    (hx0 : 8 ≤ x0) (hX : 0 < X) (hT : 1 ≤ T) :
    ‖bhpHorizontalBoundaryIntegral chi X t
        (canonicalRamachandraOffset x0)
        (1 / 2 + (Real.log x0)⁻¹) (2 * T)‖ ≤
      ‖((((2 * Real.pi : ℝ) : ℂ)⁻¹) * Complex.I)‖ *
        (((ambientHorizontalGeneralEndpointNumerator q
              (canonicalRamachandraOffset x0) (Real.log x0)⁻¹
              (canonicalRamachandraOffset x0) X (t + 2 * T) / (2 * T)) +
          (ambientHorizontalGeneralEndpointNumerator q
              (canonicalRamachandraOffset x0) (Real.log x0)⁻¹
              (canonicalRamachandraOffset x0) X (t - 2 * T) / (2 * T))) *
            (1 / 2 + (Real.log x0)⁻¹ -
              canonicalRamachandraOffset x0)) := by
  have hx0one : 1 < x0 := by linarith
  have hlog : 0 < Real.log x0 := Real.log_pos hx0one
  have hlog2le : Real.log 2 ≤ Real.log x0 :=
    Real.strictMonoOn_log.monotoneOn (by norm_num : (0 : ℝ) < 2)
      (by linarith : 0 < x0) (by linarith)
  have hlogTwo : (2 : ℝ) ≤ Real.log x0 := by
    have hlog8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      norm_num
    have hlog8le : Real.log 8 ≤ Real.log x0 :=
      Real.strictMonoOn_log.monotoneOn (by norm_num : (0 : ℝ) < 8)
        (by linarith : 0 < x0) hx0
    rw [hlog8] at hlog8le
    nlinarith [Real.log_two_gt_d9]
  have hdelta : 0 < canonicalRamachandraOffset x0 := by
    unfold canonicalRamachandraOffset
    positivity
  have hdeltaHalf : canonicalRamachandraOffset x0 ≤ (1 / 2 : ℝ) := by
    unfold canonicalRamachandraOffset
    have hden : (2 : ℝ) ≤ 400 * Real.log x0 := by nlinarith
    have hinv := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hden
    simpa [one_div] using hinv
  have hr : 0 < (Real.log x0)⁻¹ := inv_pos.mpr hlog
  have hrHalf : (Real.log x0)⁻¹ ≤ (1 / 2 : ℝ) := by
    have hinv := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hlogTwo
    simpa [one_div] using hinv
  have hdeltaRight : canonicalRamachandraOffset x0 ≤
      1 / 2 + (Real.log x0)⁻¹ := by
    exact hdeltaHalf.trans (le_add_of_nonneg_right hr.le)
  exact norm_bhpHorizontalBoundaryIntegral_le_general_endpoints
    chi hchi hdelta hdeltaHalf hr hrHalf hdelta hdeltaRight hX
      (by linarith : 0 < 2 * T)

/-! ## Polylogarithmic collapse on the source-faithful rectangle -/

set_option maxHeartbeats 1200000 in
/-- The exact general endpoint numerator has the required square-root scale.
The apparently larger left exponent is only `1/2 + O(1/log x0)`; the extra
power is bounded by `exp 4` using `q,T ≤ x0`. -/
theorem ambientHorizontalGeneralEndpointNumerator_canonical_le
    {q : ℕ} (hq : 1 ≤ q) {X x0 T u : ℝ}
    (hx0 : 8 ≤ x0) (hX : 0 < X) (hXx : X ≤ x0)
    (hqx : (q : ℝ) ≤ x0) (hT : 1 ≤ T) (hTx : T ≤ x0)
    (hu : |u| ≤ 3 * T) :
    ambientHorizontalGeneralEndpointNumerator q
        (canonicalRamachandraOffset x0) (Real.log x0)⁻¹
        (canonicalRamachandraOffset x0) X u ≤
      20000 * (1 + Real.log x0) ^ 2 * Real.exp 9 *
        (Real.sqrt (2 * (q : ℝ) * (3 + |u|)) + Real.sqrt X) := by
  let L : ℝ := Real.log x0
  let d : ℝ := canonicalRamachandraOffset x0
  let r : ℝ := L⁻¹
  let P : ℝ := 1 + 400 * L
  let Q : ℝ := 2 * (q : ℝ) * (3 + |u|)
  let A : ℝ := 48 * P * Real.rpow Q (d + 1)
  let B : ℝ := rightEdgePSeries r * Real.exp ((1 + r) ^ 2)
  let theta : ℝ := ((1 / 2 + r) - d) / (1 + r)
  let phi : ℝ := (d + 1 / 2) / (1 + r)
  have hx0one : 1 < x0 := by linarith
  have hx0pos : 0 < x0 := zero_lt_one.trans hx0one
  have hL : 0 < L := by dsimp [L]; exact Real.log_pos hx0one
  have hlog8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  have hlog8le : Real.log 8 ≤ L := by
    dsimp [L]
    exact Real.strictMonoOn_log.monotoneOn (by norm_num) hx0pos hx0
  have hLtwo : 2 ≤ L := by
    rw [hlog8] at hlog8le
    nlinarith [Real.log_two_gt_d9]
  have hr : 0 < r := by dsimp [r]; positivity
  have hr0 : 0 ≤ r := hr.le
  have hrOne : r ≤ 1 := by
    have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hLtwo
    have : r ≤ (1 / 2 : ℝ) := by simpa [r, one_div] using hi
    linarith
  have hd : 0 < d := by dsimp [d, canonicalRamachandraOffset]; positivity
  have hd0 : 0 ≤ d := hd.le
  have hdr : d ≤ r := by
    dsimp [d, r, L, canonicalRamachandraOffset]
    have hden : Real.log x0 ≤ 400 * Real.log x0 := by
      have := Real.log_pos hx0one
      nlinarith
    have hi := one_div_le_one_div_of_le (Real.log_pos hx0one) hden
    simpa [one_div] using hi
  have hP : 1 ≤ P := by dsimp [P]; nlinarith
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have hqR : 1 ≤ (q : ℝ) := by exact_mod_cast hq
  have hQ : 1 ≤ Q := by
    dsimp [Q]
    nlinarith [abs_nonneg u]
  have hQ0 : 0 ≤ Q := zero_le_one.trans hQ
  have hA : 1 ≤ A := by
    have hp48 : 1 ≤ 48 * P := by nlinarith
    have hQr : 1 ≤ Real.rpow Q (d + 1) := by
      exact Real.one_le_rpow hQ (by linarith)
    dsimp [A]
    simpa only [one_mul] using!
      (mul_le_mul hp48 hQr (by norm_num : (0 : ℝ) ≤ 1)
        (by positivity : 0 ≤ 48 * P))
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hB : 1 ≤ B := by
    dsimp [B]
    have hp := one_le_rightEdgePSeries hr
    have he : 1 ≤ Real.exp ((1 + r) ^ 2) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (sq_nonneg _)
    nlinarith [mul_le_mul hp he (by positivity) (by positivity)]
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have htheta0 : 0 ≤ theta := by
    dsimp [theta]
    exact div_nonneg (by nlinarith) (by nlinarith)
  have htheta1 : theta ≤ 1 := by
    dsimp [theta]
    rw [div_le_one (by nlinarith : 0 < 1 + r)]
    linarith
  have hphi0 : 0 ≤ phi := by
    dsimp [phi]
    exact div_nonneg (by linarith) (by linarith)
  have hphi1 : phi ≤ 1 := by
    dsimp [phi]
    rw [div_le_one (by nlinarith : 0 < 1 + r)]
    linarith
  have hExpTheta : (d + 1) * theta ≤ 1 / 2 + r := by
    dsimp [theta]
    field_simp [ne_of_gt (by nlinarith : 0 < 1 + r)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hdr) (by linarith : 0 ≤ 1 / 2 + d)]
  have hQx4 : Q ≤ x0 ^ 4 := by
    have hheight : 3 + |u| ≤ 6 * T := by linarith
    have hqT : (q : ℝ) * T ≤ x0 ^ 2 := by
      have hm := mul_le_mul hqx hTx (by linarith : 0 ≤ T)
        (by linarith : 0 ≤ x0)
      nlinarith
    dsimp [Q]
    have hx02 : 12 ≤ x0 ^ 2 := by nlinarith [sq_nonneg (x0 - 8)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hx02) (sq_nonneg x0)]
  have hQr : Real.rpow Q r ≤ Real.exp 4 := by
    have hmono := Real.rpow_le_rpow hQ0 hQx4 hr0
    have hxpow : Real.rpow (x0 ^ 4) r = Real.exp 4 := by
      change (x0 ^ 4) ^ r = Real.exp 4
      rw [Real.rpow_def_of_pos (pow_pos hx0pos 4) r]
      congr 1
      dsimp [r, L]
      rw [Real.log_pow]
      field_simp [(Real.log_pos hx0one).ne']
      norm_num
    exact hmono.trans_eq hxpow
  have hQexp : Real.rpow Q ((d + 1) * theta) ≤
      Real.sqrt Q * Real.exp 4 := by
    have hmono := Real.rpow_le_rpow_of_exponent_le hQ hExpTheta
    have hsplit : Real.rpow Q (1 / 2 + r) =
        Real.sqrt Q * Real.rpow Q r := by
      change Q ^ (1 / 2 + r) = Real.sqrt Q * Q ^ r
      rw [Real.rpow_add (by linarith : 0 < Q) (1 / 2) r,
        ← Real.sqrt_eq_rpow]
    calc
      Real.rpow Q ((d + 1) * theta) ≤ Real.rpow Q (1 / 2 + r) := hmono
      _ = Real.sqrt Q * Real.rpow Q r := hsplit
      _ ≤ Real.sqrt Q * Real.exp 4 :=
        mul_le_mul_of_nonneg_left hQr (Real.sqrt_nonneg _)
  have hAtheta : Real.rpow A theta ≤
      48 * P * (Real.sqrt Q * Real.exp 4) := by
    have hbaseOne : 1 ≤ 48 * P := by nlinarith
    have hbase0 : 0 ≤ 48 * P := zero_le_one.trans hbaseOne
    have hbaseTheta : Real.rpow (48 * P) theta ≤ 48 * P := by
      simpa [Real.rpow_one] using
        (Real.rpow_le_rpow_of_exponent_le hbaseOne htheta1)
    have hrewrite : Real.rpow A theta =
        Real.rpow (48 * P) theta * Real.rpow Q ((d + 1) * theta) := by
      dsimp [A]
      rw [Real.mul_rpow hbase0 (Real.rpow_nonneg hQ0 _)]
      rw [← Real.rpow_mul hQ0]
    rw [hrewrite]
    exact mul_le_mul hbaseTheta hQexp
      (Real.rpow_nonneg hQ0 _) hbase0
  have hBinv : rightEdgePSeries r ≤ 1 + L := by
    have hp := MAPRightEdgePSeriesExplicitBound.rightEdgePSeries_le_one_add_inv hr
    have hir : r⁻¹ = L := by dsimp [r]; rw [inv_inv]
    simpa [one_div, hir] using hp
  have hBupper : B ≤ (1 + L) * Real.exp 4 := by
    dsimp [B]
    have he : Real.exp ((1 + r) ^ 2) ≤ Real.exp 4 := by
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg r]
    exact mul_le_mul hBinv he (Real.exp_pos _).le (by linarith)
  have hBphi : Real.rpow B phi ≤ (1 + L) * Real.exp 4 := by
    have hpow : Real.rpow B phi ≤ B := by
      simpa [Real.rpow_one] using
        (Real.rpow_le_rpow_of_exponent_le hB hphi1)
    exact hpow.trans hBupper
  have hXd := rpow_canonicalRamachandraOffset_le hX hXx hx0one
  have hXr : Real.rpow X r ≤ Real.exp 1 := by
    have hmono := Real.rpow_le_rpow hX.le hXx hr0
    have hxpow : Real.rpow x0 r = Real.exp 1 := by
      change x0 ^ r = Real.exp 1
      rw [Real.rpow_def_of_pos hx0pos r]
      congr 1
      dsimp [r, L]
      field_simp [(Real.log_pos hx0one).ne']
    exact hmono.trans_eq hxpow
  have hXright : Real.rpow X (1 / 2 + r) ≤
      Real.sqrt X * Real.exp 1 := by
    change X ^ (1 / 2 + r) ≤ Real.sqrt X * Real.exp 1
    rw [Real.rpow_add hX (1 / 2) r, ← Real.sqrt_eq_rpow]
    exact mul_le_mul_of_nonneg_left hXr (Real.sqrt_nonneg _)
  have hPcollapse : 48 * P * (1 + L) ≤
      19200 * (1 + L) ^ 2 := by
    dsimp [P]
    have hL0 : 0 ≤ L := hL.le
    nlinarith [sq_nonneg (1 + L)]
  have hleft : Real.rpow A theta * Real.rpow B phi * Real.rpow X d ≤
      19200 * (1 + L) ^ 2 * Real.exp 9 * Real.sqrt Q := by
    have hXd' : Real.rpow X d ≤ Real.exp (1 / 400 : ℝ) := by
      simpa only [d] using! hXd
    have hmulAB : Real.rpow A theta * Real.rpow B phi ≤
        (48 * P * (Real.sqrt Q * Real.exp 4)) *
          ((1 + L) * Real.exp 4) := by
      exact mul_le_mul hAtheta hBphi
        (Real.rpow_nonneg hB0 _) (by positivity)
    have hmulABC :
        Real.rpow A theta * Real.rpow B phi * Real.rpow X d ≤
          (48 * P * (Real.sqrt Q * Real.exp 4)) *
            ((1 + L) * Real.exp 4) * Real.exp (1 / 400 : ℝ) := by
      exact mul_le_mul hmulAB hXd'
        (Real.rpow_nonneg hX.le _) (by positivity)
    have hexp : Real.exp (8 + (1 / 400 : ℝ)) ≤ Real.exp 9 :=
      Real.exp_le_exp.mpr (by norm_num)
    have hcoeff0 : 0 ≤ 48 * P * (1 + L) := by positivity
    have hscale0 : 0 ≤ 19200 * (1 + L) ^ 2 := by positivity
    calc
      Real.rpow A theta * Real.rpow B phi * Real.rpow X d ≤
        (48 * P * (Real.sqrt Q * Real.exp 4)) *
          ((1 + L) * Real.exp 4) * Real.exp (1 / 400 : ℝ) := hmulABC
      _ = (48 * P * (1 + L)) * Real.sqrt Q *
          Real.exp (8 + (1 / 400 : ℝ)) := by
        have he8 : Real.exp 4 * Real.exp 4 = Real.exp 8 := by
          rw [← Real.exp_add]
          norm_num
        have he8400 : Real.exp 8 * Real.exp (1 / 400 : ℝ) =
            Real.exp (8 + (1 / 400 : ℝ)) := by rw [Real.exp_add]
        rw [show 48 * P * (Real.sqrt Q * Real.exp 4) *
              ((1 + L) * Real.exp 4) * Real.exp (1 / 400 : ℝ) =
            (48 * P * (1 + L)) * Real.sqrt Q *
              ((Real.exp 4 * Real.exp 4) * Real.exp (1 / 400 : ℝ)) by ring,
          he8, he8400]
      _ ≤ (19200 * (1 + L) ^ 2) * Real.sqrt Q * Real.exp 9 := by
        have hc := mul_le_mul hPcollapse hexp (Real.exp_pos _).le hscale0
        have hsqrt := Real.sqrt_nonneg Q
        nlinarith [mul_nonneg hcoeff0 hsqrt,
          mul_nonneg hscale0 hsqrt]
      _ = 19200 * (1 + L) ^ 2 * Real.exp 9 * Real.sqrt Q := by ring
  have hright : Real.rpow B 1 * Real.rpow X (1 / 2 + r) ≤
      (1 + L) * Real.exp 5 * Real.sqrt X := by
    have hBone : Real.rpow B 1 = B := by
      change B ^ (1 : ℝ) = B
      rw [Real.rpow_one]
    rw [hBone]
    calc
      B * Real.rpow X (1 / 2 + r) ≤
        ((1 + L) * Real.exp 4) * (Real.sqrt X * Real.exp 1) := by
          exact mul_le_mul hBupper hXright
            (Real.rpow_nonneg hX.le _)
            (mul_nonneg (by linarith) (Real.exp_pos _).le)
      _ = (1 + L) * Real.exp 5 * Real.sqrt X := by
        have he5 : Real.exp 4 * Real.exp 1 = Real.exp 5 := by
          rw [← Real.exp_add]
          norm_num
        rw [show (1 + L) * Real.exp 4 * (Real.sqrt X * Real.exp 1) =
          (1 + L) * (Real.exp 4 * Real.exp 1) * Real.sqrt X by ring,
          he5]
  have hright' : Real.rpow B 1 * Real.rpow X (1 / 2 + r) ≤
      800 * (1 + L) ^ 2 * Real.exp 9 * Real.sqrt X := by
    have hLsq : 1 + L ≤ (1 + L) ^ 2 := by
      nlinarith [sq_nonneg L]
    have he : Real.exp 5 ≤ Real.exp 9 := Real.exp_le_exp.mpr (by norm_num)
    have hprod : (1 + L) * Real.exp 5 ≤
        (1 + L) ^ 2 * Real.exp 9 :=
      mul_le_mul hLsq he (Real.exp_pos _).le (by linarith)
    have hsqrt0 : 0 ≤ Real.sqrt X := Real.sqrt_nonneg _
    calc
      Real.rpow B 1 * Real.rpow X (1 / 2 + r) ≤
          (1 + L) * Real.exp 5 * Real.sqrt X := hright
      _ ≤ ((1 + L) ^ 2 * Real.exp 9) * Real.sqrt X :=
        mul_le_mul_of_nonneg_right hprod hsqrt0
      _ ≤ 800 * ((1 + L) ^ 2 * Real.exp 9) * Real.sqrt X := by
        have hbase0 : 0 ≤ (1 + L) ^ 2 * Real.exp 9 := by positivity
        nlinarith [mul_nonneg hbase0 hsqrt0]
      _ = 800 * (1 + L) ^ 2 * Real.exp 9 * Real.sqrt X := by ring
  have hdInv : d⁻¹ = 400 * L := by
    dsimp [d, L]
    exact canonicalRamachandraOffset_inv x0
  have hleftActual :
      Real.rpow (48 * (1 + d⁻¹) * Real.rpow Q (d + 1)) theta *
          Real.rpow B phi * Real.rpow X d ≤
        19200 * (1 + L) ^ 2 * Real.exp 9 * Real.sqrt Q := by
    simpa only [A, P, hdInv] using hleft
  unfold ambientHorizontalGeneralEndpointNumerator
  change
    Real.rpow (48 * (1 + d⁻¹) * Real.rpow Q (d + 1)) theta *
          Real.rpow B phi * Real.rpow X d +
        Real.rpow B 1 * Real.rpow X (1 / 2 + r) ≤
      20000 * (1 + L) ^ 2 * Real.exp 9 *
        (Real.sqrt Q + Real.sqrt X)
  calc
    Real.rpow (48 * (1 + d⁻¹) * Real.rpow Q (d + 1)) theta *
          Real.rpow B phi * Real.rpow X d +
        Real.rpow B 1 * Real.rpow X (1 / 2 + r) ≤
      19200 * (1 + L) ^ 2 * Real.exp 9 * Real.sqrt Q +
        800 * (1 + L) ^ 2 * Real.exp 9 * Real.sqrt X :=
      add_le_add hleftActual hright'
    _ ≤ 20000 * (1 + L) ^ 2 * Real.exp 9 *
        (Real.sqrt Q + Real.sqrt X) := by
      have hL0 : 0 ≤ L := hL.le
      have hE0 : 0 ≤ Real.exp 9 := (Real.exp_pos _).le
      have hsqQ : 0 ≤ Real.sqrt Q := Real.sqrt_nonneg _
      have hsqX : 0 ≤ Real.sqrt X := Real.sqrt_nonneg _
      nlinarith [mul_nonneg (sq_nonneg (1 + L)) hE0]

/-- Final polylogarithmic horizontal error on the literal Titchmarsh
rectangle.  This is the exact square-root saving consumed after fourth
powers are summed. -/
theorem norm_bhpHorizontalBoundaryIntegral_titchmarshCanonical_polylog_le
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hchi : chi ≠ 1) {X x0 t T : ℝ}
    (hx0 : 8 ≤ x0) (hX : 0 < X) (hXx : X ≤ x0)
    (hqx : (q : ℝ) ≤ x0) (hT : 1 ≤ T) (hTx : T ≤ x0)
    (ht : |t| ≤ T) :
    ‖bhpHorizontalBoundaryIntegral chi X t
        (canonicalRamachandraOffset x0)
        (1 / 2 + (Real.log x0)⁻¹) (2 * T)‖ ≤
      ‖((((2 * Real.pi : ℝ) : ℂ)⁻¹) * Complex.I)‖ *
        (20000 * (1 + Real.log x0) ^ 2 * Real.exp 9 *
          (4 * Real.sqrt (q : ℝ) / Real.sqrt T + Real.sqrt X / T)) := by
  have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
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
  let M : ℝ := S * (4 * Real.sqrt (q : ℝ) * Real.sqrt T + Real.sqrt X)
  have hS0 : 0 ≤ S := by dsimp [S]; positivity
  have hM0 : 0 ≤ M := by dsimp [M]; positivity
  have htopRaw := ambientHorizontalGeneralEndpointNumerator_canonical_le
    hq hx0 hX hXx hqx hT hTx htopHeight
      (u := t + 2 * T)
  have hbottomRaw := ambientHorizontalGeneralEndpointNumerator_canonical_le
    hq hx0 hX hXx hqx hT hTx hbottomHeight
      (u := t - 2 * T)
  have htopSqrt := sqrt_edge_height_le hq hT htopHeight
  have hbottomSqrt := sqrt_edge_height_le hq hT hbottomHeight
  have htop :
      ambientHorizontalGeneralEndpointNumerator q
          (canonicalRamachandraOffset x0) (Real.log x0)⁻¹
          (canonicalRamachandraOffset x0) X (t + 2 * T) ≤ M := by
    refine htopRaw.trans ?_
    exact mul_le_mul_of_nonneg_left
      (add_le_add htopSqrt (le_refl (Real.sqrt X))) hS0
  have hbottom :
      ambientHorizontalGeneralEndpointNumerator q
          (canonicalRamachandraOffset x0) (Real.log x0)⁻¹
          (canonicalRamachandraOffset x0) X (t - 2 * T) ≤ M := by
    refine hbottomRaw.trans ?_
    exact mul_le_mul_of_nonneg_left
      (add_le_add hbottomSqrt (le_refl (Real.sqrt X))) hS0
  have hraw := norm_bhpHorizontalBoundaryIntegral_titchmarshCanonical_le
    chi hchi hx0 hX hT (X := X) (x0 := x0) (t := t) (T := T)
  let Ntop := ambientHorizontalGeneralEndpointNumerator q
    (canonicalRamachandraOffset x0) (Real.log x0)⁻¹
    (canonicalRamachandraOffset x0) X (t + 2 * T)
  let Nbottom := ambientHorizontalGeneralEndpointNumerator q
    (canonicalRamachandraOffset x0) (Real.log x0)⁻¹
    (canonicalRamachandraOffset x0) X (t - 2 * T)
  let width : ℝ := 1 / 2 + (Real.log x0)⁻¹ -
    canonicalRamachandraOffset x0
  have hx0one : 1 < x0 := by linarith
  have hlog : 0 < Real.log x0 := Real.log_pos hx0one
  have hlog8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  have hlog8le : Real.log 8 ≤ Real.log x0 :=
    Real.strictMonoOn_log.monotoneOn (by norm_num : (0 : ℝ) < 8)
      (by exact zero_lt_one.trans hx0one) hx0
  have hlogTwo : 2 ≤ Real.log x0 := by
    rw [hlog8] at hlog8le
    nlinarith [Real.log_two_gt_d9]
  have hrHalf : (Real.log x0)⁻¹ ≤ (1 / 2 : ℝ) := by
    have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hlogTwo
    simpa [one_div] using hi
  have hwidth0 : 0 ≤ width := by
    dsimp [width]
    have hdHalf : canonicalRamachandraOffset x0 ≤ (1 / 2 : ℝ) := by
      unfold canonicalRamachandraOffset
      have hden : (2 : ℝ) ≤ 400 * Real.log x0 := by nlinarith
      have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hden
      simpa [one_div] using hi
    linarith [inv_nonneg.mpr hlog.le]
  have hwidthOne : width ≤ 1 := by
    dsimp [width]
    have hd0 : 0 ≤ canonicalRamachandraOffset x0 := by
      unfold canonicalRamachandraOffset
      positivity
    linarith
  have hNtop0 : 0 ≤ Ntop := by
    dsimp [Ntop]
    exact ambientHorizontalGeneralEndpointNumerator_nonneg q
      (by unfold canonicalRamachandraOffset; positivity)
      (inv_pos.mpr hlog) hX
  have hNbottom0 : 0 ≤ Nbottom := by
    dsimp [Nbottom]
    exact ambientHorizontalGeneralEndpointNumerator_nonneg q
      (by unfold canonicalRamachandraOffset; positivity)
      (inv_pos.mpr hlog) hX
  have htopDiv : Ntop / (2 * T) ≤ M / (2 * T) := by
    exact div_le_div_of_nonneg_right (by simpa [Ntop] using htop) h2T0.le
  have hbottomDiv : Nbottom / (2 * T) ≤ M / (2 * T) := by
    exact div_le_div_of_nonneg_right (by simpa [Nbottom] using hbottom) h2T0.le
  have hsum0 : 0 ≤ Ntop / (2 * T) + Nbottom / (2 * T) := by positivity
  have hsum : Ntop / (2 * T) + Nbottom / (2 * T) ≤ M / T := by
    have hsum2 := add_le_add htopDiv hbottomDiv
    have heq : M / (2 * T) + M / (2 * T) = M / T := by
      field_simp [hT0.ne']
      ring
    exact hsum2.trans_eq heq
  have hweighted :
      (Ntop / (2 * T) + Nbottom / (2 * T)) * width ≤ M / T := by
    calc
      (Ntop / (2 * T) + Nbottom / (2 * T)) * width ≤
          (Ntop / (2 * T) + Nbottom / (2 * T)) * 1 :=
        mul_le_mul_of_nonneg_left hwidthOne hsum0
      _ ≤ M / T := by simpa using hsum
  have hsqrtT : 0 < Real.sqrt T := Real.sqrt_pos.2 hT0
  have hsqrtSq : Real.sqrt T * Real.sqrt T = T := by
    simpa [pow_two] using Real.sq_sqrt hT0.le
  have hsqrtDiv : Real.sqrt T / T = 1 / Real.sqrt T := by
    field_simp [hT0.ne', hsqrtT.ne']
    simpa [pow_two] using hsqrtSq
  have hMdiv : M / T =
      S * (4 * Real.sqrt (q : ℝ) / Real.sqrt T + Real.sqrt X / T) := by
    dsimp [M]
    calc
      S * (4 * Real.sqrt (q : ℝ) * Real.sqrt T + Real.sqrt X) / T =
          S * (4 * Real.sqrt (q : ℝ) * (Real.sqrt T / T) +
            Real.sqrt X / T) := by ring
      _ = S * (4 * Real.sqrt (q : ℝ) / Real.sqrt T +
            Real.sqrt X / T) := by rw [hsqrtDiv]; ring
  calc
    ‖bhpHorizontalBoundaryIntegral chi X t
        (canonicalRamachandraOffset x0)
        (1 / 2 + (Real.log x0)⁻¹) (2 * T)‖ ≤
      ‖((((2 * Real.pi : ℝ) : ℂ)⁻¹) * Complex.I)‖ *
        ((Ntop / (2 * T) + Nbottom / (2 * T)) * width) := by
      simpa [Ntop, Nbottom, width] using hraw
    _ ≤ ‖((((2 * Real.pi : ℝ) : ℂ)⁻¹) * Complex.I)‖ * (M / T) :=
      mul_le_mul_of_nonneg_left hweighted (norm_nonneg _)
    _ = ‖((((2 * Real.pi : ℝ) : ℂ)⁻¹) * Complex.I)‖ *
        (20000 * (1 + Real.log x0) ^ 2 * Real.exp 9 *
          (4 * Real.sqrt (q : ℝ) / Real.sqrt T + Real.sqrt X / T)) := by
      rw [hMdiv]

end
end MAPBHPCanonicalHorizontalScalar

#print axioms MAPBHPCanonicalHorizontalScalar.ambientHorizontalEndpointNumerator_le_squareRootScales
#print axioms MAPBHPCanonicalHorizontalScalar.ambientHorizontalEndpointNumerator_canonical_le
#print axioms MAPBHPCanonicalHorizontalScalar.sqrt_edge_height_le
#print axioms MAPBHPCanonicalHorizontalScalar.ambientHorizontalEndpointNumerator_canonical_edge_le
#print axioms MAPBHPCanonicalHorizontalScalar.norm_bhpHorizontalBoundaryIntegral_canonical_le
#print axioms MAPBHPCanonicalHorizontalScalar.norm_bhpHorizontalBoundaryIntegral_titchmarshCanonical_le
#print axioms MAPBHPCanonicalHorizontalScalar.ambientHorizontalGeneralEndpointNumerator_canonical_le
#print axioms MAPBHPCanonicalHorizontalScalar.norm_bhpHorizontalBoundaryIntegral_titchmarshCanonical_polylog_le
