import AppendixA4RecenteredGammaRepair

/-!
# Paper-scale absorption of the recentered detector envelope

The lemmas here retain the literal paper choices
`Y = T^(1/2)`, `N = ceil (Y (log T)^2)`, and `B = (log T)^2`.
They charge conductor, mollifier, zero-height, and fixed numerical factors
before concluding a negative power of `T`.
-/

namespace PostA5RecenteredDetectorAbsorption

open Filter CGLProofDAG
open MAPAppendixA4DetectorDichotomy
open MAPAppendixA4RecenteredGammaRepair

noncomputable section

/-- A Gaussian in `log T` beats an arbitrary fixed power, in the exact
normalization used by the arithmetic tail. -/
theorem rpow_mul_exp_neg_log_sq_le_rpow_neg
    {T a d : ℝ} (hT : 0 < T) (hlog : 0 ≤ Real.log T)
    (hgap : a + d ≤ Real.log T) :
    Real.rpow T a * Real.exp (-(Real.log T) ^ 2) ≤
      Real.rpow T (-d) := by
  change T ^ a * Real.exp (-(Real.log T) ^ 2) ≤ T ^ (-d)
  rw [Real.rpow_def_of_pos hT a, Real.rpow_def_of_pos hT (-d),
    ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hmul : (a + d) * Real.log T ≤ (Real.log T) ^ 2 := by
    calc
      (a + d) * Real.log T ≤ Real.log T * Real.log T :=
        mul_le_mul_of_nonneg_right hgap hlog
      _ = (Real.log T) ^ 2 := by ring
  nlinarith

/-- The corresponding ledger for the vertical tail, whose Gaussian has
coefficient `1/2`. -/
theorem rpow_mul_exp_neg_half_log_sq_le_rpow_neg
    {T a d : ℝ} (hT : 0 < T) (hlog : 0 ≤ Real.log T)
    (hgap : 2 * (a + d) ≤ Real.log T) :
    Real.rpow T a * Real.exp (-(Real.log T) ^ 2 / 2) ≤
      Real.rpow T (-d) := by
  change T ^ a * Real.exp (-(Real.log T) ^ 2 / 2) ≤ T ^ (-d)
  rw [Real.rpow_def_of_pos hT a, Real.rpow_def_of_pos hT (-d),
    ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hmul : 2 * (a + d) * Real.log T ≤ (Real.log T) ^ 2 := by
    calc
      2 * (a + d) * Real.log T ≤ Real.log T * Real.log T :=
        mul_le_mul_of_nonneg_right hgap hlog
      _ = (Real.log T) ^ 2 := by ring
  nlinarith

/-- Exact inverse-geometric-factor bound at the paper scale. -/
theorem one_sub_exp_neg_inv_le_exp_mul
    {Y : ℝ} (hY : 1 ≤ Y) :
    (1 - Real.exp (-(1 / Y)))⁻¹ ≤ Real.exp 1 * Y := by
  have hYpos : 0 < Y := zero_lt_one.trans_le hY
  let x : ℝ := 1 / Y
  have hxpos : 0 < x := by dsimp [x]; positivity
  have hxle : x ≤ 1 := by
    dsimp [x]
    exact (div_le_one hYpos).2 hY
  have hexpLower : Real.exp (-1) ≤ Real.exp (-x) :=
    Real.exp_le_exp.mpr (by linarith)
  have hbasic : x * Real.exp (-x) ≤ 1 - Real.exp (-x) := by
    have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp x)
      (Real.exp_pos (-x)).le
    rw [mul_add, ← Real.exp_add] at h
    have hcancel : Real.exp (-x + x) = 1 := by simp
    rw [hcancel] at h
    nlinarith
  have hdenpos : 0 < 1 - Real.exp (-x) := by
    exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  change (1 - Real.exp (-x))⁻¹ ≤ Real.exp 1 * Y
  rw [inv_le_iff_one_le_mul₀ hdenpos]
  calc
    1 = (Real.exp 1 * Y) * (x * Real.exp (-1)) := by
      dsimp [x]
      field_simp
      rw [← Real.exp_add]
      norm_num
    _ ≤ (Real.exp 1 * Y) * (x * Real.exp (-x)) := by
      gcongr
    _ ≤ (Real.exp 1 * Y) * (1 - Real.exp (-x)) := by
      exact mul_le_mul_of_nonneg_left hbasic (by positivity)

/-- The literal arithmetic-tail summand at
`Y=T^(1/2)`, `N=ceil(Y(log T)^2)` is an arbitrary negative power after
charging the mollifier and the fixed denominator constant. -/
theorem arithmetic_detector_tail_le_rpow_neg
    {T u c d : ℝ} {U : ℕ}
    (hT : 1 ≤ T)
    (hUscale : (U + 1 : ℝ) ≤ Real.rpow T u)
    (hconst : Real.exp 1 ≤ Real.rpow T c)
    (hgap : u + c + 1 / 2 + d ≤ Real.log T) :
    (U + 1 : ℝ) *
        (Real.exp (-(1 / Real.rpow T (1 / 2)))) ^
          (detectorArithmeticCutoff (Real.rpow T (1 / 2)) T + 1) *
        (1 - Real.exp (-(1 / Real.rpow T (1 / 2))))⁻¹ ≤
      Real.rpow T (-d) := by
  let Y : ℝ := Real.rpow T (1 / 2)
  let N : ℕ := detectorArithmeticCutoff Y T
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hlog : 0 ≤ Real.log T := Real.log_nonneg hT
  have hYpos : 0 < Y := by
    dsimp [Y]
    exact Real.rpow_pos_of_pos hTpos _
  have hYone : 1 ≤ Y := by
    dsimp [Y]
    exact Real.one_le_rpow hT (by norm_num)
  have hceil : Y * (Real.log T) ^ 2 ≤ (N : ℝ) := by
    dsimp [N, detectorArithmeticCutoff]
    exact Nat.le_ceil _
  have hcut : Y * (Real.log T) ^ 2 ≤ (N + 1 : ℕ) := by
    exact hceil.trans (by exact_mod_cast Nat.le_succ N)
  have hdiv : (Real.log T) ^ 2 ≤ (N + 1 : ℕ) / Y := by
    rw [le_div_iff₀ hYpos]
    simpa [mul_comm] using hcut
  have hpow :
      (Real.exp (-(1 / Y))) ^ (N + 1) ≤
        Real.exp (-(Real.log T) ^ 2) := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    push_cast
    have hdiv' : (Real.log T) ^ 2 ≤ ((N : ℝ) + 1) / Y := by
      simpa using hdiv
    have : -((N : ℝ) + 1) / Y ≤ -(Real.log T) ^ 2 := by
      calc
        -((N : ℝ) + 1) / Y = -(((N : ℝ) + 1) / Y) := by ring
        _ ≤ -(Real.log T) ^ 2 := neg_le_neg hdiv'
    convert this using 1 <;> ring
  have hinv := one_sub_exp_neg_inv_le_exp_mul hYone
  have hinv0 : 0 ≤ (1 - Real.exp (-(1 / Y)))⁻¹ := by
    apply inv_nonneg.mpr
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr
      (by have := one_div_pos.mpr hYpos; linarith))
  have hYdef : Y = Real.rpow T (1 / 2) := rfl
  have hmain :
      (U + 1 : ℝ) * (Real.exp (-(1 / Y))) ^ (N + 1) *
          (1 - Real.exp (-(1 / Y)))⁻¹ ≤
        Real.rpow T (u + c + 1 / 2) *
          Real.exp (-(Real.log T) ^ 2) := by
    calc
      (U + 1 : ℝ) * (Real.exp (-(1 / Y))) ^ (N + 1) *
            (1 - Real.exp (-(1 / Y)))⁻¹ ≤
          (U + 1 : ℝ) * Real.exp (-(Real.log T) ^ 2) *
            (Real.exp 1 * Y) := by
        calc
          (U + 1 : ℝ) * (Real.exp (-(1 / Y))) ^ (N + 1) *
                (1 - Real.exp (-(1 / Y)))⁻¹ ≤
              (U + 1 : ℝ) * Real.exp (-(Real.log T) ^ 2) *
                (1 - Real.exp (-(1 / Y)))⁻¹ := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hpow (by positivity)) hinv0
          _ ≤ (U + 1 : ℝ) * Real.exp (-(Real.log T) ^ 2) *
                (Real.exp 1 * Y) := by
            exact mul_le_mul_of_nonneg_left hinv
              (mul_nonneg (by positivity) (Real.exp_nonneg _))
      _ ≤ Real.rpow T u * Real.exp (-(Real.log T) ^ 2) *
            (Real.rpow T c * Real.rpow T (1 / 2)) := by
        rw [hYdef]
        have hT0 : 0 ≤ T := zero_le_one.trans hT
        calc
          (U + 1 : ℝ) * Real.exp (-(Real.log T) ^ 2) *
                (Real.exp 1 * Real.rpow T (1 / 2)) ≤
              Real.rpow T u * Real.exp (-(Real.log T) ^ 2) *
                (Real.exp 1 * Real.rpow T (1 / 2)) := by
            gcongr
          _ ≤ Real.rpow T u * Real.exp (-(Real.log T) ^ 2) *
                (Real.rpow T c * Real.rpow T (1 / 2)) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hconst
                (Real.rpow_nonneg hT0 _))
              (mul_nonneg (Real.rpow_nonneg hT0 _) (Real.exp_nonneg _))
      _ = Real.rpow T (u + c + 1 / 2) *
            Real.exp (-(Real.log T) ^ 2) := by
        have huc : Real.rpow T u * Real.rpow T c =
            Real.rpow T (u + c) := by
          change T ^ u * T ^ c = T ^ (u + c)
          exact (Real.rpow_add hTpos u c).symm
        have huchalf : Real.rpow T (u + c) * Real.rpow T (1 / 2) =
            Real.rpow T (u + c + 1 / 2) := by
          change T ^ (u + c) * T ^ (1 / 2 : ℝ) =
            T ^ (u + c + (1 / 2 : ℝ))
          exact (Real.rpow_add hTpos (u + c) (1 / 2 : ℝ)).symm
        calc
          Real.rpow T u * Real.exp (-(Real.log T) ^ 2) *
                (Real.rpow T c * Real.rpow T (1 / 2)) =
              (Real.rpow T u * Real.rpow T c) *
                Real.rpow T (1 / 2) * Real.exp (-(Real.log T) ^ 2) := by ring
          _ = Real.rpow T (u + c) * Real.rpow T (1 / 2) *
                Real.exp (-(Real.log T) ^ 2) := by
              rw [huc]
          _ = Real.rpow T (u + c + 1 / 2) *
                Real.exp (-(Real.log T) ^ 2) := by
              rw [huchalf]
  change (U + 1 : ℝ) * (Real.exp (-(1 / Y))) ^ (N + 1) *
      (1 - Real.exp (-(1 / Y)))⁻¹ ≤ Real.rpow T (-d)
  exact hmain.trans
    (rpow_mul_exp_neg_log_sq_le_rpow_neg hTpos hlog hgap)

/-- The repaired vertical summand is an arbitrary negative power at the
literal top-ordinate scale `|Im rho| <= T`.  The hypotheses expose every
charged exponent: `q <= T^qexp`, `U+1 <= T^u`, and the fixed numerical
prefactor `<= T^c`. -/
theorem vertical_detector_tail_le_rpow_neg
    {T qexp u c d : ℝ} {q U : ℕ} {rho : ℂ}
    (hT : 1 ≤ T)
    (hq : (q : ℝ) ≤ Real.rpow T qexp)
    (hUscale : (U + 1 : ℝ) ≤ Real.rpow T u)
    (hheight : |rho.im| ≤ T)
    (hconst :
      (1 / (2 * Real.pi)) * (460800 * 36 * Real.exp (1 / 2)) ≤
        Real.rpow T c)
    (hgap : 2 * (c + 2 * qexp + u + 2 + d) ≤ Real.log T) :
    (1 / (2 * Real.pi)) *
        (460800 * (q : ℝ) ^ 2 * (U + 1) * (5 + |rho.im|) ^ 2 *
          Real.exp (1 / 2) *
            Real.exp (-(detectorVerticalCutoff T) / 2)) ≤
      Real.rpow T (-d) := by
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hT0 : 0 ≤ T := hTpos.le
  have hlog : 0 ≤ Real.log T := Real.log_nonneg hT
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hqpow0 : 0 ≤ Real.rpow T qexp := Real.rpow_nonneg hT0 _
  have hqSq : (q : ℝ) ^ 2 ≤ (Real.rpow T qexp) ^ 2 := by
    nlinarith [sq_nonneg ((q : ℝ) + Real.rpow T qexp)]
  have hqSq' : (q : ℝ) ^ 2 ≤ Real.rpow T (2 * qexp) := by
    calc
      (q : ℝ) ^ 2 ≤ (Real.rpow T qexp) ^ 2 := hqSq
      _ = Real.rpow T qexp * Real.rpow T qexp := by ring
      _ = Real.rpow T (qexp + qexp) := by
        change T ^ qexp * T ^ qexp = T ^ (qexp + qexp)
        exact (Real.rpow_add hTpos qexp qexp).symm
      _ = Real.rpow T (2 * qexp) := by congr 1 <;> ring
  have hheightLinear : 5 + |rho.im| ≤ 6 * T := by linarith
  have hheight0 : 0 ≤ 5 + |rho.im| := by positivity
  have hheightSq : (5 + |rho.im|) ^ 2 ≤ 36 * T ^ 2 := by
    nlinarith [sq_nonneg ((5 + |rho.im|) + 6 * T)]
  let C : ℝ := (1 / (2 * Real.pi)) *
    (460800 * 36 * Real.exp (1 / 2))
  have hraw :
      (1 / (2 * Real.pi)) *
          (460800 * (q : ℝ) ^ 2 * (U + 1) * (5 + |rho.im|) ^ 2 *
            Real.exp (1 / 2) *
              Real.exp (-(detectorVerticalCutoff T) / 2)) ≤
        C * (Real.rpow T (2 * qexp) * Real.rpow T u * T ^ 2) *
          Real.exp (-(Real.log T) ^ 2 / 2) := by
    unfold detectorVerticalCutoff
    dsimp [C]
    have hpi : 0 ≤ 1 / (2 * Real.pi) := by positivity
    calc
      (1 / (2 * Real.pi)) *
          (460800 * (q : ℝ) ^ 2 * (U + 1) * (5 + |rho.im|) ^ 2 *
            Real.exp (1 / 2) * Real.exp (-(Real.log T) ^ 2 / 2)) ≤
        (1 / (2 * Real.pi)) *
          (460800 * Real.rpow T (2 * qexp) * Real.rpow T u *
            (36 * T ^ 2) * Real.exp (1 / 2) *
              Real.exp (-(Real.log T) ^ 2 / 2)) := by
          gcongr
          · exact mul_nonneg
              (mul_nonneg (by norm_num) (Real.rpow_nonneg hT0 _))
              (Real.rpow_nonneg hT0 _)
          · exact mul_nonneg (by norm_num) (Real.rpow_nonneg hT0 _)
      _ = ((1 / (2 * Real.pi)) *
            (460800 * 36 * Real.exp (1 / 2))) *
          (Real.rpow T (2 * qexp) * Real.rpow T u * T ^ 2) *
            Real.exp (-(Real.log T) ^ 2 / 2) := by ring
  have hTtwo : T ^ 2 = Real.rpow T (2 : ℝ) := by
    exact (Real.rpow_natCast T 2).symm
  have hmerge :
      Real.rpow T c *
          (Real.rpow T (2 * qexp) * Real.rpow T u * T ^ 2) =
        Real.rpow T (c + 2 * qexp + u + 2) := by
    rw [hTtwo]
    change T ^ c * (T ^ (2 * qexp) * T ^ u * T ^ (2 : ℝ)) =
      T ^ (c + 2 * qexp + u + 2)
    rw [← Real.rpow_add hTpos, ← Real.rpow_add hTpos,
      ← Real.rpow_add hTpos]
    congr 1
    ring
  calc
    (1 / (2 * Real.pi)) *
        (460800 * (q : ℝ) ^ 2 * (U + 1) * (5 + |rho.im|) ^ 2 *
          Real.exp (1 / 2) *
            Real.exp (-(detectorVerticalCutoff T) / 2)) ≤
      C * (Real.rpow T (2 * qexp) * Real.rpow T u * T ^ 2) *
        Real.exp (-(Real.log T) ^ 2 / 2) := hraw
    _ ≤ Real.rpow T c *
          (Real.rpow T (2 * qexp) * Real.rpow T u * T ^ 2) *
            Real.exp (-(Real.log T) ^ 2 / 2) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hconst
          (mul_nonneg
            (mul_nonneg (Real.rpow_nonneg hT0 _)
              (Real.rpow_nonneg hT0 _)) (sq_nonneg T)))
        (Real.exp_nonneg _)
    _ = Real.rpow T (c + 2 * qexp + u + 2) *
          Real.exp (-(Real.log T) ^ 2 / 2) := by rw [hmerge]
    _ ≤ Real.rpow T (-d) :=
      rpow_mul_exp_neg_half_log_sq_le_rpow_neg hTpos hlog hgap

/-- Literal repaired envelope bound at `R=T`, `Y=T^(1/2)`. -/
theorem detector_envelope_le_two_mul_rpow_neg
    {T qexp u carith cvert d : ℝ} {q U : ℕ} {rho : ℂ}
    (hT : 1 ≤ T)
    (hq : (q : ℝ) ≤ Real.rpow T qexp)
    (hUscale : (U + 1 : ℝ) ≤ Real.rpow T u)
    (hheight : |rho.im| ≤ T)
    (hconstArith : Real.exp 1 ≤ Real.rpow T carith)
    (hconstVert :
      (1 / (2 * Real.pi)) * (460800 * 36 * Real.exp (1 / 2)) ≤
        Real.rpow T cvert)
    (hgapArith : u + carith + 1 / 2 + d ≤ Real.log T)
    (hgapVert : 2 * (cvert + 2 * qexp + u + 2 + d) ≤ Real.log T) :
    detectorTruncationErrorEnvelopePolynomialHeight q U rho
        (Real.rpow T (1 / 2)) T ≤
      2 * Real.rpow T (-d) := by
  have harith := arithmetic_detector_tail_le_rpow_neg
    (T := T) (u := u) (c := carith) (d := d) (U := U)
      hT hUscale hconstArith hgapArith
  have hvert := vertical_detector_tail_le_rpow_neg
    (T := T) (qexp := qexp) (u := u) (c := cvert) (d := d)
      (q := q) (U := U) (rho := rho)
      hT hq hUscale hheight hconstVert hgapVert
  unfold detectorTruncationErrorEnvelopePolynomialHeight
  exact (add_le_add harith hvert).trans_eq (by ring)

/-- Multiplicity/crowding/mesh-safe form.  Any explicit consumer cost bounded
by `T^m` is absorbed together with the factor `2` by running the two detector
tails at exponent `m+c+d`, where `2 <= T^c`. -/
theorem cost_mul_detector_envelope_le_rpow_neg
    {T qexp u carith cvert m c d cost : ℝ} {q U : ℕ} {rho : ℂ}
    (hT : 1 ≤ T)
    (hq : (q : ℝ) ≤ Real.rpow T qexp)
    (hUscale : (U + 1 : ℝ) ≤ Real.rpow T u)
    (hheight : |rho.im| ≤ T)
    (hconstArith : Real.exp 1 ≤ Real.rpow T carith)
    (hconstVert :
      (1 / (2 * Real.pi)) * (460800 * 36 * Real.exp (1 / 2)) ≤
        Real.rpow T cvert)
    (hcost0 : 0 ≤ cost) (hcost : cost ≤ Real.rpow T m)
    (htwo : 2 ≤ Real.rpow T c)
    (hgapArith : u + carith + 1 / 2 + (m + c + d) ≤ Real.log T)
    (hgapVert :
      2 * (cvert + 2 * qexp + u + 2 + (m + c + d)) ≤ Real.log T) :
    cost * detectorTruncationErrorEnvelopePolynomialHeight q U rho
        (Real.rpow T (1 / 2)) T ≤
      Real.rpow T (-d) := by
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hT0 : 0 ≤ T := hTpos.le
  have henv := detector_envelope_le_two_mul_rpow_neg
    (T := T) (qexp := qexp) (u := u) (carith := carith)
      (cvert := cvert) (d := m + c + d) (q := q) (U := U) (rho := rho)
      hT hq hUscale hheight hconstArith hconstVert hgapArith hgapVert
  have hmcpow :
      Real.rpow T m * (Real.rpow T c * Real.rpow T (-(m + c + d))) =
        Real.rpow T (-d) := by
    change T ^ m * (T ^ c * T ^ (-(m + c + d))) = T ^ (-d)
    rw [← Real.rpow_add hTpos, ← Real.rpow_add hTpos]
    congr 1
    ring
  calc
    cost * detectorTruncationErrorEnvelopePolynomialHeight q U rho
        (Real.rpow T (1 / 2)) T ≤
      cost * (2 * Real.rpow T (-(m + c + d))) :=
        mul_le_mul_of_nonneg_left henv hcost0
    _ ≤ Real.rpow T m * (2 * Real.rpow T (-(m + c + d))) := by
      exact mul_le_mul_of_nonneg_right hcost
        (mul_nonneg (by norm_num) (Real.rpow_nonneg hT0 _))
    _ ≤ Real.rpow T m *
        (Real.rpow T c * Real.rpow T (-(m + c + d))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hT0 _))
        (Real.rpow_nonneg hT0 _)
    _ = Real.rpow T (-d) := hmcpow

/-- Uniform asymptotic consumer form for a polylogarithmic conductor.  The
mollifier exponent `u` and the complete mesh/crowding/multiplicity exponent
`m` remain explicit; the repaired Gaussian absorbs both with an arbitrary
remaining power saving `d`. -/
theorem eventually_cost_mul_detector_envelope_polylog_level_le_rpow_neg
    (K u m d : ℝ) :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ (q U : ℕ) (rho : ℂ) (cost : ℝ),
        (q : ℝ) ≤ Real.rpow (Real.log T) K →
        (U + 1 : ℝ) ≤ Real.rpow T u →
        |rho.im| ≤ T →
        0 ≤ cost → cost ≤ Real.rpow T m →
        cost * detectorTruncationErrorEnvelopePolynomialHeight q U rho
            (Real.rpow T (1 / 2)) T ≤
          Real.rpow T (-d) := by
  let Cvert : ℝ :=
    (1 / (2 * Real.pi)) * (460800 * 36 * Real.exp (1 / 2))
  let L : ℝ := max (u + 1 + 1 / 2 + (m + 1 + d))
    (2 * (1 + 2 * 1 + u + 2 + (m + 1 + d)))
  have hpoly := ZeroDensityArithmetic.polylog_absorption K 1 (by norm_num)
  have hlog := Real.tendsto_log_atTop.eventually (eventually_ge_atTop L)
  filter_upwards [hpoly, hlog, eventually_ge_atTop 1,
    eventually_ge_atTop (Real.exp 1), eventually_ge_atTop Cvert,
    eventually_ge_atTop 2] with T hpolyT hlogT hTone hTexp hTvert hTtwo
  intro q U rho cost hq hU hheight hcost0 hcost
  have hqT : (q : ℝ) ≤ Real.rpow T (1 : ℝ) := hq.trans hpolyT
  have hconstArith : Real.exp 1 ≤ Real.rpow T (1 : ℝ) := by
    simpa [Real.rpow_one] using hTexp
  have hconstVert : Cvert ≤ Real.rpow T (1 : ℝ) := by
    simpa [Real.rpow_one] using hTvert
  have htwo : 2 ≤ Real.rpow T (1 : ℝ) := by
    simpa [Real.rpow_one] using hTtwo
  apply cost_mul_detector_envelope_le_rpow_neg
    (T := T) (qexp := 1) (u := u) (carith := 1) (cvert := 1)
      (m := m) (c := 1) (d := d) (cost := cost)
      (q := q) (U := U) (rho := rho)
      hTone hqT hU hheight hconstArith
      (by simpa [Cvert] using hconstVert) hcost0 hcost htwo
  · exact le_trans (le_max_left _ _) hlogT
  · exact le_trans (le_max_right _ _) hlogT

/-- Exact manuscript-height specialization `T = X^tau`. -/
theorem eventually_cost_mul_detector_envelope_at_rpow_height_le_rpow_neg
    (K u m d tau : ℝ) (htau : 0 < tau) :
    ∀ᶠ X : ℝ in Filter.atTop,
      ∀ (q U : ℕ) (rho : ℂ) (cost : ℝ),
        (q : ℝ) ≤
            Real.rpow (Real.log (Real.rpow X tau)) K →
        (U + 1 : ℝ) ≤ Real.rpow (Real.rpow X tau) u →
        |rho.im| ≤ Real.rpow X tau →
        0 ≤ cost → cost ≤ Real.rpow (Real.rpow X tau) m →
        cost * detectorTruncationErrorEnvelopePolynomialHeight q U rho
            (Real.rpow (Real.rpow X tau) (1 / 2))
            (Real.rpow X tau) ≤
          Real.rpow (Real.rpow X tau) (-d) := by
  exact (tendsto_rpow_atTop htau).eventually
    (eventually_cost_mul_detector_envelope_polylog_level_le_rpow_neg
      K u m d)

/-- Exact high-strip exponent of the normalized Type-II budget term. -/
theorem normalized_typeII_budget_term_le
    {T u delta beta : ℝ} {U : ℕ}
    (hT : 1 ≤ T) (hbeta : 7 / 10 ≤ beta)
    (hUscale : (U + 1 : ℝ) ≤ Real.rpow T u) :
    29 * Real.rpow (Real.rpow T (1 / 2)) (1 / 2 - beta) *
          (U + 1) * Real.rpow T (-delta) ≤
      29 * Real.rpow T (-(1 / 10 + delta - u)) := by
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hT0 : 0 ≤ T := hTpos.le
  have hbetaExp : (1 / 2 : ℝ) * (1 / 2 - beta) ≤ -(1 / 10) := by
    linarith
  have hYpow :
      Real.rpow (Real.rpow T (1 / 2)) (1 / 2 - beta) ≤
        Real.rpow T (-(1 / 10)) := by
    have hrewrite :
        Real.rpow (Real.rpow T (1 / 2)) (1 / 2 - beta) =
          Real.rpow T ((1 / 2) * (1 / 2 - beta)) := by
      change (T ^ (1 / 2 : ℝ)) ^ (1 / 2 - beta) =
        T ^ ((1 / 2 : ℝ) * (1 / 2 - beta))
      exact (Real.rpow_mul hT0 (1 / 2 : ℝ) (1 / 2 - beta)).symm
    rw [hrewrite]
    exact Real.rpow_le_rpow_of_exponent_le hT hbetaExp
  have hmerge :
      Real.rpow T (-(1 / 10)) * Real.rpow T u *
          Real.rpow T (-delta) =
        Real.rpow T (-(1 / 10 + delta - u)) := by
    change T ^ (-(1 / 10 : ℝ)) * T ^ u * T ^ (-delta) =
      T ^ (-(1 / 10 + delta - u))
    rw [← Real.rpow_add hTpos, ← Real.rpow_add hTpos]
    congr 1
    ring
  calc
    29 * Real.rpow (Real.rpow T (1 / 2)) (1 / 2 - beta) *
          (U + 1) * Real.rpow T (-delta) ≤
      29 * Real.rpow T (-(1 / 10)) *
          Real.rpow T u * Real.rpow T (-delta) := by
        gcongr
        · exact Real.rpow_nonneg hT0 _
        · exact mul_nonneg (by norm_num) (Real.rpow_nonneg hT0 _)
    _ = 29 * Real.rpow T (-(1 / 10 + delta - u)) := by
      calc
        29 * Real.rpow T (-(1 / 10)) *
              Real.rpow T u * Real.rpow T (-delta) =
            29 * (Real.rpow T (-(1 / 10)) *
              Real.rpow T u * Real.rpow T (-delta)) := by ring
        _ = 29 * Real.rpow T (-(1 / 10 + delta - u)) := by
          rw [hmerge]

/-- The complete repaired pointwise detector budget is eventually automatic
at the project scale.  The sole exponent condition is the source-faithful
normalization margin `u < 1/10 + delta`. -/
theorem eventually_recentered_detector_budget
    (K u delta : ℝ) (hdelta : 0 < delta)
    (hmargin : u < 1 / 10 + delta) :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ (q U : ℕ) (rho : ℂ),
        (q : ℝ) ≤ Real.rpow (Real.log T) K →
        (U + 1 : ℝ) ≤ Real.rpow T u →
        |rho.im| ≤ T → 7 / 10 ≤ rho.re →
        detectorTruncationErrorEnvelopePolynomialHeight q U rho
              (Real.rpow T (1 / 2)) T +
            Real.rpow T (-delta) +
            29 * Real.rpow (Real.rpow T (1 / 2)) (1 / 2 - rho.re) *
              (U + 1) * Real.rpow T (-delta) ≤
          Real.exp (-(1 / Real.rpow T (1 / 2))) := by
  let s : ℝ := 1 / 10 + delta - u
  have hs : 0 < s := by dsimp [s]; linarith
  have henv :=
    eventually_cost_mul_detector_envelope_polylog_level_le_rpow_neg K u 0 1
  have hVgrow := (tendsto_rpow_atTop hdelta).eventually
    (eventually_ge_atTop 16)
  have hNgrow := (tendsto_rpow_atTop hs).eventually
    (eventually_ge_atTop 464)
  have hYgrow := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).eventually
    (eventually_ge_atTop 2)
  filter_upwards [henv, hVgrow, hNgrow, hYgrow,
    eventually_ge_atTop 16] with T henvT hVgrowT hNgrowT hYgrowT hT16
  intro q U rho hq hU hheight hbeta
  have hT : 1 ≤ T := by linarith
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hT0 : 0 ≤ T := hTpos.le
  have henvRaw := henvT q U rho 1 hq hU hheight
    (by norm_num) (by simp [Real.rpow_zero])
  have henvPower :
      detectorTruncationErrorEnvelopePolynomialHeight q U rho
          (Real.rpow T (1 / 2)) T ≤ Real.rpow T (-1) := by
    simpa using henvRaw
  have hTinv : Real.rpow T (-1) ≤ 1 / 16 := by
    rw [show Real.rpow T (-1) = T⁻¹ by
      change T ^ (-1 : ℝ) = T⁻¹
      simp [Real.rpow_neg_one]]
    simpa [one_div] using
      ((inv_le_inv₀ hTpos (by norm_num : (0 : ℝ) < 16)).2 hT16)
  have henvSmall :
      detectorTruncationErrorEnvelopePolynomialHeight q U rho
          (Real.rpow T (1 / 2)) T ≤ 1 / 16 := henvPower.trans hTinv
  have hVsmall : Real.rpow T (-delta) ≤ 1 / 16 := by
    rw [show Real.rpow T (-delta) = (Real.rpow T delta)⁻¹ by
      change T ^ (-delta) = (T ^ delta)⁻¹
      exact Real.rpow_neg hT0 delta]
    simpa [one_div] using
      ((inv_le_inv₀ (Real.rpow_pos_of_pos hTpos delta)
        (by norm_num : (0 : ℝ) < 16)).2 hVgrowT)
  have hnormRaw := normalized_typeII_budget_term_le
    (T := T) (u := u) (delta := delta) (beta := rho.re) (U := U)
      hT hbeta hU
  have hnormSmall :
      29 * Real.rpow (Real.rpow T (1 / 2)) (1 / 2 - rho.re) *
          (U + 1) * Real.rpow T (-delta) ≤ 1 / 16 := by
    apply hnormRaw.trans
    change 29 * Real.rpow T (-s) ≤ 1 / 16
    rw [show Real.rpow T (-s) = (Real.rpow T s)⁻¹ by
      change T ^ (-s) = (T ^ s)⁻¹
      exact Real.rpow_neg hT0 s]
    calc
      29 * (Real.rpow T s)⁻¹ ≤ 29 * (464 : ℝ)⁻¹ := by
        exact mul_le_mul_of_nonneg_left
          ((inv_le_inv₀ (Real.rpow_pos_of_pos hTpos s)
            (by norm_num : (0 : ℝ) < 464)).2 hNgrowT) (by norm_num)
      _ = 1 / 16 := by norm_num
  have hYpos : 0 < Real.rpow T (1 / 2) := Real.rpow_pos_of_pos hTpos _
  have hinvY : 1 / Real.rpow T (1 / 2) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) hYgrowT
  have hrhs : 1 / 2 ≤ Real.exp (-(1 / Real.rpow T (1 / 2))) := by
    have hadd := Real.add_one_le_exp (-(1 / Real.rpow T (1 / 2)))
    linarith
  calc
    detectorTruncationErrorEnvelopePolynomialHeight q U rho
          (Real.rpow T (1 / 2)) T +
        Real.rpow T (-delta) +
        29 * Real.rpow (Real.rpow T (1 / 2)) (1 / 2 - rho.re) *
          (U + 1) * Real.rpow T (-delta) ≤
      1 / 16 + 1 / 16 + 1 / 16 := by
        exact add_le_add (add_le_add henvSmall hVsmall) hnormSmall
    _ ≤ 1 / 2 := by norm_num
    _ ≤ Real.exp (-(1 / Real.rpow T (1 / 2))) := hrhs

/-- Exact input-loss specialization with the floor mollifier
`U=floor(T^kappa)`.  The harmless `U+1` is charged by `T^(2*kappa)`; hence
`kappa<1/20` leaves the fixed high-strip `1/10` normalization gap. -/
theorem eventually_recentered_detector_budget_floor_inputLoss
    (K kappa eta : ℝ) (hkappa : 0 < kappa)
    (hkappaCap : kappa < 1 / 20) (heta : 0 < eta) :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ (q : ℕ) (rho : ℂ),
        (q : ℝ) ≤ Real.rpow (Real.log T) K →
        |rho.im| ≤ T → 7 / 10 ≤ rho.re →
        detectorTruncationErrorEnvelopePolynomialHeight q
              ⌊Real.rpow T kappa⌋₊ rho (Real.rpow T (1 / 2)) T +
            Real.rpow T (-inputLoss kappa eta) +
            29 * Real.rpow (Real.rpow T (1 / 2)) (1 / 2 - rho.re) *
              (⌊Real.rpow T kappa⌋₊ + 1) *
                Real.rpow T (-inputLoss kappa eta) ≤
          Real.exp (-(1 / Real.rpow T (1 / 2))) := by
  have hloss : 0 < inputLoss kappa eta := inputLoss_pos hkappa heta
  have hmargin : 2 * kappa < 1 / 10 + inputLoss kappa eta := by
    nlinarith
  have hbudget := eventually_recentered_detector_budget
    K (2 * kappa) (inputLoss kappa eta) hloss hmargin
  have hpowGrow := (tendsto_rpow_atTop hkappa).eventually
    (eventually_ge_atTop 2)
  filter_upwards [hbudget, hpowGrow, eventually_ge_atTop 1]
    with T hbudgetT hpowGrowT hTone
  intro q rho hq hheight hbeta
  apply hbudgetT q ⌊Real.rpow T kappa⌋₊ rho hq
  · have hT0 : 0 ≤ T := zero_le_one.trans hTone
    have hpow0 : 0 ≤ Real.rpow T kappa := Real.rpow_nonneg hT0 _
    have hfloor : (⌊Real.rpow T kappa⌋₊ : ℝ) ≤
        Real.rpow T kappa := Nat.floor_le hpow0
    have hpowGrowT' : 2 ≤ Real.rpow T kappa := by exact hpowGrowT
    have hquad : Real.rpow T kappa + 1 ≤
        Real.rpow T kappa * Real.rpow T kappa := by
      nlinarith [mul_nonneg
        (sub_nonneg.mpr hpowGrowT') (sub_nonneg.mpr hpowGrowT')]
    calc
      (⌊Real.rpow T kappa⌋₊ : ℝ) + 1 ≤
          Real.rpow T kappa + 1 := by linarith
      _ ≤ Real.rpow T kappa * Real.rpow T kappa := hquad
      _ = Real.rpow T (2 * kappa) := by
        change T ^ kappa * T ^ kappa = T ^ (2 * kappa)
        rw [← Real.rpow_add (zero_lt_one.trans_le hTone)]
        congr 1
        ring
  · exact hheight
  · exact hbeta

/-- The preceding literal budget at the project Perron height
`T=X^tau`. -/
theorem eventually_recentered_detector_budget_floor_inputLoss_at_rpow_height
    (K kappa eta tau : ℝ) (hkappa : 0 < kappa)
    (hkappaCap : kappa < 1 / 20) (heta : 0 < eta) (htau : 0 < tau) :
    ∀ᶠ X : ℝ in Filter.atTop,
      ∀ (q : ℕ) (rho : ℂ),
        (q : ℝ) ≤
            Real.rpow (Real.log (Real.rpow X tau)) K →
        |rho.im| ≤ Real.rpow X tau → 7 / 10 ≤ rho.re →
        detectorTruncationErrorEnvelopePolynomialHeight q
              ⌊Real.rpow (Real.rpow X tau) kappa⌋₊ rho
              (Real.rpow (Real.rpow X tau) (1 / 2))
              (Real.rpow X tau) +
            Real.rpow (Real.rpow X tau) (-inputLoss kappa eta) +
            29 * Real.rpow (Real.rpow (Real.rpow X tau) (1 / 2))
                (1 / 2 - rho.re) *
              (⌊Real.rpow (Real.rpow X tau) kappa⌋₊ + 1) *
                Real.rpow (Real.rpow X tau) (-inputLoss kappa eta) ≤
          Real.exp (-(1 /
            Real.rpow (Real.rpow X tau) (1 / 2))) := by
  exact (tendsto_rpow_atTop htau).eventually
    (eventually_recentered_detector_budget_floor_inputLoss
      K kappa eta hkappa hkappaCap heta)

end
end PostA5RecenteredDetectorAbsorption

#print axioms PostA5RecenteredDetectorAbsorption.rpow_mul_exp_neg_log_sq_le_rpow_neg
#print axioms PostA5RecenteredDetectorAbsorption.rpow_mul_exp_neg_half_log_sq_le_rpow_neg
#print axioms PostA5RecenteredDetectorAbsorption.one_sub_exp_neg_inv_le_exp_mul
#print axioms PostA5RecenteredDetectorAbsorption.arithmetic_detector_tail_le_rpow_neg
#print axioms PostA5RecenteredDetectorAbsorption.vertical_detector_tail_le_rpow_neg
#print axioms PostA5RecenteredDetectorAbsorption.detector_envelope_le_two_mul_rpow_neg
#print axioms PostA5RecenteredDetectorAbsorption.cost_mul_detector_envelope_le_rpow_neg
#print axioms PostA5RecenteredDetectorAbsorption.eventually_cost_mul_detector_envelope_polylog_level_le_rpow_neg
#print axioms PostA5RecenteredDetectorAbsorption.eventually_cost_mul_detector_envelope_at_rpow_height_le_rpow_neg
#print axioms PostA5RecenteredDetectorAbsorption.normalized_typeII_budget_term_le
#print axioms PostA5RecenteredDetectorAbsorption.eventually_recentered_detector_budget
#print axioms PostA5RecenteredDetectorAbsorption.eventually_recentered_detector_budget_floor_inputLoss
#print axioms PostA5RecenteredDetectorAbsorption.eventually_recentered_detector_budget_floor_inputLoss_at_rpow_height
