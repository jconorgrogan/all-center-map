import APFoundation
import MajorArcPrimePairWeld
import Mathlib.NumberTheory.AbelSummation

/-!
# Abel weld for the pointwise MAP major-arc estimate

MRT Proposition 4.1 cites Nathanson, Lemma 8.3.  Once the rational-point
prefix discrepancy is known, the only analytic operation in that lemma is
Abel summation against the small phase `e(beta t)`.  This file certifies that
operation with literal constants.  It deliberately does not package the
desired prime-polynomial estimate as an assumption.
-/

namespace MAPPointwiseMajorArc

open AddCircle Finset MeasureTheory Set
open MAPMajorArcWeld
open scoped ArithmeticFunction

noncomputable section

/-- A completely quantitative form of the Abel-summation step in Nathanson,
Lemma 8.3.  If every prefix of `c` between `a` and `b` has norm at most `E`,
then twisting by a differentiable phase of endpoint norm at most one and
derivative norm at most `D` costs at most
`2 E + (b-a) D E`.

The two endpoint copies of `E` are retained because this version is designed
for an arbitrary dyadic interval.  In the prefix version with `a = 0` and
vanishing initial coefficient, one of them disappears. -/
theorem norm_sum_Ioc_mul_le_of_prefix_bound
    (c : ℕ → ℂ) {f : ℝ → ℂ} {a b E D : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hE : 0 ≤ E) (hD : 0 ≤ D)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (hf_int : IntegrableOn (deriv f) (Set.Icc a b))
    (hf_a : ‖f a‖ ≤ 1) (hf_b : ‖f b‖ ≤ 1)
    (hderiv : ∀ t ∈ Set.Icc a b, ‖deriv f t‖ ≤ D)
    (hprefix : ∀ t ∈ Set.Icc a b,
      ‖∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k‖ ≤ E) :
    ‖∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f k * c k‖ ≤
      2 * E + (b - a) * D * E := by
  let C : ℝ → ℂ := fun t => ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k
  have hAbel := sum_mul_eq_sub_sub_integral_mul c ha hab hf_diff hf_int
  have hCa : ‖C a‖ ≤ E := hprefix a ⟨le_rfl, hab⟩
  have hCb : ‖C b‖ ≤ E := hprefix b ⟨hab, le_rfl⟩
  have hend : ‖f b * C b - f a * C a‖ ≤ 2 * E := by
    calc
      ‖f b * C b - f a * C a‖ ≤
          ‖f b * C b‖ + ‖f a * C a‖ := norm_sub_le _ _
      _ = ‖f b‖ * ‖C b‖ + ‖f a‖ * ‖C a‖ := by
        simp only [norm_mul]
      _ ≤ 1 * E + 1 * E := by gcongr
      _ = 2 * E := by ring
  have hInt :
      ‖∫ t in Set.Ioc a b, deriv f t * C t‖ ≤
        (D * E) * (b - a) := by
    have hbound :
        ‖∫ t in a..b, deriv f t * C t‖ ≤ (D * E) * |b - a| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t ht
      have ht' : t ∈ Set.Icc a b := by
        rw [Set.uIoc_of_le hab] at ht
        exact Set.Ioc_subset_Icc_self ht
      rw [norm_mul]
      exact mul_le_mul (hderiv t ht') (hprefix t ht')
        (norm_nonneg _) hD
    rw [← intervalIntegral.integral_of_le hab]
    simpa [abs_of_nonneg (sub_nonneg.mpr hab)] using hbound
  rw [hAbel]
  change ‖f b * C b - f a * C a -
      ∫ t in Set.Ioc a b, deriv f t * C t‖ ≤ _
  calc
    ‖f b * C b - f a * C a -
        ∫ t in Set.Ioc a b, deriv f t * C t‖ ≤
        ‖f b * C b - f a * C a‖ +
          ‖∫ t in Set.Ioc a b, deriv f t * C t‖ := norm_sub_le _ _
    _ ≤ 2 * E + (D * E) * (b - a) := add_le_add hend hInt
    _ = 2 * E + (b - a) * D * E := by ring

/-! ## The literal small Fourier phase -/

/-- The real-frequency Fourier phase, using the same positive `2 pi i`
convention as `AddCircle.fourier`. -/
def realFourierPhase (β t : ℝ) : ℂ :=
  Complex.exp ((2 * Real.pi * Complex.I * (β : ℂ)) * (t : ℂ))

theorem hasDerivAt_realFourierPhase (β t : ℝ) :
    HasDerivAt (realFourierPhase β)
      (realFourierPhase β t * (2 * Real.pi * Complex.I * (β : ℂ))) t := by
  let c : ℂ := 2 * Real.pi * Complex.I * (β : ℂ)
  have hlin : HasDerivAt (fun y : ℝ => c * (y : ℂ)) c t := by
    convert (hasDerivAt_id t).ofReal_comp.const_mul c using 1 <;> simp
  simpa only [realFourierPhase, c] using! hlin.cexp

theorem norm_realFourierPhase (β t : ℝ) :
    ‖realFourierPhase β t‖ = 1 := by
  have harg :
      (2 * Real.pi * Complex.I * (β : ℂ)) * (t : ℂ) =
        ((2 * Real.pi * β * t : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [realFourierPhase, harg, Complex.norm_exp_ofReal_mul_I]

theorem norm_deriv_realFourierPhase (β t : ℝ) :
    ‖deriv (realFourierPhase β) t‖ = 2 * Real.pi * |β| := by
  rw [(hasDerivAt_realFourierPhase β t).deriv, norm_mul,
    norm_realFourierPhase]
  simp only [one_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_I]
  rw [abs_of_pos Real.pi_pos]
  norm_num

/-- Nathanson's exact `1 + |beta| X` loss, in a dyadic form and with the
Fourier normalization exposed. -/
theorem norm_sum_Ioc_realFourierPhase_le_of_prefix_bound
    (c : ℕ → ℂ) {a b E β : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hE : 0 ≤ E)
    (hprefix : ∀ t ∈ Set.Icc a b,
      ‖∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k‖ ≤ E) :
    ‖∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊,
        realFourierPhase β k * c k‖ ≤
      2 * E + (b - a) * (2 * Real.pi * |β|) * E := by
  apply norm_sum_Ioc_mul_le_of_prefix_bound c ha hab hE
    (mul_nonneg (mul_nonneg (by positivity) Real.pi_pos.le) (abs_nonneg β))
  · intro t ht
    exact (hasDerivAt_realFourierPhase β t).differentiableAt
  · rw [show deriv (realFourierPhase β) =
        fun t => realFourierPhase β t *
          (2 * Real.pi * Complex.I * (β : ℂ)) by
      funext t
      exact (hasDerivAt_realFourierPhase β t).deriv]
    have hcont : Continuous (realFourierPhase β) :=
      continuous_iff_continuousAt.mpr fun t =>
        (hasDerivAt_realFourierPhase β t).continuousAt
    exact (hcont.mul continuous_const).integrableOn_Icc
  · rw [norm_realFourierPhase]
  · rw [norm_realFourierPhase]
  · intro t ht
    rw [norm_deriv_realFourierPhase]
  · exact hprefix

/-! ## Exact reduction of the prime polynomial to a rational-prefix estimate -/

theorem realFourierPhase_nat_eq_fourier (β : ℝ) (n : ℕ) :
    realFourierPhase β n = fourier (n : ℤ) (β : UnitAddCircle) := by
  rw [fourier_coe_apply]
  unfold realFourierPhase
  congr 1
  push_cast
  ring

/-- The centered coefficient at the rational point `a/q`.  Its zeroth term is
set to zero so its prefix is exactly
`sum_{1 ≤ n ≤ t} Lambda(n)e(an/q) - mu(q)/phi(q) floor(t)`.
This is Nathanson's Lemma 8.2 object, not Proposition 4.1. -/
def rationalCenteredCoefficient (q a n : ℕ) : ℂ :=
  if n = 0 then 0 else
    (ArithmeticFunction.vonMangoldt n : ℂ) *
        fourier (n : ℤ) (rationalCenter q a) -
      primeMajorCoefficient q

/-- The discrete dyadic amplitude before the harmless sum-to-integral
replacement in MRT Proposition 4.1. -/
def discreteDyadicAmplitude (X β : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊, realFourierPhase β n

theorem primeExponentialSum_sub_discrete_model
    {X : ℝ} (hX : 0 ≤ X) (q a : ℕ) (β : ℝ) :
    PrimePairEndpoints.primeExponentialSum X
        (rationalCenter q a + (β : UnitAddCircle)) -
      primeMajorCoefficient q * discreteDyadicAmplitude X β =
    ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
      realFourierPhase β n * rationalCenteredCoefficient q a n := by
  classical
  unfold PrimePairEndpoints.primeExponentialSum discreteDyadicAmplitude
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := by
    have hnlt := (Finset.mem_Ioc.mp hn).1
    have hfloor : 0 ≤ ⌊X⌋₊ := Nat.zero_le _
    omega
  rw [rationalCenteredCoefficient, if_neg hn0,
    realFourierPhase_nat_eq_fourier]
  simp only [fourier_apply, zsmul_add, toCircle_add, Circle.coe_mul]
  ring

/-- The exact dyadic pointwise approximation obtained from the rational-center
prefix discrepancy.  This closes the Abel/twist part of MRT Proposition 4.1;
the remaining analytic leaf is precisely the prefix estimate supplied by
Siegel--Walfisz through Nathanson Lemma 8.2. -/
theorem norm_primeExponentialSum_sub_discrete_model_le_of_prefix
    {X E β : ℝ} (hX : 0 ≤ X) (hE : 0 ≤ E) (q a : ℕ)
    (hprefix : ∀ t ∈ Set.Icc X (2 * X),
      ‖∑ n ∈ Finset.Icc 0 ⌊t⌋₊,
          rationalCenteredCoefficient q a n‖ ≤ E) :
    ‖PrimePairEndpoints.primeExponentialSum X
          (rationalCenter q a + (β : UnitAddCircle)) -
        primeMajorCoefficient q * discreteDyadicAmplitude X β‖ ≤
      2 * E + X * (2 * Real.pi * |β|) * E := by
  rw [primeExponentialSum_sub_discrete_model hX]
  have hX2 : X ≤ 2 * X := by linarith
  have h := norm_sum_Ioc_realFourierPhase_le_of_prefix_bound
    (rationalCenteredCoefficient q a) (β := β) hX hX2 hE hprefix
  convert h using 1 <;> ring

/-! ## Direct continuous-main-term form -/

/-- The uncentered rational-point Mangoldt coefficient. -/
def rationalRawCoefficient (q a n : ℕ) : ℂ :=
  if n = 0 then 0 else
    (ArithmeticFunction.vonMangoldt n : ℂ) *
      fourier (n : ℤ) (rationalCenter q a)

/-- The source-faithful Siegel--Walfisz discrepancy needed below.  Unlike the
discrete centering above, its main term is literally `M*t`; this is the form
which Abel summation turns into the continuous MRT amplitude without a
separate Riemann-sum estimate. -/
def rationalContinuousPrefixError (q a : ℕ) (t : ℝ) : ℂ :=
  (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, rationalRawCoefficient q a n) -
    primeMajorCoefficient q * (t : ℂ)

theorem primeExponentialSum_eq_sum_raw
    {X : ℝ} (hX : 0 ≤ X) (q a : ℕ) (β : ℝ) :
    PrimePairEndpoints.primeExponentialSum X
        (rationalCenter q a + (β : UnitAddCircle)) =
      ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
        realFourierPhase β n * rationalRawCoefficient q a n := by
  classical
  unfold PrimePairEndpoints.primeExponentialSum
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := by
    have hnlt := (Finset.mem_Ioc.mp hn).1
    have hfloor : 0 ≤ ⌊X⌋₊ := Nat.zero_le _
    omega
  rw [rationalRawCoefficient, if_neg hn0,
    realFourierPhase_nat_eq_fourier]
  simp only [fourier_apply, zsmul_add, toCircle_add, Circle.coe_mul]
  ring

/-- Direct continuous-amplitude version of Nathanson's Abel step.  The only
number-theoretic premise is the rational-point prefix discrepancy; every
operation from that premise to the literal MAP prime-polynomial model is
certified here. -/
theorem norm_primeExponentialSum_sub_continuous_model_le_of_prefix
    {X E β : ℝ} (hX : 0 ≤ X) (hE : 0 ≤ E) (q a : ℕ)
    (hprefix : ∀ t ∈ Set.Icc X (2 * X),
      ‖rationalContinuousPrefixError q a t‖ ≤ E) :
    ‖PrimePairEndpoints.primeExponentialSum X
          (rationalCenter q a + (β : UnitAddCircle)) -
        primeMajorCoefficient q * dyadicContinuousAmplitude X β‖ ≤
      2 * E + X * (2 * Real.pi * |β|) * E := by
  let c : ℕ → ℂ := rationalRawCoefficient q a
  let f : ℝ → ℂ := realFourierPhase β
  let M : ℂ := primeMajorCoefficient q
  let A : ℝ → ℂ := fun t => ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n
  let R : ℝ → ℂ := fun t => A t - M * (t : ℂ)
  have hX2 : X ≤ 2 * X := by linarith
  have hfDiff : ∀ t ∈ Set.Icc X (2 * X), DifferentiableAt ℝ f t := by
    intro t ht
    exact (hasDerivAt_realFourierPhase β t).differentiableAt
  have hderivEq : deriv f = fun t =>
      f t * (2 * Real.pi * Complex.I * (β : ℂ)) := by
    funext t
    exact (hasDerivAt_realFourierPhase β t).deriv
  have hfInt : IntegrableOn (deriv f) (Set.Icc X (2 * X)) := by
    rw [hderivEq]
    have hcont : Continuous f :=
      continuous_iff_continuousAt.mpr fun t =>
        (hasDerivAt_realFourierPhase β t).continuousAt
    exact (hcont.mul continuous_const).integrableOn_Icc
  have hAbel := sum_mul_eq_sub_sub_integral_mul c hX hX2 hfDiff hfInt
  rw [← intervalIntegral.integral_of_le hX2] at hAbel
  have hphaseInt : IntervalIntegrable f volume X (2 * X) := by
    have hcont : Continuous f :=
      continuous_iff_continuousAt.mpr fun t =>
        (hasDerivAt_realFourierPhase β t).continuousAt
    exact hcont.intervalIntegrable _ _
  have hderivInt : IntervalIntegrable (deriv f) volume X (2 * X) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hX2).mpr hfInt
  have hcastDeriv : ∀ t ∈ Set.uIcc X (2 * X),
      HasDerivAt (fun y : ℝ => (y : ℂ)) 1 t := by
    intro t ht
    exact (hasDerivAt_id t).ofReal_comp
  have hparts :
      (∫ t in X..2 * X, f t) =
        f (2 * X) * ((2 * X : ℝ) : ℂ) - f X * (X : ℂ) -
          ∫ t in X..2 * X, deriv f t * (t : ℂ) := by
    have hfDeriv : ∀ t ∈ Set.uIcc X (2 * X), HasDerivAt f (deriv f t) t := by
      intro t ht
      simpa only [hderivEq] using hasDerivAt_realFourierPhase β t
    have honeInt : IntervalIntegrable (fun _t : ℝ => (1 : ℂ))
        volume X (2 * X) := continuous_const.intervalIntegrable _ _
    simpa only [mul_one] using
      (intervalIntegral.integral_mul_deriv_eq_deriv_mul
        (u := f) (v := fun t : ℝ => (t : ℂ))
        (u' := deriv f) (v' := fun _t : ℝ => (1 : ℂ))
        hfDeriv hcastDeriv hderivInt honeInt)
  have hIntA : IntervalIntegrable (fun t => deriv f t * A t)
      volume X (2 * X) := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hX2).mpr
    exact integrableOn_mul_sum_Icc c hX hfInt
  have hIntLine : IntervalIntegrable
      (fun t => deriv f t * (M * (t : ℂ))) volume X (2 * X) := by
    apply hderivInt.mul_continuousOn
    fun_prop
  have hIntR : IntervalIntegrable (fun t => deriv f t * R t)
      volume X (2 * X) := by
    have heq : (fun t => deriv f t * R t) =
        fun t => deriv f t * A t - deriv f t * (M * (t : ℂ)) := by
      funext t
      simp only [R]
      ring
    rw [heq]
    exact hIntA.sub hIntLine
  have hIntFactor :
      (∫ t in X..2 * X, deriv f t * (M * (t : ℂ))) =
        M * ∫ t in X..2 * X, deriv f t * (t : ℂ) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    ring
  have hIntSplit :
      (∫ t in X..2 * X, deriv f t * R t) =
        (∫ t in X..2 * X, deriv f t * A t) -
          M * ∫ t in X..2 * X, deriv f t * (t : ℂ) := by
    have heq : (fun t => deriv f t * R t) =
        fun t => deriv f t * A t - deriv f t * (M * (t : ℂ)) := by
      funext t
      simp only [R]
      ring
    rw [heq, intervalIntegral.integral_sub hIntA hIntLine, hIntFactor]
  have hExact :
      (∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊, f n * c n) -
          M * ∫ t in X..2 * X, f t =
        f (2 * X) * R (2 * X) - f X * R X -
          ∫ t in X..2 * X, deriv f t * R t := by
    rw [hAbel, hparts, hIntSplit]
    simp only [R]
    ring
  have hRX : ‖R X‖ ≤ E := by
    simpa only [R, A, M, c, rationalContinuousPrefixError] using
      hprefix X ⟨le_rfl, hX2⟩
  have hR2X : ‖R (2 * X)‖ ≤ E := by
    simpa only [R, A, M, c, rationalContinuousPrefixError] using
      hprefix (2 * X) ⟨hX2, le_rfl⟩
  have hend : ‖f (2 * X) * R (2 * X) - f X * R X‖ ≤ 2 * E := by
    calc
      ‖f (2 * X) * R (2 * X) - f X * R X‖ ≤
          ‖f (2 * X) * R (2 * X)‖ + ‖f X * R X‖ := norm_sub_le _ _
      _ = ‖f (2 * X)‖ * ‖R (2 * X)‖ + ‖f X‖ * ‖R X‖ := by
        simp only [norm_mul]
      _ ≤ 1 * E + 1 * E := by
        gcongr <;> simp only [f, norm_realFourierPhase, le_rfl]
      _ = 2 * E := by ring
  have hIntBound :
      ‖∫ t in X..2 * X, deriv f t * R t‖ ≤
        (2 * Real.pi * |β| * E) * |2 * X - X| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    have ht' : t ∈ Set.Icc X (2 * X) := by
      rw [Set.uIoc_of_le hX2] at ht
      exact Set.Ioc_subset_Icc_self ht
    rw [norm_mul]
    have hd : ‖deriv f t‖ = 2 * Real.pi * |β| := by
      simpa only [f] using norm_deriv_realFourierPhase β t
    rw [hd]
    gcongr
    simpa only [R, A, M, c, rationalContinuousPrefixError] using hprefix t ht'
  rw [primeExponentialSum_eq_sum_raw hX, dyadicContinuousAmplitude]
  have hamp :
      (∫ x in X..2 * X, Complex.exp
        (2 * Real.pi * Complex.I * (β * x))) =
        ∫ x in X..2 * X, f x := by
    apply intervalIntegral.integral_congr
    intro x hx
    simp only [f, realFourierPhase]
    congr 1
    push_cast
    ring
  rw [hamp, hExact]
  calc
    ‖f (2 * X) * R (2 * X) - f X * R X -
        ∫ t in X..2 * X, deriv f t * R t‖ ≤
        ‖f (2 * X) * R (2 * X) - f X * R X‖ +
          ‖∫ t in X..2 * X, deriv f t * R t‖ := norm_sub_le _ _
    _ ≤ 2 * E + (2 * Real.pi * |β| * E) * |2 * X - X| :=
      add_le_add hend hIntBound
    _ = 2 * E + X * (2 * Real.pi * |β|) * E := by
      rw [show 2 * X - X = X by ring, abs_of_nonneg hX]
      ring

/-! ## Exact residue decomposition before Siegel--Walfisz -/

theorem fourier_rationalCenter_eq_stdAddChar
    {q : ℕ} [NeZero q] (a n : ℕ) :
    fourier (n : ℤ) (rationalCenter q a) =
      ZMod.stdAddChar ((a : ZMod q) * (n : ZMod q)) := by
  unfold rationalCenter
  rw [fourier_coe_apply]
  rw [show (a : ZMod q) * (n : ZMod q) =
      ((a * n : ℕ) : ZMod q) by norm_num]
  rw [show ZMod.stdAddChar ((a * n : ℕ) : ZMod q) =
      Complex.exp (2 * Real.pi * Complex.I * (a * n : ℤ) / q) by
        simpa using ZMod.stdAddChar_coe (N := q) (a * n : ℤ)]
  congr 1
  push_cast
  field_simp

theorem fourier_rationalCenter_mod
    {q : ℕ} [NeZero q] (a n : ℕ) :
    fourier (n : ℤ) (rationalCenter q a) =
      fourier ((n % q : ℕ) : ℤ) (rationalCenter q a) := by
  rw [fourier_rationalCenter_eq_stdAddChar,
    fourier_rationalCenter_eq_stdAddChar]
  congr 2
  simp

/-- The rational-point Mangoldt prefix is exactly the finite Fourier transform
of the progression sums.  No analytic estimate or character theorem enters. -/
theorem sum_rationalRawCoefficient_eq_sum_progressionPsi
    {q : ℕ} (hq : 1 ≤ q) (a : ℕ) (t : ℝ) :
    (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, rationalRawCoefficient q a n) =
      ∑ r ∈ Finset.range q,
        fourier (r : ℤ) (rationalCenter q a) *
          (APFoundation.progressionPsi t q r : ℂ) := by
  classical
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  have hdropZero :
      (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, rationalRawCoefficient q a n) =
        ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, rationalRawCoefficient q a n := by
    symm
    apply Finset.sum_subset
    · intro n hn
      simp only [Finset.mem_Icc] at hn ⊢
      omega
    · intro n hn hn'
      simp only [Finset.mem_Icc] at hn hn'
      have hn0 : n = 0 := by omega
      subst n
      simp [rationalRawCoefficient]
  rw [hdropZero]
  let S := Finset.Icc 1 ⌊t⌋₊
  have hmaps : ∀ n ∈ S, n % q ∈ Finset.range q := by
    intro n hn
    exact Finset.mem_range.mpr (Nat.mod_lt n (Nat.zero_lt_of_lt hq))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun n => rationalRawCoefficient q a n)]
  apply Finset.sum_congr rfl
  intro r hr
  symm
  unfold APFoundation.progressionPsi
  push_cast
  rw [Finset.mul_sum]
  have hite (n : ℕ) :
      fourier (r : ℤ) (rationalCenter q a) *
          ((if n % q = r % q then ArithmeticFunction.vonMangoldt n else 0 : ℝ) : ℂ) =
        if n % q = r % q then
          fourier (r : ℤ) (rationalCenter q a) *
            (ArithmeticFunction.vonMangoldt n : ℂ)
        else 0 := by
    by_cases h : n % q = r % q <;> simp [h]
  simp_rw [hite]
  simp only [Nat.mod_eq_of_lt (Finset.mem_range.mp hr)]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext n
    simp only [S, Finset.mem_filter, Finset.mem_Icc]
  · intro n hn
    rw [rationalRawCoefficient]
    have hnbase := (Finset.mem_filter.mp hn).1
    have hnpos : 1 ≤ n := (Finset.mem_Icc.mp hnbase).1
    rw [if_neg (by omega)]
    have hmod : n % q = r := (Finset.mem_filter.mp hn).2
    rw [fourier_rationalCenter_mod a n, hmod]
    ring

end

end MAPPointwiseMajorArc
