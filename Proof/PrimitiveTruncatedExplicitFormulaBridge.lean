import TruncatedTwistedPerron
import PrimitiveEulerZeroTransport
import BadEulerFactorMass

/-!
# A literal primitive-character Perron/contour bridge

This file stops immediately before the missing finite-pole residue theorem.
Every error below is an actual finite sum or an actual contour segment; no
explicit formula is postulated through a proposition-valued interface.
-/

namespace PrimitiveTruncatedExplicitFormulaBridge

open Set Filter Topology MeasureTheory
open scoped BigOperators Interval ArithmeticFunction
open PerronKernel PrimitiveExplicitFormulaSpine TruncatedTwistedPerron
open DirichletZeros

noncomputable section

/-- The standard half-integer Perron evaluation point for the prefix through
`N`; it avoids the discontinuity at every natural coefficient index. -/
def halfIntegerPoint (N : ℕ) : ℝ := (N : ℝ) + 1 / 2

theorem halfIntegerPoint_pos (N : ℕ) : 0 < halfIntegerPoint N := by
  unfold halfIntegerPoint
  positivity

/-- Replacing a nonnegative real endpoint by the half-integer above its floor
changes the exact main term by at most `1/2`. -/
theorem abs_halfIntegerPoint_floor_sub_le (t : ℝ) (ht : 0 ≤ t) :
    |halfIntegerPoint ⌊t⌋₊ - t| ≤ 1 / 2 := by
  rw [abs_le]
  have hlo : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht
  have hhi : t < (⌊t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one t
  unfold halfIntegerPoint
  constructor <;> norm_num at * <;> linarith

/-- An ambient character has trivial primitive inducer exactly when it is the
principal ambient character. -/
theorem primitiveCharacter_eq_one_iff
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    χ.primitiveCharacter = 1 ↔ χ = 1 := by
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  constructor
  · intro h
    calc
      χ = DirichletCharacter.changeLevel χ.conductor_dvd_level
          χ.primitiveCharacter := χ.changeLevel_primitiveCharacter.symm
      _ = 1 := by rw [h, DirichletCharacter.changeLevel_one]
  · intro h
    subst χ
    exact DirichletCharacter.primitiveCharacter_one

/-- The exact pole main term, separated from the contour errors. -/
def residueMain {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  @ite ℂ (χ = 1) (Classical.propDecidable _) (x : ℂ) 0

/-- Passing to the primitive inducer does not change whether the pole main
term is present. -/
theorem residueMain_primitiveCharacter
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ) :
    letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    residueMain χ.primitiveCharacter x = residueMain χ x := by
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  classical
  by_cases hχ : χ = 1
  · simp [residueMain, hχ, (primitiveCharacter_eq_one_iff χ).mpr hχ]
  · have hp : χ.primitiveCharacter ≠ 1 :=
      fun hp => hχ ((primitiveCharacter_eq_one_iff χ).mp hp)
    simp [residueMain, hχ, hp]

/-- The finite Perron error from replacing the kernel by one on `1 ≤ n ≤ N`.
This is a literal finite sum, including the transition behavior near `N`. -/
def insideKernelError {q : ℕ} (χ : DirichletCharacter ℂ q)
    (N : ℕ) (c T : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N,
    twistedMangoldtCoeff χ n *
      (1 - kernel (halfIntegerPoint N / n) c T)

/-- Exact finite-height Perron bridge for a twisted Mangoldt prefix.  The two
errors are respectively the literal inside-kernel discrepancy and the
literal omitted-coefficient vertical integral. -/
theorem twistedMangoldtPrefix_eq_rightLine_add_errors
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (N : ℕ) {c T : ℝ} (hc : 1 < c) :
    APFoundation.twistedMangoldtSum χ (Finset.Icc 1 N) =
      rightLineIntegral χ (halfIntegerPoint N) c T +
        insideKernelError χ N c T -
        coefficientTail χ (halfIntegerPoint N) c T (Finset.Icc 1 N) := by
  have hright := rightLineIntegral_eq_Icc_kernel_sum_add_tail χ
    (T := T) (halfIntegerPoint_pos N) hc N
  rw [APFoundation.twistedMangoldtSum, hright]
  symm
  calc
    (∑ n ∈ Finset.Icc 1 N,
          twistedMangoldtCoeff χ n *
            kernel (halfIntegerPoint N / n) c T) +
          coefficientTail χ (halfIntegerPoint N) c T (Finset.Icc 1 N) +
        insideKernelError χ N c T -
          coefficientTail χ (halfIntegerPoint N) c T (Finset.Icc 1 N) =
        (∑ n ∈ Finset.Icc 1 N,
          twistedMangoldtCoeff χ n *
            kernel (halfIntegerPoint N / n) c T) +
          insideKernelError χ N c T := by ring
    _ = ∑ n ∈ Finset.Icc 1 N, χ n *
          (ArithmeticFunction.vonMangoldt n : ℂ) := by
      simp only [insideKernelError, ← Finset.sum_add_distrib,
        twistedMangoldtCoeff]
      apply Finset.sum_congr rfl
      intro n hn
      ring

/-- The inside-kernel error is bounded coefficientwise by the ordinary von
Mangoldt function.  No asymptotic Perron estimate is hidden here. -/
theorem norm_insideKernelError_le
    {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ) (c T : ℝ) :
    ‖insideKernelError χ N c T‖ ≤
      ∑ n ∈ Finset.Icc 1 N,
        ArithmeticFunction.vonMangoldt n *
          ‖1 - kernel (halfIntegerPoint N / n) c T‖ := by
  unfold insideKernelError
  calc
    ‖∑ n ∈ Finset.Icc 1 N,
        twistedMangoldtCoeff χ n *
          (1 - kernel (halfIntegerPoint N / n) c T)‖
        ≤ ∑ n ∈ Finset.Icc 1 N,
            ‖twistedMangoldtCoeff χ n *
              (1 - kernel (halfIntegerPoint N / n) c T)‖ :=
          norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 N,
        ArithmeticFunction.vonMangoldt n *
          ‖1 - kernel (halfIntegerPoint N / n) c T‖ := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (norm_twistedMangoldtCoeff_le χ n) (norm_nonneg _)

/-- The exact ambient-to-primitive correction for a prefix has the already
certified logarithmic bad-Euler-factor bound. -/
theorem norm_imprimitiveMangoldtCorrection_prefix_le
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (N : ℕ) :
    ‖APFoundation.imprimitiveMangoldtCorrection χ (Finset.Icc 1 N)‖ ≤
      (⌊Real.log (N : ℝ) / Real.log 2⌋₊ : ℝ) * Real.log q := by
  have hset : Finset.Icc 1 N = Finset.Ioc 0 N := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hset]
  exact MAPBadEulerFactorMass.norm_imprimitiveMangoldtCorrection_Ioc_le χ 0 N

/-! ## The actual meromorphic contour integrand -/

/-- The source integrand `-(L'/L)(s) x^s/s`. -/
def perronContourIntegrand {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (x : ℝ) (s : ℂ) : ℂ :=
  (-logDeriv (DirichletCharacter.LFunction χ) s) *
    (x : ℂ) ^ s / s

/-- The integrand after removing the possible principal-character pole.  Its
poles in `Re s > 0` are precisely the zeros recorded by `zeroDivisor`. -/
def regularizedPerronContourIntegrand {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (x : ℝ) (s : ℂ) : ℂ :=
  (-logDeriv (regularizedLFunction χ) s) * (x : ℂ) ^ s / s

/-- The separated `s = 1` pole contribution for the principal character. -/
def principalPoleIntegrand {q : ℕ}
    (χ : DirichletCharacter ℂ q) (x : ℝ) (s : ℂ) : ℂ :=
  @ite ℂ (χ = 1) (Classical.propDecidable _)
    ((x : ℂ) ^ s / (s * (s - 1))) 0

/-- Euler-product nonvanishing on the absolute-convergence half-plane, proved
from Mathlib's exact L-series inverse. -/
theorem LFunction_ne_zero_of_one_lt_re
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    DirichletCharacter.LFunction χ s ≠ 0 := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  intro hzero
  let g : ℕ → ℂ := (fun n : ℕ => χ n) *
    (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ))
  have hone : LSeries (fun n : ℕ => χ n) s * LSeries g s = 1 := by
    simpa [g] using DirichletCharacter.LSeries.mul_mu_eq_one χ hs
  rw [hzero, zero_mul] at hone
  exact zero_ne_one hone

/-- The regularized L-function has no zeros in `Re s > 1`; consequently no
unrecorded zero lies between the hard-coded divisor edge `Re s = 1` and a
Perron line `Re s = c > 1`. -/
theorem regularizedLFunction_ne_zero_of_one_lt_re
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    regularizedLFunction χ s ≠ 0 := by
  classical
  by_cases hχ : χ = 1
  · subst χ
    have hs1 : s ≠ 1 := by
      intro h
      subst s
      simp at hs
    have hL := LFunction_ne_zero_of_one_lt_re
      (1 : DirichletCharacter ℂ q) hs
    simp only [regularizedLFunction, if_pos]
    unfold DirichletCharacter.LFunctionTrivChar₁
    rw [Function.update_of_ne hs1]
    exact mul_ne_zero (sub_ne_zero.mpr hs1) hL
  · simpa [regularizedLFunction, hχ] using
      LFunction_ne_zero_of_one_lt_re χ hs

/-- Positive real powers agree exactly with the branch-free vertical power
used in `TruncatedTwistedPerron`. -/
theorem cpow_on_verticalLine_eq_verticalPower
    {x : ℝ} (hx : 0 < x) (c t : ℝ) :
    (x : ℂ) ^ ((c : ℂ) + Complex.I * t) = verticalPower x c t := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    ← Complex.ofReal_log hx.le, verticalPower_eq_exp hx]
  congr 1
  ring

/-- The parameterized source contour integrand is definitionally the actual
right-line integrand already connected to the twisted Mangoldt series. -/
theorem perronContourIntegrand_on_rightLine
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x : ℝ} (hx : 0 < x) (c t : ℝ) :
    perronContourIntegrand χ x ((c : ℂ) + Complex.I * t) =
      logDerivPerronIntegrand χ x c t := by
  rw [perronContourIntegrand, logDerivPerronIntegrand,
    cpow_on_verticalLine_eq_verticalPower hx]

/-- The genuine Perron line is the normalized right boundary integral of the
source meromorphic integrand. -/
theorem rightLineIntegral_eq_contourIntegrand
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x : ℝ} (hx : 0 < x) (c T : ℝ) :
    rightLineIntegral χ x c T =
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        ∫ t in (-T)..T,
          perronContourIntegrand χ x ((c : ℂ) + Complex.I * t) := by
  unfold rightLineIntegral
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  exact (perronContourIntegrand_on_rightLine χ hx c t).symm

/-- Away from `s = 1`, the source integrand splits into the zero-divisor
integrand and the exact principal main-term pole. -/
theorem perronContourIntegrand_eq_regularized_add_principal
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x : ℝ} {s : ℂ} (hs : s ≠ 1)
    (hL : DirichletCharacter.LFunction χ s ≠ 0) :
    perronContourIntegrand χ x s =
      regularizedPerronContourIntegrand χ x s +
        principalPoleIntegrand χ x s := by
  classical
  by_cases hχ : χ = 1
  · subst χ
    by_cases hs0 : s = 0
    · subst s
      simp [perronContourIntegrand, regularizedPerronContourIntegrand,
        principalPoleIntegrand]
    have hderiv :=
      DirichletCharacter.deriv_LFunctionTrivChar₁_apply_of_ne_one q hs
    simp only [perronContourIntegrand, regularizedPerronContourIntegrand,
      principalPoleIntegrand, DirichletZeros.regularizedLFunction, if_pos,
      logDeriv_apply]
    rw [hderiv]
    have hreg : DirichletCharacter.LFunctionTrivChar₁ q s =
        (s - 1) * DirichletCharacter.LFunctionTrivChar q s := by
      unfold DirichletCharacter.LFunctionTrivChar₁
      rw [Function.update_of_ne hs]
    rw [hreg]
    have hms : -1 + s ≠ 0 := by
      intro h
      apply hs
      apply sub_eq_zero.mp
      calc
        s - 1 = -1 + s := by ring
        _ = 0 := h
    have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs
    field_simp [hL, hs, hs0, hsub]
    ring
  · simp only [perronContourIntegrand, regularizedPerronContourIntegrand,
      principalPoleIntegrand, regularizedLFunction, if_neg hχ, add_zero]

/-! ## Exact local residues -/

/-- The separated principal pole has residue exactly `x`, which is the main
term in the explicit formula. -/
theorem tendsto_mul_principalPoleIntegrand_one
    {q : ℕ} [NeZero q] (x : ℝ) (hx : 0 < x) :
    Tendsto
      (fun s => (s - 1) *
        principalPoleIntegrand (1 : DirichletCharacter ℂ q) x s)
      (𝓝[≠] (1 : ℂ)) (𝓝 (x : ℂ)) := by
  have hpow : Tendsto (fun s : ℂ => (x : ℂ) ^ s)
      (𝓝[≠] (1 : ℂ)) (𝓝 (x : ℂ)) := by
    have hdiff : Differentiable ℂ (fun s : ℂ => (x : ℂ) ^ s) :=
      differentiable_id.const_cpow
        (.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
    have ht := (hdiff.continuous.continuousAt.tendsto.mono_left
      (show 𝓝[≠] (1 : ℂ) ≤ 𝓝 (1 : ℂ) from nhdsWithin_le_nhds))
    simpa [Complex.ofReal_cpow hx.le, Real.rpow_one] using ht
  have hid : Tendsto (fun s : ℂ => s) (𝓝[≠] (1 : ℂ)) (𝓝 1) :=
    continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
  have hquot : Tendsto (fun s : ℂ => (x : ℂ) ^ s / s)
      (𝓝[≠] (1 : ℂ)) (𝓝 (x : ℂ)) := by
    simpa using! hpow.div hid (by norm_num)
  apply hquot.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [principalPoleIntegrand, if_pos rfl]
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  field_simp

/-- At every point other than `0` and `1`, multiplying the separated
principal pole by `s - ρ` tends to zero. -/
theorem tendsto_sub_mul_principalPoleIntegrand_at_other
    {q : ℕ} [NeZero q] (x : ℝ) (hx : 0 < x) {ρ : ℂ}
    (hρ0 : ρ ≠ 0) (hρ1 : ρ ≠ 1) :
    Tendsto
      (fun s => (s - ρ) *
        principalPoleIntegrand (1 : DirichletCharacter ℂ q) x s)
      (𝓝[≠] ρ) (𝓝 0) := by
  have hpow : Tendsto (fun s : ℂ => (x : ℂ) ^ s)
      (𝓝[≠] ρ) (𝓝 ((x : ℂ) ^ ρ)) := by
    have hdiff : Differentiable ℂ (fun s : ℂ => (x : ℂ) ^ s) :=
      differentiable_id.const_cpow
        (.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
    exact hdiff.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hid : Tendsto (fun s : ℂ => s) (𝓝[≠] ρ) (𝓝 ρ) :=
    continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
  have hone : Tendsto (fun _s : ℂ => (1 : ℂ)) (𝓝[≠] ρ) (𝓝 1) :=
    tendsto_const_nhds
  have hden : Tendsto (fun s : ℂ => s * (s - 1)) (𝓝[≠] ρ)
      (𝓝 (ρ * (ρ - 1))) := hid.mul (hid.sub hone)
  have hdenne : ρ * (ρ - 1) ≠ 0 :=
    mul_ne_zero hρ0 (sub_ne_zero.mpr hρ1)
  have hquot : Tendsto
      (fun s : ℂ => (x : ℂ) ^ s / (s * (s - 1))) (𝓝[≠] ρ)
      (𝓝 ((x : ℂ) ^ ρ / (ρ * (ρ - 1)))) :=
    hpow.div hden hdenne
  have hsubzero : Tendsto (fun s : ℂ => s - ρ)
      (𝓝[≠] ρ) (𝓝 0) := by
    have hconst : Tendsto (fun _s : ℂ => ρ) (𝓝[≠] ρ) (𝓝 ρ) :=
      tendsto_const_nhds
    simpa using hid.sub hconst
  simpa [principalPoleIntegrand] using hsubzero.mul hquot

/-- At every divisor-backed zero in `Re ρ > 0`, the regularized contour
integrand has residue `-m(ρ) x^ρ/ρ`, with analytic multiplicity. -/
theorem tendsto_mul_regularizedPerronContourIntegrand_at_zero
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ T x : ℝ} (hx : 0 < x) {ρ : ℂ}
    (hρ : ρ ∈ zeroSupport χ σ T) (hσ : 0 < σ) :
    Tendsto
      (fun s => (s - ρ) * regularizedPerronContourIntegrand χ x s)
      (𝓝[≠] ρ)
      (𝓝 (-(zeroMultiplicity χ σ T ρ : ℂ) * (x : ℂ) ^ ρ / ρ)) := by
  have hrect := mem_zeroRectangle_of_mem_zeroSupport χ σ T hρ
  have hρre : 0 < ρ.re := lt_of_lt_of_le hσ hrect.1.1
  have hρne : ρ ≠ 0 := by
    intro hz
    rw [hz] at hρre
    simp at hρre
  have hres := tendsto_mul_neg_logDeriv_regularizedLFunction χ σ T hρ
  have hpow : Tendsto (fun s : ℂ => (x : ℂ) ^ s)
      (𝓝[≠] ρ) (𝓝 ((x : ℂ) ^ ρ)) := by
    have hdiff : Differentiable ℂ (fun s : ℂ => (x : ℂ) ^ s) :=
      differentiable_id.const_cpow
        (.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
    exact hdiff.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hid : Tendsto (fun s : ℂ => s) (𝓝[≠] ρ) (𝓝 ρ) :=
    continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
  have hfactor : Tendsto (fun s : ℂ => (x : ℂ) ^ s / s)
      (𝓝[≠] ρ) (𝓝 ((x : ℂ) ^ ρ / ρ)) :=
    hpow.div hid hρne
  have hmul := hres.mul hfactor
  convert hmul using 1
  · ext s
    simp only [regularizedPerronContourIntegrand]
    ring
  · ring

/-- The same divisor-backed residue theorem for the source integrand
`-(L'/L)(s)x^s/s`, including principal characters.  The principal pole at
`s = 1` is disjoint from the zero divisor of the regularized L-function. -/
theorem tendsto_mul_perronContourIntegrand_at_zero
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ T x : ℝ} (hx : 0 < x) {ρ : ℂ}
    (hρ : ρ ∈ zeroSupport χ σ T) (hσ : 0 < σ) :
    Tendsto
      (fun s => (s - ρ) * perronContourIntegrand χ x s)
      (𝓝[≠] ρ)
      (𝓝 (-(zeroMultiplicity χ σ T ρ : ℂ) * (x : ℂ) ^ ρ / ρ)) := by
  classical
  have hregres :=
    tendsto_mul_regularizedPerronContourIntegrand_at_zero χ hx hρ hσ
  by_cases hχ : χ = 1
  · subst χ
    have hrect := mem_zeroRectangle_of_mem_zeroSupport
      (1 : DirichletCharacter ℂ q) σ T hρ
    have hρre : 0 < ρ.re := lt_of_lt_of_le hσ hrect.1.1
    have hρ0 : ρ ≠ 0 := by
      intro hz
      rw [hz] at hρre
      simp at hρre
    have hRzero := regularizedLFunction_eq_zero_of_mem_zeroSupport
      (1 : DirichletCharacter ℂ q) σ T hρ
    have hρ1 : ρ ≠ 1 := by
      intro hr
      subst ρ
      exact (regularizedLFunction_one_ne_zero
        (1 : DirichletCharacter ℂ q)) hRzero
    have hpole := tendsto_sub_mul_principalPoleIntegrand_at_other
      (q := q) x hx hρ0 hρ1
    have hsum := hregres.add hpole
    have hRne : ∀ᶠ s in 𝓝[≠] ρ,
        regularizedLFunction (1 : DirichletCharacter ℂ q) s ≠ 0 := by
      have han := (differentiable_regularizedLFunction
        (1 : DirichletCharacter ℂ q)).analyticAt ρ
      rcases han.eventually_eq_zero_or_eventually_ne_zero with hzero | hne
      · exfalso
        have htop : analyticOrderAt
            (regularizedLFunction (1 : DirichletCharacter ℂ q)) ρ = ⊤ :=
          analyticOrderAt_eq_top.mpr hzero
        rw [analyticOrderAt_eq_zeroMultiplicity
          (1 : DirichletCharacter ℂ q) σ T hρ] at htop
        simp at htop
      · exact hne
    have hs1 : ∀ᶠ s in 𝓝[≠] ρ, s ≠ 1 :=
      (eventually_ne_nhds hρ1).filter_mono nhdsWithin_le_nhds
    have hLne : ∀ᶠ s in 𝓝[≠] ρ,
        DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s ≠ 0 := by
      filter_upwards [hRne, hs1] with s hRs hs
      have hreg : regularizedLFunction (1 : DirichletCharacter ℂ q) s =
          (s - 1) * DirichletCharacter.LFunction
            (1 : DirichletCharacter ℂ q) s := by
        simp only [regularizedLFunction, if_pos]
        unfold DirichletCharacter.LFunctionTrivChar₁
        rw [Function.update_of_ne hs]
      intro hL
      apply hRs
      rw [hreg, hL, mul_zero]
    have heq :
        (fun s =>
          (s - ρ) * regularizedPerronContourIntegrand
            (1 : DirichletCharacter ℂ q) x s +
          (s - ρ) * principalPoleIntegrand
            (1 : DirichletCharacter ℂ q) x s) =ᶠ[𝓝[≠] ρ]
        (fun s => (s - ρ) * perronContourIntegrand
          (1 : DirichletCharacter ℂ q) x s) := by
      filter_upwards [hs1, hLne] with s hs hL
      rw [perronContourIntegrand_eq_regularized_add_principal
        (1 : DirichletCharacter ℂ q) hs hL]
      ring
    simpa using hsum.congr' heq
  · simpa [perronContourIntegrand, regularizedPerronContourIntegrand,
      regularizedLFunction, hχ] using hregres

/-- The literal multiplicity-weighted zero-residue sum dictated by the local
residue theorem above. -/
def multiplicityWeightedPerronZeroSum
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (σ T x : ℝ) : ℂ :=
  ∑ ρ ∈ zeroSupport χ σ T,
    (zeroMultiplicity χ σ T ρ : ℂ) * (x : ℂ) ^ ρ / ρ

/-! ## Literal rectangle segments -/

/-- The normalized upward left vertical segment. -/
def leftLineIntegral {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (x σ T : ℝ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
    ∫ t in (-T)..T,
      perronContourIntegrand χ x ((σ : ℂ) + Complex.I * t)

/-- The normalized sum of the positively oriented top and bottom horizontal
segments.  Both are parameterized from the left edge to the right edge. -/
def horizontalBoundaryIntegral {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (x σ c T : ℝ) : ℂ :=
  (((2 * Real.pi : ℝ) : ℂ)⁻¹ * Complex.I) *
      (∫ u in σ..c,
        perronContourIntegrand χ x ((u : ℂ) + Complex.I * T)) -
    (((2 * Real.pi : ℝ) : ℂ)⁻¹ * Complex.I) *
      (∫ u in σ..c,
        perronContourIntegrand χ x ((u : ℂ) - Complex.I * T))

/-- Literal normalized positively oriented rectangle boundary. -/
def normalizedRectangleBoundary {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (x σ c T : ℝ) : ℂ :=
  rightLineIntegral χ x c T - leftLineIntegral χ x σ T +
    horizontalBoundaryIntegral χ x σ c T

/-- Pure contour bookkeeping: isolate the right edge from the other three
literal boundary segments. -/
theorem rightLineIntegral_eq_boundary_add_left_sub_horizontal
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (x σ c T : ℝ) :
    rightLineIntegral χ x c T =
      normalizedRectangleBoundary χ x σ c T +
        leftLineIntegral χ x σ T -
        horizontalBoundaryIntegral χ x σ c T := by
  unfold normalizedRectangleBoundary
  ring

/-- Deepest unconditional primitive/imprimitive bridge currently available:
an ambient prefix is the primitive character's literal rectangle boundary,
left/horizontal contour errors, Perron errors, and exact bad-Euler-factor
correction.  Replacing `normalizedRectangleBoundary` by its main and zero
residues is precisely the missing analytic theorem. -/
theorem ambientTwistedMangoldtPrefix_eq_primitive_contour_decomposition
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (N : ℕ) {σ c T : ℝ} (hc : 1 < c) :
    letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    APFoundation.twistedMangoldtSum χ (Finset.Icc 1 N) =
      normalizedRectangleBoundary χ.primitiveCharacter
          (halfIntegerPoint N) σ c T +
        leftLineIntegral χ.primitiveCharacter (halfIntegerPoint N) σ T -
        horizontalBoundaryIntegral χ.primitiveCharacter
          (halfIntegerPoint N) σ c T +
        insideKernelError χ.primitiveCharacter N c T -
        coefficientTail χ.primitiveCharacter
          (halfIntegerPoint N) c T (Finset.Icc 1 N) -
        APFoundation.imprimitiveMangoldtCorrection χ (Finset.Icc 1 N) := by
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  rw [APFoundation.twistedMangoldtSum_eq_primitive_sub_correction]
  rw [twistedMangoldtPrefix_eq_rightLine_add_errors
    χ.primitiveCharacter N hc]
  rw [rightLineIntegral_eq_boundary_add_left_sub_horizontal]

end

end PrimitiveTruncatedExplicitFormulaBridge
