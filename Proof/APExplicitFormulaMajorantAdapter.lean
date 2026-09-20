import APMaximalExplicitFormulaBridge
import OneSidedMaximalL2
import PrimitiveExplicitFormulaSpine
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace APExplicitFormulaMajorantAdapter

open MeasureTheory Set
open scoped BigOperators ENNReal ArithmeticFunction

noncomputable section

open APFoundation APMaximalExplicitFormulaBridge
  PrimitiveExplicitFormulaSpine DirichletZeros

/-- The literal finite zero field whose antiderivative is the regularized
zero term in the truncated explicit formula. -/
def finiteZeroField (zeros : Finset ℂ) (multiplicity : ℂ → ℕ)
    (t : ℝ) : ℂ :=
  ∑ ρ ∈ zeros, (multiplicity ρ : ℂ) * (t : ℂ) ^ (ρ - 1)

/-- The corresponding regularized finite zero primitive. -/
def finiteZeroPrimitive (zeros : Finset ℂ) (multiplicity : ℂ → ℕ)
    (t : ℝ) : ℂ :=
  ∑ ρ ∈ zeros, (multiplicity ρ : ℂ) * regularizedZeroTerm t ρ

/-- Exact finite-sum antiderivative identity.  The only zero hypothesis needed
is positive real part, which holds in the rectangles used in Proposition 2.2. -/
theorem intervalIntegral_finiteZeroField
    (zeros : Finset ℂ) (multiplicity : ℂ → ℕ)
    (hzeros : ∀ ρ ∈ zeros, 0 < ρ.re) (x Y : ℝ) :
    (∫ t : ℝ in x..x + Y, finiteZeroField zeros multiplicity t) =
      finiteZeroPrimitive zeros multiplicity (x + Y) -
        finiteZeroPrimitive zeros multiplicity x := by
  classical
  unfold finiteZeroField finiteZeroPrimitive
  rw [intervalIntegral.integral_finset_sum]
  · rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro ρ hρ
    rw [intervalIntegral.integral_const_mul]
    have hr : -1 < (ρ - 1).re := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith [hzeros ρ hρ]
    rw [integral_cpow (Or.inl hr)]
    simp only [sub_add_cancel]
    unfold regularizedZeroTerm
    simp only [div_eq_mul_inv]
    noncomm_ring
  · intro ρ hρ
    exact (intervalIntegral.intervalIntegrable_cpow'
      (by
        simp only [Complex.sub_re, Complex.one_re]
        linarith [hzeros ρ hρ])).const_mul _

/-- The zero contribution over a positive-length interval is bounded by the
ordinary integral of the norm of the literal finite zero field. -/
theorem norm_finiteZeroPrimitive_sub_le_integral_norm
    (zeros : Finset ℂ) (multiplicity : ℂ → ℕ)
    (hzeros : ∀ ρ ∈ zeros, 0 < ρ.re) {x Y : ℝ} (hY : 0 ≤ Y) :
    ‖finiteZeroPrimitive zeros multiplicity (x + Y) -
        finiteZeroPrimitive zeros multiplicity x‖ ≤
      ∫ t : ℝ in x..x + Y, ‖finiteZeroField zeros multiplicity t‖ := by
  rw [← intervalIntegral_finiteZeroField zeros multiplicity hzeros x Y]
  exact intervalIntegral.norm_integral_le_integral_norm (by linarith)

variable {q : ℕ} [NeZero q]

/-- The literal ambient twisted prefix, parameterized by a real endpoint as
in the published explicit formula. -/
def ambientTwistedPsi (χ : DirichletCharacter ℂ q) (t : ℝ) : ℂ :=
  twistedMangoldtSum χ (Finset.Icc 1 ⌊t⌋₊)

/-- The arithmetic window is exactly the difference of the two real-endpoint
twisted prefixes. -/
theorem twistedMangoldtWindow_eq_ambientTwistedPsi_sub
    (χ : DirichletCharacter ℂ q) {x Y : ℝ} (hY : 0 ≤ Y) :
    twistedMangoldtSum χ (Finset.Ioc ⌊x⌋₊ ⌊x + Y⌋₊) =
      ambientTwistedPsi χ (x + Y) - ambientTwistedPsi χ x := by
  classical
  have hfloor : ⌊x⌋₊ ≤ ⌊x + Y⌋₊ := Nat.floor_mono (by linarith)
  have hsets0 (t : ℝ) : Finset.Icc 1 ⌊t⌋₊ = Finset.Ioc 0 ⌊t⌋₊ := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hsubset : Finset.Ioc 0 ⌊x⌋₊ ⊆ Finset.Ioc 0 ⌊x + Y⌋₊ := by
    intro k hk
    simp only [Finset.mem_Ioc] at hk ⊢
    exact ⟨hk.1, hk.2.trans hfloor⟩
  have hsdiff :
      Finset.Ioc 0 ⌊x + Y⌋₊ \ Finset.Ioc 0 ⌊x⌋₊ =
        Finset.Ioc ⌊x⌋₊ ⌊x + Y⌋₊ := by
    ext k
    simp only [Finset.mem_sdiff, Finset.mem_Ioc]
    omega
  unfold ambientTwistedPsi twistedMangoldtSum
  rw [hsets0, hsets0, ← hsdiff]
  exact (Finset.sum_sdiff_eq_sub
    (f := fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ))
    hsubset)

/-- Principal coefficient in the ambient explicit formula. -/
def principalCoefficient (χ : DirichletCharacter ℂ q) : ℂ :=
  if χ = 1 then 1 else 0

/-- A source-faithful real-endpoint explicit formula immediately gives the
exact interval identity consumed by the maximal AP bridge. -/
theorem ambientCharacterWindowError_eq_integral_zeroField_add_remainder
    (χ : DirichletCharacter ℂ q)
    (zeros : Finset ℂ) (multiplicity : ℂ → ℕ)
    (hzeros : ∀ ρ ∈ zeros, 0 < ρ.re)
    (remainder : ℝ → ℂ) {x Y : ℝ} (hY : 0 ≤ Y)
    (hformula : ∀ t ∈ ({x, x + Y} : Set ℝ),
      ambientTwistedPsi χ t =
        principalCoefficient χ * t -
          finiteZeroPrimitive zeros multiplicity t + remainder t) :
    ambientCharacterWindowError χ (Finset.Ioc ⌊x⌋₊ ⌊x + Y⌋₊) Y =
      -(∫ t : ℝ in x..x + Y, finiteZeroField zeros multiplicity t) +
        (remainder (x + Y) - remainder x) := by
  rw [ambientCharacterWindowError,
    twistedMangoldtWindow_eq_ambientTwistedPsi_sub χ hY]
  rw [hformula (x + Y) (by simp), hformula x (by simp)]
  rw [intervalIntegral_finiteZeroField zeros multiplicity hzeros x Y]
  unfold principalCoefficient
  by_cases hχ : χ = 1
  · simp [hχ]
    ring
  · simp [hχ]
    ring

/-- Direct pointwise `Gχ`-shaped majorant.  The first summand is the literal
one-sided field average; the second is the explicit-formula remainder. -/
theorem norm_ambientCharacterWindowError_div_le_fieldAverage_add_remainder
    (χ : DirichletCharacter ℂ q)
    (zeros : Finset ℂ) (multiplicity : ℂ → ℕ)
    (hzeros : ∀ ρ ∈ zeros, 0 < ρ.re)
    (remainder : ℝ → ℂ) {x Y : ℝ} (hY : 0 < Y)
    (hformula : ∀ t ∈ ({x, x + Y} : Set ℝ),
      ambientTwistedPsi χ t =
        principalCoefficient χ * t -
          finiteZeroPrimitive zeros multiplicity t + remainder t) :
    ‖ambientCharacterWindowError χ
        (Finset.Ioc ⌊x⌋₊ ⌊x + Y⌋₊) Y / Y‖ ≤
      Y⁻¹ * (∫ t : ℝ in x..x + Y,
        ‖finiteZeroField zeros multiplicity t‖) +
      ‖(remainder (x + Y) - remainder x) / Y‖ := by
  rw [ambientCharacterWindowError_eq_integral_zeroField_add_remainder
    χ zeros multiplicity hzeros remainder hY.le hformula]
  rw [add_div]
  refine (norm_add_le _ _).trans ?_
  have hnormInt :
      ‖∫ t : ℝ in x..x + Y, finiteZeroField zeros multiplicity t‖ ≤
        ∫ t : ℝ in x..x + Y, ‖finiteZeroField zeros multiplicity t‖ :=
    intervalIntegral.norm_integral_le_integral_norm (by linarith)
  have hYnorm : ‖(Y : ℂ)‖ = Y := by simp [abs_of_pos hY]
  calc
    ‖-(∫ t : ℝ in x..x + Y, finiteZeroField zeros multiplicity t) / Y‖ +
        ‖(remainder (x + Y) - remainder x) / Y‖ =
      Y⁻¹ * ‖∫ t : ℝ in x..x + Y,
        finiteZeroField zeros multiplicity t‖ +
        ‖(remainder (x + Y) - remainder x) / Y‖ := by
          rw [norm_div, norm_neg, hYnorm]
          ring
    _ ≤ Y⁻¹ * (∫ t : ℝ in x..x + Y,
          ‖finiteZeroField zeros multiplicity t‖) +
        ‖(remainder (x + Y) - remainder x) / Y‖ := by
          gcongr

/-- Exact conclusion shape required by
`normalizedAPError_sq_le_mean_characterMajorants`. -/
theorem norm_ambientCharacterWindowError_div_le_G
    (χ : DirichletCharacter ℂ q)
    (zeros : Finset ℂ) (multiplicity : ℂ → ℕ)
    (hzeros : ∀ ρ ∈ zeros, 0 < ρ.re)
    (remainder : ℝ → ℂ) {x Y G : ℝ} (hY : 0 < Y)
    (hformula : ∀ t ∈ ({x, x + Y} : Set ℝ),
      ambientTwistedPsi χ t =
        principalCoefficient χ * t -
          finiteZeroPrimitive zeros multiplicity t + remainder t)
    (hG : Y⁻¹ * (∫ t : ℝ in x..x + Y,
        ‖finiteZeroField zeros multiplicity t‖) +
      ‖(remainder (x + Y) - remainder x) / Y‖ ≤ G) :
    ‖ambientCharacterWindowError χ
        (Finset.Ioc ⌊x⌋₊ ⌊x + Y⌋₊) Y / Y‖ ≤ G := by
  exact (norm_ambientCharacterWindowError_div_le_fieldAverage_add_remainder
    χ zeros multiplicity hzeros remainder hY hformula).trans hG

/-- The literal divisor-backed field in equation (2.8), with analytic
multiplicity and no modeled zero list. -/
def actualZeroField (χ : DirichletCharacter ℂ q) (σ T t : ℝ) : ℂ :=
  finiteZeroField (zeroSupport χ σ T)
    (zeroMultiplicity χ σ T) t

/-- The generic finite primitive is definitionally the existing literal
multiplicity-weighted zero term. -/
theorem finiteZeroPrimitive_actual_eq
    (χ : DirichletCharacter ℂ q) (σ T t : ℝ) :
    finiteZeroPrimitive (zeroSupport χ σ T)
        (zeroMultiplicity χ σ T) t =
      multiplicityWeightedZeroTerm χ σ T t := by
  rfl

/-- Every zero in a positive-left-edge counting rectangle has positive real
part, discharging the only hypothesis of the finite antiderivative lemma. -/
theorem actualZero_re_pos (χ : DirichletCharacter ℂ q)
    {σ T : ℝ} (hσ : 0 < σ) {ρ : ℂ} (hρ : ρ ∈ zeroSupport χ σ T) :
    0 < ρ.re := by
  have hrect := mem_zeroRectangle_of_mem_zeroSupport χ σ T hρ
  exact hσ.trans_le hrect.1.1

/-- Literal divisor-backed specialization of the exact `Gχ` interface.  After
this theorem, the first remaining source theorem is precisely the truncated
real-endpoint explicit formula displayed in `hformula`; no finite-zero
calculus or AP normalization remains. -/
theorem norm_ambientCharacterWindowError_div_le_actualZero_G
    (χ : DirichletCharacter ℂ q) {σ T : ℝ} (hσ : 0 < σ)
    (remainder : ℝ → ℂ) {x Y G : ℝ} (hY : 0 < Y)
    (hformula : ∀ t ∈ ({x, x + Y} : Set ℝ),
      ambientTwistedPsi χ t =
        principalCoefficient χ * t -
          multiplicityWeightedZeroTerm χ σ T t + remainder t)
    (hG : Y⁻¹ * (∫ t : ℝ in x..x + Y,
        ‖actualZeroField χ σ T t‖) +
      ‖(remainder (x + Y) - remainder x) / Y‖ ≤ G) :
    ‖ambientCharacterWindowError χ
        (Finset.Ioc ⌊x⌋₊ ⌊x + Y⌋₊) Y / Y‖ ≤ G := by
  apply norm_ambientCharacterWindowError_div_le_G χ
    (zeroSupport χ σ T) (zeroMultiplicity χ σ T)
    (fun ρ hρ => actualZero_re_pos χ hσ hρ) remainder hY
  · intro t ht
    simpa only [finiteZeroPrimitive_actual_eq] using hformula t ht
  · simpa only [actualZeroField] using hG

end
end APExplicitFormulaMajorantAdapter

#print axioms APExplicitFormulaMajorantAdapter.intervalIntegral_finiteZeroField
#print axioms APExplicitFormulaMajorantAdapter.twistedMangoldtWindow_eq_ambientTwistedPsi_sub
#print axioms APExplicitFormulaMajorantAdapter.norm_ambientCharacterWindowError_div_le_G
#print axioms APExplicitFormulaMajorantAdapter.actualZero_re_pos
#print axioms APExplicitFormulaMajorantAdapter.norm_ambientCharacterWindowError_div_le_actualZero_G
