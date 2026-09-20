import APExplicitFormulaMajorantAdapter
import OneSidedMaximalL2
import GallagherEnergyExports
import NearCollarGallagher
import CGLMeshFormalization

/-!
# Fixed-scale AP zero route

The final MAP weld uses only two interval lengths: `gallagherWindow` in the
near collar and `paperGallagherWindow` in the major-arc power comparison.
Consequently no supremum over `Y` and no Hardy--Littlewood maximal theorem is
needed.  Fixed-scale one-sided convolution is an `L²` contraction, already
proved in `OneSidedMaximalL2`.

This module records the literal weighted-zero source (manuscript (2.7)), the
zero-field energy (2.8), and the two fixed-scale consumers.  The only
number-theoretic source proposition is (2.7); (2.8) is the next deterministic
formalization target, using the closed local zero count from Appendix (A.5).
-/

namespace MAPFixedScaleAPZeroRoute

open MeasureTheory Set
open scoped ENNReal BigOperators
open APExplicitFormulaMajorantAdapter OneSidedMaximalL2
open MAPNearCollarGallagher
open MAPMajorArcWeld

noncomputable section

/-- The height used in Proposition 2.2. -/
def apZeroHeight (epsilon X : ℝ) : ℝ :=
  Real.rpow X (13 / 15 - epsilon / 2)

/-- Literal full weighted zero mass of the primitive character inducing one
ambient character.  The divisor is restricted to `0 ≤ β ≤ 1`, `|γ|≤T`,
which is the nontrivial rectangle used by the explicit formula. -/
def primitiveWeightedZeroMass {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (X T : ℝ) : ℝ := by
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  exact ∑ ρ ∈ DirichletZeros.zeroSupport χ.primitiveCharacter 0 T,
    (DirichletZeros.zeroMultiplicity χ.primitiveCharacter 0 T ρ : ℝ) *
      Real.rpow X (2 * (ρ.re - 1))

/-- Weighted mass at one positive ambient level. -/
def weightedZeroMassAtLevel (q : ℕ) (X T : ℝ) : ℝ :=
  if hq : q = 0 then 0
  else
    letI : NeZero q := ⟨hq⟩
    ∑ χ : DirichletCharacter ℂ q, primitiveWeightedZeroMass χ X T

/-- The literal family mass `Z` in manuscript (2.7). -/
def apWeightedZeroMass (Q : ℕ) (X T : ℝ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q, weightedZeroMassAtLevel q X T

/-- The indispensable analytic source for the fixed-scale route: equation
(2.7), including the low strip, compact CGL mesh, Jutila near-one range,
Vinogradov--Korobov region, and the possible exceptional real zero.  This
proposition is strictly below any prime-in-AP conclusion. -/
def APWeightedZeroMassLogSaving : Prop :=
  ∀ K A epsilon : ℝ,
    0 < K → 0 < A → 0 < epsilon → epsilon ≤ 1 / 10 →
    ∃ C X₀ : ℝ, 0 < C ∧ 2 ≤ X₀ ∧
      ∀ X : ℝ, X₀ ≤ X →
        let Q := ⌊Real.rpow (Real.log X) K⌋₊
        apWeightedZeroMass Q X (apZeroHeight epsilon X) ≤
          C * Real.rpow (Real.log X) (-A)

/-- The primitive-inducer zero field used in equation (2.8). -/
def primitiveActualZeroField {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (T t : ℝ) : ℂ := by
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  exact actualZeroField χ.primitiveCharacter 0 T t

/-- Norm field extended by zero outside the manuscript interval
`[X/4,6X]`. -/
def primitiveZeroNormField {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (X T : ℝ) (t : ℝ) : ℝ≥0∞ :=
  (Set.Icc (X / 4) (6 * X)).indicator
    (fun u => ENNReal.ofReal ‖primitiveActualZeroField χ T u‖) t

theorem measurable_primitiveZeroNormField {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (X T : ℝ) :
    Measurable (primitiveZeroNormField χ X T) := by
  unfold primitiveZeroNormField primitiveActualZeroField actualZeroField
    finiteZeroField
  apply Measurable.indicator _ measurableSet_Icc
  fun_prop

/-- Literal `L²` zero-field energy at one ambient level.  `lintegral` is used
so fixed-scale convolution can consume it without any hidden finiteness
conversion. -/
def zeroFieldEnergyAtLevel (q : ℕ) (X T : ℝ) : ℝ≥0∞ :=
  if hq : q = 0 then 0
  else
    letI : NeZero q := ⟨hq⟩
    ∑ χ : DirichletCharacter ℂ q,
      ∫⁻ t : ℝ, (primitiveZeroNormField χ X T t) ^ 2

/-- Family form of the literal zero-field energy in manuscript (2.8). -/
def apZeroFieldEnergy (Q : ℕ) (X T : ℝ) : ℝ≥0∞ :=
  ∑ q ∈ Finset.Icc 1 Q, zeroFieldEnergyAtLevel q X T

/-- Exact equation-(2.8) target in source-faithful quantitative form.  The
constant is allowed to depend on the fixed polylogarithmic conductor exponent
`K`, exactly as in Proposition 2.2; the local zero count contains `log q`, so
no uniform statement for unrestricted `Q` is asserted.  This is not a second
number-theoretic hypothesis: its intended proof is direct integration of pairs
of zero monomials, followed by the certified closed local zero count (A.5),
giving the `log(X)^2` factor. -/
def APZeroFieldEnergy28 : Prop :=
  ∀ K : ℝ, 0 < K →
    ∃ C X₀ : ℝ, 0 < C ∧ 2 ≤ X₀ ∧
      ∀ (Q : ℕ) (epsilon X : ℝ),
        Q ≤ ⌊Real.rpow (Real.log X) K⌋₊ →
        0 < epsilon → epsilon ≤ 1 / 10 → X₀ ≤ X →
        apZeroFieldEnergy Q X (apZeroHeight epsilon X) ≤
          ENNReal.ofReal
            (C * X * (Real.log X) ^ 2 *
              apWeightedZeroMass Q X (apZeroHeight epsilon X))

/-- Diagnostic record of the accidentally overstrong quantifier order.  A.5
produces `log(q(T+2))`, so this unrestricted-`Q` proposition is not the
manuscript target and is not used downstream. -/
def UnrestrictedAPZeroFieldEnergy28 : Prop :=
  ∃ C X₀ : ℝ, 0 < C ∧ 2 ≤ X₀ ∧
    ∀ (Q : ℕ) (epsilon X : ℝ),
      0 < epsilon → epsilon ≤ 1 / 10 → X₀ ≤ X →
      apZeroFieldEnergy Q X (apZeroHeight epsilon X) ≤
        ENNReal.ofReal
          (C * X * (Real.log X) ^ 2 *
            apWeightedZeroMass Q X (apZeroHeight epsilon X))

/-- The unrestricted diagnostic would imply the corrected fixed-`K` target;
the converse is deliberately not claimed. -/
theorem unrestrictedAPZeroFieldEnergy28_implies
    (h : UnrestrictedAPZeroFieldEnergy28) : APZeroFieldEnergy28 := by
  intro K hK
  rcases h with ⟨C, X₀, hC, hX₀, hbound⟩
  exact ⟨C, X₀, hC, hX₀, fun Q epsilon X _hQ => hbound Q epsilon X⟩

/-- Fixed-scale zero-average energy at one ambient level. -/
def fixedZeroAverageEnergyAtLevel
    (q : ℕ) (X T y : ℝ) : ℝ≥0∞ :=
  if hq : q = 0 then 0
  else
    letI : NeZero q := ⟨hq⟩
    ∑ χ : DirichletCharacter ℂ q,
      ∫⁻ x : ℝ,
        (rightAverage (primitiveZeroNormField χ X T) y x) ^ 2

/-- Family fixed-scale averaged zero energy. -/
def fixedZeroAverageEnergy (Q : ℕ) (X T y : ℝ) : ℝ≥0∞ :=
  ∑ q ∈ Finset.Icc 1 Q, fixedZeroAverageEnergyAtLevel q X T y

/-- Fixed-scale Young/convolution contraction at one ambient level. -/
theorem fixedZeroAverageEnergyAtLevel_le
    (q : ℕ) {X T y : ℝ} (hy : 0 < y) :
    fixedZeroAverageEnergyAtLevel q X T y ≤
      zeroFieldEnergyAtLevel q X T := by
  by_cases hq : q = 0
  · simp [fixedZeroAverageEnergyAtLevel, zeroFieldEnergyAtLevel, hq]
  · letI : NeZero q := ⟨hq⟩
    simp only [fixedZeroAverageEnergyAtLevel, zeroFieldEnergyAtLevel, hq,
      dite_false]
    apply Finset.sum_le_sum
    intro χ hχ
    exact lintegral_rightAverage_sq_le
      (primitiveZeroNormField χ X T)
      (measurable_primitiveZeroNormField χ X T) hy

/-- Family fixed-scale contraction.  This is the replacement for the maximal
operator in the published proof and costs no logarithm. -/
theorem fixedZeroAverageEnergy_le
    (Q : ℕ) {X T y : ℝ} (hy : 0 < y) :
    fixedZeroAverageEnergy Q X T y ≤ apZeroFieldEnergy Q X T := by
  unfold fixedZeroAverageEnergy apZeroFieldEnergy
  apply Finset.sum_le_sum
  intro q hq
  exact fixedZeroAverageEnergyAtLevel_le q hy

/-- Near-collar fixed-scale family: exactly the first sliding length consumed
by final MAP. -/
def nearFixedZeroAverageEnergy
    (epsilon X : ℝ) (B Cc : ℕ) : ℝ≥0∞ :=
  fixedZeroAverageEnergy ⌊collarQ X B⌋₊ X
    (apZeroHeight (apReserve epsilon) X)
    (gallagherWindow epsilon X Cc)

/-- Major-arc fixed-scale family: exactly the paper Gallagher length. -/
def paperFixedZeroAverageEnergy
    (epsilon X : ℝ) (B D : ℕ) : ℝ≥0∞ :=
  fixedZeroAverageEnergy (paperDenominatorCutoff X B) X
    (apZeroHeight epsilon X) (paperGallagherWindow X D)

theorem nearFixedZeroAverageEnergy_le
    {epsilon X : ℝ} (B Cc : ℕ)
    (hy : 0 < gallagherWindow epsilon X Cc) :
    nearFixedZeroAverageEnergy epsilon X B Cc ≤
      apZeroFieldEnergy ⌊collarQ X B⌋₊ X
        (apZeroHeight (apReserve epsilon) X) := by
  exact fixedZeroAverageEnergy_le _ hy

theorem paperFixedZeroAverageEnergy_le
    {epsilon X : ℝ} (B D : ℕ)
    (hy : 0 < paperGallagherWindow X D) :
    paperFixedZeroAverageEnergy epsilon X B D ≤
      apZeroFieldEnergy (paperDenominatorCutoff X B) X
        (apZeroHeight epsilon X) := by
  exact fixedZeroAverageEnergy_le _ hy

/-- Direct insertion of equation (2.8) after fixed-scale contraction. -/
theorem fixedZeroAverageEnergy_le_of_equation28
    {Q : ℕ} {X T y C Z : ℝ}
    (hy : 0 < y)
    (h28 : apZeroFieldEnergy Q X T ≤
      ENNReal.ofReal (C * X * (Real.log X) ^ 2 * Z)) :
    fixedZeroAverageEnergy Q X T y ≤
      ENNReal.ofReal (C * X * (Real.log X) ^ 2 * Z) :=
  (fixedZeroAverageEnergy_le Q hy).trans h28

/-- Monotone insertion of the weighted-zero saving into equation (2.8). -/
theorem fixedZeroAverageEnergy_le_of_weighted_bound
    {Q : ℕ} {X T y C Z Zbd : ℝ}
    (hy : 0 < y) (hC : 0 ≤ C) (hX : 0 ≤ X)
    (hlog : 0 ≤ Real.log X) (hZ : 0 ≤ Z) (hZZ : Z ≤ Zbd)
    (h28 : apZeroFieldEnergy Q X T ≤
      ENNReal.ofReal (C * X * (Real.log X) ^ 2 * Z)) :
    fixedZeroAverageEnergy Q X T y ≤
      ENNReal.ofReal (C * X * (Real.log X) ^ 2 * Zbd) := by
  refine (fixedZeroAverageEnergy_le_of_equation28 hy h28).trans ?_
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left hZZ
  positivity

/-- Spending two logarithms in (2.7) exactly pays for the `log(X)^2` in
equation (2.8). -/
theorem log_sq_mul_rpow_neg_add_two
    {X A : ℝ} (hlog : 0 < Real.log X) :
    (Real.log X) ^ 2 *
        Real.rpow (Real.log X) (-(A + 2)) =
      Real.rpow (Real.log X) (-A) := by
  have hpow : (Real.log X) ^ (2 : ℕ) =
      Real.rpow (Real.log X) (2 : ℝ) :=
    MAPNearCollarGallagher.log_pow_eq_rpow (X := X) 2
  calc
    (Real.log X) ^ 2 * Real.rpow (Real.log X) (-(A + 2)) =
        Real.rpow (Real.log X) 2 *
          Real.rpow (Real.log X) (-(A + 2)) := by
            rw [hpow]
    _ = Real.rpow (Real.log X) (2 + -(A + 2)) :=
      (Real.rpow_add hlog 2 (-(A + 2))).symm
    _ = Real.rpow (Real.log X) (-A) := by
      congr 1
      ring

/-- Near endpoint export with the exact fixed Gallagher length. -/
theorem nearFixedZeroAverageEnergy_le_of_weighted_bound
    {epsilon X C Z Zbd : ℝ} (B Cc : ℕ)
    (hy : 0 < gallagherWindow epsilon X Cc)
    (hC : 0 ≤ C) (hX : 0 ≤ X) (hlog : 0 ≤ Real.log X)
    (hZ : 0 ≤ Z) (hZZ : Z ≤ Zbd)
    (h28 : apZeroFieldEnergy ⌊collarQ X B⌋₊ X
        (apZeroHeight (apReserve epsilon) X) ≤
      ENNReal.ofReal (C * X * (Real.log X) ^ 2 * Z)) :
    nearFixedZeroAverageEnergy epsilon X B Cc ≤
      ENNReal.ofReal (C * X * (Real.log X) ^ 2 * Zbd) := by
  exact fixedZeroAverageEnergy_le_of_weighted_bound
    hy hC hX hlog hZ hZZ h28

/-- Paper-major endpoint export with the exact paper Gallagher length. -/
theorem paperFixedZeroAverageEnergy_le_of_weighted_bound
    {epsilon X C Z Zbd : ℝ} (B D : ℕ)
    (hy : 0 < paperGallagherWindow X D)
    (hC : 0 ≤ C) (hX : 0 ≤ X) (hlog : 0 ≤ Real.log X)
    (hZ : 0 ≤ Z) (hZZ : Z ≤ Zbd)
    (h28 : apZeroFieldEnergy (paperDenominatorCutoff X B) X
        (apZeroHeight epsilon X) ≤
      ENNReal.ofReal (C * X * (Real.log X) ^ 2 * Z)) :
    paperFixedZeroAverageEnergy epsilon X B D ≤
      ENNReal.ofReal (C * X * (Real.log X) ^ 2 * Zbd) := by
  exact fixedZeroAverageEnergy_le_of_weighted_bound
    hy hC hX hlog hZ hZZ h28

end
end MAPFixedScaleAPZeroRoute

#print axioms MAPFixedScaleAPZeroRoute.measurable_primitiveZeroNormField
#print axioms MAPFixedScaleAPZeroRoute.fixedZeroAverageEnergyAtLevel_le
#print axioms MAPFixedScaleAPZeroRoute.fixedZeroAverageEnergy_le
#print axioms MAPFixedScaleAPZeroRoute.nearFixedZeroAverageEnergy_le
#print axioms MAPFixedScaleAPZeroRoute.paperFixedZeroAverageEnergy_le
#print axioms MAPFixedScaleAPZeroRoute.fixedZeroAverageEnergy_le_of_weighted_bound
#print axioms MAPFixedScaleAPZeroRoute.log_sq_mul_rpow_neg_add_two
#print axioms MAPFixedScaleAPZeroRoute.nearFixedZeroAverageEnergy_le_of_weighted_bound
#print axioms MAPFixedScaleAPZeroRoute.paperFixedZeroAverageEnergy_le_of_weighted_bound
