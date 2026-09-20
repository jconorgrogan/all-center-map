import RamachandraLongContourInfiniteAssembly
import RamachandraLongDyadicCutoff
import RamachandraLongTailActiveShells

/-!
# Primitive-family L² assembly of the exact long contour

The character and source ordinate are treated as one product measure space.
This makes the infinite-shell step a literal Minkowski inequality in `L²`,
so no characterwise triangle inequality can lose a family-size factor.
-/

namespace RamachandraLongFamilyLpAssembly

open scoped BigOperators Interval ENNReal
open Complex MeasureTheory Filter
open RamachandraPrimitiveShiftedContourReduction
open RamachandraLongTailShellCauchy
open RamachandraLongTailShellSecondMoment
open RamachandraLongContourInfiniteAssembly
open RamachandraLongDyadicScalarSummability
open RamachandraLongDyadicCutoff
open RamachandraLongTailActiveShells
open RamachandraLpSeriesMinkowski

noncomputable section

set_option maxHeartbeats 1200000

variable {d : ℕ} [NeZero d]

local instance characterMeasurableSpace (n : ℕ) :
    MeasurableSpace (DirichletCharacter ℂ n) := ⊤

/-- Product measure: counting measure on the finite character family and the
literal source interval in `t`. -/
def primitiveLongFamilyMeasure (d : ℕ) [NeZero d] (T : ℝ) :
    Measure (DirichletCharacter ℂ d × ℝ) :=
  Measure.count.prod (volume.restrict (Set.uIoc (-T) T))

/-- One raw integrated long shell, zeroed off the primitive subfamily. -/
def primitiveLongShellField
    (d : ℕ) [NeZero d] (X sigma : ℝ) (j : ℕ) :
    DirichletCharacter ℂ d × ℝ → ℂ := by
  classical
  exact fun p => if p.1.IsPrimitive then
    ∫ v : ℝ, longTailShellIntegrand p.1 X sigma p.2 j v
  else 0

/-- The raw full long contour integral, zeroed off the primitive subfamily. -/
def primitiveLongRawField
    (d : ℕ) [NeZero d] (X sigma : ℝ) :
    DirichletCharacter ℂ d × ℝ → ℂ := by
  classical
  exact fun p => if p.1.IsPrimitive then
    ∫ v : ℝ, ramachandraShiftedContourIntegrand p.1 X sigma
      (-(sigma + 1 / 4)) p.2 v true
  else 0

/-- A family shell below the literal reflected-tail threshold is identically
zero, including the nonprimitive branch. -/
theorem primitiveLongShellField_eq_zero_of_upper_le
    (d : ℕ) [NeZero d] {X sigma : ℝ} {j : ℕ}
    (hupper : ((2 ^ (j + 1) : ℕ) : ℝ) ≤ X)
    (p : DirichletCharacter ℂ d × ℝ) :
    primitiveLongShellField d X sigma j p = 0 := by
  classical
  unfold primitiveLongShellField
  by_cases hp : p.1.IsPrimitive
  · simp only [hp, if_true]
    exact integral_longTailShell_eq_zero_of_upper_le p.1 hupper
  · simp [hp]

private theorem stronglyMeasurable_integral_longShell
    (psi : DirichletCharacter ℂ d) {X sigma : ℝ} (hX : 0 < X)
    (hcLo : -1 < -(sigma + 1 / 4))
    (hcHi : -(sigma + 1 / 4) < 0) (j : ℕ) :
    StronglyMeasurable (fun t =>
      ∫ v : ℝ, longTailShellIntegrand psi X sigma t j v) :=
  (continuous_uncurry_longTailShellIntegrand psi hX hcLo hcHi j).stronglyMeasurable
    |>.integral_prod_right'

/-- Joint measurability of one primitive-family shell field. -/
theorem stronglyMeasurable_primitiveLongShellField
    (d : ℕ) [NeZero d] {X sigma : ℝ} (hX : 0 < X)
    (hcLo : -1 < -(sigma + 1 / 4))
    (hcHi : -(sigma + 1 / 4) < 0) (j : ℕ) :
    StronglyMeasurable (primitiveLongShellField d X sigma j) := by
  classical
  let F : DirichletCharacter ℂ d →
      DirichletCharacter ℂ d × ℝ → ℂ := fun psi p =>
    if p.1 = psi ∧ psi.IsPrimitive then
      ∫ v : ℝ, longTailShellIntegrand psi X sigma p.2 j v
    else 0
  have hF : ∀ psi, StronglyMeasurable (F psi) := by
    intro psi
    have hcond : MeasurableSet
        {p : DirichletCharacter ℂ d × ℝ | p.1 = psi ∧ psi.IsPrimitive} := by
      by_cases hp : psi.IsPrimitive
      · simp only [hp, and_true]
        change MeasurableSet ((Prod.fst : (DirichletCharacter ℂ d × ℝ) → DirichletCharacter ℂ d) ⁻¹' ({psi} : Set (DirichletCharacter ℂ d)))
        exact measurable_fst (α := DirichletCharacter ℂ d) (β := ℝ)
          (measurableSet_singleton psi)
      · simp [hp]
    apply StronglyMeasurable.ite hcond
    · exact (stronglyMeasurable_integral_longShell psi hX hcLo hcHi j).comp_measurable
        measurable_snd
    · exact stronglyMeasurable_const
  have hsum : StronglyMeasurable (fun p =>
      ∑ psi : DirichletCharacter ℂ d, F psi p) := by
    fun_prop
  convert hsum using 1
  funext p
  simp only [primitiveLongShellField, F]
  have hsingle : (∑ psi : DirichletCharacter ℂ d, F psi p) = F p.1 p := by
    apply Finset.sum_eq_single p.1
    · intro b hb hne
      dsimp [F]
      rw [if_neg]
      intro h
      exact hne h.1.symm
    · simp
  rw [hsingle]
  dsimp [F]
  by_cases hp : p.1.IsPrimitive <;> simp [hp]


/-- The square norm of one family shell is integrable on the exact product
measure. -/
theorem integrable_norm_sq_primitiveLongShellField
    (d : ℕ) [NeZero d] {X T sigma : ℝ} (hX : 0 < X) (hT : 0 ≤ T)
    (hcLo : -1 < -(sigma + 1 / 4))
    (hcHi : -(sigma + 1 / 4) < 0) (j : ℕ) :
    Integrable (fun p => ‖primitiveLongShellField d X sigma j p‖ ^ 2)
      (primitiveLongFamilyMeasure d T) := by
  classical
  rcases RamachandraFunctionalFactorEnvelope.exists_norm_ramachandraFunctionalFactor_le_global
      (q := d) with ⟨Cgamma, hCgamma, hglobal⟩
  let W : ℝ := ∫ v : ℝ, RamachandraGammaWeightIntegrability.gammaPolynomialWeight
    (-(sigma + 1 / 4)) v
  let M : ℝ := Real.rpow (d : ℝ) (3 / 2) * Cgamma ^ 2 *
      Real.rpow X (-(sigma + 1 / 4)) * (1 + T) ^ 6 * W *
      longTailShellUniformNormBound (1 : DirichletCharacter ℂ d) X sigma j
  have hfield := stronglyMeasurable_primitiveLongShellField d hX hcLo hcHi j
  have hsqMeas : AEStronglyMeasurable
      (fun p => ‖primitiveLongShellField d X sigma j p‖ ^ 2)
      (primitiveLongFamilyMeasure d T) :=
    (hfield.norm.pow 2).aestronglyMeasurable
  unfold primitiveLongFamilyMeasure at hsqMeas ⊢
  rw [integrable_prod_iff hsqMeas]
  constructor
  · filter_upwards with psi
    let Cpsi : ℝ := Real.rpow (d : ℝ) (3 / 2) * Cgamma ^ 2 *
      Real.rpow X (-(sigma + 1 / 4)) * (1 + T) ^ 6 * W *
      longTailShellUniformNormBound psi X sigma j
    have hconst : IntegrableOn (fun _t : ℝ => Cpsi ^ 2)
        (Set.uIoc (-T) T) volume := by
      exact integrableOn_const
        (by rw [Real.volume_uIoc]; simp) (by simp)
    apply hconst.mono'
    · exact ((stronglyMeasurable_primitiveLongShellField d hX hcLo hcHi j).comp_measurable
        (measurable_const.prodMk measurable_id)).norm.pow 2 |>.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      by_cases hp : psi.IsPrimitive
      · rw [Set.uIoc_of_le (by linarith)] at ht
        have htAbs : |t| ≤ T := (abs_le).2 ⟨by linarith [ht.1], ht.2⟩
        have hnorm := norm_integral_longTailShell_le_global psi hp
          (sigma := sigma) (t := t) hX hcLo hcHi
          (le_trans (by norm_num) hCgamma) (hglobal psi hp) j
        have ht6 : (1 + |t|) ^ 6 ≤ (1 + T) ^ 6 := by gcongr
        have hW0 : 0 ≤ W := by
          dsimp [W]
          exact integral_nonneg (fun v =>
            RamachandraGammaWeightIntegrability.gammaPolynomialWeight_nonneg _ _)
        have hC0 : 0 ≤ longTailShellUniformNormBound psi X sigma j := by
          unfold longTailShellUniformNormBound
          positivity
        have hnorm' : ‖∫ v : ℝ, longTailShellIntegrand psi X sigma t j v‖ ≤ Cpsi := by
          let A : ℝ := Real.rpow (d : ℝ) (3 / 2) * Cgamma ^ 2 *
            Real.rpow X (-(sigma + 1 / 4))
          have hA0 : 0 ≤ A := by dsimp [A]; positivity
          calc
            _ ≤ (A * (1 + |t|) ^ 6) * W *
              longTailShellUniformNormBound psi X sigma j := by
              simpa [A, W, mul_assoc] using hnorm
            _ ≤ (A * (1 + T) ^ 6) * W *
              longTailShellUniformNormBound psi X sigma j := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left ht6 hA0) hW0) hC0
            _ = Cpsi := by rfl
        unfold primitiveLongShellField
        simp only [hp, if_true]
        exact pow_le_pow_left₀ (norm_nonneg _) hnorm' 2
      · unfold primitiveLongShellField
        simp [hp, sq_nonneg]
  · rw [integrable_count_iff]
    exact (hasSum_fintype _).summable

/-- The product integral of one shell square is exactly the source-order
primitive-family shell moment. -/
theorem integral_norm_sq_primitiveLongShellField_eq
    (d : ℕ) [NeZero d] {X T sigma : ℝ} (hX : 0 < X) (hT : 0 ≤ T)
    (hcLo : -1 < -(sigma + 1 / 4))
    (hcHi : -(sigma + 1 / 4) < 0) (j : ℕ) :
    (∫ p, ‖primitiveLongShellField d X sigma j p‖ ^ 2
        ∂primitiveLongFamilyMeasure d T) =
      primitiveLongTailShellSecondMoment d X T sigma j := by
  classical
  have hint := integrable_norm_sq_primitiveLongShellField d hX hT hcLo hcHi j
  unfold primitiveLongFamilyMeasure at hint ⊢
  rw [MeasureTheory.integral_prod _ hint, MeasureTheory.integral_count]
  unfold primitiveLongTailShellSecondMoment primitiveLongShellField
  apply Finset.sum_congr rfl
  intro psi hpsi
  by_cases hp : psi.IsPrimitive
  · simp only [hp, if_true]
    rw [Set.uIoc_of_le (by linarith)]
    rw [intervalIntegral.integral_of_le (by linarith)]
  · simp [hp]


/-- Exact `L²` seminorm of one family shell in terms of the source-order
second moment. -/
theorem eLpNorm_primitiveLongShellField_eq_ofReal_sqrt
    (d : ℕ) [NeZero d] {X T sigma : ℝ} (hX : 0 < X) (hT : 0 ≤ T)
    (hcLo : -1 < -(sigma + 1 / 4))
    (hcHi : -(sigma + 1 / 4) < 0) (j : ℕ) :
    eLpNorm (primitiveLongShellField d X sigma j) 2
      (primitiveLongFamilyMeasure d T) =
      ENNReal.ofReal (Real.sqrt
        (primitiveLongTailShellSecondMoment d X T sigma j)) := by
  have hsm := stronglyMeasurable_primitiveLongShellField d hX hcLo hcHi j
  have hint := integrable_norm_sq_primitiveLongShellField d hX hT hcLo hcHi j
  have hmem : MemLp (primitiveLongShellField d X sigma j) 2
      (primitiveLongFamilyMeasure d T) :=
    (memLp_two_iff_integrable_sq_norm hsm.aestronglyMeasurable).2 hint
  rw [hmem.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  norm_num
  rw [← Real.sqrt_eq_rpow]
  congr 2
  exact integral_norm_sq_primitiveLongShellField_eq d hX hT hcLo hcHi j


/-- Literal pointwise family shell series equals the raw full long contour. -/
theorem hasSum_primitiveLongShellField
    (d : ℕ) [NeZero d] {X sigma : ℝ} (hX : 1 ≤ X)
    (hcLo : -1 < -(sigma + 1 / 4))
    (hcHi : -(sigma + 1 / 4) < 0)
    (p : DirichletCharacter ℂ d × ℝ) :
    HasSum (fun j => primitiveLongShellField d X sigma j p)
      (primitiveLongRawField d X sigma p) := by
  classical
  by_cases hp : p.1.IsPrimitive
  · unfold primitiveLongShellField primitiveLongRawField
    simp only [hp, if_true]
    exact hasSum_integral_longTailShellIntegrand p.1 hp hX hcLo hcHi
  · unfold primitiveLongShellField primitiveLongRawField
    simp [hp]

/-- The raw full long-contour family field is strongly measurable, obtained
as the literal pointwise limit of its certified shell partial sums. -/
theorem stronglyMeasurable_primitiveLongRawField
    (d : ℕ) [NeZero d] {X sigma : ℝ} (hX : 1 ≤ X)
    (hcLo : -1 < -(sigma + 1 / 4))
    (hcHi : -(sigma + 1 / 4) < 0) :
    StronglyMeasurable (primitiveLongRawField d X sigma) := by
  let F : ℕ → DirichletCharacter ℂ d × ℝ → ℂ := fun N p =>
    ∑ j ∈ Finset.range N, primitiveLongShellField d X sigma j p
  apply stronglyMeasurable_of_tendsto (ι := ℕ) (f := F) atTop
  · intro N
    dsimp [F]
    have hs := Finset.stronglyMeasurable_sum (Finset.range N) (fun j hj =>
      stronglyMeasurable_primitiveLongShellField d
        (lt_of_lt_of_le zero_lt_one hX) hcLo hcHi j)
    have heq : (fun p => ∑ j ∈ Finset.range N,
        primitiveLongShellField d X sigma j p) =
        ∑ j ∈ Finset.range N, primitiveLongShellField d X sigma j := by
      funext p
      exact (Finset.sum_apply p (Finset.range N)
        (fun j => primitiveLongShellField d X sigma j)).symm
    rw [heq]
    exact hs
  · rw [tendsto_pi_nhds]
    intro p
    simpa [F] using (hasSum_primitiveLongShellField d hX hcLo hcHi p).tendsto_sum_nat


/-- Exact scalar majorant appearing on the right side of the one-shell family
estimate. -/
def longFamilyShellMomentMajorant
    (d : ℕ) (X T sigma : ℝ) (j : ℕ) : ℝ :=
  (∫ v : ℝ, RamachandraGammaWeightIntegrability.gammaPolynomialWeight
      (-(sigma + 1 / 4)) v) ^ 2 *
    (RamachandraShiftedFunctionalFactorMomentEnvelope.longFunctionalMomentConstant *
      (d : ℝ) ^ 3 * Real.rpow X (-2 * (sigma + 1 / 4)) *
      (1 + T) ^ 3) *
    (((d : ℝ) * (2 * T) + 8 * Real.pi * ((2 ^ j : ℕ) : ℝ)) *
      (Real.rpow ((2 ^ j : ℕ) : ℝ) (-(3 / 2 : ℝ)) *
        (harmonic (2 * (2 ^ j)) : ℝ) ^ 4))

/-- Its nonnegative square root, the exact `L²` shell cost. -/
def longFamilyShellRootMajorant
    (d : ℕ) (X T sigma : ℝ) (j : ℕ) : ℝ :=
  Real.sqrt (longFamilyShellMomentMajorant d X T sigma j)

theorem longFamilyShellMomentMajorant_nonneg
    (d : ℕ) {X T sigma : ℝ} (hX : 0 ≤ X) (hT : 0 ≤ T) (j : ℕ) :
    0 ≤ longFamilyShellMomentMajorant d X T sigma j := by
  unfold longFamilyShellMomentMajorant
  have hA : 0 ≤
      RamachandraShiftedFunctionalFactorMomentEnvelope.longFunctionalMomentConstant *
        (d : ℝ) ^ 3 * Real.rpow X (-2 * (sigma + 1 / 4)) *
        (1 + T) ^ 3 := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          RamachandraShiftedFunctionalFactorMomentEnvelope.longFunctionalMomentConstant_nonneg
          (by positivity))
        (Real.rpow_nonneg hX _))
      (by positivity)
  have hC : 0 ≤
      (((d : ℝ) * (2 * T) + 8 * Real.pi * ((2 ^ j : ℕ) : ℝ)) *
        (Real.rpow ((2 ^ j : ℕ) : ℝ) (-(3 / 2 : ℝ)) *
          (harmonic (2 * (2 ^ j)) : ℝ) ^ 4)) := by
    exact mul_nonneg
      (add_nonneg (mul_nonneg (by positivity) (by positivity))
        (mul_nonneg (mul_nonneg (by positivity) Real.pi_pos.le) (by positivity)))
      (mul_nonneg (Real.rpow_nonneg (by positivity) _) (by positivity))
  exact mul_nonneg (mul_nonneg (sq_nonneg _) hA) hC

theorem longFamilyShellRootMajorant_nonneg
    (d : ℕ) (X T sigma : ℝ) (j : ℕ) :
    0 ≤ longFamilyShellRootMajorant d X T sigma j :=
  Real.sqrt_nonneg _

/-- One shell's exact family `L²` seminorm is bounded by the certified scalar
root majorant. -/
theorem eLpNorm_primitiveLongShellField_le_rootMajorant
    (d : ℕ) [NeZero d] {X T sigma : ℝ} (hX : 0 < X) (hT : 0 ≤ T)
    (hcLo : -1 < -(sigma + 1 / 4))
    (hcHi : -(sigma + 1 / 4) < 0) (j : ℕ) :
    eLpNorm (primitiveLongShellField d X sigma j) 2
      (primitiveLongFamilyMeasure d T) ≤
      ENNReal.ofReal (longFamilyShellRootMajorant d X T sigma j) := by
  rw [eLpNorm_primitiveLongShellField_eq_ofReal_sqrt d hX hT hcLo hcHi j]
  apply ENNReal.ofReal_le_ofReal
  apply Real.sqrt_le_sqrt
  exact primitiveLongTailShellSecondMoment_le d hX hT hcLo hcHi j

/-- The square-root majorant factors into one common analytic coefficient and
the pure dyadic root cost. -/
theorem longFamilyShellRootMajorant_eq
    (d : ℕ) {X T sigma : ℝ} (hX : 0 ≤ X) (hT : 0 ≤ T) (j : ℕ) :
    longFamilyShellRootMajorant d X T sigma j =
      (∫ v : ℝ, RamachandraGammaWeightIntegrability.gammaPolynomialWeight
          (-(sigma + 1 / 4)) v) *
      Real.sqrt
        (RamachandraShiftedFunctionalFactorMomentEnvelope.longFunctionalMomentConstant *
          (d : ℝ) ^ 3 * Real.rpow X (-2 * (sigma + 1 / 4)) *
          (1 + T) ^ 3) *
      longDyadicRootCost ((d : ℝ) * (2 * T)) j := by
  let W : ℝ := ∫ v : ℝ,
    RamachandraGammaWeightIntegrability.gammaPolynomialWeight
      (-(sigma + 1 / 4)) v
  let A : ℝ :=
    RamachandraShiftedFunctionalFactorMomentEnvelope.longFunctionalMomentConstant *
      (d : ℝ) ^ 3 * Real.rpow X (-2 * (sigma + 1 / 4)) *
      (1 + T) ^ 3
  let C : ℝ := (((d : ℝ) * (2 * T) +
      8 * Real.pi * ((2 ^ j : ℕ) : ℝ)) *
    (Real.rpow ((2 ^ j : ℕ) : ℝ) (-(3 / 2 : ℝ)) *
      (harmonic (2 * (2 ^ j)) : ℝ) ^ 4))
  have hW : 0 ≤ W := by
    dsimp [W]
    exact integral_nonneg (fun v =>
      RamachandraGammaWeightIntegrability.gammaPolynomialWeight_nonneg _ _)
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          RamachandraShiftedFunctionalFactorMomentEnvelope.longFunctionalMomentConstant_nonneg
          (by positivity))
        (Real.rpow_nonneg hX _))
      (by positivity)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg
      (add_nonneg (mul_nonneg (by positivity) (by positivity))
        (mul_nonneg (mul_nonneg (by positivity) Real.pi_pos.le) (by positivity)))
      (mul_nonneg (Real.rpow_nonneg (by positivity) _) (by positivity))
  have hroot : longDyadicRootCost ((d : ℝ) * (2 * T)) j = Real.sqrt C := by
    unfold longDyadicRootCost
    dsimp [C]
    congr 1
    ring
  unfold longFamilyShellRootMajorant longFamilyShellMomentMajorant
  change Real.sqrt (W ^ 2 * A * C) = W * Real.sqrt A *
    longDyadicRootCost ((d : ℝ) * (2 * T)) j
  rw [show W ^ 2 * A * C = (W ^ 2) * (A * C) by ring]
  rw [Real.sqrt_mul (sq_nonneg W), Real.sqrt_sq hW,
    Real.sqrt_mul hA, hroot]
  ring

/-- The exact scalar root majorants are summable. -/
theorem summable_longFamilyShellRootMajorant
    (d : ℕ) {X T sigma : ℝ} (hX : 0 ≤ X) (hT : 0 ≤ T) :
    Summable (longFamilyShellRootMajorant d X T sigma) := by
  let P : ℝ :=
      (∫ v : ℝ, RamachandraGammaWeightIntegrability.gammaPolynomialWeight
          (-(sigma + 1 / 4)) v) *
      Real.sqrt
        (RamachandraShiftedFunctionalFactorMomentEnvelope.longFunctionalMomentConstant *
          (d : ℝ) ^ 3 * Real.rpow X (-2 * (sigma + 1 / 4)) *
          (1 + T) ^ 3)
  have hD : 0 ≤ (d : ℝ) * (2 * T) := by positivity
  have hs := (summable_longDyadicRootCost hD).mul_left P
  convert hs using 1
  funext j
  exact longFamilyShellRootMajorant_eq d hX hT j

/-- After deleting the canonically inactive initial segment, the remaining
literal family shells still sum pointwise to the raw long contour. -/
theorem hasSum_primitiveLongShellField_natAdd_cutoff
    (d : ℕ) [NeZero d] {X sigma : ℝ} (hX : 3 ≤ X)
    (hcLo : -1 < -(sigma + 1 / 4))
    (hcHi : -(sigma + 1 / 4) < 0)
    (p : DirichletCharacter ℂ d × ℝ) :
    HasSum
      (fun k => primitiveLongShellField d X sigma
        (k + longDyadicCutoff X) p)
      (primitiveLongRawField d X sigma p) := by
  let K := longDyadicCutoff X
  have hfull := hasSum_primitiveLongShellField d
    (show 1 ≤ X by linarith) hcLo hcHi p
  have hprefix :
      (∑ j ∈ Finset.range K, primitiveLongShellField d X sigma j p) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hjK : j < K := Finset.mem_range.mp hj
    exact primitiveLongShellField_eq_zero_of_upper_le d
      (dyadic_upper_le_of_lt_longDyadicCutoff hX hjK) p
  change HasSum (fun k => primitiveLongShellField d X sigma (k + K) p)
    (primitiveLongRawField d X sigma p)
  apply (hasSum_nat_add_iff
    (f := fun j => primitiveLongShellField d X sigma j p)
    (g := primitiveLongRawField d X sigma p) K).2
  simpa only [hprefix, add_zero] using hfull

/-- Exact infinite Minkowski bound for the active long-contour shells on the
primitive-character/source-ordinate product space. -/
theorem eLpNorm_primitiveLongRawField_le_shifted_tsum
    (d : ℕ) [NeZero d] {X T sigma : ℝ} (hX : 3 ≤ X) (hT : 0 ≤ T)
    (hcLo : -1 < -(sigma + 1 / 4))
    (hcHi : -(sigma + 1 / 4) < 0) :
    eLpNorm (primitiveLongRawField d X sigma) 2
        (primitiveLongFamilyMeasure d T) ≤
      ENNReal.ofReal
        (∑' k : ℕ, longFamilyShellRootMajorant d X T sigma
          (k + longDyadicCutoff X)) := by
  let K := longDyadicCutoff X
  apply eLpNorm_two_le_tsum_of_ae_hasSum
      (f := fun k => primitiveLongShellField d X sigma (k + K))
      (a := fun k => longFamilyShellRootMajorant d X T sigma (k + K))
  · intro k
    exact (stronglyMeasurable_primitiveLongShellField d
      (by linarith) hcLo hcHi (k + K)).aestronglyMeasurable
  · intro k
    exact longFamilyShellRootMajorant_nonneg d X T sigma (k + K)
  · exact (summable_nat_add_iff K).2
      (summable_longFamilyShellRootMajorant d (by linarith) hT)
  · intro k
    exact eLpNorm_primitiveLongShellField_le_rootMajorant d
      (by linarith) hT hcLo hcHi (k + K)
  · filter_upwards with p
    simpa only [K] using
      hasSum_primitiveLongShellField_natAdd_cutoff d hX hcLo hcHi p

/-- Quantitative scalar form of the preceding Minkowski bound.  It retains the
first-active-shell gain instead of paying for the killed dyadic cells. -/
theorem eLpNorm_primitiveLongRawField_le_cutoff_majorant
    (d : ℕ) [NeZero d] {X T sigma : ℝ} (hX : 3 ≤ X) (hT : 0 ≤ T)
    (hcLo : -1 < -(sigma + 1 / 4))
    (hcHi : -(sigma + 1 / 4) < 0) :
    eLpNorm (primitiveLongRawField d X sigma) 2
        (primitiveLongFamilyMeasure d T) ≤
      ENNReal.ofReal
        (((∫ v : ℝ, RamachandraGammaWeightIntegrability.gammaPolynomialWeight
              (-(sigma + 1 / 4)) v) *
            Real.sqrt
              (RamachandraShiftedFunctionalFactorMomentEnvelope.longFunctionalMomentConstant *
                (d : ℝ) ^ 3 * Real.rpow X (-2 * (sigma + 1 / 4)) *
                (1 + T) ^ 3)) *
          (Real.sqrt ((d : ℝ) * (2 * T) + 8 * Real.pi) *
            ((longDyadicCutoff X : ℝ) + 2) ^ 2 *
            (Real.rpow 2 (-(1 / 4 : ℝ))) ^ longDyadicCutoff X *
            longDyadicTailMass)) := by
  let P : ℝ :=
      (∫ v : ℝ, RamachandraGammaWeightIntegrability.gammaPolynomialWeight
          (-(sigma + 1 / 4)) v) *
      Real.sqrt
        (RamachandraShiftedFunctionalFactorMomentEnvelope.longFunctionalMomentConstant *
          (d : ℝ) ^ 3 * Real.rpow X (-2 * (sigma + 1 / 4)) *
          (1 + T) ^ 3)
  let D : ℝ := (d : ℝ) * (2 * T)
  let K := longDyadicCutoff X
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hsummable : Summable (fun k : ℕ => longDyadicRootCost D (k + K)) :=
    (summable_nat_add_iff K).2 (summable_longDyadicRootCost hD)
  have hrootEq : ∀ k : ℕ,
      longFamilyShellRootMajorant d X T sigma (k + K) =
        P * longDyadicRootCost D (k + K) := by
    intro k
    dsimp [P, D]
    exact longFamilyShellRootMajorant_eq d (by linarith) hT (k + K)
  have htsumEq :
      (∑' k : ℕ, longFamilyShellRootMajorant d X T sigma (k + K)) =
        P * (∑' k : ℕ, longDyadicRootCost D (k + K)) := by
    simp_rw [hrootEq]
    exact tsum_mul_left
  have hP : 0 ≤ P := by
    dsimp [P]
    exact mul_nonneg
      (integral_nonneg (fun v =>
        RamachandraGammaWeightIntegrability.gammaPolynomialWeight_nonneg _ _))
      (Real.sqrt_nonneg _)
  have htail := tsum_longDyadicRootCost_natAdd_le hD K
  have hscalar :
      (∑' k : ℕ, longFamilyShellRootMajorant d X T sigma (k + K)) ≤
        P * (Real.sqrt (D + 8 * Real.pi) * ((K : ℝ) + 2) ^ 2 *
          (Real.rpow 2 (-(1 / 4 : ℝ))) ^ K * longDyadicTailMass) := by
    rw [htsumEq]
    exact mul_le_mul_of_nonneg_left htail hP
  refine (eLpNorm_primitiveLongRawField_le_shifted_tsum d hX hT hcLo hcHi).trans ?_
  exact ENNReal.ofReal_le_ofReal (by simpa only [P, D, K] using hscalar)

/-- Scale-sharp source specialization.  With `X=dT`, every active long-tail
cell is already comparable to the conductor-height scale, eliminating the
spurious `sqrt X` loss in the generic scalar estimate. -/
theorem eLpNorm_primitiveLongRawField_le_sourceCutoffMajorant
    (d : ℕ) [NeZero d] {X T sigma : ℝ}
    (hscale : X = (d : ℝ) * T) (hX : 3 ≤ X) (hT : 0 ≤ T)
    (hcLo : -1 < -(sigma + 1 / 4))
    (hcHi : -(sigma + 1 / 4) < 0) :
    eLpNorm (primitiveLongRawField d X sigma) 2
        (primitiveLongFamilyMeasure d T) ≤
      ENNReal.ofReal
        (((∫ v : ℝ, RamachandraGammaWeightIntegrability.gammaPolynomialWeight
              (-(sigma + 1 / 4)) v) *
            Real.sqrt
              (RamachandraShiftedFunctionalFactorMomentEnvelope.longFunctionalMomentConstant *
                (d : ℝ) ^ 3 * Real.rpow X (-2 * (sigma + 1 / 4)) *
                (1 + T) ^ 3)) *
          (Real.sqrt (8 + 8 * Real.pi) *
            ((longDyadicCutoff X : ℝ) + 2) ^ 2 *
            (Real.rpow 2 (-(1 / 4 : ℝ))) ^ longDyadicCutoff X *
            longDyadicTailMass)) := by
  let P : ℝ :=
      (∫ v : ℝ, RamachandraGammaWeightIntegrability.gammaPolynomialWeight
          (-(sigma + 1 / 4)) v) *
      Real.sqrt
        (RamachandraShiftedFunctionalFactorMomentEnvelope.longFunctionalMomentConstant *
          (d : ℝ) ^ 3 * Real.rpow X (-2 * (sigma + 1 / 4)) *
          (1 + T) ^ 3)
  let D : ℝ := (d : ℝ) * (2 * T)
  let K := longDyadicCutoff X
  have hD : D = 2 * X := by dsimp [D]; rw [hscale]; ring
  have hrootEq : ∀ k : ℕ,
      longFamilyShellRootMajorant d X T sigma (k + K) =
        P * longDyadicRootCost D (k + K) := by
    intro k
    dsimp [P, D]
    exact longFamilyShellRootMajorant_eq d (by linarith) hT (k + K)
  have htsumEq :
      (∑' k : ℕ, longFamilyShellRootMajorant d X T sigma (k + K)) =
        P * (∑' k : ℕ, longDyadicRootCost D (k + K)) := by
    simp_rw [hrootEq]
    exact tsum_mul_left
  have hP : 0 ≤ P := by
    dsimp [P]
    exact mul_nonneg
      (integral_nonneg (fun v =>
        RamachandraGammaWeightIntegrability.gammaPolynomialWeight_nonneg _ _))
      (Real.sqrt_nonneg _)
  have htail := tsum_longDyadicRootCost_twoX_natAdd_cutoff_le hX
  rw [← hD] at htail
  have hscalar :
      (∑' k : ℕ, longFamilyShellRootMajorant d X T sigma (k + K)) ≤
        P * (Real.sqrt (8 + 8 * Real.pi) * ((K : ℝ) + 2) ^ 2 *
          (Real.rpow 2 (-(1 / 4 : ℝ))) ^ K * longDyadicTailMass) := by
    rw [htsumEq]
    exact mul_le_mul_of_nonneg_left htail hP
  refine (eLpNorm_primitiveLongRawField_le_shifted_tsum d hX hT hcLo hcHi).trans ?_
  exact ENNReal.ofReal_le_ofReal (by simpa only [P, K] using hscalar)

end
end RamachandraLongFamilyLpAssembly

#print axioms RamachandraLongFamilyLpAssembly.stronglyMeasurable_primitiveLongShellField
#print axioms RamachandraLongFamilyLpAssembly.integral_norm_sq_primitiveLongShellField_eq
#print axioms RamachandraLongFamilyLpAssembly.eLpNorm_primitiveLongShellField_eq_ofReal_sqrt
#print axioms RamachandraLongFamilyLpAssembly.stronglyMeasurable_primitiveLongRawField
#print axioms RamachandraLongFamilyLpAssembly.summable_longFamilyShellRootMajorant
