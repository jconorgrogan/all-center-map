import FullMAP
import FejerLocalMass

/-!
# Exact harmonic interfaces for the MAP endpoint

Everything in this file is finite or measure-theoretic.  In particular, no
minor-arc estimate, major-arc approximation, prime-pair asymptotic, or
singular-series estimate is used.

The normalized probability Haar measure is written explicitly in every
integral that enters the public interfaces.
-/

namespace MAPHarmonicEndpoint

open AddCircle MeasureTheory
open scoped BigOperators ComplexConjugate ArithmeticFunction

noncomputable section

/-- Fourier coefficient of a real density, with the sign convention used by
the paper: the integrand contains `fourier (-h)` explicitly. -/
def circleCoefficient (w : UnitAddCircle → ℝ) (h : ℤ) : ℂ :=
  ∫ α : UnitAddCircle, (w α : ℂ) * fourier (-h) α
    ∂AddCircle.haarAddCircle

theorem circleCoefficient_eq_fourierCoeff
    (w : UnitAddCircle → ℝ) (h : ℤ) :
    circleCoefficient w h = fourierCoeff (fun α ↦ (w α : ℂ)) h := by
  simp only [circleCoefficient, fourierCoeff, smul_eq_mul, mul_comm]

/-- The literal twice-supported correlation of the polynomial in `FullMAP`.
This definition deliberately retains both dyadic support conditions. -/
def supportedCorrelation (X : ℝ) (h : ℤ) : ℝ :=
  ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
    ∑ m ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
      if (n : ℤ) - (m : ℤ) = h then
        ArithmeticFunction.vonMangoldt n *
          ArithmeticFunction.vonMangoldt m
      else 0

/-- Complex version of the literal squared density. -/
def primeNormSqDensity (X : ℝ) (α : UnitAddCircle) : ℂ :=
  ((‖PrimePairEndpoints.primeExponentialSum X α‖ ^ 2 : ℝ) : ℂ)

theorem primeExponentialSum_continuous (X : ℝ) :
    Continuous (PrimePairEndpoints.primeExponentialSum X) := by
  unfold PrimePairEndpoints.primeExponentialSum
  fun_prop

theorem primeNormSqDensity_continuous (X : ℝ) :
    Continuous (primeNormSqDensity X) := by
  unfold primeNormSqDensity
  exact Complex.continuous_ofReal.comp
    ((primeExponentialSum_continuous X).norm.pow 2)

theorem primeNormSqDensity_integrable (X : ℝ) :
    Integrable (primeNormSqDensity X) AddCircle.haarAddCircle :=
  (primeNormSqDensity_continuous X).integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact isCompact_univ
      (Set.subset_univ _))

/-- Finite expansion of the literal squared polynomial. -/
theorem primeNormSqDensity_eq_doubleSum (X : ℝ) (α : UnitAddCircle) :
    primeNormSqDensity X α =
      ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
        ∑ m ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
          ((ArithmeticFunction.vonMangoldt n *
              ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) *
            fourier ((n : ℤ) - (m : ℤ)) α := by
  classical
  rw [primeNormSqDensity, PrimePairEndpoints.primeExponentialSum]
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, map_sum]
  simp only [map_mul, Complex.conj_ofReal]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  calc
    (ArithmeticFunction.vonMangoldt n : ℂ) * fourier (n : ℤ) α *
        ((ArithmeticFunction.vonMangoldt m : ℂ) *
          conj (fourier (m : ℤ) α)) =
      ((ArithmeticFunction.vonMangoldt n : ℂ) *
        (ArithmeticFunction.vonMangoldt m : ℂ)) *
          (fourier (n : ℤ) α * conj (fourier (m : ℤ) α)) := by ring
    _ = ((ArithmeticFunction.vonMangoldt n *
            ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) *
          fourier ((n : ℤ) - (m : ℤ)) α := by
      rw [← fourier_neg, ← fourier_add]
      push_cast
      simp only [sub_eq_add_neg]

/-- Exact Fourier coefficient of the supported dyadic correlation. -/
theorem fourierCoeff_primeNormSqDensity (X : ℝ) (h : ℤ) :
    fourierCoeff (primeNormSqDensity X) h =
      (supportedCorrelation X h : ℂ) := by
  classical
  have hfun : primeNormSqDensity X = fun α : UnitAddCircle ↦
      ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
        ∑ m ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
          ((ArithmeticFunction.vonMangoldt n *
              ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) *
            fourier ((n : ℤ) - (m : ℤ)) α := by
    funext α
    exact primeNormSqDensity_eq_doubleSum X α
  rw [hfun]
  have houter :
      (fun α : UnitAddCircle ↦
        ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
          ∑ m ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
            ((ArithmeticFunction.vonMangoldt n *
                ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) *
              fourier ((n : ℤ) - (m : ℤ)) α) =
        ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
          (fun α : UnitAddCircle ↦
            ∑ m ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
              ((ArithmeticFunction.vonMangoldt n *
                  ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) *
                fourier ((n : ℤ) - (m : ℤ)) α) := by
    funext α
    simp
  rw [houter, fourierCoeff.sum]
  · simp only [Finset.sum_apply]
    calc
      (∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
          fourierCoeff
            (fun α : UnitAddCircle ↦
              ∑ m ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
                ((ArithmeticFunction.vonMangoldt n *
                    ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) *
                  fourier ((n : ℤ) - (m : ℤ)) α) h) =
          ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
            ∑ m ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
              if (n : ℤ) - (m : ℤ) = h then
                ((ArithmeticFunction.vonMangoldt n *
                    ArithmeticFunction.vonMangoldt m : ℝ) : ℂ)
              else 0 := by
        apply Finset.sum_congr rfl
        intro n hn
        have hinner :
            (fun α : UnitAddCircle ↦
              ∑ m ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
                ((ArithmeticFunction.vonMangoldt n *
                    ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) *
                  fourier ((n : ℤ) - (m : ℤ)) α) =
              ∑ m ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
                (fun α : UnitAddCircle ↦
                  ((ArithmeticFunction.vonMangoldt n *
                      ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) *
                    fourier ((n : ℤ) - (m : ℤ)) α) := by
          funext α
          simp
        rw [hinner, fourierCoeff.sum]
        · simp only [Finset.sum_apply]
          apply Finset.sum_congr rfl
          intro m hm
          rw [fourierCoeff.const_mul, fourierCoeff_fourier, Pi.single_apply]
          by_cases hnm : (n : ℤ) - (m : ℤ) = h
          · subst h
            simp only [if_true, mul_one]
          · have hrev : ¬h = (n : ℤ) - (m : ℤ) := Ne.symm hnm
            simp only [hnm, hrev, if_false, mul_zero]
        · intro m hm
          apply Continuous.integrable_of_hasCompactSupport
          · fun_prop
          · exact HasCompactSupport.of_support_subset_isCompact isCompact_univ
              (Set.subset_univ _)
      _ = (supportedCorrelation X h : ℂ) := by
        simp only [supportedCorrelation]
        symm
        calc
          Complex.ofRealHom
              (∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
                ∑ m ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
                  if (n : ℤ) - (m : ℤ) = h then
                    ArithmeticFunction.vonMangoldt n *
                      ArithmeticFunction.vonMangoldt m else 0) =
              ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
                Complex.ofRealHom
                  (∑ m ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
                    if (n : ℤ) - (m : ℤ) = h then
                      ArithmeticFunction.vonMangoldt n *
                        ArithmeticFunction.vonMangoldt m else 0) := by
            rw [map_sum]
          _ = ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
                ∑ m ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
                  Complex.ofRealHom
                    (if (n : ℤ) - (m : ℤ) = h then
                      ArithmeticFunction.vonMangoldt n *
                        ArithmeticFunction.vonMangoldt m else 0) := by
            apply Finset.sum_congr rfl
            intro n hn
            rw [map_sum]
          _ = ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
                ∑ m ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
                  if (n : ℤ) - (m : ℤ) = h then
                    ((ArithmeticFunction.vonMangoldt n *
                        ArithmeticFunction.vonMangoldt m : ℝ) : ℂ)
                  else 0 := by
            apply Finset.sum_congr rfl
            intro n hn
            apply Finset.sum_congr rfl
            intro m hm
            by_cases hnm : (n : ℤ) - (m : ℤ) = h
            · simp only [hnm, if_true]
              rfl
            · simp only [hnm, if_false, map_zero]
  · intro n hn
    apply Continuous.integrable_of_hasCompactSupport
    · fun_prop
    · exact HasCompactSupport.of_support_subset_isCompact isCompact_univ
        (Set.subset_univ _)

/-- The same coefficient identity through the paper-facing integral
convention. -/
theorem circleCoefficient_primeNormSq (X : ℝ) (h : ℤ) :
    circleCoefficient
        (fun α ↦ ‖PrimePairEndpoints.primeExponentialSum X α‖ ^ 2) h =
      (supportedCorrelation X h : ℂ) := by
  rw [circleCoefficient_eq_fourierCoeff]
  exact fourierCoeff_primeNormSqDensity X h

/-- At frequency zero the double support forces the diagonal, with no
endpoint or extension term. -/
theorem supportedCorrelation_zero (X : ℝ) :
    supportedCorrelation X 0 =
      ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
        (ArithmeticFunction.vonMangoldt n : ℝ) ^ 2 := by
  classical
  simp only [supportedCorrelation]
  apply Finset.sum_congr rfl
  intro n hn
  calc
    (∑ m ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
      if (n : ℤ) - (m : ℤ) = 0 then
        ArithmeticFunction.vonMangoldt n *
          ArithmeticFunction.vonMangoldt m else 0) =
        ArithmeticFunction.vonMangoldt n *
          ArithmeticFunction.vonMangoldt n := by
      rw [Finset.sum_eq_single n]
      · simp
      · intro m hm hmn
        have hcast : (n : ℤ) ≠ (m : ℤ) := by
          exact_mod_cast hmn.symm
        simp [sub_eq_zero, hcast]
      · simp [hn]
    _ = (ArithmeticFunction.vonMangoldt n : ℝ) ^ 2 := by ring

/-- Literal normalized-Haar Parseval identity for the dyadic von Mangoldt
polynomial. -/
theorem integral_normSq_primeExponentialSum (X : ℝ) :
    (∫ α : UnitAddCircle,
        ‖PrimePairEndpoints.primeExponentialSum X α‖ ^ 2
          ∂AddCircle.haarAddCircle) =
      ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
        (ArithmeticFunction.vonMangoldt n : ℝ) ^ 2 := by
  have hcoeff := fourierCoeff_primeNormSqDensity X 0
  have hzero : fourierCoeff (primeNormSqDensity X) 0 =
      ∫ α : UnitAddCircle, primeNormSqDensity X α
        ∂AddCircle.haarAddCircle := by
    simp [fourierCoeff]
  rw [hzero, supportedCorrelation_zero] at hcoeff
  have hre := congrArg Complex.re hcoeff
  calc
    (∫ α : UnitAddCircle,
        ‖PrimePairEndpoints.primeExponentialSum X α‖ ^ 2
          ∂AddCircle.haarAddCircle) =
        ∫ α : UnitAddCircle, (primeNormSqDensity X α).re
          ∂AddCircle.haarAddCircle := by rfl
    _ = (∫ α : UnitAddCircle, primeNormSqDensity X α
          ∂AddCircle.haarAddCircle).re :=
      integral_re (primeNormSqDensity_integrable X)
    _ = ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
        (ArithmeticFunction.vonMangoldt n : ℝ) ^ 2 := by
      rw [hre]
      norm_cast

/-! ## Exact major/minor mask partition -/

theorem measurableSet_majorArcs (X : ℝ) (B D : ℕ) :
    MeasurableSet (PrimePairEndpoints.majorArcs X B D) := by
  let P : ℕ → ℕ → Prop := fun q a ↦
    1 ≤ q ∧ (q : ℝ) ≤ (Real.log X) ^ B ∧ a < q ∧ a.Coprime q
  have heq : PrimePairEndpoints.majorArcs X B D =
      ⋃ q : ℕ, ⋃ a : ℕ,
        if P q a then
          Metric.closedBall
            ((↑((a : ℝ) / (q : ℝ)) : UnitAddCircle))
            ((Real.log X) ^ D / X)
        else ∅ := by
    ext α
    constructor
    · rintro ⟨q, a, hq1, hqB, haq, hcop, hdist⟩
      refine Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr ⟨a, ?_⟩⟩
      have hPqa : P q a := ⟨hq1, hqB, haq, hcop⟩
      simp only [hPqa, if_true, Metric.mem_closedBall]
      exact hdist
    · intro ha
      rcases Set.mem_iUnion.mp ha with ⟨q, ha⟩
      rcases Set.mem_iUnion.mp ha with ⟨a, ha⟩
      by_cases hP : P q a
      · simp only [hP, if_true, Metric.mem_closedBall] at ha
        exact ⟨q, a, hP.1, hP.2.1, hP.2.2.1, hP.2.2.2, ha⟩
      · simp only [hP, if_false, Set.mem_empty_iff_false] at ha
  rw [heq]
  apply MeasurableSet.iUnion
  intro q
  apply MeasurableSet.iUnion
  intro a
  by_cases hP : P q a
  · simpa only [hP, if_true] using
      (measurableSet_closedBall : MeasurableSet
        (Metric.closedBall
          ((↑((a : ℝ) / (q : ℝ)) : UnitAddCircle))
          ((Real.log X) ^ D / X)))
  · simp only [hP, if_false, MeasurableSet.empty]

theorem measurableSet_minorArcs (X : ℝ) (B D : ℕ) :
    MeasurableSet (PrimePairEndpoints.minorArcs X B D) := by
  exact (measurableSet_majorArcs X B D).compl

/-- Positive major-arc part of the literal squared polynomial. -/
def majorWeight (X : ℝ) (B D : ℕ) : UnitAddCircle → ℝ :=
  (PrimePairEndpoints.majorArcs X B D).indicator
    (fun a ↦ ‖PrimePairEndpoints.primeExponentialSum X a‖ ^ 2)

/-- Positive minor-arc part of the literal squared polynomial. -/
def minorWeight (X : ℝ) (B D : ℕ) : UnitAddCircle → ℝ :=
  (PrimePairEndpoints.minorArcs X B D).indicator
    (fun a ↦ ‖PrimePairEndpoints.primeExponentialSum X a‖ ^ 2)

theorem majorWeight_nonneg (X : ℝ) (B D : ℕ) (a : UnitAddCircle) :
    0 ≤ majorWeight X B D a := by
  unfold majorWeight
  by_cases ha : a ∈ PrimePairEndpoints.majorArcs X B D
  · simp only [Set.indicator_of_mem ha]
    positivity
  · simp only [Set.indicator_of_notMem ha]
    exact le_rfl

theorem minorWeight_nonneg (X : ℝ) (B D : ℕ) (a : UnitAddCircle) :
    0 ≤ minorWeight X B D a := by
  unfold minorWeight
  by_cases ha : a ∈ PrimePairEndpoints.minorArcs X B D
  · simp only [Set.indicator_of_mem ha]
    positivity
  · simp only [Set.indicator_of_notMem ha]
    exact le_rfl

theorem normSq_primeExponentialSum_integrable (X : ℝ) :
    Integrable (fun a : UnitAddCircle ↦
      ‖PrimePairEndpoints.primeExponentialSum X a‖ ^ 2)
      AddCircle.haarAddCircle :=
  ((primeExponentialSum_continuous X).norm.pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact isCompact_univ
      (Set.subset_univ _))

theorem majorWeight_integrable (X : ℝ) (B D : ℕ) :
    Integrable (majorWeight X B D) AddCircle.haarAddCircle := by
  have hi := (normSq_primeExponentialSum_integrable X).indicator
    (measurableSet_majorArcs X B D)
  simpa only [majorWeight] using hi

theorem minorWeight_integrable (X : ℝ) (B D : ℕ) :
    Integrable (minorWeight X B D) AddCircle.haarAddCircle := by
  have hi := (normSq_primeExponentialSum_integrable X).indicator
    (measurableSet_minorArcs X B D)
  simpa only [minorWeight] using hi

theorem majorWeight_add_minorWeight (X : ℝ) (B D : ℕ)
    (a : UnitAddCircle) :
    majorWeight X B D a + minorWeight X B D a =
      ‖PrimePairEndpoints.primeExponentialSum X a‖ ^ 2 := by
  by_cases ha : a ∈ PrimePairEndpoints.majorArcs X B D
  · simp [majorWeight, minorWeight, PrimePairEndpoints.minorArcs,
      Set.indicator, ha]
  · simp [majorWeight, minorWeight, PrimePairEndpoints.minorArcs,
      Set.indicator, ha]

def majorCoefficient (X : ℝ) (B D : ℕ) (h : ℤ) : ℂ :=
  circleCoefficient (majorWeight X B D) h

def minorCoefficient (X : ℝ) (B D : ℕ) (h : ℤ) : ℂ :=
  circleCoefficient (minorWeight X B D) h

theorem integrable_circleIntegrand
    {w : UnitAddCircle → ℝ}
    (hw : Integrable w AddCircle.haarAddCircle) (h : ℤ) :
    Integrable (fun a : UnitAddCircle ↦
      (w a : ℂ) * fourier (-h) a) AddCircle.haarAddCircle := by
  apply hw.ofReal.mul_bdd
  · exact (map_continuous (fourier (-h))).aestronglyMeasurable
  · apply ae_of_all
    intro a
    rw [fourier_apply, Circle.norm_coe]

theorem circleCoefficient_add
    {u v : UnitAddCircle → ℝ}
    (hu : Integrable u AddCircle.haarAddCircle)
    (hv : Integrable v AddCircle.haarAddCircle) (h : ℤ) :
    circleCoefficient (fun a ↦ u a + v a) h =
      circleCoefficient u h + circleCoefficient v h := by
  unfold circleCoefficient
  rw [← integral_add (integrable_circleIntegrand hu h)
    (integrable_circleIntegrand hv h)]
  apply integral_congr_ae
  filter_upwards with a
  push_cast
  ring

/-- Exact Fourier partition.  It targets the twice-supported correlation,
not the one-sided public `primePairCorrelation`. -/
theorem supportedCorrelation_eq_major_add_minor
    (X : ℝ) (B D : ℕ) (h : ℤ) :
    (supportedCorrelation X h : ℂ) =
      majorCoefficient X B D h + minorCoefficient X B D h := by
  unfold majorCoefficient minorCoefficient
  rw [← circleCoefficient_primeNormSq]
  rw [← circleCoefficient_add (majorWeight_integrable X B D)
    (minorWeight_integrable X B D)]
  apply congrArg (fun w : UnitAddCircle → ℝ ↦ circleCoefficient w h)
  funext a
  exact (majorWeight_add_minorWeight X B D a).symm

end

end MAPHarmonicEndpoint
