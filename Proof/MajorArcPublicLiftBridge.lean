import MajorArcIntegratedError
import MajorArcMaskGeometry

/-!
# Public normalized-Haar major arcs equal the lifted beta sums

This file closes the measure-normalization bridge between the public
`majorCoefficient` on `ℝ/ℤ` and the literal real interval integrals used by the
pointwise major-arc approximation.
-/

namespace MAPMajorArcPublicLiftBridge

open AddCircle MeasureTheory Metric Set
open MAPMajorArcWeld MAPMajorArcIntegratedError MAPMajorArcMaskGeometry
  MAPContinuousOverlap

noncomputable section

/-- Inside a centered fundamental interval, a circle ball of radius strictly
less than a half-period has exactly the expected real preimage. -/
theorem fundamental_inter_preimage_closedBall
    {t R : ℝ} (hRhalf : R < (1 : ℝ) / 2) :
    Set.Ioc (t - 1 / 2) (t - 1 / 2 + 1) ∩
        ((fun x : ℝ => (x : UnitAddCircle)) ⁻¹'
          closedBall (t : UnitAddCircle) R) =
      Set.Icc (t - R) (t + R) := by
  ext x
  constructor
  · rintro ⟨hxFund, hxBall⟩
    have hxhalf : |x - t| ≤ (1 : ℝ) / 2 := by
      rw [abs_le]
      constructor <;> linarith [hxFund.1, hxFund.2]
    have hxabs : |x - t| ≤ R := by
      rw [mem_preimage, mem_closedBall, dist_eq_norm,
        ← QuotientAddGroup.mk_sub,
        (norm_coe_eq_abs_iff (p := (1 : ℝ)) one_ne_zero).2 (by
          simpa only [abs_sub_comm, abs_one] using hxhalf)] at hxBall
      simpa only [abs_sub_comm] using hxBall
    rw [mem_Icc]
    rw [abs_le] at hxabs
    constructor <;> linarith
  · intro hx
    rw [mem_Icc] at hx
    have hxFund : x ∈ Set.Ioc (t - 1 / 2) (t - 1 / 2 + 1) := by
      constructor <;> linarith
    refine ⟨hxFund, ?_⟩
    have hxabs : |x - t| ≤ R := by
      rw [abs_le]
      constructor <;> linarith
    have hxhalf : |x - t| ≤ (1 : ℝ) / 2 := hxabs.trans hRhalf.le
    rw [mem_preimage, mem_closedBall, dist_eq_norm,
      ← QuotientAddGroup.mk_sub,
      (norm_coe_eq_abs_iff (p := (1 : ℝ)) one_ne_zero).2 (by
        simpa only [abs_sub_comm, abs_one] using hxhalf)]
    simpa only [abs_sub_comm] using hxabs

/-- Exact normalized-Haar-to-Lebesgue parameterization of a circle arc.
No missing `2π` factor occurs because `haarAddCircle` has total mass one. -/
theorem setIntegral_closedBall_eq_intervalIntegral_lift
    {t R : ℝ} (hR0 : 0 ≤ R) (hRhalf : R < (1 : ℝ) / 2)
    (f : UnitAddCircle → ℂ) :
    (∫ α in closedBall (t : UnitAddCircle) R, f α
        ∂AddCircle.haarAddCircle) =
      ∫ β in -R..R, f ((t : UnitAddCircle) + (β : UnitAddCircle)) := by
  let g : UnitAddCircle → ℂ := (closedBall (t : UnitAddCircle) R).indicator f
  have hball : MeasurableSet (closedBall (t : UnitAddCircle) R) :=
    measurableSet_closedBall
  calc
    (∫ α in closedBall (t : UnitAddCircle) R, f α
        ∂AddCircle.haarAddCircle) =
        ∫ α : UnitAddCircle, g α ∂AddCircle.haarAddCircle := by
      rw [show g = (closedBall (t : UnitAddCircle) R).indicator f by rfl,
        integral_indicator hball]
    _ = ∫ x in Set.Ioc (t - 1 / 2) (t - 1 / 2 + 1),
          g (x : UnitAddCircle) := by
      simpa [AddCircle.volume_eq_smul_haarAddCircle] using
        (UnitAddCircle.integral_preimage (t - 1 / 2) g).symm
    _ = ∫ x in
          Set.Ioc (t - 1 / 2) (t - 1 / 2 + 1) ∩
            ((fun x : ℝ => (x : UnitAddCircle)) ⁻¹'
              closedBall (t : UnitAddCircle) R),
          f (x : UnitAddCircle) := by
      change (∫ x in Set.Ioc (t - 1 / 2) (t - 1 / 2 + 1),
          (((fun x : ℝ => (x : UnitAddCircle)) ⁻¹'
            closedBall (t : UnitAddCircle) R).indicator
              (fun x : ℝ => f (x : UnitAddCircle))) x) = _
      exact setIntegral_indicator
        (hball.preimage AddCircle.measurable_mk')
    _ = ∫ x in Set.Icc (t - R) (t + R),
          f (x : UnitAddCircle) := by
      rw [fundamental_inter_preimage_closedBall hRhalf]
    _ = ∫ x in Set.Ioc (t - R) (t + R),
          f (x : UnitAddCircle) := integral_Icc_eq_integral_Ioc
    _ = ∫ x in t - R..t + R, f (x : UnitAddCircle) := by
      rw [intervalIntegral.integral_of_le (by linarith)]
    _ = ∫ β in -R..R,
          f ((t : UnitAddCircle) + (β : UnitAddCircle)) := by
      symm
      calc
        (∫ β in -R..R,
            f ((t : UnitAddCircle) + (β : UnitAddCircle))) =
            ∫ β in -R..R, f ((β + t : ℝ) : UnitAddCircle) := by
          apply intervalIntegral.integral_congr
          intro β hβ
          change f ((t : UnitAddCircle) + (β : UnitAddCircle)) =
            f ((β + t : ℝ) : UnitAddCircle)
          rw [← QuotientAddGroup.mk_add]
          congr 1
          ring_nf
        _ = ∫ x in -R + t..R + t, f (x : UnitAddCircle) :=
          intervalIntegral.integral_comp_add_right
            (fun x : ℝ => f (x : UnitAddCircle)) t
        _ = ∫ x in t - R..t + R, f (x : UnitAddCircle) := by
          congr 1 <;> ring_nf

/-! ## The public finite major mask -/

def legalRationalPairs (X : ℝ) (B : ℕ) : Finset ((q : ℕ) × ℕ) :=
  (Finset.Icc 1 (paperDenominatorCutoff X B)).sigma reducedResidues

theorem mem_legalRationalPairs {X : ℝ} {B q a : ℕ} :
    ⟨q, a⟩ ∈ legalRationalPairs X B ↔
      1 ≤ q ∧ q ≤ paperDenominatorCutoff X B ∧
        a < q ∧ a.Coprime q := by
  simp only [legalRationalPairs, Finset.mem_sigma, Finset.mem_Icc,
    mem_reducedResidues]
  tauto

def indexedRationalArc (X : ℝ) (B D : ℕ)
    (i : ↑(legalRationalPairs X B)) : Set UnitAddCircle :=
  closedBall (rationalCenter i.1.1 i.1.2) (paperArcRadius X D)

theorem majorArcs_eq_finite_iUnion
    {X : ℝ} {B D : ℕ} (hX : 1 ≤ X) :
    PrimePairEndpoints.majorArcs X B D =
      ⋃ i : ↑(legalRationalPairs X B), indexedRationalArc X B D i := by
  have hlog : 0 ≤ Real.log X := Real.log_nonneg hX
  have hpow : 0 ≤ (Real.log X) ^ B := pow_nonneg hlog _
  ext α
  constructor
  · rintro ⟨q, a, hq1, hqX, haq, hcop, hdist⟩
    have hqfloor : q ≤ paperDenominatorCutoff X B := by
      unfold paperDenominatorCutoff
      exact Nat.le_floor hqX
    let i : ↑(legalRationalPairs X B) :=
      ⟨⟨q, a⟩, mem_legalRationalPairs.mpr
        ⟨hq1, hqfloor, haq, hcop⟩⟩
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    simpa [indexedRationalArc, rationalCenter, paperArcRadius,
      Metric.mem_closedBall] using hdist
  · intro hα
    rcases Set.mem_iUnion.mp hα with ⟨i, hi⟩
    have himem := mem_legalRationalPairs.mp i.2
    refine ⟨i.1.1, i.1.2, himem.1, ?_, himem.2.2.1,
      himem.2.2.2, ?_⟩
    · exact (Nat.le_floor_iff hpow).mp himem.2.1
    · simpa [indexedRationalArc, rationalCenter, paperArcRadius,
        Metric.mem_closedBall] using hi

theorem indexedRationalArcs_pairwiseDisjoint_of_growth
    {X : ℝ} {B D : ℕ} (hX : 1 < X)
    (hgrowth : 2 * (Real.log X) ^ (D + 2 * B) < X) :
    Pairwise (Function.onFun Disjoint (indexedRationalArc X B D)) := by
  intro i j hij
  have hi := mem_legalRationalPairs.mp i.2
  have hj := mem_legalRationalPairs.mp j.2
  have hlog : 0 ≤ Real.log X := Real.log_nonneg hX.le
  have hiq : (i.1.1 : ℝ) ≤ (Real.log X) ^ B :=
    (Nat.le_floor_iff (pow_nonneg hlog _)).mp hi.2.1
  have hjq : (j.1.1 : ℝ) ≤ (Real.log X) ^ B :=
    (Nat.le_floor_iff (pow_nonneg hlog _)).mp hj.2.1
  have hidx : i.1.1 ≠ j.1.1 ∨ i.1.2 ≠ j.1.2 := by
    by_contra hn
    push Not at hn
    apply hij
    apply Subtype.ext
    exact Sigma.ext hn.1 (by simpa [hn.1] using hn.2)
  change Disjoint (indexedRationalArc X B D i) (indexedRationalArc X B D j)
  exact
    disjoint_paper_rationalArcs_of_growth hX hi.1 hj.1 hiq hjq
      hi.2.2.1 hj.2.2.1 hi.2.2.2 hj.2.2.2 hidx hgrowth

/-- Beyond one explicit threshold, the manuscript radius is positive, below a
half-period, and its reduced rational arcs satisfy the Farey disjointness
width. -/
theorem eventually_paperArc_geometry (B D : ℕ) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      1 < X ∧ 0 < paperArcRadius X D ∧
      paperArcRadius X D < (1 : ℝ) / 2 ∧
      2 * (Real.log X) ^ (D + 2 * B) < X := by
  rcases eventually_two_mul_log_pow_lt_id B D with ⟨X₁, hX₁⟩
  refine ⟨max X₁ (Real.exp 1), ?_⟩
  intro X hX
  have hbase := hX₁ X ((le_max_left X₁ (Real.exp 1)).trans hX)
  have hExp : Real.exp 1 ≤ X := (le_max_right X₁ (Real.exp 1)).trans hX
  have hXpos : 0 < X := lt_trans zero_lt_one hbase.1
  have hlog1 : 1 ≤ Real.log X :=
    (Real.le_log_iff_exp_le hXpos).2 hExp
  have hpow : (Real.log X) ^ D ≤ (Real.log X) ^ (D + 2 * B) :=
    pow_le_pow_right₀ hlog1 (by omega)
  have hshort : 2 * (Real.log X) ^ D < X :=
    (mul_le_mul_of_nonneg_left hpow (by norm_num)).trans_lt hbase.2
  have hRpos : 0 < paperArcRadius X D := by
    unfold paperArcRadius
    exact div_pos (pow_pos (lt_of_lt_of_le zero_lt_one hlog1) _) hXpos
  have hRhalf : paperArcRadius X D < (1 : ℝ) / 2 := by
    unfold paperArcRadius
    rw [div_lt_iff₀ hXpos]
    nlinarith
  exact ⟨hbase.1, hRpos, hRhalf, hbase.2⟩

/-- One indexed public arc is exactly its lifted beta integral. -/
theorem setIntegral_indexedRationalArc_eq_actualLifted
    {X : ℝ} {B D : ℕ} {h : ℤ}
    (hR0 : 0 ≤ paperArcRadius X D)
    (hRhalf : paperArcRadius X D < (1 : ℝ) / 2)
    (i : ↑(legalRationalPairs X B)) :
    (∫ α in indexedRationalArc X B D i,
      MAPHarmonicEndpoint.primeNormSqDensity X α * fourier (-h) α
        ∂AddCircle.haarAddCircle) =
      actualLiftedRationalArc X (paperArcRadius X D)
        i.1.1 i.1.2 h := by
  let t : ℝ := (i.1.2 : ℝ) / (i.1.1 : ℝ)
  have hparam := setIntegral_closedBall_eq_intervalIntegral_lift
    (t := t) hR0 hRhalf
    (fun α => MAPHarmonicEndpoint.primeNormSqDensity X α * fourier (-h) α)
  simpa [indexedRationalArc, rationalCenter, t,
    MAPHarmonicEndpoint.primeNormSqDensity, actualLiftedRationalArc] using hparam

/-- Exact public-to-lifted equality.  The left side is the manuscript's
normalized-Haar `majorCoefficient`; the right side is the finite collection
to which the pointwise MRT estimate is integrated. -/
theorem majorCoefficient_eq_actualLiftedPaperMajorContribution
    {X : ℝ} {B D : ℕ} {h : ℤ}
    (hX : 1 < X)
    (hRhalf : paperArcRadius X D < (1 : ℝ) / 2)
    (hgrowth : 2 * (Real.log X) ^ (D + 2 * B) < X) :
    MAPHarmonicEndpoint.majorCoefficient X B D h =
      actualLiftedPaperMajorContribution X B D h := by
  have hR0 : 0 ≤ paperArcRadius X D := by
    unfold paperArcRadius
    have hlog : 0 ≤ Real.log X := Real.log_nonneg hX.le
    positivity
  let f : UnitAddCircle → ℂ := fun α =>
    MAPHarmonicEndpoint.primeNormSqDensity X α * fourier (-h) α
  have hf : Integrable f AddCircle.haarAddCircle := by
    dsimp [f]
    exact (MAPHarmonicEndpoint.primeNormSqDensity_continuous X).mul
      (by fun_prop) |>.integrable_of_hasCompactSupport
        (HasCompactSupport.of_support_subset_isCompact isCompact_univ
          (Set.subset_univ _))
  have hmajorSet :
      (∫ α in PrimePairEndpoints.majorArcs X B D, f α
        ∂AddCircle.haarAddCircle) =
        ∑ i : ↑(legalRationalPairs X B),
          ∫ α in indexedRationalArc X B D i, f α
            ∂AddCircle.haarAddCircle := by
    rw [majorArcs_eq_finite_iUnion hX.le]
    apply MeasureTheory.integral_iUnion_fintype
    · intro i
      exact measurableSet_closedBall
    · exact indexedRationalArcs_pairwiseDisjoint_of_growth hX hgrowth
    · intro i
      exact hf.integrableOn
  have hpublic : MAPHarmonicEndpoint.majorCoefficient X B D h =
      ∫ α in PrimePairEndpoints.majorArcs X B D, f α
        ∂AddCircle.haarAddCircle := by
    unfold MAPHarmonicEndpoint.majorCoefficient
      MAPHarmonicEndpoint.circleCoefficient MAPHarmonicEndpoint.majorWeight
    change (∫ α : UnitAddCircle,
      (((PrimePairEndpoints.majorArcs X B D).indicator
        (fun a => ‖PrimePairEndpoints.primeExponentialSum X a‖ ^ 2) α : ℝ) : ℂ) *
        fourier (-h) α ∂AddCircle.haarAddCircle) = _
    have hindicator : (fun α : UnitAddCircle =>
        ((((PrimePairEndpoints.majorArcs X B D).indicator
          (fun a => ‖PrimePairEndpoints.primeExponentialSum X a‖ ^ 2) α : ℝ) : ℂ) *
          fourier (-h) α)) =
        (PrimePairEndpoints.majorArcs X B D).indicator f := by
      funext α
      by_cases hα : α ∈ PrimePairEndpoints.majorArcs X B D <;>
        simp [hα, f, MAPHarmonicEndpoint.primeNormSqDensity]
    rw [hindicator]
    exact integral_indicator (MAPHarmonicEndpoint.measurableSet_majorArcs X B D)
  rw [hpublic, hmajorSet]
  dsimp [f]
  unfold actualLiftedPaperMajorContribution actualLiftedMajorContribution
  calc
    (∑ i ∈ (legalRationalPairs X B).attach,
        ∫ α in indexedRationalArc X B D i,
          MAPHarmonicEndpoint.primeNormSqDensity X α * fourier (-h) α
            ∂AddCircle.haarAddCircle) =
        ∑ i ∈ (legalRationalPairs X B).attach,
          actualLiftedRationalArc X (paperArcRadius X D) i.1.1 i.1.2 h := by
      apply Finset.sum_congr rfl
      intro i hi
      exact setIntegral_indexedRationalArc_eq_actualLifted hR0 hRhalf i
    _ = ∑ i ∈ legalRationalPairs X B,
          actualLiftedRationalArc X (paperArcRadius X D) i.1 i.2 h := by
      exact Finset.sum_attach (legalRationalPairs X B)
        (fun i : ((q : ℕ) × ℕ) =>
          actualLiftedRationalArc X (paperArcRadius X D) i.1 i.2 h)
    _ = ∑ q ∈ Finset.Icc 1 (paperDenominatorCutoff X B),
          ∑ a ∈ reducedResidues q,
            actualLiftedRationalArc X (paperArcRadius X D) q a h := by
      unfold legalRationalPairs
      exact Finset.sum_sigma (Finset.Icc 1 (paperDenominatorCutoff X B))
        reducedResidues
        (fun i : ((q : ℕ) × ℕ) =>
          actualLiftedRationalArc X (paperArcRadius X D) i.1 i.2 h)

/-- End-to-end MAP-owned major-arc weld from the source-faithful pointwise
prime-polynomial input to the public normalized-Haar coefficient. -/
theorem norm_majorCoefficient_sub_modeledPaperMajorContribution_le_coarse
    {X E : ℝ} {B D : ℕ} {h : ℤ}
    (hX : 1 < X) (hE : 0 ≤ E)
    (hRhalf : paperArcRadius X D < (1 : ℝ) / 2)
    (hgrowth : 2 * (Real.log X) ^ (D + 2 * B) < X)
    (hpointwise : ∀ q a : ℕ, ∀ β : ℝ,
      1 ≤ q → (q : ℝ) ≤ (Real.log X) ^ B →
      a < q → a.Coprime q →
      |β| ≤ paperArcRadius X D →
      ‖PrimePairEndpoints.primeExponentialSum X
          (rationalCenter q a + (β : UnitAddCircle)) -
        primeMajorCoefficient q * dyadicAmplitude X β‖ ≤ E) :
    ‖MAPHarmonicEndpoint.majorCoefficient X B D h -
        modeledPaperMajorContribution X B D h‖ ≤
      ((paperDenominatorCutoff X B : ℕ) : ℝ) ^ 2 *
        (2 * paperArcRadius X D * (E * (2 * X + E))) := by
  rw [majorCoefficient_eq_actualLiftedPaperMajorContribution
    hX hRhalf hgrowth]
  exact norm_actualLiftedPaperMajorContribution_sub_modeled_le_coarse
    hX.le hE hpointwise

end

end MAPMajorArcPublicLiftBridge
