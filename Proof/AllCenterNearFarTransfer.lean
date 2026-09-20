import AllCenterApertureTransfer
import MajorArcMaskGeometry

/-!
# Exact near/far exhaustion behind manuscript Theorem 1.1

This module isolates the literal outputs of the two analytic branches in
paper equations (3.2) and (3.3)--(3.7), and proves that they imply the
canonical-aperture estimate and hence `AllCenterLocalMAP`.

It does not assert Gallagher--Plancherel, Proposition 2.2, or any MRT theorem.
Those inputs must inhabit the two branch estimates below.
-/

namespace MAPAllCenterNearFarTransfer

open MeasureTheory Metric Set
open PrimePairEndpoints MAPHarmonicEndpoint MAPMajorArcWeld
open MAPAllCenterApertureTransfer

noncomputable section

/-- Centers within the paper's `2R/H_*` near-rational threshold. -/
def innerRationalCollars
    (epsilon X : ℝ) (B Cc : ℕ) : Set UnitAddCircle :=
  {center | ∃ q a : ℕ,
    1 ≤ q ∧
    (q : ℝ) ≤ (Real.log X) ^ B ∧
    a < q ∧ a.Coprime q ∧
    dist center (rationalCenter q a) ≤
      2 * (Real.log X) ^ Cc / baseAperture epsilon X}

/-- The paper's global wide collar `W`, of radius `4R/H_*`. -/
def outerRationalCollars
    (epsilon X : ℝ) (B Cc : ℕ) : Set UnitAddCircle :=
  {alpha | ∃ q a : ℕ,
    1 ≤ q ∧
    (q : ℝ) ≤ (Real.log X) ^ B ∧
    a < q ∧ a.Coprime q ∧
    dist alpha (rationalCenter q a) ≤
      4 * (Real.log X) ^ Cc / baseAperture epsilon X}

/-- If a center lies in the inner collar, its complete canonical target arc is
contained in the wide collar.  This is the exact geometric step used between
(3.1) and (3.2). -/
theorem centeredArc_subset_outerRationalCollars
    {epsilon X : ℝ} {B Cc : ℕ} (hX : 1 ≤ X)
    (hlog : 1 ≤ Real.log X) {center : UnitAddCircle}
    (hcenter : center ∈ innerRationalCollars epsilon X B Cc) :
    centeredArc (baseAperture epsilon X) center ⊆
      outerRationalCollars epsilon X B Cc := by
  rintro alpha halpha
  rcases hcenter with ⟨q, a, hq, hqcap, ha, hacop, hdistCenter⟩
  refine ⟨q, a, hq, hqcap, ha, hacop, ?_⟩
  have hHpos : 0 < baseAperture epsilon X :=
    baseAperture_pos (zero_lt_one.trans_le hX)
  have hR : 1 ≤ (Real.log X) ^ Cc := one_le_pow₀ hlog
  have halphaDist :
      dist alpha center ≤ (2 * baseAperture epsilon X)⁻¹ := by
    simpa [centeredArc] using halpha
  have htri :
      dist alpha (rationalCenter q a) ≤
        dist alpha center + dist center (rationalCenter q a) :=
    dist_triangle _ _ _
  have hhalf :
      (2 * baseAperture epsilon X)⁻¹ ≤
        2 * (Real.log X) ^ Cc / baseAperture epsilon X := by
    have hinv : 0 < (baseAperture epsilon X)⁻¹ := inv_pos.mpr hHpos
    rw [mul_inv_rev]
    norm_num
    have : (1 / 2 : ℝ) ≤ 2 * (Real.log X) ^ Cc := by nlinarith
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (mul_le_mul_of_nonneg_right this hinv.le)
  calc
    dist alpha (rationalCenter q a) ≤
        dist alpha center + dist center (rationalCenter q a) := htri
    _ ≤ (2 * baseAperture epsilon X)⁻¹ +
          2 * (Real.log X) ^ Cc / baseAperture epsilon X :=
      add_le_add halphaDist hdistCenter
    _ ≤ 2 * (Real.log X) ^ Cc / baseAperture epsilon X +
          2 * (Real.log X) ^ Cc / baseAperture epsilon X :=
      add_le_add hhalf le_rfl
    _ = 4 * (Real.log X) ^ Cc / baseAperture epsilon X := by ring

/-- The two literal analytic outputs required after parameter selection:

* `(3.2)`: a global minor-arc bound on the wide rational collars;
* `(3.3)--(3.7)`: a full local bound for every center outside the inner
  rational collars.

The same `B,D,Cc,C,X₀` serve both branches, making cutoff synchronization and
quantifier order explicit. -/
def CanonicalNearFarEstimates : Prop :=
  ∀ A epsilon : ℝ, 0 < A → 0 < epsilon →
    ∃ B D Cc : ℕ, ∃ C X₀ : ℝ,
      0 < C ∧ 2 ≤ X₀ ∧
      ∀ X : ℝ, X₀ ≤ X →
        1 ≤ Real.log X ∧
        (∫ alpha in outerRationalCollars epsilon X B Cc ∩
              minorArcs X B D,
            ‖primeExponentialSum X alpha‖ ^ 2
              ∂AddCircle.haarAddCircle) ≤
          C * X * Real.rpow (Real.log X) (-A) ∧
        ∀ center : UnitAddCircle,
          center ∉ innerRationalCollars epsilon X B Cc →
          (∫ alpha in centeredArc (baseAperture epsilon X) center,
              ‖primeExponentialSum X alpha‖ ^ 2
                ∂AddCircle.haarAddCircle) ≤
            C * X * Real.rpow (Real.log X) (-A)

/-- Near/far exhaustion at the canonical aperture.  Positivity is used twice:
to restrict the global near-collar integral to one target arc, and to restrict
the full far-arc integral to its minor-arc part. -/
theorem canonicalScaleLocalMAP_of_nearFarEstimates
    (hNF : CanonicalNearFarEstimates) : BaseApertureAllCenterEstimate := by
  intro A epsilon hA hepsilon
  obtain ⟨B, D, Cc, C, X₀, hC, hX₀, hest⟩ := hNF A epsilon hA hepsilon
  refine ⟨B, D, C, X₀, hC, hX₀, ?_⟩
  intro X hXX₀ center
  obtain ⟨hlog, hnear, hfar⟩ := hest X hXX₀
  have hX : 1 ≤ X := (by norm_num : (1 : ℝ) ≤ 2).trans (hX₀.trans hXX₀)
  let f : UnitAddCircle → ℝ := fun alpha ↦
    ‖primeExponentialSum X alpha‖ ^ 2
  have hf : Integrable f AddCircle.haarAddCircle :=
    normSq_primeExponentialSum_integrable X
  rw [FejerMAPInterfaceWeld.integral_minorWeight_centeredArc]
  by_cases hcenter : center ∈ innerRationalCollars epsilon X B Cc
  · have harc := centeredArc_subset_outerRationalCollars hX hlog hcenter
    have hsubset :
        centeredArc (baseAperture epsilon X) center ∩ minorArcs X B D ⊆
          outerRationalCollars epsilon X B Cc ∩ minorArcs X B D :=
      Set.inter_subset_inter harc Set.Subset.rfl
    exact (MeasureTheory.setIntegral_mono_set hf.integrableOn
      (Filter.Eventually.of_forall (fun _ ↦ sq_nonneg _))
      (Filter.Eventually.of_forall hsubset)).trans hnear
  · have hsubset :
        centeredArc (baseAperture epsilon X) center ∩ minorArcs X B D ⊆
          centeredArc (baseAperture epsilon X) center := Set.inter_subset_left
    exact (MeasureTheory.setIntegral_mono_set hf.integrableOn
      (Filter.Eventually.of_forall (fun _ ↦ sq_nonneg _))
      (Filter.Eventually.of_forall hsubset)).trans (hfar center hcenter)

/-- Final exact connector from the two branch estimates to the public local
MAP statement. -/
theorem allCenterLocalMAP_of_nearFarEstimates
    (hNF : CanonicalNearFarEstimates) : AllCenterLocalMAP :=
  allCenterLocalMAP_of_baseAperture
    (canonicalScaleLocalMAP_of_nearFarEstimates hNF)

end
end MAPAllCenterNearFarTransfer

#print axioms MAPAllCenterNearFarTransfer.allCenterLocalMAP_of_nearFarEstimates
