import MAPDynamicHBSourceV3

/-!
# Dynamic-order HB source decomposition

The legacy source assigned the eight raw terms of a fixed-order
Heath--Brown identity to the eight final MRT Type labels.  Those are
different indices.  This module keeps the arbitrary-order raw family intact,
takes its honest Cauchy loss, and places the aggregate into one harmless
bookkeeping cutoff slot.  Type-II/Type-d classification happens only later,
inside the exact dyadic classifier.
-/

namespace MAPDynamicHBSourceDecompositionV3

open scoped BigOperators
open MAPMRTCorollary53Source MAPMRTCorollary25Instantiation
open MAPFarSourceWeldScaffold MAPHBPerronSourceData
open MAPDynamicHBSourceV3

noncomputable section

/-- Exact dynamic-order analogue of `componentIntegral_map_le_hbBranches`.
The Cauchy factor is the actual raw HB order, not the number of final Type
labels. -/
theorem componentIntegral_map_le_dynamicHBBranches
    {X H beta eta delta : ℝ} (hX : 0 ≤ X) (hH : 0 ≤ H)
    (heta : 0 < eta) (hetaOne : eta ≤ 1) (hdelta : 0 < delta)
    (q₁ : ℕ) (component : OuterComponent) :
    componentIntegral X H 1 q₁ (mapMangoldtCoeff X) beta eta component ≤
      (hbOrder delta : ℝ) * ∑ branch : Fin (hbOrder delta),
        componentIntegral X H 1 q₁
          (dynamicHBBranchCoeff X (hbOrder delta) branch)
          beta eta component := by
  rw [show mapMangoldtCoeff X = fun n ↦
      ∑ branch : Fin (hbOrder delta),
        dynamicHBBranchCoeff X (hbOrder delta) branch n by
    funext n
    exact mapMangoldtCoeff_eq_sum_dynamicHBBranchCoeff hX
      (hbOrder_one hdelta) n]
  simpa using componentIntegral_finset_sum_le
    (Finset.univ : Finset (Fin (hbOrder delta)))
    (fun branch ↦ dynamicHBBranchCoeff X (hbOrder delta) branch)
    hX hH heta hetaOne component

/-- The exact dynamic HB family is aggregated into one cutoff bookkeeping
slot.  The slot name carries no Type-d meaning; the true Type labels are
assigned after dyadic expansion. -/
def dynamicHBSourceMassV3
    (p : Corollary53Input) (delta : ℝ)
    (component : OuterComponent) : FarSourceBranch → ℝ
  | .cutoff .typeD3 =>
      (hbOrder delta : ℝ) * ∑ branch : Fin (hbOrder delta),
        componentIntegral p.X p.H 1 p.q
          (dynamicHBBranchCoeff p.X (hbOrder delta) branch)
          p.beta p.eta component
  | .cutoff _ => 0
  | .smallRemainder => smallRemainderMass p component
  | .badEulerFactor => 0

theorem dynamicHBSourceMassV3_nonneg
    {p : Corollary53Input} {delta : ℝ}
    (hX : 0 ≤ p.X) (heta : 0 < p.eta) (hetaOne : p.eta ≤ 1)
    (component : OuterComponent) (branch : FarSourceBranch) :
    0 ≤ dynamicHBSourceMassV3 p delta component branch := by
  cases branch with
  | cutoff branch =>
      cases branch with
      | typeD3 =>
          exact mul_nonneg (by positivity) <|
            Finset.sum_nonneg fun i hi ↦
              componentIntegral_nonneg_of_admissibleGeometry
                hX heta hetaOne component
      | typeD1 => simp [dynamicHBSourceMassV3]
      | typeD2 => simp [dynamicHBSourceMassV3]
      | typeD4 => simp [dynamicHBSourceMassV3]
      | typeD5 => simp [dynamicHBSourceMassV3]
      | typeD6 => simp [dynamicHBSourceMassV3]
      | typeD7 => simp [dynamicHBSourceMassV3]
      | typeII => simp [dynamicHBSourceMassV3]
  | smallRemainder =>
      exact smallRemainderMass_nonneg hX heta hetaOne component
  | badEulerFactor => simp [dynamicHBSourceMassV3]

/-- Source-faithful dynamic replacement for the fixed-eight decomposition.
The `q₀>1` branch is unchanged; only the principal-factor HB split is
corrected. -/
theorem sourceBranchDecomposition_dynamicHBV3
    {p : Corollary53Input} {delta : ℝ}
    (hp : Corollary53Admissible 1 1 p) (hdelta : 0 < delta)
    (hf : p.f = mapMangoldtCoeff p.X) :
    SourceBranchDecomposition p (hbDecompositionError p)
      (dynamicHBSourceMassV3 p delta) := by
  have hH : 0 ≤ p.H := le_trans (by norm_num) hp.1
  have hX : 0 ≤ p.X := hH.trans hp.2.1
  have heta : 0 < p.eta := hp.2.2.2.2.1
  have hetaOne : p.eta ≤ 1 := hp.2.2.2.2.2.1
  intro q₀ q₁ hfac hq₀ hq₁ component
  by_cases hq₀one : q₀ = 1
  · subst q₀
    have hq₁eq : q₁ = p.q := by simpa using hfac
    subst q₁
    rw [hf]
    have hmain := componentIntegral_map_le_dynamicHBBranches
      (delta := delta) (beta := p.beta) hX hH heta hetaOne hdelta p.q component
    calc
      componentIntegral p.X p.H 1 p.q (mapMangoldtCoeff p.X)
          p.beta p.eta component ≤
          (hbOrder delta : ℝ) * ∑ branch : Fin (hbOrder delta),
            componentIntegral p.X p.H 1 p.q
              (dynamicHBBranchCoeff p.X (hbOrder delta) branch)
              p.beta p.eta component := hmain
      _ = dynamicHBSourceMassV3 p delta component (.cutoff .typeD3) := rfl
      _ ≤ ∑ branch : FarSourceBranch,
          dynamicHBSourceMassV3 p delta component branch := by
        apply Finset.single_le_sum
        · intro branch hbranch
          exact dynamicHBSourceMassV3_nonneg hX heta hetaOne component branch
        · simp
      _ = hbDecompositionError p component +
          ∑ branch : FarSourceBranch,
            dynamicHBSourceMassV3 p delta component branch := by
        simp [hbDecompositionError]
  · have hq₀gt : 1 < q₀ := lt_of_le_of_ne hq₀ (Ne.symm hq₀one)
    have hq₀le : q₀ ≤ p.q := by nlinarith
    have hq₁le : q₁ ≤ p.q := by nlinarith
    have hz : (q₀, q₁) ∈
        (modulusFactorizations p.q).filter (fun z ↦ 1 < z.1) := by
      simp [modulusFactorizations, hq₀, hq₁, hq₀le, hq₁le, hfac, hq₀gt]
    have hterm : componentIntegral p.X p.H q₀ q₁ p.f
        p.beta p.eta component ≤ smallRemainderMass p component := by
      unfold smallRemainderMass
      have hsingle := Finset.single_le_sum
        (s := (modulusFactorizations p.q).filter (fun z ↦ 1 < z.1))
        (f := fun z ↦ componentIntegral p.X p.H z.1 z.2 p.f
          p.beta p.eta component)
        (fun z hz' ↦ componentIntegral_nonneg_of_admissibleGeometry
          hX heta hetaOne component) hz
      simpa using hsingle
    calc
      componentIntegral p.X p.H q₀ q₁ p.f p.beta p.eta component ≤
          smallRemainderMass p component := hterm
      _ = dynamicHBSourceMassV3 p delta component .smallRemainder := rfl
      _ ≤ ∑ branch : FarSourceBranch,
          dynamicHBSourceMassV3 p delta component branch := by
        apply Finset.single_le_sum
        · intro branch hbranch
          exact dynamicHBSourceMassV3_nonneg hX heta hetaOne component branch
        · simp
      _ = hbDecompositionError p component +
          ∑ branch : FarSourceBranch,
            dynamicHBSourceMassV3 p delta component branch := by
        simp [hbDecompositionError]

end
end MAPDynamicHBSourceDecompositionV3

#print axioms MAPDynamicHBSourceDecompositionV3.componentIntegral_map_le_dynamicHBBranches
#print axioms MAPDynamicHBSourceDecompositionV3.sourceBranchDecomposition_dynamicHBV3
