import GuthMaynardHeathBrownCertified
import GuthMaynardHeathBrownIccIocEndpointAdapter
import GuthMaynardLemma118EnergyPacking

noncomputable section
namespace GuthMaynardEnergy115Actual
open CGLProofDAG GuthMaynardHeathBrownInterface GuthMaynardHeathBrownMajorant
open GuthMaynardHeathBrownIccIocEndpointAdapter GuthMaynardRatioKernelIdentity
open GuthMaynardLemma118

/-- The literal closed-block discrete second moment from certified Heath--Brown. -/
theorem discrete_second_moment {eta : ℝ} (heta : 0 < eta) :
    ∃ C T0 : ℝ, 0 < C ∧ 2 ≤ T0 ∧
      ∀ (T : ℝ) (M : ℕ) (W : Finset ℝ),
        T0 ≤ T → 1 ≤ M → OneSeparated W →
        ContainedInIntervalOfLength W T →
        ratioKernelMoment 2 M W ≤
          C * Real.rpow T eta * heathBrownShape T M W := by
  obtain ⟨C,T0,hC,hT0,hbound⟩ :=
    GuthMaynardHeathBrownCertified.heathBrownOneCoefficientCore eta heta
  refine ⟨C,T0,hC,hT0,?_⟩
  intro T M W hT hM hsep hcontained
  have hh := hbound T M W hT hM hsep hcontained
  rw [differenceQuadraticForm_one_eq_ratioKernelSecondMoment M W hM] at hh
  simpa only [ratioKernelMoment, Finset.product_eq_sprod, Finset.sum_product] using hh

end GuthMaynardEnergy115Actual
#print axioms GuthMaynardEnergy115Actual.discrete_second_moment
