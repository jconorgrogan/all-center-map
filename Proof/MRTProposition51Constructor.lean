import MRTProposition51FirstAnalytic

/-!
# Constructor for the literal half-range MRT Proposition 5.1

This module closes the easy/hard case split at the source theorem interface.
Its sole premise is the final hard-regime estimate obtained after equation
(72); no packet, van der Corput, or equation-(81)--(84) detail is hidden here.
-/

namespace MAPMRTProposition51Constructor

open MeasureTheory Set
open MAPMRTCorollary53Source
open MAPMRTProposition51Source
open MAPMRTProposition51FirstAnalytic

noncomputable section

theorem proposition51I_nonneg_of_admissible
    {cBetaEta cEta : ℝ} {p : Proposition51Input}
    (hp : Proposition51Admissible cBetaEta cEta p) :
    0 ≤ proposition51I p.X p.H p.f p.beta p.eta := by
  have hX : 0 ≤ p.X := by linarith [hp.1, hp.2.1]
  unfold proposition51I untwistedComponentIntegral
  apply Finset.sum_nonneg
  intro component hcomponent
  apply intervalIntegral.integral_nonneg
    (componentEndpoints_mono hX hp.2.2.1 hp.2.2.2.1 component)
  intro t ht
  exact sq_nonneg _

theorem ordinaryError_nonneg
    {X H beta eta : ℝ} {f : ℕ → ℂ} :
    0 ≤ ordinaryError X H f beta eta := by
  unfold ordinaryError
  apply mul_nonneg
  · positivity
  · unfold ordinarySlidingMass
    exact integral_nonneg (fun x ↦ sq_nonneg _)

/-- Inhabit the exact source proposition once the post-(72) hard estimate is
available uniformly.  The easy regimes are discharged by the compiled
Gallagher reduction. -/
theorem mrtProposition51_of_hard_branch
    {cBetaEta cEta Chard : ℝ}
    (hChard : 0 < Chard)
    (hHard : ∀ (p : Proposition51Input),
      Proposition51Admissible cBetaEta cEta p →
      1 < |p.beta| * p.H → p.eta < 1 / 100 →
      proposition51Energy p ≤ Chard *
        (1 / (|p.beta| ^ 2 * p.H ^ 2) *
            proposition51I p.X p.H p.f p.beta p.eta +
          ordinaryError p.X p.H p.f p.beta p.eta)) :
    MRTProposition51 cBetaEta cEta := by
  refine ⟨Chard + 2560000, by positivity, ?_⟩
  intro p hp
  have hI : 0 ≤ proposition51I p.X p.H p.f p.beta p.eta :=
    proposition51I_nonneg_of_admissible hp
  have hscale : 0 ≤ 1 / (|p.beta| ^ 2 * p.H ^ 2) := by positivity
  have hmain : 0 ≤ 1 / (|p.beta| ^ 2 * p.H ^ 2) *
      proposition51I p.X p.H p.f p.beta p.eta := mul_nonneg hscale hI
  have herr : 0 ≤ ordinaryError p.X p.H p.f p.beta p.eta := ordinaryError_nonneg
  have hrhs : 0 ≤ 1 / (|p.beta| ^ 2 * p.H ^ 2) *
        proposition51I p.X p.H p.f p.beta p.eta +
      ordinaryError p.X p.H p.f p.beta p.eta := add_nonneg hmain herr
  by_cases hhard : 1 < |p.beta| * p.H ∧ p.eta < 1 / 100
  · have hh := hHard p hp hhard.1 hhard.2
    exact hh.trans (mul_le_mul_of_nonneg_right
      (by linarith : Chard ≤ Chard + 2560000) hrhs)
  · have heasy : |p.beta| * p.H ≤ 1 ∨ 1 / 100 ≤ p.eta := by
      rcases not_and_or.mp hhard with hsmall | heta
      · exact Or.inl (le_of_not_gt hsmall)
      · exact Or.inr (le_of_not_gt heta)
    have he := proposition51_easy_regime p.X p.H p.beta p.eta p.f
      (lt_of_lt_of_le zero_lt_one hp.1) hp.2.2.2.2.2.2.1 hp.2.2.1.le heasy
    have herr_le : 2560000 * ordinaryError p.X p.H p.f p.beta p.eta ≤
        (Chard + 2560000) *
          (1 / (|p.beta| ^ 2 * p.H ^ 2) *
              proposition51I p.X p.H p.f p.beta p.eta +
            ordinaryError p.X p.H p.f p.beta p.eta) := by
      nlinarith [mul_nonneg hChard.le hrhs, mul_nonneg (by norm_num : (0 : ℝ) ≤ 2560000) hmain]
    exact he.trans herr_le

#print axioms MAPMRTProposition51Constructor.mrtProposition51_of_hard_branch

end
end MAPMRTProposition51Constructor
