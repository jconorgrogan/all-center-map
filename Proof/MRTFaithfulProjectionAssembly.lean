import MRTFaithfulEquation79Duality
import MRTProposition51SmoothDualityWeld
import MRTFaithfulHighProjection
import MRTFaithfulLowEstimate
import MAPLambdaHardRangeConnector

/-! Source-supported finite sums and the faithful projection assembly. -/
namespace MAPMRTFaithfulProjectionAssembly
open MeasureTheory Set
open MAPMRTCorollary53Source MAPMRTProposition51Source MAPMRTProposition51HardBranch
open MAPMRTFaithfulSmoothCutoff MAPMRTFaithfulEquation79Duality
noncomputable section

theorem critical_projection_sum_Ioc_eq_Icc
    {X : ℝ} {f : ℕ → ℂ} (P : ℝ → ℂ)
    (hX : 0 ≤ X)
    (hf : ∀ n : ℕ, ¬(X < (n : ℝ) ∧ (n : ℝ) ≤ 2 * X) → f n = 0) :
    (∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊, f n * (Real.sqrt n : ℂ)⁻¹ * P (Real.log n - Real.log X)) =
      ∑ n ∈ Finset.Icc 1 ⌊2 * X⌋₊, f n * (Real.sqrt n : ℂ)⁻¹ * P (Real.log n - Real.log X) := by
  apply Finset.sum_subset
  · intro n hn
    simp only [Finset.mem_Ioc, Finset.mem_Icc] at hn ⊢
    omega
  · intro n hn hnot
    have hnle : n ≤ ⌊X⌋₊ := by
      simp only [Finset.mem_Icc] at hn
      simp only [Finset.mem_Ioc] at hnot
      omega
    have hnreal : (n : ℝ) ≤ X :=
      (show (n : ℝ) ≤ (⌊X⌋₊ : ℝ) by exact_mod_cast hnle).trans (Nat.floor_le hX)
    have hz := hf n (fun hc ↦ (not_lt_of_ge hnreal) hc.1)
    simp [hz]

theorem faithful_mediumProjection_Ioc_sq_le
    {X H beta eta : ℝ} {f : ℕ → ℂ} {g : ℝ → ℂ}
    (hX : 0 < X) (hH : 1 ≤ H) (hHalf : H ≤ X / 2)
    (hbeta : beta ≠ 0) (hhard : 1 < |beta| * H)
    (heta : 0 < eta) (hetaSmall : eta < 1 / 100)
    (hf : ∀ n : ℕ, ¬(X < (n : ℝ) ∧ (n : ℝ) ≤ 2 * X) → f n = 0)
    (hg : Integrable g) (hg2 : Integrable (fun x : ℝ ↦ ‖g x‖ ^ 2))
    (hgOne : (∫ x : ℝ, ‖g x‖ ^ 2) ≤ 1)
    (hgSupport : ∀ x, x ∉ Icc (X / 2) (4 * X) → g x = 0) :
    ‖∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊, f n * (Real.sqrt n : ℂ)⁻¹ *
      mediumFrequencyProjection X beta eta faithfulCutoff
        (logarithmicDualFunction X H beta faithfulCutoff g)
        (Real.log n - Real.log X)‖ ^ 2 ≤
      (216 * MAPMRTFaithfulEquation81Weld.faithfulEquation82Constant / beta ^ 2) *
        proposition51I X H f beta eta := by
  rw [critical_projection_sum_Ioc_eq_Icc _ hX.le hf]
  exact faithful_mediumProjectedSum_sq_le hX hH hHalf hbeta hhard heta hetaSmall hg
    ((memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).2 hg2) hgOne hgSupport

open MAPMRTFaithfulHighProjection MAPMRTFaithfulLowEstimate
open MAPMRTProposition51SmoothDualityWeld MAPMRTProposition51Constructor

def faithfulMediumConstant : ℝ := 216 * MAPMRTFaithfulEquation81Weld.faithfulEquation82Constant
def faithfulLowProjectionConstant : ℝ := 260 * faithfulLowConstant ^ 2
def faithfulProjectionTotalConstant : ℝ :=
  faithfulMediumConstant + faithfulLowProjectionConstant + faithfulHighProjectionConstant + 1
def faithfulProposition51Constant : ℝ := 300 * faithfulProjectionTotalConstant

theorem faithfulMediumConstant_nonneg : 0 ≤ faithfulMediumConstant := by
  exact mul_nonneg (by norm_num) MAPMRTFaithfulEquation81Weld.faithfulEquation82Constant_nonneg

theorem faithfulLowProjectionConstant_nonneg : 0 ≤ faithfulLowProjectionConstant := by
  unfold faithfulLowProjectionConstant
  positivity

theorem faithfulHighProjectionConstant_nonneg : 0 ≤ faithfulHighProjectionConstant := by
  unfold faithfulHighProjectionConstant
  positivity

theorem faithfulProposition51Constant_pos : 0 < faithfulProposition51Constant := by
  have hm := faithfulMediumConstant_nonneg
  have hl := faithfulLowProjectionConstant_nonneg
  have hh := faithfulHighProjectionConstant_nonneg
  unfold faithfulProposition51Constant faithfulProjectionTotalConstant
  positivity

theorem norm_add_three_sq_le (a b c : ℂ) :
    ‖a + b + c‖ ^ 2 ≤ 3 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2) := by
  have ht : ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ :=
    (norm_add_le _ _).trans (add_le_add (norm_add_le a b) le_rfl)
  have hs := pow_le_pow_left₀ (norm_nonneg _) ht 2
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), sq_nonneg (‖a‖ - ‖c‖), sq_nonneg (‖b‖ - ‖c‖)]

/-- The hard branch of MRT Proposition 5.1, now proved for the actual faithful
cutoff and dyadically supported coefficients.  Equation (72) is used once. -/
theorem faithful_proposition51_hard_bound
    {cBetaEta cEta : ℝ} {p : Proposition51Input}
    (hp : Proposition51Admissible cBetaEta cEta p)
    (hhard : 1 < |p.beta| * p.H) (hetaSmall : p.eta < 1 / 100) :
    proposition51Energy p ≤ faithfulProposition51Constant *
      (1 / (|p.beta| ^ 2 * p.H ^ 2) * proposition51I p.X p.H p.f p.beta p.eta +
        ordinaryError p.X p.H p.f p.beta p.eta) := by
  have hI := proposition51I_nonneg_of_admissible hp
  rcases hp with ⟨hH, hHalf, heta, hetaOne, hbetaEta, hetaCap, hbeta, hf⟩
  have hX : 0 < p.X := by linarith
  have hHpos : 0 < p.H := lt_of_lt_of_le zero_lt_one hH
  obtain ⟨g, hg, hg2, hgSupport, hgOne, harc⟩ :=
    smoothEquation72_dual_witness p.f hX hHpos hHalf
  let G := logarithmicDualFunction p.X p.H p.beta faithfulCutoff g
  let L := ∑ n ∈ Finset.Ioc ⌊p.X⌋₊ ⌊2 * p.X⌋₊, p.f n * (Real.sqrt n : ℂ)⁻¹ *
    lowFrequencyProjection p.X p.beta p.eta faithfulCutoff G (Real.log n - Real.log p.X)
  let M := ∑ n ∈ Finset.Ioc ⌊p.X⌋₊ ⌊2 * p.X⌋₊, p.f n * (Real.sqrt n : ℂ)⁻¹ *
    mediumFrequencyProjection p.X p.beta p.eta faithfulCutoff G (Real.log n - Real.log p.X)
  let U := ∑ n ∈ Finset.Ioc ⌊p.X⌋₊ ⌊2 * p.X⌋₊, p.f n * (Real.sqrt n : ℂ)⁻¹ *
    highFrequencyProjection p.X p.beta p.eta faithfulCutoff G (Real.log n - Real.log p.X)
  let E := (p.eta + 1 / (|p.beta| * p.H)) ^ 2 * ordinarySlidingMass p.X p.H p.f
  let T := (1 / p.beta ^ 2) * proposition51I p.X p.H p.f p.beta p.eta
  have hmass : 0 ≤ ordinarySlidingMass p.X p.H p.f := integral_nonneg fun x ↦ sq_nonneg _
  have hE : 0 ≤ E := mul_nonneg (sq_nonneg _) hmass
  have hT : 0 ≤ T := mul_nonneg (by positivity) hI
  have hL : ‖L‖ ^ 2 ≤ faithfulLowProjectionConstant * E := by
    simpa only [L, G, MAPFinishP51Projection.lowProjectionEnergy, faithfulLowProjectionConstant, E,
      mul_assoc] using faithful_lowProjectionEnergy_le
        (f := p.f) hX hHpos hHalf hbeta heta hg hg2 hgOne hgSupport
  have hM : ‖M‖ ^ 2 ≤ faithfulMediumConstant * T := by
    have hm := faithful_mediumProjection_Ioc_sq_le
      hX hH hHalf hbeta hhard heta hetaSmall hf hg hg2 hgOne hgSupport
    simpa [M, G, faithfulMediumConstant, T, div_eq_mul_inv, mul_assoc] using hm
  have hUraw := faithful_highProjectedSum_sq_le (f := p.f)
    hX hH hHalf hbeta hhard heta hg
    ((memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).2 hg2) hgOne hgSupport
  have hEta : p.eta ^ 2 ≤ (p.eta + 1 / (|p.beta| * p.H)) ^ 2 := by
    have hi : 0 ≤ 1 / (|p.beta| * p.H) := by positivity
    exact pow_le_pow_left₀ heta.le (le_add_of_nonneg_right hi) 2
  have hU : ‖U‖ ^ 2 ≤ faithfulHighProjectionConstant * E := by
    change ‖U‖ ^ 2 ≤ faithfulHighProjectionConstant * p.eta ^ 2 * ordinarySlidingMass p.X p.H p.f at hUraw
    exact hUraw.trans (by
      dsimp [E]
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hEta faithfulHighProjectionConstant_nonneg) hmass)
  have hsplit : (∑ n ∈ Finset.Ioc ⌊p.X⌋₊ ⌊2 * p.X⌋₊,
      p.f n * (Real.sqrt n : ℂ)⁻¹ * G (Real.log n - Real.log p.X)) = L + M + U :=
    critical_sum_eq_low_add_medium_add_high p.X p.beta p.eta faithfulCutoff G _ p.f
  change proposition51Energy p ≤ 100 / p.H ^ 2 * ‖∑ n ∈ Finset.Ioc ⌊p.X⌋₊ ⌊2 * p.X⌋₊,
    p.f n * (Real.sqrt n : ℂ)⁻¹ * G (Real.log n - Real.log p.X)‖ ^ 2 at harc
  rw [hsplit] at harc
  have hcm : faithfulMediumConstant ≤ faithfulProjectionTotalConstant := by
    unfold faithfulProjectionTotalConstant
    linarith [faithfulLowProjectionConstant_nonneg, faithfulHighProjectionConstant_nonneg]
  have hce : faithfulLowProjectionConstant + faithfulHighProjectionConstant ≤ faithfulProjectionTotalConstant := by
    unfold faithfulProjectionTotalConstant
    linarith [faithfulMediumConstant_nonneg]
  have hraw : ‖L + M + U‖ ^ 2 ≤ 3 * faithfulProjectionTotalConstant * (T + E) := by
    calc
      _ ≤ 3 * (‖L‖ ^ 2 + ‖M‖ ^ 2 + ‖U‖ ^ 2) := norm_add_three_sq_le _ _ _
      _ ≤ 3 * (faithfulLowProjectionConstant * E + faithfulMediumConstant * T + faithfulHighProjectionConstant * E) :=
        mul_le_mul_of_nonneg_left (add_le_add (add_le_add hL hM) hU) (by norm_num)
      _ = 3 * (faithfulMediumConstant * T + (faithfulLowProjectionConstant + faithfulHighProjectionConstant) * E) := by ring
      _ ≤ 3 * (faithfulProjectionTotalConstant * T + faithfulProjectionTotalConstant * E) :=
        mul_le_mul_of_nonneg_left
          (add_le_add (mul_le_mul_of_nonneg_right hcm hT) (mul_le_mul_of_nonneg_right hce hE)) (by norm_num)
      _ = _ := by ring
  calc
    _ ≤ 100 / p.H ^ 2 * ‖L + M + U‖ ^ 2 := harc
    _ ≤ 100 / p.H ^ 2 * (3 * faithfulProjectionTotalConstant * (T + E)) :=
      mul_le_mul_of_nonneg_left hraw (by positivity)
    _ = _ := by
      unfold faithfulProposition51Constant T E ordinaryError
      rw [sq_abs]
      field_simp [hHpos.ne', hbeta]
      <;> ring

/-- The full source Proposition 5.1 follows by the already-proved easy/hard split. -/
theorem faithful_mrtProposition51 (cBetaEta cEta : ℝ) : MRTProposition51 cBetaEta cEta := by
  apply mrtProposition51_of_hard_branch faithfulProposition51Constant_pos
  intro p hp hhard hetaSmall
  exact faithful_proposition51_hard_bound hp hhard hetaSmall

/-- The exact MAP-only hard-range root consumed by the endpoint. -/
theorem faithful_mapLambdaCorollary53HardRange :
    MAPSubmissionRouteOptimizer.MAPLambdaCorollary53HardRange := by
  refine ⟨faithfulProposition51Constant, faithfulProposition51Constant_pos, ?_⟩
  intro X H beta eta q a
  dsimp only
  intro hp hHalf hhard hetaSmall
  let p := mapCorollary53Input X H q a beta eta
  have hp51 := MAPMRTProposition51Supported.twistedProposition51Input_admissible hp hHalf
  have hbound := faithful_proposition51_hard_bound hp51 hhard hetaSmall
  rw [MAPMRTProposition51Supported.proposition51Energy_twisted_eq_sourceEnergy] at hbound
  apply hbound.trans
  apply mul_le_mul_of_nonneg_left _ faithfulProposition51Constant_pos.le
  have hmain := MAPMRTProposition51Supported.proposition51_main_le_stationaryMain
    MAPMRTLemma29Proof.mrtLemma29Supported_proof hp
  simpa [MAPMRTProposition51Supported.twistedProposition51Input,
    MAPMRTProposition51Supported.ordinaryError_additiveTwist] using
      add_le_add_right hmain (ordinaryError X H (additiveTwist q a p.f) beta eta)

#print axioms faithful_proposition51_hard_bound
#print axioms faithful_mrtProposition51
#print axioms faithful_mapLambdaCorollary53HardRange
#print axioms faithful_mediumProjection_Ioc_sq_le
end
end MAPMRTFaithfulProjectionAssembly
