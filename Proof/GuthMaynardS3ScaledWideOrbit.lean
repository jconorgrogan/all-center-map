import GuthMaynardS3ScaledWideProfile
import GuthMaynardS3NormalizedBump

open scoped BigOperators Real FourierTransform ContDiff
open MeasureTheory

noncomputable section
namespace GuthMaynardS3ScaledWideOrbit

open GuthMaynardJIteration
open GuthMaynardS3ScaledWideProfile
open GuthMaynardS3WideProfile
open GuthMaynardS3LiteralProfileFourier

/-- The finite normalized smoothing orbit of the scaled wide profile. -/
def scaledWideOrbit
    (B T delta : ℝ) (hdeltaB : 0 < Real.rpow T delta)
    (W : Finset ℝ) (n : ℕ) : ℝ → ℝ :=
  affineSmoothingIterate T
    (sourceBumpNormalized (Real.rpow T delta) hdeltaB) n
    (scaledWideProfile B W)

theorem rpow_delta_pos
    {T delta : ℝ} (hT : 1 ≤ T) (hdelta : 0 ≤ delta) :
    0 < Real.rpow T delta := by
  exact Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hT) _

theorem rpow_delta_one_le
    {T delta : ℝ} (hT : 1 ≤ T) (hdelta : 0 ≤ delta) :
    1 ≤ Real.rpow T delta := by
  exact Real.one_le_rpow hT hdelta

theorem scaledWideOrbit_admissible
    {B T delta : ℝ} (hT : 1 ≤ T) (hB4 : (4 : ℝ) ≤ B)
    (hBT : B ≤ T) (hdelta : 0 ≤ delta) (W : Finset ℝ) (n : ℕ) :
    SourceAdmissibleProfile T (4 * (W.card : ℝ) ^ 2)
      ((7 : ℝ) / 4 + (n : ℝ) *
        ((2 * Real.rpow T delta) / T))
      (scaledWideOrbit B T delta (rpow_delta_pos hT hdelta) W n) := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hRpos : 0 < Real.rpow T delta := rpow_delta_pos hT hdelta
  have hkernel : SourceSmoothingKernel (2 * Real.rpow T delta)
      (sourceBumpNormalized (Real.rpow T delta) hRpos) :=
    sourceBumpNormalized_sourceSmoothingKernel hRpos
      (rpow_delta_one_le hT hdelta)
  have hf := scaledWideProfile_sourceAdmissibleProfile hT hB4 hBT W
  exact sourceAdmissibleProfile_affineSmoothingIterate hTpos
    (sourceBumpNormalized (Real.rpow T delta) hRpos)
    (scaledWideProfile B W) hf hkernel n

theorem scaledWideOrbit_fourier_bound
    {B T delta : ℝ} (hT : 1 ≤ T) (hB4 : (4 : ℝ) ≤ B)
    (hBT : B ≤ T) (hdelta : 0 ≤ delta) (W : Finset ℝ) (n q : ℕ)
    {eta : ℝ} (heta : 0 < eta) {z : ℝ} (hz : z ≠ 0) :
    ‖FourierTransform.fourier
      (fun u : ℝ =>
        (scaledWideOrbit B T delta (rpow_delta_pos hT hdelta) W n u : ℂ)) z‖ ≤
      (4 : ℝ) ^ q * lemma84SmoothingFourierConstant q * T ^ eta *
        (T / |z|) ^ q * (4 * (W.card : ℝ) ^ 2) := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hRpos : 0 < Real.rpow T delta := rpow_delta_pos hT hdelta
  have hR1 : 1 ≤ Real.rpow T delta := rpow_delta_one_le hT hdelta
  have hkernel : SourceSmoothingKernel (2 * Real.rpow T delta)
      (sourceBumpNormalized (Real.rpow T delta) hRpos) :=
    sourceBumpNormalized_sourceSmoothingKernel hRpos hR1
  induction n with
  | zero =>
      exact scaledWideProfile_fourier_bound hT hB4 hBT W q heta hz
  | succ n ih =>
      have hprev := scaledWideOrbit_admissible hT hB4 hBT hdelta W n
      have hone := norm_fourier_ofReal_affineSmoothing_le hTpos
        (sourceBumpNormalized (Real.rpow T delta) hRpos)
        (scaledWideOrbit B T delta hRpos W n)
        hkernel.nonneg hkernel.mass_le_one hkernel.integrable
        hprev.integrable hkernel.continuous hprev.continuous z
      have hstep := hone.trans ih
      simpa only [scaledWideOrbit, affineSmoothingIterate] using hstep

theorem scaledWideOrbit_L1_L2_contractions
    {B T delta : ℝ} (hT : 1 ≤ T) (hB4 : (4 : ℝ) ≤ B)
    (hBT : B ≤ T) (hdelta : 0 ≤ delta) (W : Finset ℝ) (n : ℕ) :
    (∫ u : ℝ,
      scaledWideOrbit B T delta (rpow_delta_pos hT hdelta) W n u) ≤
        ∫ u : ℝ, scaledWideProfile B W u ∧
    (∫ u : ℝ,
      scaledWideOrbit B T delta (rpow_delta_pos hT hdelta) W n u ^ 2) ≤
        ∫ u : ℝ, scaledWideProfile B W u ^ 2 := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hRpos : 0 < Real.rpow T delta := rpow_delta_pos hT hdelta
  have hR1 : 1 ≤ Real.rpow T delta := rpow_delta_one_le hT hdelta
  have hkernel : SourceSmoothingKernel (2 * Real.rpow T delta)
      (sourceBumpNormalized (Real.rpow T delta) hRpos) :=
    sourceBumpNormalized_sourceSmoothingKernel hRpos hR1
  induction n with
  | zero => exact ⟨le_rfl, le_rfl⟩
  | succ n ih =>
      have hprev := scaledWideOrbit_admissible hT hB4 hBT hdelta W n
      have hstepL1 := integral_affineSmoothing_le_of_integrable
        hTpos (sourceBumpNormalized (Real.rpow T delta) hRpos)
        (scaledWideOrbit B T delta hRpos W n) hprev.nonneg
        hkernel.mass_le_one hkernel.integrable hprev.integrable
      have hstepL2 := integral_sq_affineSmoothing_le_one_of_integrable
        hTpos (sourceBumpNormalized (Real.rpow T delta) hRpos)
        (scaledWideOrbit B T delta hRpos W n) hkernel.nonneg hprev.nonneg
        hkernel.mass_le_one hkernel.integrable hprev.integrable
        hprev.squareIntegrable
      constructor
      · exact le_trans (by
          simpa only [scaledWideOrbit, affineSmoothingIterate] using hstepL1) ih.1
      · exact le_trans (by
          simpa only [scaledWideOrbit, affineSmoothingIterate] using hstepL2) ih.2

theorem scaledWideOrbit_L1_L2_quarter_original
    {B T delta : ℝ} (hT : 1 ≤ T) (hB4 : (4 : ℝ) ≤ B)
    (hBT : B ≤ T) (hdelta : 0 ≤ delta) (W : Finset ℝ) (n : ℕ) :
    (∫ u : ℝ,
      scaledWideOrbit B T delta (rpow_delta_pos hT hdelta) W n u) ≤
        (1 / 4 : ℝ) * ∫ u : ℝ, |wideProfile B W u| ∧
    (∫ u : ℝ,
      scaledWideOrbit B T delta (rpow_delta_pos hT hdelta) W n u ^ 2) ≤
        (1 / 4 : ℝ) * ∫ u : ℝ, wideProfile B W u ^ 2 := by
  have hcontract := scaledWideOrbit_L1_L2_contractions
    hT hB4 hBT hdelta W n
  have hL1 := scaledWideProfile_L1_eq_quarter hT hB4 hBT W
  have hL2 := scaledWideProfile_L2_sq_eq_quarter hT hB4 hBT W
  have hscaled0 : ∀ u : ℝ,
      0 ≤ scaledWideProfile B W u := scaledWideProfile_nonneg
        (lt_of_lt_of_le (by norm_num) hB4) W
  have hL1abs : (∫ u : ℝ, scaledWideProfile B W u) =
      ∫ u : ℝ, |scaledWideProfile B W u| := by
    apply integral_congr_ae
    filter_upwards [] with u
    rw [abs_of_nonneg (hscaled0 u)]
  exact ⟨hcontract.1.trans_eq (hL1abs.trans hL1),
    hcontract.2.trans_eq hL2⟩

end GuthMaynardS3ScaledWideOrbit

#print axioms GuthMaynardS3ScaledWideOrbit.scaledWideOrbit_admissible
#print axioms GuthMaynardS3ScaledWideOrbit.scaledWideOrbit_fourier_bound
#print axioms GuthMaynardS3ScaledWideOrbit.scaledWideOrbit_L1_L2_contractions
#print axioms GuthMaynardS3ScaledWideOrbit.scaledWideOrbit_L1_L2_quarter_original
