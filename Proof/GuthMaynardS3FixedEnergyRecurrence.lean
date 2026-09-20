import GuthMaynardS3PositiveFourierBridge
import GuthMaynardS3JClosure
import GuthMaynardS3IterationClosure

open scoped BigOperators Real FourierTransform ContDiff
open MeasureTheory
noncomputable section
namespace GuthMaynardS3FixedEnergyRecurrence
open GuthMaynardJIteration GuthMaynardS3FullUniform GuthMaynardS3IterationClosure

/-- A uniform actual signed-energy step with the literal J supremum discharged
into one fixed positive-coordinate energy. No region or J estimate is assumed. -/
theorem signed_energy_step_uniform
    (Cdec : ℕ → ℝ) (hCdec : ∀ q, 0 ≤ Cdec q)
    {eta delta : ℝ} (heta : 0 < eta) (heta1 : eta ≤ 1) (hdelta : 0 < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T S F : ℝ) (f : ℝ → ℝ) (M1 M : ℕ)
      (hT : 7 ≤ T) (hF0 : 0 ≤ F) (hF2 : F ≤ 2)
      (hS0 : 0 ≤ S) (hS : S ≤ T^(4:ℝ))
      (hM1 : 1 ≤ M1) (hM : 1 ≤ M) (hM1hi : M1 ≤ 16*M)
      (hMT : (16*M : ℝ) ≤ T) (hdT : T^delta ≤ T)
      (hf : SourceAdmissibleProfile T S F f)
      (hdec : ∀ q : ℕ, ∀ z : ℝ, z ≠ 0 →
        ‖FourierTransform.fourier (fun u : ℝ => (f u : ℂ)) z‖ ≤
          Cdec q * T^eta * (T/|z|)^q * S),
      sourceFiniteAffineEnergy (sourceSignedDyadicRange M1)
        (sourcePositiveDyadicRange M) (sourceCenteredRange (16*M)) f ≤
      C * (T^(3*eta) * (16*M : ℝ)^6 * (∫u : ℝ, ‖(f u : ℂ)‖)^2 +
        T^(4*eta+delta) * (16*M : ℝ)^2 * Real.sqrt ((∫u : ℝ, f u^2) *
          sourceFiniteAffineEnergy (sourcePositiveDyadicRange M)
            (sourcePositiveDyadicRange M) (sourceCenteredRange (16*M))
            (affineSmoothing T (sourceBumpNormalized (T^delta)
              (Real.rpow_pos_of_pos (by linarith [hT]) delta)) f))) + C/T^100 := by
  obtain ⟨C,hC,hfull⟩ := source_fullFrequencyIntegral_uniform Cdec hCdec heta heta1 hdelta
  refine ⟨C,hC,?_⟩
  intro T S F f M1 M hT hF0 hF2 hS0 hS hM1 hM hM1hi hMT hdT hf hdec
  have hT1 : 1 ≤ T := by linarith
  have hTpos : 0 < T := by linarith
  have hMpos : 0 < M := by omega
  have hM1pos : 0 < M1 := by omega
  have hmax : 1 ≤ 16*M := by omega
  have hfull' := hfull T S F f (16*M) M1 M (16*M)
    hT hT1 hF0 (by linarith) (by linarith) hS0 hS hmax hM1 hM hmax
    (by exact_mod_cast hM1hi) (by exact_mod_cast (show M ≤ 16*M by omega))
    (le_refl _) (by simpa using hMT) (by omega) (by push_cast; rfl)
    hf hdec
  have hpl := sourceCenteredAffineEnergy_le_wholeSupport_fourierIntegral_of_sourceProfile
    hf heta hTpos.le hM1pos hMpos (by omega : 0 < 16*M)
  have hfirst := hpl.trans (by
    simpa only [sourceBumpEllRange, Nat.cast_one, mul_one, div_one] using hfull')
  have hnorm := normalizedAffineSmoothing_sourceAdmissibleProfile hTpos
    (Real.rpow_pos_of_pos hTpos delta) (Real.one_le_rpow hT1 hdelta.le) f hf
  have hj := sourceAffineJ_le_full_centered_energy hnorm hMpos hTpos hF0 hF2 hdT
  have hI : 0 ≤ ∫u : ℝ, f u^2 := integral_nonneg (fun u => sq_nonneg _)
  push_cast at hfirst
  apply hfirst.trans
  gcongr
  all_goals first | exact hj | exact le_rfl

end GuthMaynardS3FixedEnergyRecurrence
#print axioms GuthMaynardS3FixedEnergyRecurrence.signed_energy_step_uniform
