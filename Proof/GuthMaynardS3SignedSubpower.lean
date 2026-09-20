import GuthMaynardS3PositiveEnergyShiftedBound
import GuthMaynardS3FiniteSqrtEnvelope
import GuthMaynardS3EpsilonCollar
import GuthMaynardS3OneStepSubpower

open scoped BigOperators Real FourierTransform ContDiff
open MeasureTheory Filter
noncomputable section
set_option maxHeartbeats 3000000
namespace GuthMaynardS3SignedSubpower
open GuthMaynardJIteration GuthMaynardS3ScaledWideProfile GuthMaynardS3ScaledWideOrbit
open GuthMaynardS3LiteralProfileFourier GuthMaynardS3FixedEnergyRecurrence
open GuthMaynardS3EnergyNormalization GuthMaynardS3PositiveEnergyShiftedBound
open GuthMaynardS3FiniteSqrtEnvelope GuthMaynardS3EpsilonCollar
open GuthMaynardS3OneStepSubpower

/-- Uniform signed affine-energy estimate for the literal compressed source
profile. The smoothing orbit, recurrence, endcap, and epsilon choices are all
derived internally; the error is explicitly M^4/T^100. -/
theorem scaledWide_signed_energy_subpower {epsilon : ℝ} (heps : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∃ T0 : ℝ,
      ∀ (T B : ℝ) (W : Finset ℝ) (M1 M : ℕ), T0 ≤ T →
        4 ≤ B → B ≤ T → 4*(W.card : ℝ)^2 ≤ T^(4 : ℝ) →
        1 ≤ M1 → 1 ≤ M → M1 ≤ 16*M → 16*(M : ℝ) ≤ T →
        sourceFiniteAffineEnergy (sourceSignedDyadicRange M1)
          (sourcePositiveDyadicRange M) (sourceCenteredRange (16*M))
          (scaledWideProfile B W) ≤
        C*T^epsilon*((M : ℝ)^6*(∫u : ℝ, scaledWideProfile B W u)^2 +
          (M : ℝ)^4*(∫u : ℝ, scaledWideProfile B W u^2) + (M : ℝ)^4/T^100) := by
  obtain ⟨eta,delta,J,heta,heta1,hdelta,hdelta1,hexp,_⟩ :=
    exists_epsilon_collar_parameters heps
  obtain ⟨Cs,hCs,hshift⟩ := scaledWideOrbit_positive_energy_shifted_bound heta heta1 hdelta
  let Cdec : ℕ → ℝ := fun q => (4 : ℝ)^q*lemma84SmoothingFourierConstant q
  have hCdec : ∀ q, 0 ≤ Cdec q := by
    intro q
    exact mul_nonneg (by positivity) (lemma84SmoothingFourierConstant_nonneg q)
  obtain ⟨Cc,hCc,hsource⟩ := signed_energy_step_uniform Cdec hCdec heta heta1 hdelta
  let K : ℝ := 34848*(1+4*Cs*(16 : ℝ)^6+4*Cs^2*(16 : ℝ)^4)
  have hK : 0 < K := by dsimp [K]; positivity
  let Cfinal : ℝ := Cc*(16 : ℝ)^6+Cc+Cc*(16 : ℝ)^2*Real.sqrt K+1
  have hCfinal : 0 < Cfinal := by dsimp [Cfinal]; positivity
  obtain ⟨T0,hT0⟩ := eventually_atTop.1 (eventually_fixed_collar hdelta.le hdelta1 (J+1))
  refine ⟨Cfinal,hCfinal,T0,?_⟩
  intro T B W M1 M hTlarge hB4 hBT hS hM1 hM hM1hi hMT
  obtain ⟨hT7,hdT,hcollar⟩ := hT0 T hTlarge
  have hT1 : 1 ≤ T := by linarith
  have hTp : 0 < T := by linarith
  have hRp : 0 < Real.rpow T delta := Real.rpow_pos_of_pos hTp delta
  let f0 : ℝ → ℝ := scaledWideProfile B W
  let f1 : ℝ → ℝ := scaledWideOrbit B T delta hRp W 1
  let L0 : ℝ := ∫u : ℝ, f0 u
  let Q0 : ℝ := ∫u : ℝ, f0 u^2
  let D0 : ℝ := (M : ℝ)^2*L0^2+Q0+1/T^100
  let E0 : ℝ := sourceFiniteAffineEnergy (sourceSignedDyadicRange M1)
    (sourcePositiveDyadicRange M) (sourceCenteredRange (16*M)) f0
  let E1 : ℝ := sourceFiniteAffineEnergy (sourcePositiveDyadicRange M)
    (sourcePositiveDyadicRange M) (sourceCenteredRange (16*M)) f1
  have hf : SourceAdmissibleProfile T (4*(W.card : ℝ)^2) (7/4) f0 :=
    scaledWideProfile_sourceAdmissibleProfile hT1 hB4 hBT W
  have hL0 : 0 ≤ L0 := integral_nonneg (fun u => hf.nonneg u)
  have hQ0 : 0 ≤ Q0 := integral_nonneg (fun u => sq_nonneg _)
  have hD0 : 0 < D0 := by dsimp [D0]; positivity
  have hMp : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  have hMone : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hden : 0 < (M : ℝ)^4*D0 := by positivity
  have hE10 : 0 ≤ E1 := integral_nonneg (fun u => sq_nonneg _)
  let Ds : ℝ := max 1 (max (2*(Cs*(16 : ℝ)^6*T^(3*eta)+Cs))
    (4*(Cs*T^(4*eta+delta)*(16 : ℝ)^2)^2))
  let Rtail : ℝ := Ds*iterSqrt J (max 1 ((34848*T^2)/Ds))
  have hRtail : Rtail ≤ K*T^epsilon := by
    simpa only [Rtail,Ds,K] using
      finite_sqrt_scalar_envelope heta hdelta hexp.le Cs T hCs hT1
  have hs := hshift T B W M (J+1) 1 hT7 hB4 hBT hS hMT hdT hcollar hM (by omega) hRp
  have hs' : E1 ≤ (M : ℝ)^4*(Rtail*D0) := by
    simpa [E1,f1,f0,L0,Q0,D0,Rtail,Ds,scaledWideOrbit,affineSmoothingIterate] using hs
  have hE1 : E1 ≤ (K*T^epsilon)*((M : ℝ)^4*D0) := by
    have hh := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hRtail hD0.le) (by positivity : 0 ≤ (M : ℝ)^4)
    exact hs'.trans (by simpa only [mul_assoc, mul_left_comm, mul_comm] using hh)
  have hY : E1/((M : ℝ)^4*D0) ≤ K*T^epsilon := (div_le_iff₀ hden).2 hE1
  have hdec : ∀ q : ℕ, ∀ z : ℝ, z ≠ 0 →
      ‖FourierTransform.fourier (fun u : ℝ => (f0 u : ℂ)) z‖ ≤
      Cdec q*T^eta*(T/|z|)^q*(4*(W.card : ℝ)^2) := by
    intro q z hz
    exact scaledWideProfile_fourier_bound hT1 hB4 hBT W q heta hz
  have hsrc := hsource T (4*(W.card : ℝ)^2) (7/4) f0 M1 M hT7
    (by norm_num) (by norm_num) (by positivity) hS hM1 hM hM1hi hMT hdT hf hdec
  have hnorm : (∫u : ℝ, ‖(f0 u : ℂ)‖) = L0 := by
    apply integral_congr_ae
    filter_upwards [] with u
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hf.nonneg u)]
  rw [hnorm] at hsrc
  have hraw : E0 ≤ (Cc*(16 : ℝ)^6*T^(3*eta))*(M : ℝ)^6*L0^2 +
      (Cc*(16 : ℝ)^2*T^(4*eta+delta))*(M : ℝ)^2*Real.sqrt (Q0*E1)+Cc/T^100 := by
    change E0 ≤ Cc*(T^(3*eta)*(16*(M : ℝ))^6*L0^2 +
      T^(4*eta+delta)*(16*(M : ℝ))^2*Real.sqrt (Q0*E1))+Cc/T^100 at hsrc
    calc
      E0 ≤ Cc*(T^(3*eta)*(16*(M : ℝ))^6*L0^2 +
        T^(4*eta+delta)*(16*(M : ℝ))^2*Real.sqrt (Q0*E1))+Cc/T^100 := hsrc
      _ = _ := by ring
  have hLD : (M : ℝ)^2*L0^2 ≤ D0 := by
    have ht : 0 ≤ 1/T^100 := by positivity
    dsimp [D0]; linarith
  have hQD : Q0 ≤ D0 := by
    have hh : 0 ≤ (M : ℝ)^2*L0^2 := by positivity
    have ht : 0 ≤ 1/T^100 := by positivity
    dsimp [D0]; linarith only [hh, ht]
  have hremD : 1/T^100 ≤ D0 := by
    have hh : 0 ≤ (M : ℝ)^2*L0^2 := by positivity
    dsimp [D0]; linarith
  have hMpow : 1 ≤ (M : ℝ)^4 := one_le_pow₀ hMone
  have hrem : Cc/T^100 ≤ Cc*((M : ℝ)^4*D0) := by
    have hh := mul_le_mul_of_nonneg_left hremD hCc.le
    have hMD : D0 ≤ (M : ℝ)^4*D0 := le_mul_of_one_le_left hD0.le hMpow
    have hh' := mul_le_mul_of_nonneg_left hMD hCc.le
    simpa only [mul_one_div] using hh.trans hh'
  have hnormalized := normalized_energy_step hMp hD0 hQ0 hE10
    (by positivity : 0 ≤ Cc*(16 : ℝ)^6*T^(3*eta))
    (by positivity : 0 ≤ Cc*(16 : ℝ)^2*T^(4*eta+delta)) hLD hQD hrem hraw
  have hbudget : 8*eta+2*delta ≤ epsilon := by
    have hh : 0 ≤ 2/(2 : ℝ)^J := by positivity
    linarith
  have hsub := one_step_subpower hCc.le hK.le hT1 heta hdelta hbudget hY hnormalized
  have hE0norm : E0/((M : ℝ)^4*D0) ≤ Cfinal*T^epsilon := by
    dsimp [Cfinal]
    have ht : 0 ≤ T^epsilon := by positivity
    exact hsub.trans (by nlinarith only [ht])
  have hh := (div_le_iff₀ hden).1 hE0norm
  convert hh using 1 <;> dsimp [E0,D0,L0,Q0,f0] <;> ring

end GuthMaynardS3SignedSubpower
#print axioms GuthMaynardS3SignedSubpower.scaledWide_signed_energy_subpower
