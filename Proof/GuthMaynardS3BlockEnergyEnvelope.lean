import GuthMaynardS3SignedMassEnvelope
import GuthMaynardS3BlockSignedConsumer
import GuthMaynardS3BlockMainLedger
import GuthMaynardS3BlockTailLedger
import GuthMaynardS3CubicLoss

open scoped BigOperators Real
open MeasureTheory
noncomputable section
set_option maxHeartbeats 3000000
namespace GuthMaynardS3BlockEnergyEnvelope
open GuthMaynardJIteration GuthMaynardS3ScaledWideProfile
open GuthMaynardS3SignedMassEnvelope GuthMaynardS3BlockSignedConsumer
open GuthMaynardS3BlockMainLedger GuthMaynardS3BlockTailLedger
open GuthMaynardS3CubicSeamParameters GuthMaynardS3CubicLoss
open GuthMaynardS3LiteralUniform106Radial
open GuthMaynardS3LiteralLemma82 GuthMaynardHeathBrownInterface
open GuthMaynardS3LiteralRadialDecay GuthMaynardS3LiteralAffineReduction
open GuthMaynardS3LiteralLocalization GuthMaynardS3LiteralBalancedGeometry GuthMaynardEquation55Infinite
open GuthMaynardS3LiteralLemma83Energy GuthMaynardS3DilatedRectangleConsumer
open GuthMaynardS3CubicHorizonTail

/-- Actual source-block energy bound at the fixed-weight final seam. Both
moments, the signed-bin estimate, all geometric caps, and both error tails
are derived internally. Constants are fixed before all source variables. -/
theorem block_energy_envelope {eta : ℝ} (heta : 0 < eta) (heta1 : eta ≤ 1/100) :
    ∃ Cmain Ctail T0 : ℝ, 0 ≤ Cmain ∧ 0 ≤ Ctail ∧ 0 < T0 ∧
      ∀ (N : ℕ) (T : ℝ) (W : Finset ℝ) (A i k d : ℕ),
        256 ≤ N → T = (N : ℝ)^(6/5 : ℝ) → T0 ≤ 64*T^3 →
        (W.card : ℝ) ≤ 2*T → TEtaSeparated W T eta →
        ContainedInIntervalOfLength W T →
        k ∈ dyadicExponents (s3FrequencyCutoff T eta N) → d < 4 →
        orderedBalancedBlockAffine N W (s3Rho T eta) A i k d ^ 2 ≤
          Cmain * (s3Rho T eta)^9 * (k+7 : ℝ)^2 *
            (T^4*(W.card : ℝ)^3 + T^2*(N : ℝ)^2*W.card*
              (sourceApproximateAdditiveEnergy W : ℝ)) + Ctail*T^(-282 : ℝ) := by
  have hetaone : eta ≤ 1 := by linarith
  obtain ⟨Ce,Cm,T0,hCe,hCm,hT0,hmass⟩ := scaledWide_signed_mass_envelope heta heta hetaone
  let D : ℝ := radialDerivativeBudget 0
  let A82 : ℝ := lemma82Constant eta
  have hD : 0 ≤ D := radialDerivativeBudget_nonneg 0
  have hA82 : 0 ≤ A82 := lemma82Constant_nonneg eta
  let Z : ℝ := (2 : ℝ)^19*D^2*Ce*A82
  let Cmain : ℝ := 64*Z*(4096*A82^2+16*Cm)
  let Ctail : ℝ := Z*(128+8192*Cm)
  refine ⟨Cmain,Ctail,T0,?_,?_,hT0,?_⟩
  · dsimp [Cmain,Z]; positivity
  · dsimp [Ctail,Z]; positivity
  intro N T W A i k d hN hTdef hUT hcard hsep hcontained hk hd
  have hp := final_seam_cubic_parameters hN hTdef heta heta1 hk W hcard
  let U : ℝ := 64*T^3
  let rho : ℝ := s3Rho T eta
  let K : ℝ := (2 : ℝ)^k
  let R : ℝ := W.card
  let E : ℝ := sourceApproximateAdditiveEnergy W
  let L : ℝ := (k : ℝ)+7
  have hT := hp.time_one
  have hTp : 0 < T := by linarith
  have hrone : 1 ≤ rho := Real.one_le_rpow hT heta.le
  have hr0 : 0 ≤ rho := by linarith
  have hKp : 0 < K := by dsimp [K]; positivity
  have hUp : 0 < U := by dsimp [U]; positivity
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hE0 : 0 ≤ E := by dsimp [E]; positivity
  have hL0 : 0 ≤ L := by dsimp [L]; positivity
  have hL : L ≤ 8*K := dyadic_bin_factor_le k
  have hMcast : ((2^(k+2) : ℕ) : ℝ) = 4*K := by
    dsimp [K]; push_cast; rw [pow_add]; norm_num; ring
  have hMU : 16*((2^(k+2) : ℕ) : ℝ) ≤ U := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using hp.max_frequency
  have hheight : 4*(W.card : ℝ)^2 ≤ U^(4 : ℝ) := by
    norm_cast
    simpa only [U,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using hp.profile_height
  let V : ℝ := Ce*U^eta*((4*K)^6*(A82*R)^2+
    (4*K)^4*(Cm*(rho*E+T^(-400 : ℝ)))+(4*K)^4/U^100)
  have hbin : ∀ j ∈ Finset.range (k+7),
      sourceFiniteAffineEnergy (sourceSignedDyadicRange (2^j))
        (sourcePositiveDyadicRange (2^(k+2))) (sourceCenteredRange (16*2^(k+2)))
        (scaledWideProfile ((N : ℝ)*2^k/(4*rho)) W) ≤ V := by
    intro j hj
    have hm := hmass T U ((N : ℝ)*2^k/(4*rho)) W (2^j) (2^(k+2))
      hT hUT hp.profile_lower hp.profile_upper hcard hsep hcontained hheight
      (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by norm_num)) (dilated_bin_le_sixteen_middle hj) hMU
    rw [hMcast] at hm
    simpa only [V,A82,R,E,rho,mul_add,mul_assoc] using! hm
  have hblock := block_affine_sq_le_of_signed_bins N W rho A i k d
    hT heta hsep hcontained hd hp.profile_lower hbin
  let F : ℝ := 8*(16*D*rho*(N : ℝ)^2/K)^2*A82*R*L^2*Ce*U^eta
  let main : ℝ := (4*K)^6*(A82*R)^2+(4*K)^4*(Cm*rho*E)
  let tail : ℝ := (4*K)^4*(Cm*T^(-400 : ℝ))+(4*K)^4/U^100
  have hfull : orderedBalancedBlockAffine N W rho A i k d ^ 2 ≤ F*(main+tail) := by
    convert hblock using 1 <;> dsimp [F,main,tail,V,D,A82,R,L,K] <;> ring
  have hmain := main_terms_scalar_ledger (L:=L) hD hCe.le hA82 hCm.le hR0 hE0
    (by positivity : 0 ≤ (N : ℝ)) hKp.le hKp hT hrone hp.frequency_product
    (by positivity : 0 ≤ U^eta) (cubic_horizon_loss hT hetaone)
  have htail := block_tail_ledger hT hetaone hr0 hp.rho_le_time
    (by positivity : 0 ≤ (N : ℝ)) hp.length_le_time hKp hp.bin_le_time_sq
    hR0 hcard hL0 hL hD hCe.le hA82 hCm.le
  have hm : F*main ≤ Cmain*rho^9*L^2*(T^4*R^3+T^2*(N : ℝ)^2*R*E) := hmain
  have ht : F*tail ≤ Ctail*T^(-282 : ℝ) := htail
  change orderedBalancedBlockAffine N W rho A i k d ^ 2 ≤ _
  calc
    _ ≤ F*(main+tail) := hfull
    _ = F*main+F*tail := by ring
    _ ≤ Cmain*rho^9*L^2*(T^4*R^3+T^2*(N : ℝ)^2*R*E)+Ctail*T^(-282 : ℝ) :=
      add_le_add hm ht
    _ = _ := by rfl

end GuthMaynardS3BlockEnergyEnvelope
#print axioms GuthMaynardS3BlockEnergyEnvelope.block_energy_envelope
