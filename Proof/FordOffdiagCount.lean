import FordDifferenceSignedSelection
import FordOffdiagTensor
import FordOffdiagTensorFibers
import FordOffdiagTensorSignedZero
import FordUniformFiberSum

open scoped BigOperators ZMod ComplexConjugate
open FordBoundaryCountGeometry
open FordDifferenceSignedSelection
open FordOffdiagTensor
open FordOffdiagTensorFibers
open FordOffdiagTensorSignedZero
open FordSignedMixedCount
open MAPFordDifferenceFamily
open MAPFordDifferencePointBlockNorm
open MAPFordCompleteSystemMoment
open MAPFordLemma32LiteralContract
open FordDifferencePairs

noncomputable section
namespace FordOffdiagCount

theorem offdiag_count_selection
    {s k P Q p q r : ℕ}
    (phi : Fin k → Polynomial ℤ)
    (hp : 0 < p) (hq : 0 < q) (hk : 1 ≤ k)
    (hm : 0 < p ^ r) (hH : 0 < P / p ^ r) :
    ∃ h0 : PositiveHeight P (p ^ r),
      (Fintype.card (LOffdiag s k P Q p q r phi) : ℝ)^2 ≤
        ((2 : ℝ)^k * ((P / p ^ r : ℕ) : ℝ)^k)^2 *
          (completeMoment s k Q : ℝ) *
            (Fintype.card (KPoint s k P Q
              (differencePsi phi (FordPositiveHeightFamily.shift h0)) (p * q)) : ℝ) := by
  obtain ⟨h0, hSigned⟩ :=
    FordDifferenceSignedSelection.difference_signed_selection
      phi hp hq hk hm hH
  refine ⟨h0, ?_⟩
  have hTensor := FordOffdiagTensor.lOffdiag_card_le_tensor
    (s := s) (k := k) (P := P) (Q := Q) (p := p) (q := q) (r := r)
    (phi := phi) hm
  let I := FiberIndex k P (Modulus p r)
  let c : I → ℝ := fun idx =>
    (Fintype.card (SignedZero
      (fun x : FordKPointEnergy.PowerWord (s := s) (Q := Q) =>
        FordKPointEnergy.baseFreq (q := p * q) x)
      (fun h : PositiveHeight P (Modulus p r) =>
        fun z : FordKPointEnergy.SourcePoint (P := P) =>
          pointTranslatedDifferenceFrequency phi (FordPositiveHeightFamily.shift h) z)
      idx.2 idx.1) : ℝ)
  have hc_nonneg : ∀ idx : I, 0 ≤ c idx := by
    intro idx
    dsimp [c]
    positivity
  have hV : 0 ≤
      (completeMoment s k Q : ℝ) *
        (Fintype.card (KPoint s k P Q
          (differencePsi phi (FordPositiveHeightFamily.shift h0)) (p * q)) : ℝ) := by
    positivity
  have hc_bound : ∀ idx : I, c idx ^ 2 ≤
      (completeMoment s k Q : ℝ) *
        (Fintype.card (KPoint s k P Q
          (differencePsi phi (FordPositiveHeightFamily.shift h0)) (p * q)) : ℝ) := by
    intro idx
    dsimp [c]
    exact hSigned idx.2 idx.1
  have hsum := FordUniformFiberSum.sum_sq_le_uniform c hV hc_nonneg hc_bound
  have hsum_card :
      (∑ idx : I, c idx) =
        (Fintype.card (TensorPoint s k P Q p q r phi hm) : ℝ) := by
    rw [FordOffdiagTensorFibers.tensor_card_eq_sum_fixed_sign_height hm]
    dsimp [I, c]
    rw [Fintype.sum_prod_type]
    simp_rw [FordOffdiagTensorSignedZero.tensorFiber_card_eq_signedZero hm]
    norm_num
  have hIcast :
      (Fintype.card I : ℝ) =
        (2 : ℝ)^k * ((P / p ^ r : ℕ) : ℝ)^k := by
    dsimp [I]
    rw [FordOffdiagTensorFibers.fiberIndex_card]
    norm_num [Modulus, Nat.cast_mul, Nat.cast_pow]
  have hTensor_sq :
      (Fintype.card (TensorPoint s k P Q p q r phi hm) : ℝ)^2 ≤
        (Fintype.card I : ℝ)^2 *
          ((completeMoment s k Q : ℝ) *
            (Fintype.card (KPoint s k P Q
              (differencePsi phi (FordPositiveHeightFamily.shift h0)) (p * q)) : ℝ)) := by
    rw [← hsum_card]
    exact hsum
  have hLle :
      (Fintype.card (LOffdiag s k P Q p q r phi) : ℝ) ≤
        (Fintype.card (TensorPoint s k P Q p q r phi hm) : ℝ) := by
    exact_mod_cast hTensor
  have hLsq :
      (Fintype.card (LOffdiag s k P Q p q r phi) : ℝ)^2 ≤
        (Fintype.card (TensorPoint s k P Q p q r phi hm) : ℝ)^2 := by
    have hL0 : 0 ≤ (Fintype.card (LOffdiag s k P Q p q r phi) : ℝ) := by positivity
    have hT0 : 0 ≤ (Fintype.card (TensorPoint s k P Q p q r phi hm) : ℝ) := by positivity
    nlinarith
  calc
    (Fintype.card (LOffdiag s k P Q p q r phi) : ℝ)^2 ≤
        (Fintype.card (TensorPoint s k P Q p q r phi hm) : ℝ)^2 := hLsq
    _ ≤ (Fintype.card I : ℝ)^2 *
          ((completeMoment s k Q : ℝ) *
            (Fintype.card (KPoint s k P Q
              (differencePsi phi (FordPositiveHeightFamily.shift h0)) (p * q)) : ℝ)) := hTensor_sq
    _ = ((2 : ℝ)^k * ((P / p ^ r : ℕ) : ℝ)^k)^2 *
          (completeMoment s k Q : ℝ) *
            (Fintype.card (KPoint s k P Q
              (differencePsi phi (FordPositiveHeightFamily.shift h0)) (p * q)) : ℝ) := by
      rw [hIcast]
      ring

end FordOffdiagCount

#print axioms FordOffdiagCount.offdiag_count_selection
