import FordCompleteMomentLift
open scoped BigOperators ZMod ComplexConjugate
open MAPFordCompleteSystemMoment FordKPointEnergy FordBoundaryCountGeometry
open FordBoundaryEnergyMoments FordBoundaryWeightedHolder MAPFordP16FiniteFourierBridge
open MAPFordBoundaryCrossFourier
noncomputable section
namespace FordCompleteMomentLiftBound

lemma completeMoment_eq_fordA_fixed
    {S k P L : ℕ} [NeZero L]
    (hbound : ∀ r r' j,
      |FordBoundaryPinnedCross.wordFreq (FordCompleteMomentLift.zeroBase (k := k))
          (FordCompleteMomentLift.powerFrequency (k := k) (P := P)) S r j -
        FordBoundaryPinnedCross.wordFreq (FordCompleteMomentLift.zeroBase (k := k))
          (FordCompleteMomentLift.powerFrequency (k := k) (P := P)) S r' j| < (L : ℤ)) :
    (completeMoment S k P : ℝ) =
      fordA (fun alpha : Fin k → ZMod L =>
        ‖fordBoundaryBlock (FordCompleteMomentLift.zeroBase (k := k)) alpha‖ ^ 2)
      (fun alpha : Fin k → ZMod L =>
        ‖fordBoundaryBlock (FordCompleteMomentLift.powerFrequency (k := k) (P := P)) alpha‖) S := by
  have hcard := FordBoundaryEnergyMoments.energy_card_eq_fordA
    (L := L) (k := k) (s := S)
    (f := FordCompleteMomentLift.zeroBase (k := k))
    (g := FordCompleteMomentLift.powerFrequency (k := k) (P := P)) hbound
  calc
    (completeMoment S k P : ℝ) = Fintype.card (EnergyZero
        (FordCompleteMomentLift.zeroBase (k := k))
        (FordCompleteMomentLift.powerFrequency (k := k) (P := P)) S) := by
      exact_mod_cast FordCompleteMomentLift.completeMoment_eq_energy_card S k P
    _ = _ := hcard

theorem completeMoment_lift {s t k P : ℕ} (hP : 1 ≤ P) :
    completeMoment (s + t) k P ≤ P ^ (2 * t) * completeMoment s k P := by
  let L := FordCompleteMomentLift.momentModulus (s + t) k P
  letI : NeZero L := ⟨by dsimp [L, FordCompleteMomentLift.momentModulus]; omega⟩
  have hbig := FordCompleteMomentLift.moment_wordFreq_bound (s := s + t) (k := k) (P := P) hP
  have hsmall : ∀ r r' j, |FordBoundaryPinnedCross.wordFreq
      (FordCompleteMomentLift.zeroBase (k := k)) (FordCompleteMomentLift.powerFrequency (k := k) (P := P)) s r j -
      FordBoundaryPinnedCross.wordFreq (FordCompleteMomentLift.zeroBase (k := k)) (FordCompleteMomentLift.powerFrequency (k := k) (P := P)) s r' j| < (L : ℤ) := by
    intro r r' j
    have hh := FordCompleteMomentLift.moment_wordFreq_bound (s := s) (k := k) (P := P) hP r r' j
    have hL : (FordCompleteMomentLift.momentModulus s k P : ℤ) ≤ (L : ℤ) := by
      dsimp [L, FordCompleteMomentLift.momentModulus]
      have hs : s ≤ s + t := Nat.le_add_right s t
      have hm : 2 * s * P ^ (k + 1) ≤ 2 * (s + t) * P ^ (k + 1) := by
        exact Nat.mul_le_mul_right (P ^ (k + 1)) (Nat.mul_le_mul_left 2 hs)
      have hNat : 2 * s * P ^ (k + 1) + 1 ≤
          2 * (s + t) * P ^ (k + 1) + 1 := Nat.add_le_add_right hm 1
      exact_mod_cast hNat
    exact lt_of_lt_of_le hh hL
  have hbigA := completeMoment_eq_fordA_fixed (S := s + t) (k := k) (P := P) (L := L) hbig
  have hsmallA := completeMoment_eq_fordA_fixed (S := s) (k := k) (P := P) (L := L) hsmall
  have hreal : (completeMoment (s + t) k P : ℝ) ≤
      (P : ℝ) ^ (2 * t) * (completeMoment s k P : ℝ) := by
    rw [hbigA, hsmallA]
    unfold fordA fordAvg
    rw [Finset.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card]
    have hpow : ∀ alpha : Fin k → ZMod L,
        ‖fordBoundaryBlock (FordCompleteMomentLift.powerFrequency (k := k) (P := P)) alpha‖ ^ (2 * (s + t)) ≤
          (P : ℝ) ^ (2 * t) * ‖fordBoundaryBlock (FordCompleteMomentLift.powerFrequency (k := k) (P := P)) alpha‖ ^ (2 * s) := by
      intro alpha
      let B := ‖fordBoundaryBlock (FordCompleteMomentLift.powerFrequency (k := k) (P := P)) alpha‖
      have hB := FordCompleteMomentLift.power_block_norm_le hP alpha
      change B ≤ (P : ℝ) at hB
      have h1 : B ^ (2 * t) ≤ (P : ℝ) ^ (2 * t) := by gcongr
      rw [show 2 * (s + t) = 2 * t + 2 * s by omega, pow_add]
      have hm := mul_le_mul h1 (le_refl (B ^ (2 * s))) (by positivity) (by positivity)
      exact hm.trans_eq (by ring)
    have hsum :
        (∑ alpha : Fin k → ZMod L,
          ‖fordBoundaryBlock (FordCompleteMomentLift.powerFrequency (k := k) (P := P)) alpha‖ ^ (2 * (s + t))) ≤
          ∑ alpha : Fin k → ZMod L,
            (P : ℝ) ^ (2 * t) *
              ‖fordBoundaryBlock (FordCompleteMomentLift.powerFrequency (k := k) (P := P)) alpha‖ ^ (2 * s) := by
      exact Finset.sum_le_sum (fun alpha _ => hpow alpha)
    have hcard : Fintype.card (Fin k → ZMod L) = L ^ k := by simp
    have hzero : ∀ alpha : Fin k → ZMod L,
        ‖fordBoundaryBlock (FordCompleteMomentLift.zeroBase (k := k)) alpha‖ ^ 2 = (1 : ℝ) := by
      intro alpha
      simp [fordBoundaryBlock, FordCompleteMomentLift.zeroBase, fordIntegerCharTerm]
    simp_rw [hzero]
    simp only [one_mul, Finset.card_univ]
    rw [hcard]
    norm_num [Nat.cast_pow]
    have hden : 0 ≤ (L : ℝ) ^ k := by positivity
    calc
      _ ≤ (∑ alpha : Fin k → ZMod L,
          (P : ℝ) ^ (2 * t) *
            ‖fordBoundaryBlock (FordCompleteMomentLift.powerFrequency (k := k) (P := P)) alpha‖ ^ (2 * s)) /
          (L : ℝ) ^ k := by
            simpa using div_le_div_of_nonneg_right hsum hden
      _ = (P : ℝ) ^ (2 * t) *
          ((∑ alpha : Fin k → ZMod L,
            ‖fordBoundaryBlock (FordCompleteMomentLift.powerFrequency (k := k) (P := P)) alpha‖ ^ (2 * s)) /
            (L : ℝ) ^ k) := by
            rw [← Finset.mul_sum]
            field_simp
  exact_mod_cast hreal

end FordCompleteMomentLiftBound
#print axioms FordCompleteMomentLiftBound.completeMoment_lift
