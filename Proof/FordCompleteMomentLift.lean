import FordCompleteMomentBridge
import FordBoundaryEnergyMoments
import FordBoundaryPinnedCross
import FordKPointEnergy

open scoped BigOperators ZMod ComplexConjugate
open MAPFordCompleteSystemMoment
open FordCompleteMomentBridge
open FordKPointEnergy
open FordBoundaryCountGeometry
open FordBoundaryEnergyMoments
open FordBoundaryPinnedCross
open FordBoundaryWeightedHolder
open MAPFordP16FiniteFourierBridge

noncomputable section
set_option autoImplicit false
namespace FordCompleteMomentLift

abbrev SourcePoint (P : ℕ) := FordKPointEnergy.SourcePoint (P := P)

def powerFrequency {k P : ℕ} : SourcePoint P → Fin k → ℤ :=
  fun z j => (z.1.val : ℤ) ^ (j.val + 1)

def zeroBase {k : ℕ} : Unit → Fin k → ℤ := fun _ _ => 0

def completeEnergyEquiv {s k P : ℕ} :
    EnergyZero (zeroBase (k := k)) (powerFrequency (k := k) (P := P)) s ≃
      FordCompleteMomentBridge.completeSolutions (s := s) (k := k) (Q := P) := by
  let toFun : EnergyZero (zeroBase (k := k)) (powerFrequency (k := k) (P := P)) s →
      FordCompleteMomentBridge.completeSolutions (s := s) (k := k) (Q := P) := fun r => by
    let xy : FordCompleteMomentBridge.PairQ (s := s) (Q := P) :=
      (fun i => FordCompleteMomentBridge.positiveFinEquiv P (r.1.1.2 i),
        fun i => FordCompleteMomentBridge.positiveFinEquiv P (r.1.2.2 i))
    refine ⟨xy, ?_⟩
    intro j
    have hr := congrFun r.2 j
    simp only [Pi.add_apply, Finset.sum_apply, zeroBase, powerFrequency] at hr
    have hr0 :
        (∑ i : Fin s, ((r.1.1.2 i).1.val : ℤ) ^ (j.val + 1)) =
          ∑ i : Fin s, ((r.1.2.2 i).1.val : ℤ) ^ (j.val + 1) := by
      simpa only [zero_add] using hr
    have hrnat :
        (∑ i : Fin s, ((r.1.1.2 i).1.val : ℕ) ^ (j.val + 1)) =
          ∑ i : Fin s, ((r.1.2.2 i).1.val : ℕ) ^ (j.val + 1) := by
      exact_mod_cast hr0
    simpa [FordCompleteMomentBridge.allPowerEq, xy,
      FordCompleteMomentBridge.positiveFinEquiv_val_add_one] using hrnat
  let invFun : FordCompleteMomentBridge.completeSolutions (s := s) (k := k) (Q := P) →
      EnergyZero (zeroBase (k := k)) (powerFrequency (k := k) (P := P)) s := fun r => by
    let x : Fin s → SourcePoint P := fun i =>
      (FordCompleteMomentBridge.positiveFinEquiv P).symm (r.1.1 i)
    let y : Fin s → SourcePoint P := fun i =>
      (FordCompleteMomentBridge.positiveFinEquiv P).symm (r.1.2 i)
    refine ⟨((⟨(), x⟩), (⟨(), y⟩)), ?_⟩
    funext j
    have hr := r.2 j
    simp only [zeroBase, powerFrequency, FordBoundaryCountGeometry.EnergyZero,
      Pi.zero_apply, zero_add, add_zero, Finset.sum_apply]
    have hx : ∀ i : Fin s,
        ((x i).1.val : ℕ) = (r.1.1 i).val + 1 := by
      intro i
      simpa [x] using (FordCompleteMomentBridge.positiveFinEquiv_val_add_one
        ((FordCompleteMomentBridge.positiveFinEquiv P).symm (r.1.1 i))).symm
    have hy : ∀ i : Fin s,
        ((y i).1.val : ℕ) = (r.1.2 i).val + 1 := by
      intro i
      simpa [y] using (FordCompleteMomentBridge.positiveFinEquiv_val_add_one
        ((FordCompleteMomentBridge.positiveFinEquiv P).symm (r.1.2 i))).symm
    have hrnat :
        (∑ i : Fin s, ((r.1.1 i).val + 1) ^ (j.val + 1)) =
          ∑ i : Fin s, ((r.1.2 i).val + 1) ^ (j.val + 1) := by
      exact hr
    have hsum :
        (∑ i : Fin s, ((x i).1.val : ℕ) ^ (j.val + 1)) =
          ∑ i : Fin s, ((y i).1.val : ℕ) ^ (j.val + 1) := by
      simpa only [hx, hy] using hrnat
    simp only [Pi.add_apply, Finset.sum_apply, zeroBase, powerFrequency]
    simpa only [zero_add] using (show
      (∑ i : Fin s, ((x i).1.val : ℤ) ^ (j.val + 1)) =
        ∑ i : Fin s, ((y i).1.val : ℤ) ^ (j.val + 1) by exact_mod_cast hsum)
  refine { toFun := toFun, invFun := invFun, left_inv := ?_, right_inv := ?_ }
  · intro r
    apply Subtype.ext
    dsimp [invFun, toFun]
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · funext i
        change (FordCompleteMomentBridge.positiveFinEquiv P).symm
          ((FordCompleteMomentBridge.positiveFinEquiv P) (r.1.1.2 i)) = r.1.1.2 i
        exact (FordCompleteMomentBridge.positiveFinEquiv P).left_inv _
    · apply Prod.ext
      · rfl
      · funext i
        change (FordCompleteMomentBridge.positiveFinEquiv P).symm
          ((FordCompleteMomentBridge.positiveFinEquiv P) (r.1.2.2 i)) = r.1.2.2 i
        exact (FordCompleteMomentBridge.positiveFinEquiv P).left_inv _
  · intro r
    apply Subtype.ext
    dsimp [toFun, invFun]
    apply Prod.ext
    · change (fun i => (FordCompleteMomentBridge.positiveFinEquiv P)
        ((FordCompleteMomentBridge.positiveFinEquiv P).symm ((r.1.1) i))) = r.1.1
      funext i
      exact (FordCompleteMomentBridge.positiveFinEquiv P).right_inv _
    · change (fun i => (FordCompleteMomentBridge.positiveFinEquiv P)
        ((FordCompleteMomentBridge.positiveFinEquiv P).symm ((r.1.2) i))) = r.1.2
      funext i
      exact (FordCompleteMomentBridge.positiveFinEquiv P).right_inv _


lemma completeMoment_eq_energy_card (s k P : ℕ) :
    completeMoment s k P =
      Fintype.card (EnergyZero (zeroBase (k := k))
        (powerFrequency (k := k) (P := P)) s) := by
  rw [FordCompleteMomentBridge.completeMoment_eq_card_completeSolutions]
  exact (Fintype.card_congr (completeEnergyEquiv (s := s) (k := k) (P := P))).symm


def momentModulus (S k P : ℕ) : ℕ := 2 * S * P ^ (k + 1) + 1

lemma powerFrequency_abs_le {k P : ℕ} (hP : 1 ≤ P)
    (z : SourcePoint P) (j : Fin k) :
    |powerFrequency z j| ≤ (P : ℤ) ^ (k + 1) := by
  have hz : z.1.val ≤ P := by omega
  have hj : j.val + 1 ≤ k + 1 := by omega
  have hpow : z.1.val ^ (j.val + 1) ≤ P ^ (k + 1) := by
    calc
      z.1.val ^ (j.val + 1) ≤ P ^ (j.val + 1) := Nat.pow_le_pow_left hz _
      _ ≤ P ^ (k + 1) := Nat.pow_le_pow_right (by omega) hj
  simp only [powerFrequency]
  rw [abs_of_nonneg]
  · exact_mod_cast hpow
  · positivity

lemma moment_wordFreq_bound {s k P : ℕ} (hP : 1 ≤ P) :
    ∀ r r' : (Unit × (Fin s → SourcePoint P)), ∀ j : Fin k,
      |FordBoundaryPinnedCross.wordFreq (zeroBase (k := k))
          (powerFrequency (k := k) (P := P)) s r j -
        FordBoundaryPinnedCross.wordFreq (zeroBase (k := k))
          (powerFrequency (k := k) (P := P)) s r' j| <
        (momentModulus s k P : ℤ) := by
  intro r r' j
  have hsum : ∀ v : Fin s → SourcePoint P,
      |∑ i : Fin s, powerFrequency (v i) j| ≤
        (s : ℤ) * (P : ℤ) ^ (k + 1) := by
    intro v
    calc
      |∑ i : Fin s, powerFrequency (v i) j| ≤
          ∑ i : Fin s, |powerFrequency (v i) j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin s, (P : ℤ) ^ (k + 1) := by
        exact Finset.sum_le_sum (fun i _ => powerFrequency_abs_le hP (v i) j)
      _ = (s : ℤ) * (P : ℤ) ^ (k + 1) := by simp
  have hraw := abs_sub_le
    (∑ i : Fin s, powerFrequency (r.2 i) j) 0
    (∑ i : Fin s, powerFrequency (r'.2 i) j)
  simp only [FordBoundaryPinnedCross.wordFreq, zeroBase, Pi.zero_apply,
    Finset.sum_apply, zero_add] at hraw ⊢
  have h1 := hsum r.2
  have h2 := hsum r'.2
  have habs :
      |(∑ i : Fin s, powerFrequency (r.2 i) j) -
        ∑ i : Fin s, powerFrequency (r'.2 i) j| ≤
        (2 : ℤ) * (s : ℤ) * (P : ℤ) ^ (k + 1) := by
    have hraw' := hraw
    simp only [sub_zero, zero_sub, abs_neg] at hraw'
    have h1' : |∑ i : Fin s, powerFrequency (r.2 i) j| ≤
        (s : ℤ) * (P : ℤ) ^ (k + 1) := h1
    have h2' : |∑ i : Fin s, powerFrequency (r'.2 i) j| ≤
        (s : ℤ) * (P : ℤ) ^ (k + 1) := h2
    nlinarith
  have hstrict :
      (2 * s : ℤ) * (P : ℤ) ^ (k + 1) < (momentModulus s k P : ℤ) := by
    dsimp [momentModulus]
    norm_num [Nat.cast_add, Nat.cast_mul, Int.natCast_pow]
  exact lt_of_le_of_lt habs hstrict


lemma sourcePoint_card (P : ℕ) : Fintype.card (SourcePoint P) = P := by
  simpa using Fintype.card_congr (FordCompleteMomentBridge.positiveFinEquiv P)

lemma power_block_norm_le {k P : ℕ} (hP : 1 ≤ P)
    {L : ℕ} [NeZero L] (alpha : Fin k → ZMod L) :
    ‖MAPFordBoundaryCrossFourier.fordBoundaryBlock
      (powerFrequency (k := k) (P := P)) alpha‖ ≤ (P : ℝ) := by
  calc
    ‖MAPFordBoundaryCrossFourier.fordBoundaryBlock
        (powerFrequency (k := k) (P := P)) alpha‖ ≤
        ∑ z : SourcePoint P,
          ‖fordIntegerCharTerm alpha
            (powerFrequency z)‖ := by
      exact norm_sum_le (Finset.univ : Finset (SourcePoint P)) _
    _ = (P : ℝ) := by
      simp [MAPFordBoundaryCrossFourier.fordBoundaryBlock,
        fordIntegerCharTerm, sourcePoint_card]

lemma completeMoment_eq_fordA
    {S k P : ℕ} (hP : 1 ≤ P) [NeZero (momentModulus S k P)] :
    (completeMoment S k P : ℝ) =
      fordA (fun alpha : Fin k → ZMod (momentModulus S k P) =>
        ‖MAPFordBoundaryCrossFourier.fordBoundaryBlock
          (zeroBase (k := k)) alpha‖ ^ 2)
      (fun alpha : Fin k → ZMod (momentModulus S k P) =>
        ‖MAPFordBoundaryCrossFourier.fordBoundaryBlock
          (powerFrequency (k := k) (P := P)) alpha‖) S := by
  have hcard := FordBoundaryEnergyMoments.energy_card_eq_fordA
    (L := momentModulus S k P) (k := k) (s := S)
    (f := zeroBase (k := k)) (g := powerFrequency (k := k) (P := P))
    (moment_wordFreq_bound (s := S) (k := k) (P := P) hP)
  calc
    (completeMoment S k P : ℝ) =
        Fintype.card (EnergyZero (zeroBase (k := k))
          (powerFrequency (k := k) (P := P)) S) := by
      exact_mod_cast completeMoment_eq_energy_card S k P
    _ = fordA (fun alpha : Fin k → ZMod (momentModulus S k P) =>
        ‖MAPFordBoundaryCrossFourier.fordBoundaryBlock
          (zeroBase (k := k)) alpha‖ ^ 2)
      (fun alpha : Fin k → ZMod (momentModulus S k P) =>
        ‖MAPFordBoundaryCrossFourier.fordBoundaryBlock
          (powerFrequency (k := k) (P := P)) alpha‖) S := hcard

end FordCompleteMomentLift

#print axioms FordCompleteMomentLift.completeMoment_eq_energy_card
