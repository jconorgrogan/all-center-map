import FordCollisionThreeMoments
import FordCollisionPinnedFourier

open scoped BigOperators ZMod ComplexConjugate

namespace FordCollisionActualHolder

open FordBoundaryCountGeometry
open FordCollisionPinnedBound
open FordCollisionPinnedFourier
open FordCollisionThreeMoments
open FordCollisionThreeHolder
open FordBoundaryWeightedHolder
open FordBoundaryPinnedCross
open MAPFordBoundaryCrossFourier

noncomputable section

theorem collision_pinned_holder
    {A U : Type*} [Fintype A] [Fintype U]
    {k : ℕ} (hk : 2 ≤ k)
    (f : A → Fin k → ℤ) (g : U → Fin k → ℤ) :
    (Fintype.card (CollisionPinned f g (k - 2)) : ℝ) ^ (2 * k) ≤
      Fintype.card (EnergyZero f (doubled g) k) *
        (Fintype.card (EnergyZero f g k) : ℝ) ^ (2 * k - 2) *
          Fintype.card (BaseZero f) := by
  let s : ℕ := k - 2
  have hs : s + 2 = k := by
    dsimp [s]
    omega
  let pinL : ((A × U) × (Fin s → U)) → Fin k → ℤ :=
    pinLeftFreq f g s
  let pinR : (A × (Fin (s + 2) → U)) → Fin k → ℤ :=
    pinRightFreq f g s
  let third : A ⊕ (((A × U) × (Fin s → U)) ⊕
      (A × (Fin (s + 2) → U))) → Fin k → ℤ :=
    Sum.elim f (Sum.elim pinL pinR)
  obtain ⟨L, hL, henergy, henergy2, hthird⟩ :=
    exists_common_modulus_three
      (wordFreq f g k) (wordFreq f (doubled g) k) third
  letI : NeZero L := ⟨Nat.ne_of_gt hL⟩
  have hbase : ∀ a a' j, |f a j - f a' j| < (L : ℤ) := by
    intro a a' j
    have hh := hthird (Sum.inl a) (Sum.inl a') j
    simpa [third] using hh
  have hpin : ∀ x y j, |pinL x j - pinR y j| < (L : ℤ) := by
    intro x y j
    have hh := hthird (Sum.inr (Sum.inl x)) (Sum.inr (Sum.inr y)) j
    simpa [third, pinL, pinR] using hh
  have hpinRaw := collisionPinned_count_le_factorized
    (s := s) f g hpin
  have hpinMoment :
      (Fintype.card (CollisionPinned f g (k - 2)) : ℝ) ≤
        fordThreeMoment
          (fun alpha : Fin k → ZMod L => ‖fordBoundaryBlock f alpha‖ ^ 2)
          (fun alpha : Fin k → ZMod L => ‖fordBoundaryBlock (doubled g) alpha‖)
          (fun alpha : Fin k → ZMod L => ‖fordBoundaryBlock g alpha‖) k := by
    have hsum :
        (∑ alpha : Fin k → ZMod L,
          ‖fordBoundaryBlock f alpha‖ ^ 2 *
            ‖fordBoundaryBlock (fun (u : U) (j : Fin k) =>
              g u j + g u j) alpha‖ *
            ‖fordBoundaryBlock g alpha‖ ^ (2 * (s + 2) - 2)) /
            (L : ℝ) ^ k =
          fordThreeMoment
            (fun alpha : Fin k → ZMod L => ‖fordBoundaryBlock f alpha‖ ^ 2)
            (fun alpha : Fin k → ZMod L => ‖fordBoundaryBlock (doubled g) alpha‖)
            (fun alpha : Fin k → ZMod L => ‖fordBoundaryBlock g alpha‖) k := by
      have hdouble :
          (fun (u : U) (j : Fin k) => g u j + g u j) = doubled g := by
        funext u j
        simp [doubled]
        ring
      rw [hdouble, hs]
      unfold fordThreeMoment fordThreeAvg
      have hcard : Fintype.card (Fin k → ZMod L) = L ^ k := by simp
      rw [Finset.expect_eq_sum_div_card, Finset.card_univ, hcard]
      have hcast : ((L ^ k : ℕ) : ℝ) = (L : ℝ) ^ k := by norm_num
      rw [hcast]
    rw [← hsum]
    simpa [hs] using hpinRaw
  exact finite_energy_three_factor f g hk hbase henergy henergy2 hpinMoment

end
end FordCollisionActualHolder

#print axioms FordCollisionActualHolder.collision_pinned_holder
