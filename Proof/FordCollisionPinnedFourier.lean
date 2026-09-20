import FordCollisionPinnedBound

open scoped BigOperators ZMod ComplexConjugate
open MAPFordBoundaryCrossFourier MAPFordP16FiniteFourierBridge
open FordCollisionPinnedBound

noncomputable section
namespace FordCollisionPinnedFourier

variable {A U : Type*} [Fintype A] [Fintype U]
variable {L k s : ℕ} [NeZero L]

def pinLeftFreq (f : A → Fin k → ℤ) (g : U → Fin k → ℤ) (s : ℕ)
    (r : (A × U) × (Fin s → U)) : Fin k → ℤ :=
  fun j => f r.1.1 j + g r.1.2 j + g r.1.2 j +
    ∑ i : Fin s, g (r.2 i) j

def pinRightFreq (f : A → Fin k → ℤ) (g : U → Fin k → ℤ) (s : ℕ)
    (r : A × (Fin (s+2) → U)) : Fin k → ℤ :=
  fun j => f r.1 j + ∑ i : Fin (s+2), g (r.2 i) j

theorem collisionPinned_count_le_cross_avg
    (f : A → Fin k → ℤ) (g : U → Fin k → ℤ)
    (hbound : ∀ x y j,
      |pinLeftFreq f g s x j - pinRightFreq f g s y j| < (L : ℤ)) :
    (Fintype.card (CollisionPinned f g s) : ℝ) ≤
      (∑ alpha : Fin k → ZMod L,
        ‖fordBoundaryBlock (pinLeftFreq f g s) alpha‖ *
          ‖fordBoundaryBlock (pinRightFreq f g s) alpha‖) / (L : ℝ)^k := by
  rw [collisionPinned_card_eq_pinCross f g s]
  have hc := cross_count_le (pinLeftFreq f g s) (pinRightFreq f g s) hbound
  simpa [PinCross, pinLeftFreq, pinRightFreq, funext_iff] using hc

end FordCollisionPinnedFourier

#print axioms FordCollisionPinnedFourier.collisionPinned_count_le_cross_avg

namespace FordCollisionPinnedFourier

variable {A U : Type*} [Fintype A] [Fintype U]
variable {L k s : ℕ} [NeZero L]

lemma left_block_factor
    (f : A → Fin k → ℤ) (g : U → Fin k → ℤ)
    (alpha : Fin k → ZMod L) :
    fordBoundaryBlock (pinLeftFreq f g s) alpha =
      fordBoundaryBlock f alpha *
        fordBoundaryBlock (fun (u : U) (j : Fin k) => g u j + g u j) alpha *
        (fordBoundaryBlock g alpha)^s := by
  have h := block_product_word
    (f := fun (r : A × U) (j : Fin k) => f r.1 j + g r.2 j + g r.2 j)
    (h := g) (alpha := alpha) (s := s)
  change fordBoundaryBlock (pinLeftFreq f g s) alpha =
    fordBoundaryBlock (fun (r : A × U) (j : Fin k) => f r.1 j + g r.2 j + g r.2 j) alpha *
      (fordBoundaryBlock g alpha)^s at h
  have hbase : fordBoundaryBlock
      (fun (r : A × U) (j : Fin k) => f r.1 j + g r.2 j + g r.2 j) alpha =
      fordBoundaryBlock f alpha *
        fordBoundaryBlock (fun (u : U) (j : Fin k) => g u j + g u j) alpha := by
    unfold fordBoundaryBlock
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    rw [← Fintype.sum_prod_type']
    apply Finset.sum_congr rfl
    intro r hr
    have h1 := char_term_add alpha (fun j => f r.1 j) (fun j => g r.2 j)
    have h2 := char_term_add alpha
      (fun j => f r.1 j + g r.2 j) (fun j => g r.2 j)
    have h4 := char_term_add alpha (fun j => g r.2 j) (fun j => g r.2 j)
    rw [← h2, ← h1, ← h4]
    ring
  rw [hbase] at h
  exact h

lemma right_block_factor
    (f : A → Fin k → ℤ) (g : U → Fin k → ℤ)
    (alpha : Fin k → ZMod L) :
    fordBoundaryBlock (pinRightFreq f g (s)) alpha =
      fordBoundaryBlock f alpha * (fordBoundaryBlock g alpha)^(s+2) := by
  exact block_product_word f g alpha

theorem collisionPinned_norm_product
    (f : A → Fin k → ℤ) (g : U → Fin k → ℤ)
    (alpha : Fin k → ZMod L) :
    ‖fordBoundaryBlock (pinLeftFreq f g s) alpha‖ *
      ‖fordBoundaryBlock (pinRightFreq f g s) alpha‖ =
      ‖fordBoundaryBlock f alpha‖^2 *
        ‖fordBoundaryBlock (fun (u : U) (j : Fin k) => g u j + g u j) alpha‖ *
        ‖fordBoundaryBlock g alpha‖^(2*(s+2)-2) := by
  rw [left_block_factor, right_block_factor]
  simp only [norm_mul, norm_pow]
  let X : ℝ := ‖fordBoundaryBlock f alpha‖
  let Y : ℝ := ‖fordBoundaryBlock (fun (u : U) (j : Fin k) => g u j + g u j) alpha‖
  let Z : ℝ := ‖fordBoundaryBlock g alpha‖
  change X * Y * Z^s * (X * Z^(s+2)) = X^2 * Y * Z^(2*(s+2)-2)
  calc
    X * Y * Z^s * (X * Z^(s+2)) = X^2 * Y * (Z^s * Z^(s+2)) := by ring
    _ = X^2 * Y * Z^(s + (s+2)) := by rw [← pow_add]
    _ = X^2 * Y * Z^(2*(s+2)-2) := by
      have hs : s + (s+2) = 2*(s+2)-2 := by omega
      rw [hs]

end FordCollisionPinnedFourier

#print axioms FordCollisionPinnedFourier.collisionPinned_norm_product

namespace FordCollisionPinnedFourier
variable {A U : Type*} [Fintype A] [Fintype U]
variable {L k s : ℕ} [NeZero L]

theorem collisionPinned_count_le_factorized
    (f : A → Fin k → ℤ) (g : U → Fin k → ℤ)
    (hbound : ∀ x y j,
      |pinLeftFreq f g s x j - pinRightFreq f g s y j| < (L : ℤ)) :
    (Fintype.card (CollisionPinned f g s) : ℝ) ≤
      (∑ alpha : Fin k → ZMod L,
        ‖fordBoundaryBlock f alpha‖^2 *
          ‖fordBoundaryBlock (fun (u : U) (j : Fin k) => g u j + g u j) alpha‖ *
          ‖fordBoundaryBlock g alpha‖^(2*(s+2)-2)) / (L : ℝ)^k := by
  calc
    (Fintype.card (CollisionPinned f g s) : ℝ) ≤
        (∑ alpha : Fin k → ZMod L,
          ‖fordBoundaryBlock (pinLeftFreq f g s) alpha‖ *
            ‖fordBoundaryBlock (pinRightFreq f g s) alpha‖) / (L : ℝ)^k :=
      collisionPinned_count_le_cross_avg f g hbound
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro alpha ha
      exact collisionPinned_norm_product f g alpha

end FordCollisionPinnedFourier

#print axioms FordCollisionPinnedFourier.collisionPinned_count_le_factorized
