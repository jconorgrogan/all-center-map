import FordBoundaryPinnedCross
import FordBoundaryCrossFourier
import FordBoundaryWeightedHolder

open scoped BigOperators ZMod
open FordBoundaryCountGeometry FordBoundaryPinnedCross FordBoundarySlotSymmetry
open MAPFordBoundaryCrossFourier MAPFordP16FiniteFourierBridge FordBoundaryWeightedHolder
noncomputable section
namespace FordBoundaryPinnedBound

variable {A U : Type*} [Fintype A] [Fintype U] {L k : ℕ} [NeZero L]

lemma char_norm_one (alpha : Fin k → ZMod L) (v : Fin k → ℤ) :
    ‖fordIntegerCharTerm alpha v‖ = 1 := by
  simp [fordIntegerCharTerm, norm_prod, ZMod.stdAddChar_apply, Circle.norm_coe]

lemma block_shift (f : A → Fin k → ℤ) (v : Fin k → ℤ) (alpha : Fin k → ZMod L) :
    fordBoundaryBlock (fun a j => f a j + v j) alpha =
      fordBoundaryBlock f alpha * fordIntegerCharTerm alpha v := by
  unfold fordBoundaryBlock
  simp_rw [← char_term_add]
  rw [Finset.sum_mul]

lemma block_word (f : A → Fin k → ℤ) (g : U → Fin k → ℤ) (s : ℕ)
    (alpha : Fin k → ZMod L) :
    fordBoundaryBlock (wordFreq f g s) alpha =
      fordBoundaryBlock f alpha * (fordBoundaryBlock g alpha)^s :=
  block_product_word f g alpha

lemma block_pinned (f : A → Fin k → ℤ) (g : U → Fin k → ℤ) (e : U) (s : ℕ)
    (alpha : Fin k → ZMod L) :
    fordBoundaryBlock (pinnedFreq f g e s) alpha =
      (fordBoundaryBlock f alpha * fordIntegerCharTerm alpha (g e)) *
        (fordBoundaryBlock g alpha)^s := by
  have hh := block_product_word (fun a j => f a j + g e j) g alpha (s := s)
  change fordBoundaryBlock (pinnedFreq f g e s) alpha =
    fordBoundaryBlock (fun a j => f a j + g e j) alpha * (fordBoundaryBlock g alpha)^s at hh
  rw [block_shift] at hh
  exact hh

lemma pinned_word_norm_product (f : A → Fin k → ℤ) (g : U → Fin k → ℤ) (e : U) (s : ℕ)
    (alpha : Fin k → ZMod L) :
    ‖fordBoundaryBlock (pinnedFreq f g e s) alpha‖ *
      ‖fordBoundaryBlock (wordFreq f g (s+1)) alpha‖ =
      ‖fordBoundaryBlock f alpha‖^2 * ‖fordBoundaryBlock g alpha‖^(2*(s+1)-1) := by
  rw [block_pinned, block_word]
  simp only [norm_mul, norm_pow, char_norm_one, mul_one]
  calc
    _ = ‖fordBoundaryBlock f alpha‖^2 *
        (‖fordBoundaryBlock g alpha‖^s * ‖fordBoundaryBlock g alpha‖^(s+1)) := by ring
    _ = _ := by
      rw [← pow_add]
      congr 2
      omega

lemma wordFreq_cons (f : A → Fin k → ℤ) (g : U → Fin k → ℤ) (e : U) (s : ℕ)
    (r : A × (Fin s → U)) :
    wordFreq f g (s+1) (r.1,Fin.cons e r.2) = pinnedFreq f g e s r := by
  funext j
  simp only [wordFreq, pinnedFreq, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  ring

/-- A single pinned endpoint is bounded by the exact normalized odd moment. -/
theorem pinned_zero_le_H (f : A → Fin k → ℤ) (g : U → Fin k → ℤ) (e : U) (s : ℕ)
    (hbound : ∀ a b j,
      |wordFreq f g (s+1) a j - wordFreq f g (s+1) b j| < (L : ℤ)) :
    (Fintype.card (Pinned f g (s+1) e (false,0)) : ℝ) ≤
      fordH (fun alpha : Fin k → ZMod L => ‖fordBoundaryBlock f alpha‖^2)
        (fun alpha => ‖fordBoundaryBlock g alpha‖) (s+1) := by
  have hpin : ∀ a b j,
      |pinnedFreq f g e s a j - wordFreq f g (s+1) b j| < (L : ℤ) := by
    intro a b j
    have hh := hbound (a.1,Fin.cons e a.2) b j
    rw [wordFreq_cons] at hh
    exact hh
  have hc := cross_count_le (pinnedFreq f g e s) (wordFreq f g (s+1)) hpin
  have hH :
      fordH (fun alpha : Fin k → ZMod L => ‖fordBoundaryBlock f alpha‖^2)
        (fun alpha => ‖fordBoundaryBlock g alpha‖) (s+1) =
      (∑ alpha : Fin k → ZMod L,
        ‖fordBoundaryBlock (pinnedFreq f g e s) alpha‖ *
          ‖fordBoundaryBlock (wordFreq f g (s+1)) alpha‖) / (L : ℝ)^k := by
    unfold fordH fordAvg
    rw [Finset.expect_eq_sum_div_card]
    have hd : ((Finset.univ : Finset (Fin k → ZMod L)).card : ℝ) = (L : ℝ)^k := by
      simp [Fintype.card_fun, ZMod.card]
    rw [hd]
    congr 1
    apply Finset.sum_congr rfl
    intro alpha ha
    exact (pinned_word_norm_product f g e s alpha).symm
  rw [hH, pinned_zero_card_eq_cross]
  exact hc

/-- All 2s slots use the same odd-moment bound; the actual union count is retained. -/
theorem boundary_le_odd_moment (f : A → Fin k → ℤ) (g : U → Fin k → ℤ) (e : U)
    (s : ℕ) (hs : 1 ≤ s)
    (hbound : ∀ a b j, |wordFreq f g s a j - wordFreq f g s b j| < (L : ℤ)) :
    (Fintype.card (Boundary f g s e) : ℝ) ≤
      2 * (s : ℝ) * fordH (fun alpha : Fin k → ZMod L => ‖fordBoundaryBlock f alpha‖^2)
        (fun alpha => ‖fordBoundaryBlock g alpha‖) s := by
  cases s with
  | zero => omega
  | succ n =>
    apply boundary_le_two_s_mul_real f g e
    intro i
    have hi := pinned_le_fixed_left f g e (0 : Fin (n+1)) i
    have hiR : (Fintype.card (Pinned f g (n+1) e i) : ℝ) ≤
        Fintype.card (Pinned f g (n+1) e (false,0)) := by exact_mod_cast hi
    exact hiR.trans (pinned_zero_le_H f g e n hbound)

end FordBoundaryPinnedBound
#print axioms FordBoundaryPinnedBound.pinned_zero_le_H
#print axioms FordBoundaryPinnedBound.boundary_le_odd_moment
