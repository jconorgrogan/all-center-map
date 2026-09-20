import FordSignedMixedCount
import FordSignedMixedCommonModulus
import FordMixedEnergySelection

open scoped BigOperators ZMod ComplexConjugate
open FordBoundaryCountGeometry
open FordBoundaryPinnedCross
open MAPFordBoundaryCrossFourier
open FordSignedMixedCount
open FordSignedMixedCommonModulus
open FordMixedEnergySelection
open FordBoundaryWeightedHolder

noncomputable section
namespace FordSignedMixedSelectionActual

variable {A U H : Type*} [Fintype A] [Fintype U] [Fintype H] [Nonempty H]
variable {k : ℕ}

theorem signed_zero_card_selection
    (f : A → Fin k → ℤ) (g : H → U → Fin k → ℤ)
    (hk : 1 ≤ k) :
    ∃ h0 : H, ∀ (hs : Fin k → H) (sign : Fin k → Bool),
      (Fintype.card (SignedZero f g hs sign) : ℝ)^2 ≤
        (Fintype.card (BaseZero f) : ℝ) *
          (Fintype.card (EnergyZero f (g h0) k) : ℝ) := by
  obtain ⟨L, hL, hSigned, hEnergy, hBase⟩ :=
    exists_signed_mixed_common_modulus f g
  letI : NeZero (L : ℕ) := ⟨Nat.ne_of_gt hL⟩
  obtain ⟨h0, hsel⟩ :=
    mixed_energy_selection (L := L) f g hk hBase hEnergy
  refine ⟨h0, ?_⟩
  intro hs sign
  have hcount := signed_zero_card_le (L := L) f g hs sign (hSigned sign hs)
  have hgrid : Fintype.card (Fin k → ZMod L) = L ^ k := by simp
  have havg :
      (∑ alpha : Fin k → ZMod L,
        (‖fordBoundaryBlock f alpha‖ ^ 2) *
          ∏ i : Fin k, ‖fordBoundaryBlock (g (hs i)) alpha‖) /
          (L : ℝ) ^ k =
        fordAvg (fun alpha : Fin k → ZMod L =>
          ‖fordBoundaryBlock f alpha‖ ^ 2 *
            ∏ i : Fin k, ‖fordBoundaryBlock (g (hs i)) alpha‖) := by
    unfold fordAvg
    rw [Finset.expect_eq_sum_div_card, Finset.card_univ, hgrid]
    have hcast : ((L ^ k : ℕ) : ℝ) = (L : ℝ) ^ k := by norm_num
    rw [hcast]
  rw [havg] at hcount
  have hE_nonneg :
      0 ≤ (Fintype.card (SignedZero f g hs sign) : ℝ) := by positivity
  have hM_nonneg :
      0 ≤ fordAvg (fun alpha : Fin k → ZMod L =>
        ‖fordBoundaryBlock f alpha‖ ^ 2 *
          ∏ i : Fin k, ‖fordBoundaryBlock (g (hs i)) alpha‖) := by
    exact Finset.expect_nonneg (fun alpha _ =>
      mul_nonneg (sq_nonneg _) (Finset.prod_nonneg (fun i _ => norm_nonneg _)))
  exact ((sq_le_sq₀ hE_nonneg hM_nonneg).2 hcount).trans (hsel hs)

end FordSignedMixedSelectionActual

#print axioms FordSignedMixedSelectionActual.signed_zero_card_selection
