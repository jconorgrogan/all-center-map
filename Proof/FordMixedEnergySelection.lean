import FordLemma33MixedProduct
import FordBoundaryEnergyMoments
import FordBoundaryCrossFourier

open scoped BigOperators ZMod ComplexConjugate
open FordBoundaryWeightedHolder
open FordBoundaryCountGeometry
open FordBoundaryPinnedCross
open MAPFordBoundaryCrossFourier
open FordBoundaryEnergyMoments
open FordLemma33MixedProduct

noncomputable section
namespace FordMixedEnergySelection

variable {A U H : Type*} [Fintype A] [Fintype U] [Fintype H] [Nonempty H]
variable {k L : ℕ} [NeZero L]

theorem mixed_energy_selection
    (f : A → Fin k → ℤ) (g : H → U → Fin k → ℤ)
    (hk : 1 ≤ k)
    (hbase : ∀ a a' j, |f a j - f a' j| < (L : ℤ))
    (henergy : ∀ h r r' j,
      |wordFreq f (g h) k r j - wordFreq f (g h) k r' j| < (L : ℤ)) :
    ∃ h0 : H, ∀ hs : Fin k → H,
      (fordAvg (fun alpha : Fin k → ZMod L =>
        ‖fordBoundaryBlock f alpha‖ ^ 2 *
          ∏ i, ‖fordBoundaryBlock (g (hs i)) alpha‖)) ^ 2 ≤
        (Fintype.card (BaseZero f) : ℝ) *
          (Fintype.card (EnergyZero f (g h0) k) : ℝ) := by
  letI : Nonempty (Fin k → ZMod L) := ⟨fun _ => 0⟩
  let w : (Fin k → ZMod L) → ℝ := fun alpha =>
    ‖fordBoundaryBlock f alpha‖ ^ 2
  let b : H → (Fin k → ZMod L) → ℝ := fun h alpha =>
    ‖fordBoundaryBlock (g h) alpha‖
  have hw : ∀ alpha, 0 ≤ w alpha := by
    intro alpha
    dsimp [w]
    positivity
  have hb : ∀ h alpha, 0 ≤ b h alpha := by
    intro h alpha
    dsimp [b]
    positivity
  obtain ⟨h0, hh⟩ := mixed_product_uniform_bound w b k hk hw hb
  refine ⟨h0, ?_⟩
  intro hs
  have hB := base_card_eq_fordB (L := L) f hbase
  have hE := energy_card_eq_fordA (L := L) f (g h0) (henergy h0)
  simpa [w, b, fordA, hB, hE] using hh hs

end FordMixedEnergySelection

#print axioms FordMixedEnergySelection.mixed_energy_selection
