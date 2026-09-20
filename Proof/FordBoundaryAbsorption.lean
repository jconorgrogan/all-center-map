import FordBoundaryAlias
import FordBoundaryEnergyMoments
import FordBoundaryPinnedBound
import FordBoundaryScalar

open scoped BigOperators ZMod
open FordBoundaryCountGeometry FordBoundaryPinnedCross FordBoundaryWeightedHolder
open MAPFordBoundaryCrossFourier
noncomputable section
namespace FordBoundaryAbsorption

/-- Removing one endpoint loses at most half the literal solution count once
there are more than (4s)^2 letters. Fourier grids and moments are supplied
internally, with one common no-alias modulus for both required counts. -/
theorem energy_le_twice_interior {A U : Type*} [Fintype A] [Fintype U] {k : ℕ}
    (f : A → Fin k → ℤ) (g : U → Fin k → ℤ) (e : U) (s : ℕ) (hs : 1 ≤ s)
    (hsize : (4*s)^2 < Fintype.card U) :
    Fintype.card (EnergyZero f g s) ≤ 2 * Fintype.card (Interior f g s e) := by
  obtain ⟨L, hL, hW, hB⟩ := FordBoundaryAlias.exists_common_modulus
    (fun r : State A U s => fun j => wordFreq f g s r.1 j - wordFreq f g s r.2 j)
    (fun r : A × A => fun j => f r.1 j - f r.2 j)
  letI : NeZero L := ⟨Nat.ne_of_gt hL⟩
  have hWbound : ∀ a b j, |wordFreq f g s a j - wordFreq f g s b j| < (L : ℤ) :=
    fun a b j => hW (a,b) j
  have hBbound : ∀ a b j, |f a j - f b j| < (L : ℤ) := fun a b j => hB (a,b) j
  let w : (Fin k → ZMod L) → ℝ := fun alpha => ‖fordBoundaryBlock f alpha‖^2
  let gn : (Fin k → ZMod L) → ℝ := fun alpha => ‖fordBoundaryBlock g alpha‖
  let E : ℝ := Fintype.card (EnergyZero f g s)
  let B : ℝ := Fintype.card (BaseZero f)
  let I : ℝ := Fintype.card (Interior f g s e)
  let M : ℝ := Fintype.card U
  let H : ℝ := fordH w gn s
  have hEnergy : E = fordA w gn s :=
    FordBoundaryEnergyMoments.energy_card_eq_fordA f g hWbound
  have hBase : B = fordB w :=
    FordBoundaryEnergyMoments.base_card_eq_fordB f hBbound
  have hHolder := weighted_holder_normalized w gn s hs
    (fun alpha => sq_nonneg _) (fun alpha => norm_nonneg _)
  rw [← hEnergy, ← hBase] at hHolder
  have hBoundary := FordBoundaryPinnedBound.boundary_le_odd_moment f g e s hs hWbound
  change (Fintype.card (Boundary f g s e) : ℝ) ≤ 2 * (s : ℝ) * H at hBoundary
  have hpartitionN := card_energy_partition f g s e
  have hpartitionR : E = (Fintype.card (Boundary f g s e) : ℝ) + I := by
    dsimp [E, I]
    exact_mod_cast hpartitionN
  have hpartition : E ≤ I + 2 * (s : ℝ) * H := by linarith
  have hdiagonal : M^s * B ≤ E := by
    have hh : (Fintype.card (BaseZero f) : ℝ) * (Fintype.card U : ℝ)^s ≤
        Fintype.card (EnergyZero f g s) := by exact_mod_cast diagonal_lower f g s
    simpa only [M, B, E, mul_comm] using hh
  have hsizeR : (4 * (s : ℝ))^2 < M := by
    dsimp [M]
    exact_mod_cast hsize
  have hresult := FordBoundaryScalar.interior_absorption hs
    (show 0 ≤ E from Nat.cast_nonneg _)
    (show 0 ≤ B from Nat.cast_nonneg _)
    (show 0 ≤ I from Nat.cast_nonneg _)
    hpartition hHolder hdiagonal hsizeR
  dsimp [E, I] at hresult
  exact_mod_cast hresult

end FordBoundaryAbsorption
#print axioms FordBoundaryAbsorption.energy_le_twice_interior
