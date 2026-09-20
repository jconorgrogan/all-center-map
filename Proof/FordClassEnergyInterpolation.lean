import FordClassEnergyFourierCount
import FordBoundaryEnergyMoments
import FordLemma33WeightedHolder

open scoped BigOperators ZMod ComplexConjugate
open FordClassEnergyMoment FordClassEnergyFourierCount
open FordBoundaryWeightedHolder FordBoundaryEnergyMoments FordLemma33WeightedHolder FordBoundaryCountGeometry
open MAPFordBoundaryCrossFourier MAPFordP16FiniteFourierBridge

noncomputable section
namespace FordClassEnergyInterpolation

variable {A U C : Type*} [Fintype A] [Fintype U] [Fintype C]
variable {L k : ℕ} [NeZero L]

theorem classEnergy_card_interpolation
    (f : A → Fin k → ℤ) (g : U → Fin k → ℤ) (cls : U → C)
    (hk : 1 ≤ k)
    (hboundK : ∀ r j,
      |classEnergyFrequency f g cls k r j| < (L : ℤ))
    (hboundKm1 : ∀ r j,
      |classEnergyFrequency f g cls (k-1) r j| < (L : ℤ))
    (hboundBase : ∀ a b j, |f a j - f b j| < (L : ℤ)) :
    (Fintype.card (ClassEnergyZero f g cls (k-1)) : ℝ)^k ≤
      (Fintype.card (ClassEnergyZero f g cls k) : ℝ)^(k-1) *
        Fintype.card (BaseZero f) := by
  letI : Nonempty (Fin k → ZMod L) := ⟨fun _ => 0⟩
  let w : (Fin k → ZMod L) → ℝ := fun alpha =>
    ‖fordBoundaryBlock f alpha‖ ^ 2
  let a : (Fin k → ZMod L) → ℝ := fun alpha =>
    realI g cls alpha
  have hw : ∀ alpha, 0 ≤ w alpha := by
    intro alpha
    dsimp [w]
    positivity
  have ha : ∀ alpha, 0 ≤ a alpha := by
    intro alpha
    dsimp [a, realI]
    positivity
  have hh := weighted_moment_interpolation w a k hk hw ha
  have hkm1 := classEnergy_card_eq_fourier_avg (L := L) (n := k-1)
    f g cls hboundKm1
  have hkcount := classEnergy_card_eq_fourier_avg (L := L) (n := k)
    f g cls hboundK
  have hbase := base_card_eq_fordB (L := L) f hboundBase
  have hgrid : Fintype.card (Fin k → ZMod L) = L ^ k := by simp
  have hkm1' : (Fintype.card (ClassEnergyZero f g cls (k-1)) : ℝ) =
      fordAvg (fun alpha => w alpha * a alpha ^ (k-1)) := by
    rw [fordAvg, Finset.expect_eq_sum_div_card, Finset.card_univ, hgrid]
    simpa [w, a] using hkm1
  have hkcount' : (Fintype.card (ClassEnergyZero f g cls k) : ℝ) =
      fordAvg (fun alpha => w alpha * a alpha ^ k) := by
    rw [fordAvg, Finset.expect_eq_sum_div_card, Finset.card_univ, hgrid]
    simpa [w, a] using hkcount
  simpa [fordA, fordB, w, a, hkm1', hkcount', hbase] using hh

end FordClassEnergyInterpolation

#print axioms FordClassEnergyInterpolation.classEnergy_card_interpolation
