import FordClassEnergyFourier

open scoped BigOperators ZMod ComplexConjugate
open FordClassEnergyMoment FordClassEnergyFourier
open MAPFordFiniteFourierCharacterSum MAPFordBoundaryCrossFourier MAPFordP16FiniteFourierBridge

noncomputable section
namespace FordClassEnergyFourierCount

variable {A U C : Type*} [Fintype A] [Fintype U] [Fintype C]
variable {L k n : ℕ} [NeZero L]

theorem classEnergy_card_eq_fourier_avg
    (f : A → Fin k → ℤ) (g : U → Fin k → ℤ) (cls : U → C)
    (hbound : ∀ r j,
      |classEnergyFrequency f g cls n r j| < (L : ℤ)) :
    (Fintype.card (ClassEnergyZero f g cls n) : ℝ) =
      (∑ alpha : Fin k → ZMod L,
        (‖fordBoundaryBlock f alpha‖ ^ 2) *
          (realI g cls alpha ^ n)) / (L : ℝ)^k := by
  let S : ℝ := ∑ alpha : Fin k → ZMod L,
      (‖fordBoundaryBlock f alpha‖ ^ 2) * (realI g cls alpha ^ n)
  have hzero := classEnergy_card_eq_zeroCarrier f g cls n
  have hcount := finite_masked_integer_character_count
    (freq := classEnergyFrequency f g cls n) (by
      intro r j
      exact hbound r j)
  have hexpand :
      (∑ alpha : Fin k → ZMod L,
        ((‖fordBoundaryBlock f alpha‖ ^ 2 : ℝ) : ℂ) *
          ((realI g cls alpha ^ n : ℝ) : ℂ)) =
        ∑ alpha : Fin k → ZMod L,
          ∑ r : (A × A) × (Fin n → classPairCarrier cls),
            fordIntegerCharTerm alpha (classEnergyFrequency f g cls n r) := by
    apply Finset.sum_congr rfl
    intro alpha ha
    exact class_energy_integrand_expand f g cls alpha
  have hcomplex :
      (S : ℂ) = (L : ℂ)^k * Fintype.card (classZeroCarrier f g cls n) := by
    calc
      (S : ℂ) = ∑ alpha : Fin k → ZMod L,
          ((‖fordBoundaryBlock f alpha‖ ^ 2 : ℝ) : ℂ) *
            ((realI g cls alpha ^ n : ℝ) : ℂ) := by
        simp [S, map_sum, mul_assoc]
      _ = ∑ alpha : Fin k → ZMod L,
          ∑ r : (A × A) × (Fin n → classPairCarrier cls),
            fordIntegerCharTerm alpha (classEnergyFrequency f g cls n r) := hexpand
      _ = (L : ℂ)^k * Fintype.card (classZeroCarrier f g cls n) := hcount
  have hreal : S = (L : ℝ)^k * Fintype.card (classZeroCarrier f g cls n) := by
    exact_mod_cast hcomplex
  have hL : 0 < (L : ℝ) := by
    exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne L))
  have hden : 0 < (L : ℝ)^k := pow_pos hL _
  rw [hzero]
  apply (eq_div_iff hden.ne').2
  simpa [S, mul_comm] using hreal.symm

end FordClassEnergyFourierCount

#print axioms FordClassEnergyFourierCount.classEnergy_card_eq_fourier_avg
