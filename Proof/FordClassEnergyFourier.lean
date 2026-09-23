import FordClassEnergyMoment
import FordLemma33FourierPrimitive

open scoped BigOperators ZMod ComplexConjugate
open FordClassEnergyMoment FordLemma33FourierPrimitive
open MAPFordBoundaryCrossFourier MAPFordP16FiniteFourierBridge

noncomputable section
namespace FordClassEnergyFourier

variable {A U C : Type*} [Fintype A] [Fintype U] [Fintype C]
variable {L k n : ℕ} [NeZero L]

lemma class_energy_integrand_expand
    (f : A → Fin k → ℤ) (g : U → Fin k → ℤ) (cls : U → C)
    (alpha : Fin k → ZMod L) :
    ((‖fordBoundaryBlock f alpha‖ ^ 2 : ℝ) : ℂ) *
        ((realI g cls alpha ^ n : ℝ) : ℂ) =
      ∑ r : (A × A) × (Fin n → classPairCarrier cls),
        fordIntegerCharTerm alpha (classEnergyFrequency f g cls n r) := by
  have hf := norm_sum_expand (fun a : A =>
    fordIntegerCharTerm alpha (fun j => f a j))
  have hI := pairBlock_eq_sum_energy g cls alpha
  have hIcast : (realI g cls alpha : ℂ) =
      ∑ q : classPairCarrier cls,
        fordIntegerCharTerm alpha (classPairFrequency g cls q) := by
    simpa [realI, pairBlock, pairFrequency] using! hI.symm
  have hf2 := hf
  simp_rw [char_term_neg] at hf2
  rw [show ((‖fordBoundaryBlock f alpha‖ ^ 2 : ℝ) : ℂ) =
      ∑ a : A, ∑ b : A,
        fordIntegerCharTerm alpha (fun j => f a j) *
          fordIntegerCharTerm alpha (fun j => -f b j) by
    simpa [fordBoundaryBlock] using hf2]
  rw [show ((realI g cls alpha ^ n : ℝ) : ℂ) =
      ((realI g cls alpha : ℂ) ^ n) by push_cast; rfl]
  rw [hIcast, Fintype.sum_pow]
  simp_rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [← Fintype.sum_prod_type']
  rw [← Fintype.sum_prod_type']
  apply Finset.sum_congr rfl
  intro r hr
  rw [char_prod_term_sum]
  rw [char_term_add]
  rw [char_term_add]
  rfl

end FordClassEnergyFourier

#print axioms FordClassEnergyFourier.class_energy_integrand_expand
