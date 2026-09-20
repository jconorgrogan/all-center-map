import FordClassEnergyInterpolation
import FordClassEnergyCommonModulus

open scoped BigOperators ZMod ComplexConjugate
open FordClassEnergyMoment FordClassEnergyInterpolation FordClassEnergyCommonModulus
open FordBoundaryCountGeometry

noncomputable section
namespace FordClassEnergyInterpolationActual

variable {A U C : Type*} [Fintype A] [Fintype U] [Fintype C]
variable {k : ℕ}

theorem classEnergy_card_interpolation_actual
    (f : A → Fin k → ℤ) (g : U → Fin k → ℤ) (cls : U → C)
    (hk : 1 ≤ k) :
    (Fintype.card (ClassEnergyZero f g cls (k-1)) : ℝ)^k ≤
      (Fintype.card (ClassEnergyZero f g cls k) : ℝ)^(k-1) *
        Fintype.card (BaseZero f) := by
  obtain ⟨L, hL, hclass, hbase⟩ := exists_common_modulus f g cls
  letI : NeZero (L : ℕ) := ⟨Nat.ne_of_gt hL⟩
  apply classEnergy_card_interpolation (L := L) (k := k) f g cls hk
  · exact bound_full_classEnergyFrequency f g cls hclass
  · exact bound_previous_classEnergyFrequency f g cls hclass
  · exact hbase

end FordClassEnergyInterpolationActual

#print axioms FordClassEnergyInterpolationActual.classEnergy_card_interpolation_actual
