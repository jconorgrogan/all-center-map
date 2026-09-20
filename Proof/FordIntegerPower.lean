import FordPowerBox
import FordDirichletShells

open scoped BigOperators
noncomputable section
namespace FordIntegerPower

/-- Exact integer-vector lift of the literal positive-coordinate power sums. -/
def intPowerMap (r k M : ℕ) (x : Fin r → Fin M) : Fin k → ℤ :=
  fun j => (FordPowerFibers.powerMap r k M x j : ℤ)

def differenceBox (r k M : ℕ) : Finset (Fin k → ℤ) :=
  Fintype.piFinset (fun j => FordDirichletShells.diffSet (r * M ^ (j.val + 1)))

lemma intPowerMap_eq_iff (r k M : ℕ) (x y : Fin r → Fin M) :
    intPowerMap r k M x = intPowerMap r k M y ↔
      FordPowerFibers.powerMap r k M x = FordPowerFibers.powerMap r k M y := by
  constructor
  · intro h
    funext j
    have hj := congrFun h j
    dsimp [intPowerMap] at hj
    exact_mod_cast hj
  · intro h
    funext j
    dsimp [intPowerMap]
    rw [h]

/-- The exact signed differences stay inside the strict integer box. -/
theorem difference_mem_box {r k M : ℕ} (hr : 1 ≤ r)
    (x y : Fin r → Fin M) :
    intPowerMap r k M x - intPowerMap r k M y ∈ differenceBox r k M := by
  classical
  simp only [differenceBox, Fintype.mem_piFinset]
  intro j
  have hx := FordPowerBox.powerMap_mem_Icc hr x j
  have hy := FordPowerBox.powerMap_mem_Icc hr y j
  obtain ⟨hxlo, hxhi⟩ := Finset.mem_Icc.mp hx
  obtain ⟨hylo, hyhi⟩ := Finset.mem_Icc.mp hy
  have hxloZ : (1 : ℤ) ≤ (FordPowerFibers.powerMap r k M x j : ℤ) := by exact_mod_cast hxlo
  have hyloZ : (1 : ℤ) ≤ (FordPowerFibers.powerMap r k M y j : ℤ) := by exact_mod_cast hylo
  have hxhiZ : (FordPowerFibers.powerMap r k M x j : ℤ) ≤ (r * M ^ (j.val + 1) : ℕ) := by exact_mod_cast hxhi
  have hyhiZ : (FordPowerFibers.powerMap r k M y j : ℤ) ≤ (r * M ^ (j.val + 1) : ℕ) := by exact_mod_cast hyhi
  change (intPowerMap r k M x j - intPowerMap r k M y j) ∈
    FordDirichletShells.diffSet (r * M ^ (j.val + 1))
  simp only [FordDirichletShells.diffSet, Finset.mem_Icc, intPowerMap]
  constructor <;> omega

end FordIntegerPower
#print axioms FordIntegerPower.intPowerMap_eq_iff
#print axioms FordIntegerPower.difference_mem_box
