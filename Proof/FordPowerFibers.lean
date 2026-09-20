import FordPhaseFibers
import FordCompleteSystemMoment

open scoped BigOperators
noncomputable section
namespace FordPowerFibers

def powerMap (r k M : ℕ) (x : Fin r → Fin M) : Fin k → ℕ :=
  fun j => ∑ i, ((x i).val + 1) ^ (j.val + 1)

theorem powerMap_eq_iff (r k M : ℕ) (x y : Fin r → Fin M) :
    powerMap r k M x = powerMap r k M y ↔
      ∀ j ∈ Finset.Icc 1 k,
        (∑ i, ((x i).val + 1) ^ j) = ∑ i, ((y i).val + 1) ^ j := by
  constructor
  · intro h j hj
    have hj' := Finset.mem_Icc.mp hj
    have hidx : j - 1 < k := by omega
    have he := congrFun h ⟨j - 1, hidx⟩
    simpa [powerMap, Nat.sub_add_cancel hj'.1] using he
  · intro h
    funext j
    exact h (j.val + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)

theorem actual_moment_fiber_identity (r k M : ℕ)
    (S : Finset (Fin k → ℕ)) (hS : ∀ x, powerMap r k M x ∈ S) :
    ∑ c ∈ S, FordPhaseFibers.multiplicity (powerMap r k M) c ^ 2 =
      MAPFordCompleteSystemMoment.completeMoment r k M := by
  classical
  rw [FordPhaseFibers.collision_mass _ _ hS]
  unfold MAPFordCompleteSystemMoment.completeMoment
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact powerMap_eq_iff r k M p.1 p.2

theorem actual_mass (r k M : ℕ)
    (S : Finset (Fin k → ℕ)) (hS : ∀ x, powerMap r k M x ∈ S) :
    ∑ c ∈ S, FordPhaseFibers.multiplicity (powerMap r k M) c = M ^ r := by
  classical
  rw [FordPhaseFibers.total_mass _ _ hS]
  simp

end FordPowerFibers
#print axioms FordPowerFibers.actual_moment_fiber_identity
#print axioms FordPowerFibers.actual_mass
