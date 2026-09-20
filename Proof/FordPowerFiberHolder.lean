import FordPowerFibers
import FordBilinearWeightedHolder

open scoped BigOperators
noncomputable section
namespace FordPowerFiberHolder

theorem actual_power_fiber_holder (r k M s : ℕ) (hs : 1 ≤ s)
    (S : Finset (Fin k → ℕ))
    (hS : ∀ x, FordPowerFibers.powerMap r k M x ∈ S)
    (F : (Fin k → ℕ) → ℂ) :
    ‖∑ x : Fin r → Fin M, F (FordPowerFibers.powerMap r k M x)‖ ^ (2 * s) ≤
      (M : ℝ) ^ (r * (2 * s - 2)) *
        (MAPFordCompleteSystemMoment.completeMoment r k M : ℝ) *
        ∑ c ∈ S, ‖F c‖ ^ (2 * s) := by
  classical
  let n := FordPhaseFibers.multiplicity (FordPowerFibers.powerMap r k M)
  have h := FordBilinearWeightedHolder.weighted_complex_sum_holder
    (fun c : S => n c) (fun c : S => F c) hs
  have hmass : (∑ c ∈ S, (n c : ℝ)) = (M : ℝ) ^ r := by
    exact_mod_cast FordPowerFibers.actual_mass r k M S hS
  have hmoment : (∑ c ∈ S, (n c : ℝ) ^ 2) =
      (MAPFordCompleteSystemMoment.completeMoment r k M : ℝ) := by
    exact_mod_cast FordPowerFibers.actual_moment_fiber_identity r k M S hS
  have hgroup := FordPhaseFibers.grouped_sum
    (FordPowerFibers.powerMap r k M) S hS F
  rw [Finset.sum_coe_sort S (fun c => (n c : ℂ) * F c),
    Finset.sum_coe_sort S (fun c => (n c : ℝ)),
    Finset.sum_coe_sort S (fun c => (n c : ℝ) ^ 2),
    Finset.sum_coe_sort S (fun c => ‖F c‖ ^ (2 * s))] at h
  rw [hmass, hmoment, ← pow_mul] at h
  simpa only [hgroup, n] using h

end FordPowerFiberHolder
#print axioms FordPowerFiberHolder.actual_power_fiber_holder
