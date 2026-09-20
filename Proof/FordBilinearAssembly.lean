import FordPolynomialPhase
import FordFirstHolder
import FordPowerFiberHolder

open scoped BigOperators
noncomputable section
namespace FordBilinearAssembly

/-- Actual polynomial bilinear Holder step, with the complete moment count. -/
theorem polynomial_bilinear_holder {B : Type*} [Fintype B]
    (r k M s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s)
    (gamma : Fin k → ℝ) (bval : B → ℝ)
    (S : Finset (Fin k → ℕ))
    (hS : ∀ x, FordPowerFibers.powerMap r k M x ∈ S) :
    ∃ eps : B → ℂ, (∀ b, ‖eps b‖ = 1) ∧
      ‖∑ b : B, ∑ a : Fin M,
        FordPolynomialPhase.e (∑ j : Fin k,
          gamma j * bval b ^ (j.val + 1) *
            ((a.val + 1 : ℕ) : ℝ) ^ (j.val + 1))‖ ^ (r * (2 * s)) ≤
      (Fintype.card B : ℝ) ^ ((r - 1) * (2 * s)) *
        ((M : ℝ) ^ (r * (2 * s - 2)) *
          (MAPFordCompleteSystemMoment.completeMoment r k M : ℝ) *
            ∑ c ∈ S, ‖∑ b : B, eps b *
              FordPolynomialPhase.e (∑ j : Fin k,
                gamma j * bval b ^ (j.val + 1) * (c j : ℝ))‖ ^ (2 * s)) := by
  classical
  let Z : B → ℂ := fun b => ∑ a : Fin M,
    FordPolynomialPhase.e (∑ j : Fin k,
      gamma j * bval b ^ (j.val + 1) *
        ((a.val + 1 : ℕ) : ℝ) ^ (j.val + 1))
  obtain ⟨eps, heps, hfirst⟩ := FordFirstHolder.exists_unit_phase_holder Z r hr
  refine ⟨eps, heps, ?_⟩
  let F : (Fin k → ℕ) → ℂ := fun c => ∑ b : B, eps b *
    FordPolynomialPhase.e (∑ j : Fin k,
      gamma j * bval b ^ (j.val + 1) * (c j : ℝ))
  have hexpand : ∑ b : B, eps b * Z b ^ r =
      ∑ x : Fin r → Fin M, F (FordPowerFibers.powerMap r k M x) := by
    simp only [Z, FordPolynomialPhase.polynomial_phase_pow, Finset.mul_sum]
    rw [Finset.sum_comm]
  have hsecond := FordPowerFiberHolder.actual_power_fiber_holder r k M s hs S hS F
  have hp := pow_le_pow_left₀ (pow_nonneg (norm_nonneg _) r) hfirst (2 * s)
  rw [← pow_mul, mul_pow, ← pow_mul, hexpand] at hp
  exact hp.trans (mul_le_mul_of_nonneg_left hsecond (by positivity))

end FordBilinearAssembly
#print axioms FordBilinearAssembly.polynomial_bilinear_holder
