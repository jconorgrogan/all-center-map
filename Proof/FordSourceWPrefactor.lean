import FordSourceWCoefficient
import FordSourceWProduct

open scoped BigOperators
open FordSourceWEnvelope FordSourceWCoefficient FordSourceWProduct

namespace FordSourceWPrefactor
noncomputable section

theorem prefactor_le {R k : ℕ} (hR : 1 ≤ R) :
    prefactor R k ≤
      (32 * (R : ℝ) * (k + 1)) ^ k * (4 : ℝ) ^ (k * k) := by
  let C : ℝ := 32 * (R : ℝ) * (k + 1) * (4 : ℝ) ^ k
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity
  have hcoord : ∀ j : Fin k, coeff R (j.val + 1) ≤ C := by
    intro j
    have hj : 1 ≤ j.val + 1 := by omega
    have hc := coeff_le hR hj
    have hjk : j.val + 1 ≤ k := by omega
    have hjk1 : (j.val + 1 : ℝ) + 1 ≤ (k : ℝ) + 1 := by
      exact_mod_cast Nat.succ_le_succ hjk
    have hpow : (4 : ℝ) ^ (j.val + 1) ≤ (4 : ℝ) ^ k := by
      exact pow_le_pow_right₀ (by norm_num) hjk
    have hmid :
        32 * (R : ℝ) * ((j.val : ℝ) + 1 + 1) *
            (4 : ℝ) ^ (j.val + 1) ≤
          32 * (R : ℝ) * ((k : ℝ) + 1) *
            (4 : ℝ) ^ (j.val + 1) := by
      gcongr
    have htop :
        32 * (R : ℝ) * ((k : ℝ) + 1) *
            (4 : ℝ) ^ (j.val + 1) ≤
          32 * (R : ℝ) * ((k : ℝ) + 1) *
            (4 : ℝ) ^ k := by
      gcongr
    have hc' : coeff R (j.val + 1) ≤
        32 * (R : ℝ) * ((j.val : ℝ) + 1 + 1) *
          (4 : ℝ) ^ (j.val + 1) := by
      simpa using hc
    exact hc'.trans (hmid.trans (htop.trans (by rfl)))
  have hprod : prefactor R k ≤ C ^ k := by
    unfold prefactor
    have hp := Finset.prod_le_prod₀ (s := (Finset.univ : Finset (Fin k)))
      (fun j hj => by
        unfold coeff
        positivity)
      (fun j hj => hcoord j)
    simpa using hp
  calc
    prefactor R k ≤ C ^ k := hprod
    _ = (32 * (R : ℝ) * (k + 1)) ^ k * (4 : ℝ) ^ (k * k) := by
      dsimp [C]
      rw [mul_pow]
      congr 1
      rw [← pow_mul]

end
end FordSourceWPrefactor

#print axioms FordSourceWPrefactor.prefactor_le
