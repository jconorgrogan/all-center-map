import Mathlib

namespace MAPFordType
open Polynomial
noncomputable section
set_option maxHeartbeats 900000

theorem coeff_translated_sub
    (p : Polynomial ℤ) (n : ℕ) (y : ℤ)
    (hp : p.natDegree = n + 1) :
    (p.comp (X + C y) - p).coeff n =
      ((n + 1 : ℕ) : ℤ) * p.leadingCoeff * y := by
  have hqdeg : (hasseDeriv n p).natDegree ≤ 1 := by
    rw [natDegree_hasseDeriv, hp]
    omega
  have hqform : hasseDeriv n p =
      C ((hasseDeriv n p).coeff 1) * X + C ((hasseDeriv n p).coeff 0) :=
    eq_X_add_C_of_natDegree_le_one hqdeg
  have hcoeff1 : (hasseDeriv n p).coeff 1 =
      ((n + 1 : ℕ) : ℤ) * p.leadingCoeff := by
    rw [hasseDeriv_coeff]
    rw [show 1 + n = n + 1 by omega]
    have hlead : p.coeff (n + 1) = p.leadingCoeff := by
      rw [← hp]
      exact coeff_natDegree
    rw [hlead]
    simp [Nat.choose_succ_self_right]
  have hcoeff0 : (hasseDeriv n p).coeff 0 = p.coeff n := by
    rw [hasseDeriv_coeff]
    simp
  have ht : p.comp (X + C y) = taylor y p := (taylor_apply y p).symm
  rw [ht, coeff_sub, taylor_coeff]
  rw [hqform, eval_add, eval_mul, eval_C, eval_X, hcoeff1, hcoeff0]
  simp

end
end MAPFordType

#print axioms MAPFordType.coeff_translated_sub
