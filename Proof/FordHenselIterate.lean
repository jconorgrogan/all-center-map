import FordHenselStep

open scoped BigOperators
open MvPolynomial

namespace MAPFordHenselStep

noncomputable section

/- Iterating the one-step producer keeps the same system and the same
   Jacobian point.  The induction hypothesis is used only after reducing the
   value congruence to the preceding prime-power modulus. -/
theorem unique_integer_lift_to_power
    {p R d : ℕ} (hp : p.Prime) (hR : 1 ≤ R)
    (f : Fin d → MvPolynomial (Fin d) ℤ) (x y : Fin d → ℤ)
    (hxy : ∀ i, x i ≡ y i [ZMOD (p : ℤ)])
    (hval : ∀ i, (f i).eval x ≡ (f i).eval y [ZMOD (p ^ R : ℕ)])
    (hcop : p.Coprime (intJacobian f x).det.natAbs) :
    ∀ i, x i ≡ y i [ZMOD (p ^ R : ℕ)] := by
  have H : ∀ n : ℕ,
      (∀ i, (f i).eval x ≡ (f i).eval y [ZMOD (p ^ (n + 1) : ℕ)]) →
        ∀ i, x i ≡ y i [ZMOD (p ^ (n + 1) : ℕ)] := by
    intro n
    induction n with
    | zero =>
        intro _ i
        simpa using hxy i
    | succ n ih =>
        intro hv i
        have hdown : ∀ j, (f j).eval x ≡ (f j).eval y
            [ZMOD (p ^ (n + 1) : ℕ)] := by
          intro j
          apply Int.ModEq.of_dvd
            (m := (p ^ (n + 1) : ℤ)) (n := (p ^ (n + 2) : ℤ))
          · exact_mod_cast (Nat.pow_dvd_pow p (by omega : n + 1 ≤ n + 2))
          · exact hv j
        have hprev := ih hdown
        have hstep := unique_integer_lift hp (by omega : 1 ≤ n + 1) f x y
          hprev (fun j => hv j) hcop
        exact hstep i
  have hlast := H (R - 1)
    (by simpa [Nat.sub_add_cancel hR] using hval)
  simpa [Nat.sub_add_cancel hR] using hlast

/- If two solutions of the same congruence system reduce to the same point
   modulo p and one has a p-unit Jacobian, they reduce to the same point
   modulo p^R.  This is the exact injectivity statement behind Ford's fiber
   count; it does not assert the missing finite-field degree-product bound. -/
theorem nonsingular_solution_reduction_injective
    {p R d : ℕ} (hp : p.Prime) (hR : 1 ≤ R)
    (f : Fin d → MvPolynomial (Fin d) ℤ) (x y : Fin d → ℤ)
    (hsolx : ∀ i, (f i).eval x ≡ 0 [ZMOD (p ^ R : ℕ)])
    (hsoly : ∀ i, (f i).eval y ≡ 0 [ZMOD (p ^ R : ℕ)])
    (hred : ∀ i, x i ≡ y i [ZMOD (p : ℤ)])
    (hcop : p.Coprime (intJacobian f x).det.natAbs) :
    ∀ i, x i ≡ y i [ZMOD (p ^ R : ℕ)] := by
  apply unique_integer_lift_to_power hp hR f x y hred
    (fun i => (hsolx i).trans (hsoly i).symm) hcop

end
end MAPFordHenselStep

#print axioms MAPFordHenselStep.unique_integer_lift_to_power
#print axioms MAPFordHenselStep.nonsingular_solution_reduction_injective
