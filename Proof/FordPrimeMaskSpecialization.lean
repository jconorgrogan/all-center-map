import FordPrimeProductNonzero

open scoped BigOperators
open MAPFordP16LiteralResidueBridge
open MAPFordP16Source35Triangular
open MAPFordType
namespace FordTypeJacobian
noncomputable section

lemma psiNatSucc_tail_eq_fordTailPolynomials
    {k d : ℕ} (hdk : d ≤ k) (psi : Fin k → Polynomial ℤ) :
    (fun j : Fin (k-d) => psiNatSucc psi (d + j.val + 1)) =
      fordTailPolynomials hdk psi := by
  funext j
  have hjlt : d + j.val < k := by omega
  simp [fordTailPolynomials, psiNatSucc, psiNat, hjlt]

lemma source_vandermonde_ne_zero_of_injective
    {p k d P : ℕ} (hdk : d ≤ k) (hp : p.Prime)
    (z : Fin k → Fin (P+1))
    (hz : Function.Injective
      (fun i : Fin (k-d) => ((z ⟨i.val, by omega⟩).val : ZMod p))) :
    (Matrix.vandermonde
      (fun i : Fin (k-d) => ((z ⟨i.val, by omega⟩).val : ZMod p))).det ≠ 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  exact (Matrix.det_vandermonde_ne_zero_iff).2 hz

/-- Literal Ford-type rows give a nonsingular source Jacobian modulo every
prime `p > k`, provided `T` survives reduction and the free source residues
are injective.  The positivity premise is retained for the exact mask. -/
theorem fordPolynomialMask_of_fordType
    {p k d P : ℕ} (hdk : d ≤ k) (hk : 2 ≤ k)
    (hp : p.Prime) (hkp : k < p)
    {T : ℤ} {m : ℕ} (hT : (T : ZMod p) ≠ 0)
    (psi : Fin k → Polynomial ℤ)
    (hpsi : FordType k d T m (psiNatSucc psi))
    (z : Fin k → Fin (P + 1))
    (hpos : ∀ i, 1 ≤ (z i).val)
    (hz : Function.Injective
      (fun i : Fin (k-d) => ((z ⟨i.val, by omega⟩).val : ZMod p))) :
    fordPolynomialMask (P := P) hdk hp psi z := by
  letI : Fact p.Prime := ⟨hp⟩
  let x : Fin (k-d) → Fin (P+1) := fordTailCoordinates hdk z
  let v : Fin (k-d) → ZMod p := fun i => ((x i).val : ZMod p)
  have hfac : ∀ j : Fin (k-d),
      (((Nat.factorial (d + j.val + 1) /
        Nat.factorial (j.val + 1) : ℕ) : ℕ) : ZMod p) ≠ 0 := by
    intro j
    apply factorial_quotient_cast_ne_zero_zmod hp
    · omega
    · have hjlt : j.val < k-d := j.isLt
      have hsum : d + j.val + 1 ≤ k := by omega
      omega
  have hv : (Matrix.vandermonde v).det ≠ 0 := by
    apply source_vandermonde_ne_zero_of_injective hdk hp z
    simpa [v, x, fordTailCoordinates] using hz
  have hprod :
      (∏ j : Fin (k-d),
        (((j.val : ZMod p) + 1) *
          (((Nat.factorial (d + j.val + 1) /
            Nat.factorial (j.val + 1) : ℕ) : ZMod p) *
            (2 ^ m : ZMod p) * (T : ZMod p)))) *
        (Matrix.vandermonde v).det ≠ 0 :=
    source_factor_product_ne_zero_zmod hp hdk hk hkp hfac hT hv
  have hdetformula := sourceJacobian_det_formula hdk psi hpsi x
  rw [psiNatSucc_tail_eq_fordTailPolynomials hdk psi] at hdetformula
  have hcast := congrArg (fun D : ℤ => (D : ZMod p)) hdetformula
  have hD :
      ((MAPFordCoarseP18Jacobian.sourceJacobian
        (fordTailPolynomials hdk psi) x).det : ZMod p) ≠ 0 := by
    have hcast' :
        ((MAPFordCoarseP18Jacobian.sourceJacobian
          (fordTailPolynomials hdk psi) x).det : ZMod p) =
          (((∏ j : Fin (k-d),
            (((j.val : ℤ) + 1) *
              (((Nat.factorial (d + j.val + 1) /
                Nat.factorial (j.val + 1) : ℕ) : ℤ) *
                (2 ^ m : ℤ) * T))) *
            (Matrix.vandermonde (fun i => ((x i).val : ℤ))).det : ℤ) : ZMod p) := by
      simpa using hcast
    rw [hcast']
    simpa only [v, x, Matrix.det_vandermonde, Int.cast_mul, Int.cast_prod,
      Int.cast_add, Int.cast_sub, Int.cast_ofNat, Int.cast_natCast,
      Nat.cast_ofNat, Nat.cast_one, Int.cast_one, Int.cast_pow] using hprod
  exact fordPolynomialMask_of_det_cast_ne_zero hdk hp psi z hpos
    (MAPFordCoarseP18Jacobian.sourceJacobian
      (fordTailPolynomials hdk psi) x).det rfl hD

end
end FordTypeJacobian

#print axioms FordTypeJacobian.fordPolynomialMask_of_fordType
