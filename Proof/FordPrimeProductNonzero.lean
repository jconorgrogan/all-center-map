import FordFactorialPrimeNonzero

open scoped BigOperators
namespace FordTypeJacobian
noncomputable section

lemma source_factor_product_ne_zero_zmod
    {p k d : ℕ} (hp : p.Prime) (hkd : d ≤ k) (hk : k ≥ 2)
    (hkp : k < p)
    {m : ℕ} {T : ℤ}
    (hfac : ∀ j : Fin (k-d),
      (((Nat.factorial (d + j.val + 1) /
        Nat.factorial (j.val + 1) : ℕ) : ℕ) : ZMod p) ≠ 0)
    (hT : (T : ZMod p) ≠ 0)
    {v : Fin (k-d) → ZMod p}
    (hV : (Matrix.vandermonde v).det ≠ 0) :
    (∏ j : Fin (k-d),
      (((j.val : ZMod p) + 1) *
        (((Nat.factorial (d + j.val + 1) /
          Nat.factorial (j.val + 1) : ℕ) : ZMod p) *
          (2 ^ m : ZMod p) * (T : ZMod p)))) *
      (Matrix.vandermonde v).det ≠ 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  refine mul_ne_zero ?_ hV
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  apply mul_ne_zero
  · have hjlt : j.val < k - d := j.isLt
    have hsum : d + j.val + 1 ≤ k := by omega
    have hj1 : (j.val + 1 : ℕ) < p := by omega
    have hcast : ((j.val + 1 : ℕ) : ZMod p) ≠ 0 := by
      intro hz
      have hd : p ∣ j.val + 1 := (ZMod.natCast_eq_zero_iff _ _).mp hz
      have hple : p ≤ j.val + 1 := Nat.le_of_dvd (by omega) hd
      omega
    simpa [Nat.cast_add] using hcast
  · have hp2 : (2 : ZMod p) ≠ 0 := by
      intro hz
      have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff _ _).mp hz
      have hple : p ≤ 2 := Nat.le_of_dvd (by omega) hd
      omega
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact hfac j
      · exact pow_ne_zero m hp2
    · exact hT

end
end FordTypeJacobian

#print axioms FordTypeJacobian.source_factor_product_ne_zero_zmod
