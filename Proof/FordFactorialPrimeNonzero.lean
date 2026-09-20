import FordPrimeMaskBridge

open scoped BigOperators
namespace FordTypeJacobian
noncomputable section

lemma factorial_quotient_cast_ne_zero_zmod
    {p a b : ℕ} (hp : p.Prime) (ha : a ≤ b) (hb : b < p) :
    (((b.factorial / a.factorial : ℕ) : ℕ) : ZMod p) ≠ 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hcop : p.Coprime (b.factorial / a.factorial) := by
    apply Nat.Coprime.of_dvd_right (Nat.div_dvd_of_dvd (Nat.factorial_dvd_factorial ha))
    exact hp.coprime_factorial_of_lt hb
  intro hz
  have hdvd : p ∣ b.factorial / a.factorial := by
    exact (ZMod.natCast_eq_zero_iff _ _).mp hz
  have hpone : p = 1 := hcop.eq_one_of_dvd hdvd
  exact (Nat.Prime.ne_one hp) hpone

end
end FordTypeJacobian

#print axioms FordTypeJacobian.factorial_quotient_cast_ne_zero_zmod
