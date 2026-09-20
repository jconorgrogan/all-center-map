import MRTLemma29FiniteFourier
namespace MAPMRTLemma29Proof
open scoped BigOperators
open MAPMRTCorollary53Source
noncomputable section

lemma nat_le_totient_mul_divisorCount {n : ℕ} (hn : 1 ≤ n) :
    n ≤ n.totient * divisorCount n := by
  calc
    n = n.divisors.sum Nat.totient := (Nat.sum_totient n).symm
    _ ≤ n.divisors.sum (fun _ => n.totient) := by
      apply Finset.sum_le_sum
      intro d hd
      exact Nat.le_of_dvd (Nat.totient_pos.mpr (by omega))
        (Nat.totient_dvd_of_dvd (Nat.dvd_of_mem_divisors hd))
    _ = n.totient * divisorCount n := by
      simp [divisorCount, mul_comm]

lemma divisorCount_le_of_dvd {m n : ℕ} (hn : 1 ≤ n) (hdiv : m ∣ n) :
    divisorCount m ≤ divisorCount n := by
  unfold divisorCount
  exact Finset.card_le_card (Nat.divisors_subset_of_dvd (by omega) hdiv)

lemma factor_coefficient_le
    {q q0 q1 : ℕ} (hq0 : 1 ≤ q0) (hq1 : 1 ≤ q1)
    (hfactor : q0 * q1 = q) :
    Real.sqrt q1 / (Real.sqrt q0 * q1.totient) ≤
      (divisorCount q : ℝ) / Real.sqrt q := by
  have hq : 1 ≤ q := by
    rw [← hfactor]
    exact (Nat.pos_of_ne_zero (mul_ne_zero (by omega) (by omega)))
  have hdiv : q1 ∣ q := ⟨q0, by simpa [mul_comm] using hfactor.symm⟩
  have hdle : divisorCount q1 ≤ divisorCount q :=
    divisorCount_le_of_dvd hq hdiv
  have hnat := nat_le_totient_mul_divisorCount hq1
  have hq0pos : 0 < Real.sqrt q0 := Real.sqrt_pos.2 (by positivity)
  have hq1pos : 0 < Real.sqrt q1 := Real.sqrt_pos.2 (by positivity)
  have hphipos : 0 < (q1.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hcast : (q1 : ℝ) ≤ q1.totient * divisorCount q := by
    exact_mod_cast hnat.trans (Nat.mul_le_mul_left q1.totient hdle)
  have hsqrtq : Real.sqrt (q : ℝ) =
      Real.sqrt q0 * Real.sqrt q1 := by
    rw [← hfactor, Nat.cast_mul, Real.sqrt_mul (by positivity : (0 : ℝ) ≤ q0)]
  rw [hsqrtq]
  apply (div_le_div_iff₀ (mul_pos hq0pos hphipos)
    (mul_pos hq0pos hq1pos)).2
  have hsquare : Real.sqrt (q1 : ℝ) ^ 2 = q1 := Real.sq_sqrt (by positivity)
  nlinarith

end
end MAPMRTLemma29Proof
