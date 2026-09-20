import GuthMaynardEnergy118GCDReindex

open scoped BigOperators

namespace GuthMaynardEnergy118GCD

noncomputable section

theorem reducedPairs_coords_pos
    {N d : ℕ} (hN : 1 ≤ N) (hd : 1 ≤ d)
    {p : Pair} (hp : p ∈ reducedPairs N d) :
    0 < p.1 ∧ 0 < p.2 := by
  rcases Finset.mem_filter.mp hp with ⟨hpIcc, _⟩
  rcases Finset.mem_product.mp hpIcc with ⟨ha, hb⟩
  rcases Finset.mem_Icc.mp ha with ⟨ha1, _⟩
  rcases Finset.mem_Icc.mp hb with ⟨hb1, _⟩
  exact ⟨by omega, by omega⟩

theorem reducedPairs_denominator_le
    {N d : ℕ} (hN : 1 ≤ N) (hd : 1 ≤ d)
    {p : Pair} (hp : p ∈ reducedPairs N d) :
    (p.2 : ℝ) ≤ 2 * (N : ℝ) / (d : ℝ) := by
  rcases Finset.mem_filter.mp hp with ⟨_, hbounds⟩
  have hupper : d * p.2 ≤ 2 * N := hbounds.2.2.2.1
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  apply (le_div_iff₀ hdR).2
  have hupperR : (d : ℝ) * (p.2 : ℝ) ≤ 2 * (N : ℝ) := by
    exact_mod_cast hupper
  simpa [mul_comm] using hupperR

theorem reducedPairs_ratio_bounds
    {N d : ℕ} (hN : 1 ≤ N) (hd : 1 ≤ d)
    {p : Pair} (hp : p ∈ reducedPairs N d) :
    (1 : ℝ) / 2 ≤ (p.1 : ℝ) / (p.2 : ℝ) ∧
      (p.1 : ℝ) / (p.2 : ℝ) ≤ 2 := by
  rcases Finset.mem_filter.mp hp with ⟨_, hbounds⟩
  rcases reducedPairs_coords_pos hN hd hp with ⟨ha, hb⟩
  have haR : (0 : ℝ) < p.1 := by exact_mod_cast ha
  have hbR : (0 : ℝ) < p.2 := by exact_mod_cast hb
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hlow1 : N < d * p.1 := hbounds.1
  have hhigh1 : d * p.1 ≤ 2 * N := hbounds.2.1
  have hlow2 : N < d * p.2 := hbounds.2.2.1
  have hhigh2 : d * p.2 ≤ 2 * N := hbounds.2.2.2.1
  have hlow1R : (N : ℝ) < (d : ℝ) * (p.1 : ℝ) := by
    exact_mod_cast hlow1
  have hhigh1R : (d : ℝ) * (p.1 : ℝ) ≤ 2 * (N : ℝ) := by
    exact_mod_cast hhigh1
  have hlow2R : (N : ℝ) < (d : ℝ) * (p.2 : ℝ) := by
    exact_mod_cast hlow2
  have hhigh2R : (d : ℝ) * (p.2 : ℝ) ≤ 2 * (N : ℝ) := by
    exact_mod_cast hhigh2
  have hupper : (p.1 : ℝ) ≤ 2 * (p.2 : ℝ) := by
    nlinarith [hlow2R, hhigh1R]
  have hlower : (p.2 : ℝ) / 2 ≤ (p.1 : ℝ) := by
    nlinarith [hlow1R, hhigh2R]
  constructor
  · apply (le_div_iff₀ hbR).2
    nlinarith
  · exact (div_le_iff₀ hbR).2 hupper

theorem reducedPairs_cross_ne_of_ne
    {N d : ℕ} (hN : 1 ≤ N) (hd : 1 ≤ d)
    {p q : Pair} (hp : p ∈ reducedPairs N d)
    (hq : q ∈ reducedPairs N d) (hpq : p ≠ q) :
    p.1 * q.2 ≠ q.1 * p.2 := by
  intro hcross
  rcases Finset.mem_filter.mp hp with ⟨_, hpBounds⟩
  rcases Finset.mem_filter.mp hq with ⟨_, hqBounds⟩
  have hpCop : p.1.Coprime p.2 := hpBounds.2.2.2.2
  have hqCop : q.1.Coprime q.2 := hqBounds.2.2.2.2
  have hpA : p.1 ∣ q.1 := by
    apply hpCop.dvd_of_dvd_mul_left
    exact ⟨q.2, by simpa [Nat.mul_comm] using hcross.symm⟩
  have hqA : q.1 ∣ p.1 := by
    apply hqCop.dvd_of_dvd_mul_left
    exact ⟨p.2, by simpa [Nat.mul_comm] using hcross⟩
  have hpB : p.2 ∣ q.2 := by
    apply hpCop.symm.dvd_of_dvd_mul_left
    exact ⟨q.1, by simpa [Nat.mul_comm] using hcross⟩
  have hqB : q.2 ∣ p.2 := by
    apply hqCop.symm.dvd_of_dvd_mul_left
    exact ⟨p.1, by simpa [Nat.mul_comm] using hcross.symm⟩
  have hpa : p.1 = q.1 := Nat.dvd_antisymm hpA hqA
  have hpb : p.2 = q.2 := Nat.dvd_antisymm hpB hqB
  exact hpq (Prod.ext hpa hpb)

end
end GuthMaynardEnergy118GCD

#print axioms GuthMaynardEnergy118GCD.reducedPairs_coords_pos
#print axioms GuthMaynardEnergy118GCD.reducedPairs_denominator_le
#print axioms GuthMaynardEnergy118GCD.reducedPairs_ratio_bounds
#print axioms GuthMaynardEnergy118GCD.reducedPairs_cross_ne_of_ne
