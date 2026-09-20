import FordCompactEventualThreshold

noncomputable section
namespace FordCompactUniformThreshold

open Filter

/-- A single threshold works simultaneously for every integer order in the
compact range `2 ≤ r ≤ 1299`. -/
theorem compact_uniform_threshold :
    ∃ N0 : ℝ, ∀ r : ℕ, 2 ≤ r → r ≤ 1299 → ∀ N : ℝ, N0 ≤ N →
      N ≥ 2 ∧
      (r : ℝ) * N ^ ((3 : ℝ) / 4) ≤ N ∧
      16 * N ^ (-(1 / (4 * (r : ℝ)))) ≤ 1 ∧
      (r.factorial : ℝ) * N ^ (-(1 : ℝ) / 2) ≤ 1 ∧
      (12 * Real.pi * (8 : ℝ) ^ r) * N ^ (-(1 : ℝ) / 4) ≤
        N ^ (-(1 / (4 * (r : ℝ)))) := by
  let I : Finset ℕ := Finset.Icc 2 1299
  have hall : ∀ᶠ N : ℝ in atTop, ∀ r ∈ I,
      N ≥ 2 ∧
      (r : ℝ) * N ^ ((3 : ℝ) / 4) ≤ N ∧
      16 * N ^ (-(1 / (4 * (r : ℝ)))) ≤ 1 ∧
      (r.factorial : ℝ) * N ^ (-(1 : ℝ) / 2) ≤ 1 ∧
      (12 * Real.pi * (8 : ℝ) ^ r) * N ^ (-(1 : ℝ) / 4) ≤
        N ^ (-(1 / (4 * (r : ℝ)))) := by
    apply (Finset.eventually_all I).2
    intro r hr
    have hrI : 2 ≤ r ∧ r ≤ 1299 := by
      simpa [I, Finset.mem_Icc] using hr
    obtain ⟨N0, hN0⟩ :=
      FordCompactEventualThreshold.compact_eventual_threshold hrI.1
    exact Filter.eventually_atTop.2 ⟨N0, hN0⟩
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.1 hall
  refine ⟨N0, ?_⟩
  intro r hrlo hrhi N hN
  have hrI : r ∈ I := by
    simp [I, Finset.mem_Icc, hrlo, hrhi]
  exact hN0 N hN r hrI

end FordCompactUniformThreshold

#print axioms FordCompactUniformThreshold.compact_uniform_threshold
