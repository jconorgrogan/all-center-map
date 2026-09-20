import FordDiscreteShiftIdentity

open scoped BigOperators ComplexConjugate
noncomputable section

namespace FordDiscreteCorrelationShift

open FordDiscreteShiftIdentity

/-- A shifted zero-extended correlation is exactly the finite correlation at
its oriented separation. -/
theorem correlation_shift_identity
    {N Q a b : ℕ} (hQ : 1 ≤ Q) (ha : a ≤ b) (hb : b < Q)
    (f : ℕ → ℂ) :
    (∑ r ∈ Finset.range (N + Q - 1),
      zeroExtend N f ((r : ℤ) - a) *
        conj (zeroExtend N f ((r : ℤ) - b))) =
      ∑ n ∈ Finset.range (N - (b - a)),
        f (n + (b - a)) * conj (f n) := by
  let d : ℕ := b - a
  let sh : ℕ → ℕ := fun n => n + b
  let I : Finset ℕ := Finset.image sh (Finset.range (N - d))
  have hI : I ⊆ Finset.range (N + Q - 1) := by
    intro r hr
    rw [Finset.mem_image] at hr
    obtain ⟨n, hn, rfl⟩ := hr
    apply Finset.mem_range.mpr
    dsimp [sh, d]
    have hn' := Finset.mem_range.mp hn
    omega
  have hsumI :
      (∑ r ∈ I,
        zeroExtend N f ((r : ℤ) - a) *
          conj (zeroExtend N f ((r : ℤ) - b))) =
        ∑ n ∈ Finset.range (N - d),
          f (n + d) * conj (f n) := by
    unfold I
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro n hn
      dsimp [sh]
      have hn' := Finset.mem_range.mp hn
      have hnd : n + d < N := by
        dsimp [d]
        omega
      have hcastA :
          ((n + b : ℕ) : ℤ) - (a : ℤ) = (n + d : ℕ) := by
        dsimp [d]
        omega
      have hcastB :
          ((n + b : ℕ) : ℤ) - (b : ℤ) = (n : ℤ) := by
        push_cast
        ring
      rw [show (n : ℤ) + (b : ℤ) - (a : ℤ) = (n + d : ℕ) by
          dsimp [d]
          omega,
        show (n : ℤ) + (b : ℤ) - (b : ℤ) = (n : ℤ) by ring,
        zeroExtend_nat N (n + d) f hnd,
        zeroExtend_nat N n f (by omega)]
    · intro x hx y hy hxy
      dsimp [sh] at hxy
      omega
  have hzero : ∀ r ∈ Finset.range (N + Q - 1), r ∉ I →
      zeroExtend N f ((r : ℤ) - a) *
        conj (zeroExtend N f ((r : ℤ) - b)) = 0 := by
    intro r hr hri
    by_cases hA : 0 ≤ (r : ℤ) - a ∧ (r : ℤ) - a < (N : ℤ)
    · by_cases hB : 0 ≤ (r : ℤ) - b ∧ (r : ℤ) - b < (N : ℤ)
      · exfalso
        have hbr : b ≤ r := by omega
        let n : ℕ := r - b
        have hrnb : r = n + b := by
          dsimp [n]
          omega
        have hnrange : n < N - d := by
          dsimp [n, d]
          omega
        have hrmem : r ∈ I := by
          unfold I
          rw [Finset.mem_image]
          refine ⟨n, Finset.mem_range.mpr hnrange, ?_⟩
          dsimp [sh]
          exact hrnb.symm
        exact hri hrmem
      · have hzB : zeroExtend N f ((r : ℤ) - b) = 0 := by
          unfold zeroExtend
          rw [if_neg hB]
        rw [hzB]
        simp
    · have hzA : zeroExtend N f ((r : ℤ) - a) = 0 := by
        unfold zeroExtend
        rw [if_neg hA]
      rw [hzA]
      simp
  rw [← hsumI]
  exact (Finset.sum_subset hI hzero).symm

end FordDiscreteCorrelationShift

#print axioms FordDiscreteCorrelationShift.correlation_shift_identity
