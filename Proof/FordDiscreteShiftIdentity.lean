import Mathlib

open scoped BigOperators
noncomputable section

namespace FordDiscreteShiftIdentity

/-- Zero extension of a sequence supported on `[0,N)`, indexed by integers. -/
def zeroExtend (N : ℕ) (f : ℕ → ℂ) (m : ℤ) : ℂ :=
  if 0 ≤ m ∧ m < (N : ℤ) then f m.toNat else 0

lemma zeroExtend_nat (N n : ℕ) (f : ℕ → ℂ) (hn : n < N) :
    zeroExtend N f (n : ℤ) = f n := by
  unfold zeroExtend
  have hn0 : (0 : ℤ) ≤ n := by positivity
  have hn' : (n : ℤ) < N := by exact_mod_cast hn
  rw [if_pos ⟨hn0, hn'⟩]
  simp

lemma shifted_sum_eq {N Q : ℕ} (hQ : 1 ≤ Q)
    (f : ℕ → ℂ) (h : ℕ) (hh : h < Q) :
    (∑ r ∈ Finset.range (N + Q - 1),
      zeroExtend N f ((r : ℤ) - h)) =
      ∑ n ∈ Finset.range N, f n := by
  let sh : ℕ → ℕ := fun n => n + h
  let I : Finset ℕ := Finset.image sh (Finset.range N)
  have hI : I ⊆ Finset.range (N + Q - 1) := by
    intro r hr
    rw [Finset.mem_image] at hr
    obtain ⟨n, hn, rfl⟩ := hr
    apply Finset.mem_range.mpr
    dsimp [sh]
    have hn' := Finset.mem_range.mp hn
    omega
  have hsumI :
      (∑ r ∈ I, zeroExtend N f ((r : ℤ) - h)) =
        ∑ n ∈ Finset.range N, f n := by
    unfold I
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro n hn
      dsimp [sh]
      rw [show (n : ℤ) + (h : ℤ) - (h : ℤ) = (n : ℤ) by ring]
      exact zeroExtend_nat N n f (Finset.mem_range.mp hn)
    · intro a ha b hb hab
      dsimp [sh] at hab
      omega
  have hzero : ∀ r ∈ Finset.range (N + Q - 1), r ∉ I →
      zeroExtend N f ((r : ℤ) - h) = 0 := by
    intro r hr hri
    unfold zeroExtend
    by_cases hp : 0 ≤ (r : ℤ) - h ∧ (r : ℤ) - h < (N : ℤ)
    · exfalso
      have hnonneg : (h : ℤ) ≤ r := by linarith [hp.1]
      have hlt : r < N + h := by
        have := hp.2
        omega
      have hrmem : r ∈ I := by
        unfold I
        rw [Finset.mem_image]
        refine ⟨r - h, ?_, ?_⟩
        · apply Finset.mem_range.mpr
          omega
        · dsimp [sh]
          omega
      exact hri hrmem
    · rw [if_neg hp]
  rw [← hsumI]
  exact (Finset.sum_subset hI hzero).symm

/-- Exact finite differencing identity. -/
theorem sum_shift_identity {N Q : ℕ} (hQ : 1 ≤ Q)
    (f : ℕ → ℂ) :
    (Q : ℂ) * (∑ n ∈ Finset.range N, f n) =
      ∑ r ∈ Finset.range (N + Q - 1),
        ∑ h ∈ Finset.range Q,
          zeroExtend N f ((r : ℤ) - h) := by
  calc
    (Q : ℂ) * (∑ n ∈ Finset.range N, f n) =
        ∑ h ∈ Finset.range Q, (∑ n ∈ Finset.range N, f n) := by
          simp [nsmul_eq_mul]
    _ = ∑ h ∈ Finset.range Q,
        (∑ r ∈ Finset.range (N + Q - 1),
          zeroExtend N f ((r : ℤ) - h)) := by
      apply Finset.sum_congr rfl
      intro h hh
      exact (shifted_sum_eq hQ f h (Finset.mem_range.mp hh)).symm
    _ = ∑ r ∈ Finset.range (N + Q - 1),
        ∑ h ∈ Finset.range Q,
          zeroExtend N f ((r : ℤ) - h) := by
      rw [Finset.sum_comm]

end FordDiscreteShiftIdentity

#print axioms FordDiscreteShiftIdentity.sum_shift_identity
