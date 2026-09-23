import JutilaPseudocharacterAlgebra

/-!
# The absolute-coefficient half of Jutila's Lemma 3

This module proves the remaining finite Euler-product inequality in Lemma 3
of Jutila (1977), p. 49.  It is algebraic and contains no asymptotic or
zero-density input.
-/

namespace MAPJutilaLemma3AbsoluteMass

open scoped BigOperators
open MAPJutilaPseudocharacterAlgebra

/-- The exact finite Euler mass of the coefficients in Jutila's Lemma 2.
An exclusive prime contributes `1+p`; a common prime contributes
`1+p*(p-2)`. -/
def lemmaThreeAbsoluteMass (A B : Finset ℕ) : ℕ :=
  (∏ p ∈ exclusivePrimes A B, (p + 1)) *
    Finset.prod (A ∩ B) (fun p => 1 + p * (p - 2))

theorem common_local_bound (p : ℕ) (hp : 2 ≤ p) :
    1 + p * (p - 2) ≤ (p + 1) * (p + 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hp
  simp
  nlinarith

/-- Jutila Lemma 3's absolute coefficient bound at the exact finite
Euler-product level. -/
theorem lemmaThreeAbsoluteMass_le
    (A B : Finset ℕ) (hlarge : ∀ p ∈ A ∪ B, 2 ≤ p) :
    lemmaThreeAbsoluteMass A B ≤
      (∏ p ∈ A, (p + 1)) * ∏ p ∈ B, (p + 1) := by
  classical
  let I := A ∩ B
  let AD := A \ B
  let BD := B \ A
  let f : ℕ → ℕ := fun p => p + 1
  let c : ℕ → ℕ := fun p => 1 + p * (p - 2)
  have hcommon : (∏ p ∈ I, c p) ≤ ∏ p ∈ I, (f p * f p) := by
    apply Finset.prod_le_prod₀
    · intro p hp
      exact Nat.zero_le _
    · intro p hp
      apply common_local_bound
      apply hlarge p
      change p ∈ A ∩ B at hp
      exact Finset.mem_union_left B (Finset.mem_inter.mp hp).1
  rw [Finset.prod_mul_distrib] at hcommon
  have hdisj : Disjoint AD BD := by
    apply Finset.disjoint_left.2
    intro p hpAD hpBD
    have hpAD' : p ∈ A ∧ p ∉ B := by simpa [AD] using hpAD
    have hpBD' : p ∈ B ∧ p ∉ A := by simpa [BD] using hpBD
    exact hpAD'.2 hpBD'.1
  have hexclusive : (∏ p ∈ exclusivePrimes A B, f p) =
      (∏ p ∈ AD, f p) * ∏ p ∈ BD, f p := by
    change (∏ p ∈ AD ∪ BD, f p) = _
    exact Finset.prod_union hdisj
  have hAD_I : Disjoint AD I := by
    apply Finset.disjoint_left.2
    intro p hpAD hpI
    have hpAD' : p ∈ A ∧ p ∉ B := by simpa [AD] using hpAD
    have hpI' : p ∈ A ∧ p ∈ B := by simpa [I] using hpI
    exact hpAD'.2 hpI'.2
  have hBD_I : Disjoint BD I := by
    apply Finset.disjoint_left.2
    intro p hpBD hpI
    have hpBD' : p ∈ B ∧ p ∉ A := by simpa [BD] using hpBD
    have hpI' : p ∈ A ∧ p ∈ B := by simpa [I] using hpI
    exact hpBD'.2 hpI'.1
  have hAset : AD ∪ I = A := by
    dsimp [AD, I]
    exact Finset.sdiff_union_inter A B
  have hBset : BD ∪ I = B := by
    dsimp [BD, I]
    rw [Finset.inter_comm]
    exact Finset.sdiff_union_inter B A
  have hA : (∏ p ∈ AD, f p) * ∏ p ∈ I, f p = ∏ p ∈ A, f p := by
    rw [← Finset.prod_union hAD_I, hAset]
  have hB : (∏ p ∈ BD, f p) * ∏ p ∈ I, f p = ∏ p ∈ B, f p := by
    rw [← Finset.prod_union hBD_I, hBset]
  unfold lemmaThreeAbsoluteMass
  dsimp only [f, c, I] at hexclusive hcommon hA hB ⊢
  calc
    (∏ p ∈ exclusivePrimes A B, (p + 1)) *
        ∏ p ∈ A ∩ B, (1 + p * (p - 2)) =
        ((∏ p ∈ AD, (p + 1)) * ∏ p ∈ BD, (p + 1)) *
          ∏ p ∈ A ∩ B, (1 + p * (p - 2)) := by
      exact congrArg
        (fun y => y * ∏ p ∈ A ∩ B, (1 + p * (p - 2))) hexclusive
    _ ≤ ((∏ p ∈ AD, (p + 1)) * ∏ p ∈ BD, (p + 1)) *
          ((∏ p ∈ A ∩ B, (p + 1)) * ∏ p ∈ A ∩ B, (p + 1)) :=
      Nat.mul_le_mul_left _ hcommon
    _ = ((∏ p ∈ AD, (p + 1)) * ∏ p ∈ A ∩ B, (p + 1)) *
        ((∏ p ∈ BD, (p + 1)) * ∏ p ∈ A ∩ B, (p + 1)) := by ring
    _ = (∏ p ∈ A, (p + 1)) * ∏ p ∈ B, (p + 1) := by rw [hA, hB]

end MAPJutilaLemma3AbsoluteMass

#print axioms MAPJutilaLemma3AbsoluteMass.common_local_bound
#print axioms MAPJutilaLemma3AbsoluteMass.lemmaThreeAbsoluteMass_le
