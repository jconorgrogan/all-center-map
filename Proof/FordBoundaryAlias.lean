import FordFiniteFourierCharacterSum

open scoped BigOperators
noncomputable section
namespace FordBoundaryAlias

/-- A finite no-alias modulus; no estimate about frequencies is assumed. -/
def modulus {R : Type*} [Fintype R] {k : ℕ} (freq : R → Fin k → ℤ) : ℕ :=
  1 + ∑ r, ∑ j, (freq r j).natAbs

theorem modulus_pos {R : Type*} [Fintype R] {k : ℕ} (freq : R → Fin k → ℤ) :
    0 < modulus freq := by unfold modulus; omega

theorem frequency_bound {R : Type*} [Fintype R] {k : ℕ}
    (freq : R → Fin k → ℤ) (r : R) (j : Fin k) :
    |freq r j| < (modulus freq : ℤ) := by
  have h1 : (freq r j).natAbs ≤ ∑ j', (freq r j').natAbs :=
    Finset.single_le_sum (f := fun j' => (freq r j').natAbs)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have h2 : (∑ j', (freq r j').natAbs) ≤ ∑ r', ∑ j', (freq r' j').natAbs :=
    Finset.single_le_sum (f := fun r' => ∑ j', (freq r' j').natAbs)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)
  have h3 : (freq r j).natAbs < modulus freq := by unfold modulus; omega
  rw [← Int.natCast_natAbs]
  exact_mod_cast h3

/-- Two finite carrier families share one exact no-alias grid. -/
theorem exists_common_modulus {R S : Type*} [Fintype R] [Fintype S] {k : ℕ}
    (f : R → Fin k → ℤ) (g : S → Fin k → ℤ) :
    ∃ L : ℕ, 0 < L ∧ (∀ r j, |f r j| < (L : ℤ)) ∧ (∀ s j, |g s j| < (L : ℤ)) := by
  let h : R ⊕ S → Fin k → ℤ := fun | Sum.inl r => f r | Sum.inr s => g s
  refine ⟨modulus h, modulus_pos h, ?_, ?_⟩
  · intro r j
    exact frequency_bound h (Sum.inl r) j
  · intro s j
    exact frequency_bound h (Sum.inr s) j

end FordBoundaryAlias
#print axioms FordBoundaryAlias.frequency_bound
#print axioms FordBoundaryAlias.exists_common_modulus
