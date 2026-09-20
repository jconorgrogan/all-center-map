import FordBoundaryAlias
import FordClassEnergyMoment

open scoped BigOperators
open FordClassEnergyMoment

noncomputable section
namespace FordClassEnergyCommonModulus

/-- All class-energy states for every source multiplicity `n ≤ k`, packaged in
one finite dependent sum so that one modulus controls all required moments. -/
abbrev ClassEnergyStateFamily
    {A U C : Type*} (k : ℕ) (cls : U → C) :=
  Sigma (fun n : Fin (k + 1) =>
    (A × A) × (Fin n.val → classPairCarrier cls))

instance classEnergyStateFamilyFintype
    {A U C : Type*} [Fintype A] [Fintype U] [Fintype C]
    (k : ℕ) (cls : U → C) :
    Fintype (ClassEnergyStateFamily (A := A) (U := U) (C := C) k cls) := by
  classical
  unfold ClassEnergyStateFamily
  infer_instance

def classEnergyFrequencyFamily
    {A U C : Type*} {k : ℕ}
    (f : A → Fin k → ℤ) (g : U → Fin k → ℤ) (cls : U → C)
    (r : ClassEnergyStateFamily (A := A) (U := U) (C := C) k cls) :
    Fin k → ℤ :=
  classEnergyFrequency f g cls r.1.val r.2

def baseDifferenceFrequency
    {A : Type*} {k : ℕ} (f : A → Fin k → ℤ) (r : A × A) :
    Fin k → ℤ :=
  fun j => f r.1 j - f r.2 j

/-- One positive finite modulus simultaneously bounds every literal class-energy
frequency with `n ≤ k` and every base-frequency difference. This is only a
finite no-alias envelope; it makes no claim that distinct frequencies are
actually separated by the resulting grid. -/
theorem exists_common_modulus
    {A U C : Type*} [Fintype A] [Fintype U] [Fintype C]
    {k : ℕ} (f : A → Fin k → ℤ) (g : U → Fin k → ℤ) (cls : U → C) :
    ∃ L : ℕ, 0 < L ∧
      (∀ (n : Fin (k + 1))
          (r : (A × A) × (Fin n.val → classPairCarrier cls)) (j : Fin k),
        |classEnergyFrequency f g cls n.val r j| < (L : ℤ)) ∧
      (∀ a a' j, |f a j - f a' j| < (L : ℤ)) := by
  let h : ClassEnergyStateFamily (A := A) (U := U) (C := C) k cls →
      Fin k → ℤ := classEnergyFrequencyFamily f g cls
  let b : (A × A) → Fin k → ℤ := baseDifferenceFrequency f
  obtain ⟨L, hL, hclass, hbase⟩ := FordBoundaryAlias.exists_common_modulus h b
  refine ⟨L, hL, ?_, ?_⟩
  · intro n r j
    exact hclass ⟨n, r⟩ j
  · intro a a' j
    exact hbase (a, a') j

/-- The full `n = k` class-energy family is covered by the common modulus. -/
lemma bound_full_classEnergyFrequency
    {A U C : Type*} [Fintype A] [Fintype U] [Fintype C]
    {k : ℕ} (f : A → Fin k → ℤ) (g : U → Fin k → ℤ) (cls : U → C)
    {L : ℕ}
    (hbound : ∀ (n : Fin (k + 1))
        (r : (A × A) × (Fin n.val → classPairCarrier cls)) (j : Fin k),
      |classEnergyFrequency f g cls n.val r j| < (L : ℤ)) :
    ∀ (r : (A × A) × (Fin k → classPairCarrier cls)) (j : Fin k),
      |classEnergyFrequency f g cls k r j| < (L : ℤ) := by
  intro r j
  exact hbound ⟨k, Nat.lt_succ_self k⟩ r j

/-- The `n = k-1` class-energy family is covered by the same modulus. -/
lemma bound_previous_classEnergyFrequency
    {A U C : Type*} [Fintype A] [Fintype U] [Fintype C]
    {k : ℕ} (f : A → Fin k → ℤ) (g : U → Fin k → ℤ) (cls : U → C)
    {L : ℕ}
    (hbound : ∀ (n : Fin (k + 1))
        (r : (A × A) × (Fin n.val → classPairCarrier cls)) (j : Fin k),
      |classEnergyFrequency f g cls n.val r j| < (L : ℤ)) :
    ∀ (r : (A × A) × (Fin (k - 1) → classPairCarrier cls)) (j : Fin k),
      |classEnergyFrequency f g cls (k - 1) r j| < (L : ℤ) := by
  intro r j
  exact hbound ⟨k - 1, by omega⟩ r j

end FordClassEnergyCommonModulus

#print axioms FordClassEnergyCommonModulus.exists_common_modulus
#print axioms FordClassEnergyCommonModulus.bound_full_classEnergyFrequency
#print axioms FordClassEnergyCommonModulus.bound_previous_classEnergyFrequency
