import FordSignedMixedCount
import FordBoundaryAlias
import FordBoundaryPinnedCross

open scoped BigOperators
open FordBoundaryAlias
open FordBoundaryPinnedCross
open FordSignedMixedCount

noncomputable section
namespace FordSignedMixedCommonModulus

abbrev SignedFrequencyState
    (A U H : Type*) (k : ℕ) :=
  Sigma (fun sign : Fin k → Bool =>
    Sigma (fun hs : Fin k → H => SignedState A U k))

abbrev EnergyBaseDifferenceState
    (A U H : Type*) (k : ℕ) :=
  Sum
    (Sigma (fun h : H =>
      (A × (Fin k → U)) × (A × (Fin k → U))))
    (A × A)

def signedFrequencyFamily
    {A U H : Type*} {k : ℕ}
    (f : A → Fin k → ℤ) (g : H → U → Fin k → ℤ)
    (q : SignedFrequencyState A U H k) : Fin k → ℤ :=
  signedFrequency f g q.2.1 q.1 q.2.2

def energyBaseDifferenceFamily
    {A U H : Type*} {k : ℕ}
    (f : A → Fin k → ℤ) (g : H → U → Fin k → ℤ)
    (q : EnergyBaseDifferenceState A U H k) : Fin k → ℤ :=
  match q with
  | Sum.inl q =>
      fun j => wordFreq f (g q.1) k q.2.1 j - wordFreq f (g q.1) k q.2.2 j
  | Sum.inr q => fun j => f q.1 j - f q.2 j

theorem exists_signed_mixed_common_modulus
    {A U H : Type*} [Fintype A] [Fintype U] [Fintype H]
    {k : ℕ}
    (f : A → Fin k → ℤ) (g : H → U → Fin k → ℤ) :
    ∃ L : ℕ, 0 < L ∧
      (∀ (sign : Fin k → Bool) (hs : Fin k → H)
          (r : SignedState A U k) (j : Fin k),
        |signedFrequency f g hs sign r j| < (L : ℤ)) ∧
      (∀ (h : H) (r r' : A × (Fin k → U)) (j : Fin k),
        |wordFreq f (g h) k r j - wordFreq f (g h) k r' j| < (L : ℤ)) ∧
      (∀ (a a' : A) (j : Fin k), |f a j - f a' j| < (L : ℤ)) := by
  let s : SignedFrequencyState A U H k → Fin k → ℤ :=
    signedFrequencyFamily f g
  let e : EnergyBaseDifferenceState A U H k → Fin k → ℤ :=
    energyBaseDifferenceFamily f g
  obtain ⟨L, hL, hs, he⟩ :=
    FordBoundaryAlias.exists_common_modulus s e
  refine ⟨L, hL, ?_, ?_, ?_⟩
  · intro sign hs' r j
    exact hs ⟨sign, hs', r⟩ j
  · intro h r r' j
    exact he (Sum.inl ⟨h, (r, r')⟩) j
  · intro a a' j
    exact he (Sum.inr (a, a')) j

end FordSignedMixedCommonModulus

#print axioms FordSignedMixedCommonModulus.exists_signed_mixed_common_modulus
