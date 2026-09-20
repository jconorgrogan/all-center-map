import FordBoundaryCrossFourier

open scoped BigOperators ZMod ComplexConjugate
open MAPFordBoundaryCrossFourier MAPFordP16FiniteFourierBridge

noncomputable section
namespace FordLemma33FourierPrimitive

variable {U C : Type*} [Fintype U] [Fintype C]
variable {L k : ℕ} [NeZero L]

def classFiber (cls : U → C) (c : C) := {u : U // cls u = c}

instance classFiberFintype (cls : U → C) (c : C) : Fintype (classFiber cls c) := by
  classical
  unfold classFiber
  infer_instance

abbrev pairCarrier (cls : U → C) :=
  Sigma (fun c : C => classFiber cls c × classFiber cls c)

def pairFrequency (f : U → Fin k → ℤ) (cls : U → C)
    (r : pairCarrier cls) : Fin k → ℤ :=
  fun j => f r.2.1.1 j - f r.2.2.1 j

def pairBlock (f : U → Fin k → ℤ) (cls : U → C)
    (alpha : Fin k → ZMod L) : ℂ :=
  ∑ r : pairCarrier cls, fordIntegerCharTerm alpha (pairFrequency f cls r)

def restrictedBlock (f : U → Fin k → ℤ) (cls : U → C)
    (c : C) (alpha : Fin k → ZMod L) : ℂ :=
  ∑ u : classFiber cls c, fordIntegerCharTerm alpha (fun j => f u.1 j)

theorem pairBlock_eq_sum_energy
    (f : U → Fin k → ℤ) (cls : U → C)
    (alpha : Fin k → ZMod L) :
    pairBlock f cls alpha =
      ∑ c : C, ((‖restrictedBlock f cls c alpha‖ ^ 2 : ℝ) : ℂ) := by
  unfold pairBlock pairFrequency restrictedBlock
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro c hc
  rw [norm_sum_expand]
  rw [← Fintype.sum_prod_type']
  apply Finset.sum_congr rfl
  intro u hu
  rw [char_term_neg]
  rw [char_term_add]
  rfl

theorem pairBlock_real_nonneg
    (f : U → Fin k → ℤ) (cls : U → C)
    (alpha : Fin k → ZMod L) :
    ∃ r : ℝ, 0 ≤ r ∧ pairBlock f cls alpha = (r : ℂ) := by
  let r : ℝ := ∑ c : C, ‖restrictedBlock f cls c alpha‖ ^ 2
  refine ⟨r, ?_, ?_⟩
  · dsimp [r]
    positivity
  · simpa [r, map_sum] using pairBlock_eq_sum_energy f cls alpha

def pairBlockMoment (f : U → Fin k → ℤ) (cls : U → C)
    (alpha : Fin k → ZMod L) (m : ℕ) : ℂ :=
  ∑ r : Fin m → pairCarrier cls,
    ∏ i : Fin m, fordIntegerCharTerm alpha (pairFrequency f cls (r i))

theorem pairBlock_pow_eq_moment
    (f : U → Fin k → ℤ) (cls : U → C)
    (alpha : Fin k → ZMod L) (m : ℕ) :
    pairBlock f cls alpha ^ m = pairBlockMoment f cls alpha m := by
  unfold pairBlock pairBlockMoment
  rw [Fintype.sum_pow]

end FordLemma33FourierPrimitive

#print axioms FordLemma33FourierPrimitive.pairBlock_eq_sum_energy
#print axioms FordLemma33FourierPrimitive.pairBlock_real_nonneg
#print axioms FordLemma33FourierPrimitive.pairBlock_pow_eq_moment
