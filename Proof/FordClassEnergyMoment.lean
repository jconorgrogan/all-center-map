import FordLemma33FourierPrimitive
import FordBoundaryCountGeometry

open scoped BigOperators ZMod ComplexConjugate
open FordBoundaryCountGeometry
open MAPFordBoundaryCrossFourier MAPFordP16FiniteFourierBridge
open FordLemma33FourierPrimitive

noncomputable section
namespace FordClassEnergyMoment

variable {A U C : Type*} [Fintype A] [Fintype U] [Fintype C]
variable {L k n : ℕ} [NeZero L]

abbrev ClassEnergyZero (f : A → Fin k → ℤ) (g : U → Fin k → ℤ)
    (cls : U → C) (n : ℕ) :=
  {r : EnergyZero f g n // ∀ i : Fin n, cls (r.1.1.2 i) = cls (r.1.2.2 i)}

instance classEnergyZeroFintype (f : A → Fin k → ℤ) (g : U → Fin k → ℤ)
    (cls : U → C) (n : ℕ) : Fintype (ClassEnergyZero f g cls n) := by
  classical
  unfold ClassEnergyZero
  infer_instance

def realI (g : U → Fin k → ℤ) (cls : U → C)
    (alpha : Fin k → ZMod L) : ℝ :=
  ∑ c : C, ‖restrictedBlock g cls c alpha‖ ^ 2

def classPairCarrier (cls : U → C) :=
  Sigma (fun c : C => classFiber cls c × classFiber cls c)

instance classPairCarrierFintype (cls : U → C) : Fintype (classPairCarrier cls) := by
  classical
  unfold classPairCarrier
  infer_instance

def classPairFrequency (g : U → Fin k → ℤ) (cls : U → C)
    (r : classPairCarrier cls) : Fin k → ℤ :=
  fun j => g r.2.1.1 j - g r.2.2.1 j

def classEnergyFrequency (f : A → Fin k → ℤ) (g : U → Fin k → ℤ)
    (cls : U → C) (n : ℕ)
    (r : (A × A) × (Fin n → classPairCarrier cls)) : Fin k → ℤ :=
  fun j => f r.1.1 j - f r.1.2 j +
    ∑ i : Fin n, classPairFrequency g cls (r.2 i) j

/-- The Fourier side for the class-constrained energy count, before the final
common-grid normalization. -/
def classEnergyFourierSum (f : A → Fin k → ℤ) (g : U → Fin k → ℤ)
    (cls : U → C) (n : ℕ) : ℂ :=
  ∑ alpha : Fin k → ZMod L,
    ((‖fordBoundaryBlock f alpha‖ ^ 2 : ℝ) : ℂ) *
      ((realI g cls alpha ^ n : ℝ) : ℂ)

end FordClassEnergyMoment

#print axioms FordClassEnergyMoment.classEnergyZeroFintype
#print axioms FordClassEnergyMoment.classPairCarrierFintype

namespace FordClassEnergyMoment

variable {A U C : Type*} [Fintype A] [Fintype U] [Fintype C]
variable {k : ℕ}

abbrev classZeroCarrier (f : A → Fin k → ℤ) (g : U → Fin k → ℤ)
    (cls : U → C) (n : ℕ) :=
  {r : (A × A) × (Fin n → classPairCarrier cls) //
    ∀ j, classEnergyFrequency f g cls n r j = 0}

instance classZeroCarrierFintype (f : A → Fin k → ℤ) (g : U → Fin k → ℤ)
    (cls : U → C) (n : ℕ) : Fintype (classZeroCarrier f g cls n) := by
  classical
  letI : Fintype (classPairCarrier cls) := classPairCarrierFintype cls
  unfold classZeroCarrier
  infer_instance

private lemma pair_eta (cls : U → C) (a : classPairCarrier cls) :
    (⟨cls a.2.1.val, ⟨a.2.1.val, rfl⟩,
      ⟨a.2.2.val, a.2.2.property.trans a.2.1.property.symm⟩⟩ : classPairCarrier cls) = a := by
  rcases a with ⟨c, ⟨u, hu⟩, ⟨v, hv⟩⟩
  subst c
  rfl

def classEnergyEquivZero
    (f : A → Fin k → ℤ) (g : U → Fin k → ℤ) (cls : U → C) (n : ℕ) :
    ClassEnergyZero f g cls n ≃ classZeroCarrier f g cls n := by
  let toFun : ClassEnergyZero f g cls n → classZeroCarrier f g cls n := fun r =>
    let st := r.1.1
    let left := st.1
    let right := st.2
    ⟨((left.1, right.1), fun i =>
        ⟨cls (left.2 i), ⟨left.2 i, rfl⟩, ⟨right.2 i, (r.2 i).symm⟩⟩), by
      intro j
      have hh := congrFun r.1.2 j
      simp only [classEnergyFrequency, classPairFrequency, Pi.add_apply,
        Finset.sum_apply, Finset.sum_sub_distrib] at hh ⊢
      ring_nf at hh ⊢
      linarith⟩
  let invFun : classZeroCarrier f g cls n → ClassEnergyZero f g cls n := fun r =>
    let wleft : Fin n → U := fun i => (r.1.2 i).2.1.1
    let wright : Fin n → U := fun i => (r.1.2 i).2.2.1
    ⟨⟨((r.1.1.1, wleft), (r.1.1.2, wright)), by
      funext j
      have hh := r.2 j
      simp only [classEnergyFrequency, classPairFrequency, Pi.add_apply,
        Finset.sum_apply, Finset.sum_sub_distrib] at hh ⊢
      dsimp [wleft, wright] at hh ⊢
      ring_nf at hh ⊢
      linarith⟩, by
      intro i
      exact (r.1.2 i).2.1.2.trans (r.1.2 i).2.2.2.symm⟩
  refine { toFun := toFun, invFun := invFun, left_inv := ?_, right_inv := ?_ }
  · intro r
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · apply Prod.ext <;> rfl
    · apply Prod.ext <;> rfl
  · intro r
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext i
      exact pair_eta cls (r.1.2 i)

theorem classEnergy_card_eq_zeroCarrier
    (f : A → Fin k → ℤ) (g : U → Fin k → ℤ) (cls : U → C) (n : ℕ) :
    Fintype.card (ClassEnergyZero f g cls n) =
      Fintype.card (classZeroCarrier f g cls n) :=
  Fintype.card_congr (classEnergyEquivZero f g cls n)

end FordClassEnergyMoment

#print axioms FordClassEnergyMoment.classEnergy_card_eq_zeroCarrier
