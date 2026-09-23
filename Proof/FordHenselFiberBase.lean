import FordHenselFiber

open MvPolynomial
set_option maxHeartbeats 800000

namespace MAPFordHenselStep
noncomputable section

def primeSolution {p d : ℕ} (f : Fin d → MvPolynomial (Fin d) ℤ)
    (a : Fin d → Fin p) : Prop :=
  ∀ i, (f i).eval (fun j => ((a j).val : ℤ)) ≡ 0 [ZMOD (p : ℤ)]

def reducePrimePowerSolution {p R d : ℕ} (hp : p.Prime) (hR : 1 ≤ R)
    {f : Fin d → MvPolynomial (Fin d) ℤ}
    (a : {a : Fin d → Fin (p ^ R) // nonsingularPrimePowerSolution f a}) :
    {b : Fin d → Fin p // primeSolution f b} := by
  let b := reducePoint (Nat.Prime.pos hp) a.1
  have hb : primeSolution f b := by
    intro i
    have hq : (f i).eval (pointInt a.1) ≡ 0 [ZMOD (p ^ R : ℤ)] := a.2.1 i
    have hpq : (p : ℤ) ∣ (p ^ R : ℤ) := by
      have hnat : p ∣ p ^ R := by simpa using (Nat.pow_dvd_pow p hR)
      exact_mod_cast hnat
    have hq' : (f i).eval (pointInt a.1) ≡ 0 [ZMOD (p : ℤ)] :=
      Int.ModEq.of_dvd hpq hq
    have hcoords : ∀ j, pointInt a.1 j ≡ (b j).val [ZMOD (p : ℤ)] := by
      intro j
      change (a.1 j).val ≡ (a.1 j).val % p [ZMOD (p : ℤ)]
      exact (Int.mod_modEq (a.1 j).val p).symm
    have he := eval_int_modEq (m := p) (f i) (pointInt a.1)
      (fun j => ((b j).val : ℤ)) hcoords
    exact he.symm.trans hq'
  exact ⟨b, hb⟩

theorem reducePrimePowerSolution_injective
    {p R d : ℕ} (hp : p.Prime) (hR : 1 ≤ R)
    {f : Fin d → MvPolynomial (Fin d) ℤ} :
    Function.Injective (reducePrimePowerSolution hp hR :
      {a : Fin d → Fin (p ^ R) // nonsingularPrimePowerSolution f a} →
      {b : Fin d → Fin p // primeSolution f b}) := by
  intro a b hab
  exact reducePoint_injective_on_nonsingular hp hR (congrArg Subtype.val hab)

open scoped Classical in
theorem card_nonsingularPrimePowerSolution_le_card_primeSolution
    {p R d : ℕ} (hp : p.Prime) (hR : 1 ≤ R)
    (f : Fin d → MvPolynomial (Fin d) ℤ) :
    Fintype.card {a : Fin d → Fin (p ^ R) // nonsingularPrimePowerSolution f a} ≤
      Fintype.card {b : Fin d → Fin p // primeSolution f b} := by
  exact Fintype.card_le_of_injective (reducePrimePowerSolution hp hR)
    (reducePrimePowerSolution_injective hp hR)

end
end MAPFordHenselStep

#print axioms MAPFordHenselStep.reducePrimePowerSolution_injective
#print axioms MAPFordHenselStep.card_nonsingularPrimePowerSolution_le_card_primeSolution
