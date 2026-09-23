import FordHenselIterate

open MvPolynomial
set_option maxHeartbeats 800000

namespace MAPFordHenselStep
noncomputable section

lemma eval_int_modEq {m d : ℕ} (p : MvPolynomial (Fin d) ℤ)
    (x y : Fin d → ℤ) (hxy : ∀ i, x i ≡ y i [ZMOD (m : ℤ)]) :
    p.eval x ≡ p.eval y [ZMOD (m : ℤ)] := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simpa only [MvPolynomial.eval_add] using hp.add hq
  | mul_X p i hp =>
      simpa only [MvPolynomial.eval_mul, MvPolynomial.eval_X] using hp.mul (hxy i)

def pointMod {p R d : ℕ} (hp : 0 < p) (a : Fin d → Fin (p ^ R)) : Fin d → Fin p :=
  fun i => ⟨(a i).val % p, Nat.mod_lt _ hp⟩

def pointInt {p R d : ℕ} (a : Fin d → Fin (p ^ R)) : Fin d → ℤ :=
  fun i => (a i).val

def primePowerSolution {p R d : ℕ} (f : Fin d → MvPolynomial (Fin d) ℤ)
    (a : Fin d → Fin (p ^ R)) : Prop :=
  ∀ i, (f i).eval (pointInt a) ≡ 0 [ZMOD (p ^ R : ℕ)]

def nonsingularPrimePowerSolution {p R d : ℕ}
    (f : Fin d → MvPolynomial (Fin d) ℤ)
    (a : Fin d → Fin (p ^ R)) : Prop :=
  primePowerSolution f a ∧ p.Coprime (intJacobian f (pointInt a)).det.natAbs

def reducePoint {p R d : ℕ} (hp : 0 < p) (a : Fin d → Fin (p ^ R)) : Fin d → Fin p :=
  pointMod hp a

theorem reducePoint_injective_on_nonsingular
    {p R d : ℕ} (hp : p.Prime) (hR : 1 ≤ R)
    {f : Fin d → MvPolynomial (Fin d) ℤ} :
    Function.Injective (fun (a : {a : Fin d → Fin (p ^ R) //
      nonsingularPrimePowerSolution f a}) => reducePoint (Nat.Prime.pos hp) a.1) := by
  intro a b hab
  apply Subtype.ext
  funext i
  have hred : ∀ j, pointInt a.1 j ≡ pointInt b.1 j [ZMOD (p : ℤ)] := by
    intro j
    have hj := congrArg (fun z => (z j).val) hab
    have hsame : (a.1 j).val % p = (b.1 j).val % p := by
      simpa [reducePoint, pointMod] using hj
    change (a.1 j).val ≡ (b.1 j).val [ZMOD (p : ℤ)]
    calc
      (a.1 j).val ≡ ((a.1 j).val % p : ℕ) [ZMOD (p : ℤ)] :=
        (Int.mod_modEq (a.1 j).val p).symm
      _ ≡ ((b.1 j).val % p : ℕ) [ZMOD (p : ℤ)] := by simpa [hsame]
      _ ≡ (b.1 j).val [ZMOD (p : ℤ)] := Int.mod_modEq (b.1 j).val p
  have hval : ∀ j, (f j).eval (pointInt a.1) ≡
      (f j).eval (pointInt b.1) [ZMOD (p ^ R : ℕ)] := by
    intro j
    exact (a.2.1 j).trans (b.2.1 j).symm
  have hpow := unique_integer_lift_to_power hp hR f
    (pointInt a.1) (pointInt b.1) hred hval a.2.2
  have hz := (ZMod.intCast_eq_intCast_iff ((a.1 i).val : ℤ)
    ((b.1 i).val : ℤ) (p ^ R)).2 (hpow i)
  have hzv := congrArg ZMod.val hz
  exact Fin.ext (by simpa [ZMod.val_natCast_of_lt (a.1 i).isLt,
    ZMod.val_natCast_of_lt (b.1 i).isLt] using hzv)

open scoped Classical in
theorem card_nonsingularPrimePowerSolution_le_p_pow_d
    {p R d : ℕ} (hp : p.Prime) (hR : 1 ≤ R)
    (f : Fin d → MvPolynomial (Fin d) ℤ) :
    Fintype.card {a : Fin d → Fin (p ^ R) // nonsingularPrimePowerSolution f a} ≤ p ^ d := by
  let g : {a : Fin d → Fin (p ^ R) // nonsingularPrimePowerSolution f a} →
      (Fin d → Fin p) := fun a => reducePoint (Nat.Prime.pos hp) a.1
  simpa using (Fintype.card_le_of_injective g
    (reducePoint_injective_on_nonsingular hp hR))

end
end MAPFordHenselStep

#print axioms MAPFordHenselStep.reducePoint_injective_on_nonsingular
#print axioms MAPFordHenselStep.card_nonsingularPrimePowerSolution_le_p_pow_d
