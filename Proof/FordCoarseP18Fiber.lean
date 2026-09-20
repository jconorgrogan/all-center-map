import FordHenselFiberBase

open scoped BigOperators
open Finset
open MvPolynomial
set_option maxHeartbeats 800000
set_option maxRecDepth 10000

namespace MAPFordCoarseP18Fiber
noncomputable section

/-- Coefficient expansion of a univariate integer polynomial at one chosen
    multivariate coordinate.  The `+ 1` shift below identifies the source
    interval `1,...,q` with the residue representatives `0,...,q-1`. -/
def shiftedPolyAt {n : ℕ} (q : Polynomial ℤ) (i : Fin n) :
    MvPolynomial (Fin n) ℤ :=
  ∑ t ∈ range (q.natDegree + 1),
    C (q.coeff t) * (X i + C 1) ^ t

lemma eval_shiftedPolyAt {n : ℕ} (q : Polynomial ℤ) (i : Fin n)
    (x : Fin n → ℤ) :
    (shiftedPolyAt q i).eval x = q.eval (x i + 1) := by
  simp [shiftedPolyAt, Polynomial.eval_eq_sum_range]

/-- The arbitrary univariate polynomial sum system from p.18, after the
    interval-to-residue shift.  Each equation is indexed by one `Phi`. -/
def sumSystem {n : ℕ} (phi : Fin n → Polynomial ℤ) (target : Fin n → ℤ) :
    Fin n → MvPolynomial (Fin n) ℤ := fun i =>
  (∑ j : Fin n, shiftedPolyAt (phi i) j) - C (target i)

lemma eval_sumSystem_interval {q n : ℕ} (phi : Fin n → Polynomial ℤ)
    (target : Fin n → ℤ) (i : Fin n) (z : Fin n → Fin (q + 1)) :
    (sumSystem phi target i).eval (fun j => ((z j).val - 1 : ℤ)) =
      (∑ j : Fin n, (phi i).eval ((z j).val : ℤ)) - target i := by
  simp only [sumSystem, MvPolynomial.eval_sub, MvPolynomial.eval_sum,
    shiftedPolyAt, MvPolynomial.eval_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_pow, MvPolynomial.eval_add, MvPolynomial.eval_X]
  apply congrArg (fun w => w - target i)
  apply Finset.sum_congr rfl
  intro j hj
  rw [Polynomial.eval_eq_sum_range]
  apply Finset.sum_congr rfl
  intro t ht
  congr 2
  omega

/-- The source's interval representatives, as a finite subtype. -/
def intervalPositive {q n : ℕ} (z : Fin n → Fin (q + 1)) : Prop :=
  ∀ i, 1 ≤ (z i).val

def intervalToFin {q n : ℕ} (hq : 0 < q)
    (z : Fin n → Fin (q + 1)) (hz : intervalPositive z) : Fin n → Fin q :=
  fun i => ⟨(z i).val - 1, by
    have hi := (z i).isLt
    have hzi := hz i
    omega⟩

def finToInterval {q n : ℕ} (x : Fin n → Fin q) : Fin n → Fin (q + 1) :=
  fun i => ⟨(x i).val + 1, by omega⟩

lemma intervalToFin_finToInterval {q n : ℕ} (hq : 0 < q)
    (x : Fin n → Fin q) :
    intervalToFin hq (finToInterval x) (by intro i; simp [finToInterval]) = x := by
  funext i
  apply Fin.ext
  simp [intervalToFin, finToInterval]

lemma finToInterval_intervalToFin {q n : ℕ} (hq : 0 < q)
    (z : Fin n → Fin (q + 1)) (hz : intervalPositive z) :
    finToInterval (intervalToFin (q := q) (n := n) hq z hz) = z := by
  funext i
  apply Fin.ext
  simp only [finToInterval, intervalToFin]
  exact Nat.sub_add_cancel (hz i)

lemma intervalToFin_injective {q n : ℕ} (hq : 0 < q) :
    Function.Injective (fun z : {z : Fin n → Fin (q + 1) // intervalPositive z} =>
      intervalToFin (q := q) (n := n) hq z.1 z.2) := by
  intro a b hab
  apply Subtype.ext
  exact (finToInterval_intervalToFin hq a.1 a.2).symm.trans
    ((congrArg finToInterval hab).trans
      (finToInterval_intervalToFin hq b.1 b.2))

/-- Literal p.18 fiber: `z_i` lies in `1,...,p^r`, the sum equations use
    one common modulus `p^r`, and the displayed Jacobian determinant is
    explicitly required to be a p-unit. -/
def intervalFiber {p r n : ℕ} (hq : 0 < p ^ r)
    (phi : Fin n → Polynomial ℤ) (target : Fin n → ℤ) : Type :=
  {z : {z : Fin n → Fin (p ^ r + 1) // intervalPositive z} //
    (∀ i, (∑ j : Fin n, (phi i).eval ((z.1 j).val : ℤ)) - target i ≡
      0 [ZMOD (p ^ r : ℕ)]) ∧
    p.Coprime ((MAPFordHenselStep.intJacobian (sumSystem phi target)
      (MAPFordHenselStep.pointInt
        (intervalToFin (q := p ^ r) (n := n) hq z.1 z.2))).det.natAbs)}

instance intervalFiberFintype {p r n : ℕ} (hq : 0 < p ^ r)
    (phi : Fin n → Polynomial ℤ) (target : Fin n → ℤ) :
    Fintype (intervalFiber hq phi target) := by
  classical
  dsimp [intervalFiber]
  infer_instance

end
end MAPFordCoarseP18Fiber


namespace MAPFordCoarseP18Fiber
noncomputable section

def pointIntQ {q n : ℕ} (a : Fin n → Fin q) : Fin n → ℤ :=
  fun i => (a i).val

lemma eval_sumSystem_at_intervalToFin {q n : ℕ} (hq : 0 < q)
    (phi : Fin n → Polynomial ℤ) (target : Fin n → ℤ) (i : Fin n)
    (z : Fin n → Fin (q + 1)) (hz : intervalPositive z) :
    (sumSystem phi target i).eval
        (pointIntQ (intervalToFin (q := q) (n := n) hq z hz)) =
      (∑ j : Fin n, (phi i).eval ((z j).val : ℤ)) - target i := by
  have hpoint : pointIntQ (intervalToFin (q := q) (n := n) hq z hz) =
      (fun j => ((z j).val - 1 : ℤ)) := by
    funext j
    simp only [pointIntQ, intervalToFin]
    rw [Nat.cast_sub (hz j)]
    norm_num
  rw [hpoint]
  exact MAPFordCoarseP18Fiber.eval_sumSystem_interval phi target i z

lemma intervalToGeneric_mem
    {p r n : ℕ} (hp : p.Prime) (hR : 1 ≤ r)
    (phi : Fin n → Polynomial ℤ) (target : Fin n → ℤ)
    (z : intervalFiber (Nat.pow_pos (n := r) (Nat.Prime.pos hp)) phi target) :
    MAPFordHenselStep.nonsingularPrimePowerSolution
      (sumSystem phi target)
      (intervalToFin (Nat.pow_pos (n := r) (Nat.Prime.pos hp)) z.1.1 z.1.2) := by
  constructor
  · intro i
    have hi := eval_sumSystem_at_intervalToFin
      (Nat.pow_pos (n := r) (Nat.Prime.pos hp))
      phi target i z.1.1 z.1.2
    have hval :
        (sumSystem phi target i).eval
            (MAPFordHenselStep.pointInt
              (intervalToFin (Nat.pow_pos (n := r) (Nat.Prime.pos hp))
                z.1.1 z.1.2)) =
          (∑ j : Fin n, (phi i).eval ((z.1.1 j).val : ℤ)) - target i := by
      simpa [MAPFordHenselStep.pointInt, pointIntQ, intervalToFin] using hi
    rw [hval]
    exact z.2.1 i
  · exact z.2.2

/-- The interval fiber injects into the checked generic nonsingular prime-power
    fiber.  The shift is explicit: a source coordinate `z∈[1,q]` maps to the
    representative `z-1∈Fin q`, while `sumSystem` evaluates `Phi` at `z`. -/
def intervalToGeneric
    {p r n : ℕ} (hp : p.Prime) (hR : 1 ≤ r)
    (phi : Fin n → Polynomial ℤ) (target : Fin n → ℤ) :
    intervalFiber (Nat.pow_pos (n := r) (Nat.Prime.pos hp)) phi target →
      {a : Fin n → Fin (p ^ r) //
        MAPFordHenselStep.nonsingularPrimePowerSolution
          (sumSystem phi target) a} := fun z =>
  ⟨intervalToFin (Nat.pow_pos (n := r) (Nat.Prime.pos hp)) z.1.1 z.1.2,
    intervalToGeneric_mem hp hR phi target z⟩

lemma intervalToGeneric_injective
    {p r n : ℕ} (hp : p.Prime) (hR : 1 ≤ r)
    (phi : Fin n → Polynomial ℤ) (target : Fin n → ℤ) :
    Function.Injective (intervalToGeneric hp hR phi target) := by
  intro a b hab
  apply Subtype.ext
  exact intervalToFin_injective
    (Nat.pow_pos (n := r) (Nat.Prime.pos hp))
    (by exact congrArg Subtype.val hab)

/-- Exact coarse p.18 replacement: the literal interval fiber with one common
    modulus and explicit determinant coprimality has cardinal at most `p^n`.
    No degree or pure-power assumption is used. -/
theorem card_intervalFiber_le_p_pow_n
    {p r n : ℕ} (hp : p.Prime) (hR : 1 ≤ r)
    (phi : Fin n → Polynomial ℤ) (target : Fin n → ℤ) :
    Fintype.card (intervalFiber
      (Nat.pow_pos (n := r) (Nat.Prime.pos hp)) phi target) ≤ p ^ n := by
  classical
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : Fintype {a : Fin n → Fin (p ^ r) //
      MAPFordHenselStep.nonsingularPrimePowerSolution
        (sumSystem phi target) a} :=
    CategoryTheory.FinCategory.fintypeObj
  have hinj := intervalToGeneric_injective hp hR phi target
  have hcard := Fintype.card_le_of_injective
    (intervalToGeneric hp hR phi target) hinj
  have hg := MAPFordHenselStep.card_nonsingularPrimePowerSolution_le_p_pow_d
    hp hR (sumSystem phi target)
  exact hcard.trans hg

end
end MAPFordCoarseP18Fiber

#print axioms MAPFordCoarseP18Fiber.card_intervalFiber_le_p_pow_n
#print axioms MAPFordCoarseP18Fiber.intervalToGeneric_mem
