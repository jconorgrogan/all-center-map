import FordCoarseP18Fiber

open scoped BigOperators
open Finset
open MvPolynomial
set_option maxHeartbeats 800000
set_option maxRecDepth 10000

namespace MAPFordCoarseP18Jacobian
noncomputable section

lemma eval_derivative_range (q : Polynomial ℤ) (x : ℤ) :
    q.derivative.eval x =
      ∑ t ∈ range (q.natDegree + 1), q.coeff t * (t : ℤ) * x ^ (t - 1) := by
  rw [Polynomial.derivative_eval, Polynomial.sum_def]
  apply Finset.sum_subset
  · intro n hn
    rw [mem_range]
    have hne : q.coeff n ≠ 0 := (Polynomial.mem_support_iff.mp hn)
    have hle := Polynomial.le_natDegree_of_ne_zero hne
    omega
  · intro n hn hns
    have hzero : q.coeff n = 0 := by
      exact not_ne_iff.mp ((Polynomial.mem_support_iff).not.mp hns)
    simp [hzero]

lemma pderiv_shiftedPolyAt {n : ℕ} (q : Polynomial ℤ) (i j : Fin n)
    (x : Fin n → ℤ) :
    (MvPolynomial.pderiv j
      (MAPFordCoarseP18Fiber.shiftedPolyAt q i)).eval x =
      if j = i then (q.derivative).eval (x i + 1) else 0 := by
  classical
  by_cases hij : j = i
  · subst j
    simp [MAPFordCoarseP18Fiber.shiftedPolyAt, MvPolynomial.pderiv_mul,
      MvPolynomial.pderiv_pow]
    rw [eval_derivative_range]
    apply Finset.sum_congr rfl
    intro t ht
    ring
  · simp [MAPFordCoarseP18Fiber.shiftedPolyAt, MvPolynomial.pderiv_mul,
      MvPolynomial.pderiv_pow, hij, Ne.symm hij]

lemma pderiv_shiftedPolyAt_zero {n : ℕ} (q : Polynomial ℤ)
    (i j : Fin n) (hij : j ≠ i) :
    MvPolynomial.pderiv j
      (MAPFordCoarseP18Fiber.shiftedPolyAt q i) = 0 := by
  classical
  simp [MAPFordCoarseP18Fiber.shiftedPolyAt, MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_pow, hij, Ne.symm hij]

lemma pderiv_sumSystem {n : ℕ} (phi : Fin n → Polynomial ℤ)
    (target : Fin n → ℤ) (i j : Fin n) (x : Fin n → ℤ) :
    (MvPolynomial.pderiv j
      (MAPFordCoarseP18Fiber.sumSystem phi target i)).eval x =
      (phi i).derivative.eval (x j + 1) := by
  classical
  simp only [MAPFordCoarseP18Fiber.sumSystem]
  rw [map_sub, map_sum]
  simp only [MvPolynomial.pderiv_C]
  rw [Finset.sum_eq_single j]
  · simpa [pderiv_shiftedPolyAt]
  · intro b hb hbj
    rw [pderiv_shiftedPolyAt_zero _ _ _ (Ne.symm hbj)]
  · simp

/-- Ford's source orientation: rows are variables `z_i`, columns are the
    derivatives of the equations `Phi_j`. -/
def sourceJacobian {q n : ℕ} (phi : Fin n → Polynomial ℤ)
    (z : Fin n → Fin (q + 1)) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => (phi j).derivative.eval ((z i).val : ℤ)

lemma sumSystem_intJacobian_entry {p r n : ℕ} (hq : 0 < p ^ r)
    (phi : Fin n → Polynomial ℤ) (target : Fin n → ℤ)
    (z : Fin n → Fin (p ^ r + 1)) (hz : MAPFordCoarseP18Fiber.intervalPositive z)
    (i j : Fin n) :
    (MAPFordHenselStep.intJacobian
      (MAPFordCoarseP18Fiber.sumSystem phi target)
      (MAPFordHenselStep.pointInt
        (MAPFordCoarseP18Fiber.intervalToFin (q := p ^ r) (n := n) hq z hz))) i j =
      (phi i).derivative.eval ((z j).val : ℤ) := by
  have hcoord :
      MAPFordHenselStep.pointInt
          (MAPFordCoarseP18Fiber.intervalToFin (q := p ^ r) (n := n) hq z hz) j + 1 =
        (z j).val := by
    simp only [MAPFordHenselStep.pointInt,
      MAPFordCoarseP18Fiber.intervalToFin]
    rw [Nat.cast_sub (hz j)]
    norm_num
  simpa [MAPFordHenselStep.intJacobian, hcoord] using
    (pderiv_sumSystem phi target i j
      (MAPFordHenselStep.pointInt
        (MAPFordCoarseP18Fiber.intervalToFin (q := p ^ r) (n := n) hq z hz)))

lemma sumSystem_intJacobian_eq_sourceJacobian_transpose
    {p r n : ℕ} (hq : 0 < p ^ r)
    (phi : Fin n → Polynomial ℤ) (target : Fin n → ℤ)
    (z : Fin n → Fin (p ^ r + 1)) (hz : MAPFordCoarseP18Fiber.intervalPositive z) :
    MAPFordHenselStep.intJacobian
        (MAPFordCoarseP18Fiber.sumSystem phi target)
        (MAPFordHenselStep.pointInt
          (MAPFordCoarseP18Fiber.intervalToFin (q := p ^ r) (n := n) hq z hz)) =
      Matrix.transpose (sourceJacobian phi z) := by
  ext i j
  rw [sumSystem_intJacobian_entry hq phi target z hz i j]
  rfl

lemma sumSystem_intJacobian_det_eq_sourceJacobian_det
    {p r n : ℕ} (hq : 0 < p ^ r)
    (phi : Fin n → Polynomial ℤ) (target : Fin n → ℤ)
    (z : Fin n → Fin (p ^ r + 1)) (hz : MAPFordCoarseP18Fiber.intervalPositive z) :
    (MAPFordHenselStep.intJacobian
        (MAPFordCoarseP18Fiber.sumSystem phi target)
        (MAPFordHenselStep.pointInt
          (MAPFordCoarseP18Fiber.intervalToFin (q := p ^ r) (n := n) hq z hz))).det =
      (sourceJacobian phi z).det := by
  rw [sumSystem_intJacobian_eq_sourceJacobian_transpose]
  exact Matrix.det_transpose _

lemma source_nonsingularity_iff_shifted
    {p r n : ℕ} (hq : 0 < p ^ r) (phi : Fin n → Polynomial ℤ)
    (target : Fin n → ℤ) (z : Fin n → Fin (p ^ r + 1))
    (hz : MAPFordCoarseP18Fiber.intervalPositive z) :
    p.Coprime (sourceJacobian phi z).det.natAbs ↔
      p.Coprime ((MAPFordHenselStep.intJacobian
        (MAPFordCoarseP18Fiber.sumSystem phi target)
        (MAPFordHenselStep.pointInt
          (MAPFordCoarseP18Fiber.intervalToFin (q := p ^ r) (n := n) hq z hz))).det.natAbs) := by
  rw [sumSystem_intJacobian_det_eq_sourceJacobian_det hq phi target z hz]

end
end MAPFordCoarseP18Jacobian

#print axioms MAPFordCoarseP18Jacobian.sumSystem_intJacobian_entry
#print axioms MAPFordCoarseP18Jacobian.sumSystem_intJacobian_det_eq_sourceJacobian_det
#print axioms MAPFordCoarseP18Jacobian.source_nonsingularity_iff_shifted
