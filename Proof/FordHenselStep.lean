import Mathlib

open scoped BigOperators
open MvPolynomial

namespace MAPFordHenselStep

noncomputable section

/- The square-zero Taylor identity is proved by the MvPolynomial induction
   (constant, addition, and multiplication by a variable).  It is the exact
   first-order expansion needed when the increment is p^r and r >= 1. -/
lemma taylor_square_zero
    {R A σ : Type*} [CommRing R] [CommRing A] [Fintype σ]
    (φ : R →+* A) (p : MvPolynomial σ R) (x v : σ → A) (h : A)
    (hh : h * h = 0) :
    p.eval₂ φ (fun i => x i + h * v i) =
      p.eval₂ φ x + h * ∑ i, (pderiv i p).eval₂ φ x * v i := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp [hh]
  | add p q hp hq =>
      simp only [eval₂_add, hp, hq]
      rw [show (∑ i, (pderiv i (p + q)).eval₂ φ x * v i) =
          (∑ i, (pderiv i p).eval₂ φ x * v i) +
            (∑ i, (pderiv i q).eval₂ φ x * v i) by
          simp only [map_add, eval₂_add]
          simp_rw [add_mul]
          rw [Finset.sum_add_distrib]]
      ring
  | mul_X p i hp =>
      rw [eval₂_mul, eval₂_X, hp]
      have hsum :
          (∑ j, (pderiv j (p * X i)).eval₂ φ x * v j) =
            (∑ j, (pderiv j p).eval₂ φ x * v j) * x i +
              (p.eval₂ φ x) * v i := by
        simp only [pderiv_mul, eval₂_add, eval₂_mul, eval₂_X]
        simp_rw [add_mul]
        rw [Finset.sum_add_distrib, Finset.sum_mul]
        rw [show (∑ j, eval₂ φ x ((pderiv j p)) * x i * v j) =
            (∑ j, eval₂ φ x ((pderiv j p)) * v j) * x i by
              calc
                _ = ∑ j, (eval₂ φ x ((pderiv j p)) * v j) * x i := by
                  apply Finset.sum_congr rfl
                  intro j hj
                  ring
                _ = _ := (Finset.sum_mul _ _ _).symm]
        rw [show (∑ j, eval₂ φ x p * eval₂ φ x ((pderiv j (X i))) * v j) =
            eval₂ φ x p * v i by
              simp only [MvPolynomial.pderiv_X]
              rw [Finset.sum_eq_single i]
              · simp
              · intro b hb hbi
                simp [hbi]
              · simp]
        rw [show (∑ j, eval₂ φ x ((pderiv j p)) * v j) * x i =
            ∑ j, eval₂ φ x ((pderiv j p)) * v j * x i by
              rw [Finset.sum_mul]]
      simp only [eval₂_mul, eval₂_X]
      rw [hsum]
      ring_nf
      rw [pow_two, hh]
      ring

def jacobian
    {R A σ : Type*} [CommRing R] [CommRing A]
    (φ : R →+* A) (f : σ → MvPolynomial σ R) (x : σ → A) :
    Matrix σ σ A := fun i j => (pderiv j (f i)).eval₂ φ x

/- Unique infinitesimal lift in any commutative ring: if the Jacobian is a
   unit-determinant matrix, equality of polynomial values forces the whole
   square-zero increment to vanish. -/
theorem unique_square_zero_lift
    {R A σ : Type*} [CommRing R] [CommRing A] [Fintype σ] [DecidableEq σ]
    (φ : R →+* A) (f : σ → MvPolynomial σ R)
    (x v : σ → A) (h : A) (hh : h * h = 0)
    (heval : ∀ i, (f i).eval₂ φ (fun j => x j + h * v j) =
      (f i).eval₂ φ x)
    (hdet : IsUnit (jacobian φ f x).det) :
    (fun i => h * v i) = 0 := by
  let J : Matrix σ σ A := jacobian φ f x
  have hJ : J.mulVec (fun j => h * v j) = 0 := by
    funext i
    have ht := taylor_square_zero φ (f i) x v h hh
    have hi := heval i
    rw [ht] at hi
    have hsum :
        h * ∑ j, (pderiv j (f i)).eval₂ φ x * v j = 0 := by
      apply add_left_cancel (a := (f i).eval₂ φ x)
      simpa using hi
    change (∑ j, (pderiv j (f i)).eval₂ φ x * (h * v j)) = 0
    rw [show (∑ j, (pderiv j (f i)).eval₂ φ x * (h * v j)) =
        h * ∑ j, (pderiv j (f i)).eval₂ φ x * v j by
          calc
            _ = ∑ j, h * ((pderiv j (f i)).eval₂ φ x * v j) := by
              apply Finset.sum_congr rfl
              intro j hj
              ring
            _ = _ := (Finset.mul_sum _ _ _).symm]
    exact hsum
  have hzero : (J⁻¹ * J).mulVec (fun j => h * v j) = 0 := by
    rw [← Matrix.mulVec_mulVec]
    rw [hJ]
    simp
  have hmat : J⁻¹ * J = 1 := Matrix.nonsing_inv_mul J hdet
  rw [hmat] at hzero
  simpa using hzero

end
end MAPFordHenselStep

namespace MAPFordHenselStep

/- Prime-power specialization: the increment p^r is square-zero modulo
   p^(r+1) for r >= 1.  The remaining hypotheses are literal polynomial
   evaluation equality and a unit Jacobian determinant in that residue ring. -/
theorem unique_prime_power_lift
    {p r d : ℕ} (hp : p.Prime) (hr : 1 ≤ r)
    (f : Fin d → MvPolynomial (Fin d) ℤ)
    (x v : Fin d → ZMod (p ^ (r + 1)))
    (heval : ∀ i, (f i).eval₂ (Int.castRingHom _) (fun j =>
      x j + (p ^ r : ZMod (p ^ (r + 1))) * v j) =
      (f i).eval₂ (Int.castRingHom _) x)
    (hdet : IsUnit (jacobian (Int.castRingHom _) f x).det) :
    (fun i => (p ^ r : ZMod (p ^ (r + 1))) * v i) = 0 := by
  classical
  have hle : r + 1 ≤ 2 * r := by omega
  have hdiv : p ^ (r + 1) ∣ p ^ (2 * r) := by
    exact Nat.pow_dvd_pow p hle
  obtain ⟨c, hc⟩ := hdiv
  have hh : (p ^ r : ZMod (p ^ (r + 1))) * (p ^ r : ZMod (p ^ (r + 1))) = 0 := by
    rw [← pow_add, show r + r = 2 * r by omega, ← Nat.cast_pow, hc,
      Nat.cast_mul, ZMod.natCast_self, zero_mul]
  exact unique_square_zero_lift (Int.castRingHom _) f x v
    (p ^ r : ZMod (p ^ (r + 1))) hh heval hdet

end MAPFordHenselStep

namespace MAPFordHenselStep

noncomputable section

def intJacobian {d : ℕ} (f : Fin d → MvPolynomial (Fin d) ℤ)
    (x : Fin d → ℤ) : Matrix (Fin d) (Fin d) ℤ :=
  fun i j => (pderiv j (f i)).eval x

lemma eval_intCast_zmod {d q : ℕ} (p : MvPolynomial (Fin d) ℤ)
    (x : Fin d → ℤ) :
    p.eval₂ (Int.castRingHom (ZMod q)) (fun i => (x i : ZMod q)) =
      (p.eval x : ZMod q) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp only [MvPolynomial.eval₂_C, MvPolynomial.eval_C]; rfl
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

def castMatrix {d q : ℕ} (A : Matrix (Fin d) (Fin d) ℤ) :
    Matrix (Fin d) (Fin d) (ZMod q) := fun i j => (A i j : ZMod q)

lemma det_cast_zmod {d q : ℕ} (A : Matrix (Fin d) (Fin d) ℤ) :
    (castMatrix A).det = (A.det : ZMod q) := by
  classical
  rw [Matrix.det_apply]
  rw [Matrix.det_apply A]
  change _ = (Int.castRingHom (ZMod q))
    (∑ σ, Equiv.Perm.sign σ • ∏ i, A (σ i) i)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  simp [castMatrix]

/- Literal integer-coordinate form of the one-step injection.  The unit
   determinant is derived from p-coprimality, then the ZMod prime-power
   producer is applied to the residue classes. -/
theorem unique_integer_lift
    {p r d : ℕ} (hp : p.Prime) (hr : 1 ≤ r)
    (f : Fin d → MvPolynomial (Fin d) ℤ) (x y : Fin d → ℤ)
    (hxy : ∀ i, x i ≡ y i [ZMOD (p ^ r : ℕ)])
    (hval : ∀ i, (f i).eval x ≡ (f i).eval y [ZMOD (p ^ (r + 1) : ℕ)])
    (hcop : p.Coprime (intJacobian f x).det.natAbs) :
    ∀ i, x i ≡ y i [ZMOD (p ^ (r + 1) : ℕ)] := by
  classical
  let q := p ^ (r + 1)
  let z : Fin d → ZMod q := fun i => (x i : ZMod q)
  let w : Fin d → ZMod q := fun i => (y i : ZMod q)
  have hdetInt : (intJacobian f x).det.natAbs.Coprime q := by
    exact hcop.symm.pow_right (r + 1)
  have hdetNat : IsUnit ((intJacobian f x).det.natAbs : ZMod q) :=
    (ZMod.isUnit_iff_coprime _ _).2 hdetInt
  have hdet : IsUnit (jacobian (Int.castRingHom _) f z).det := by
    have heq : (jacobian (Int.castRingHom (ZMod q)) f z).det =
        ((intJacobian f x).det : ZMod q) := by
      rw [show jacobian (Int.castRingHom (ZMod q)) f z =
          castMatrix (intJacobian f x) by
            ext i j
            simpa [jacobian, intJacobian, z] using
              (eval_intCast_zmod (q := q) (pderiv j (f i)) (x))]
      exact det_cast_zmod _
    rw [heq]
    cases hD : (intJacobian f x).det with
    | ofNat n => simpa [hD] using hdetNat
    | negSucc n =>
        have hu : IsUnit ((n + 1 : ℕ) : ZMod q) := by
          simpa [Int.natAbs, hD] using hdetNat
        simpa [hD] using hu.neg
  let v : Fin d → ZMod q := fun i =>
    ((Classical.choose (Int.modEq_iff_add_fac.mp (hxy i)) : ℤ) : ZMod q)
  have hv : ∀ i, w i = z i + (p ^ r : ZMod q) * v i := by
    intro i
    have hk := Classical.choose_spec (Int.modEq_iff_add_fac.mp (hxy i))
    change (y i : ZMod q) = (x i : ZMod q) + (p ^ r : ZMod q) * v i
    rw [hk]
    simp [v]
  have hvalZ : ∀ i, (f i).eval₂ (Int.castRingHom (ZMod q))
      (fun j => z j + (p ^ r : ZMod q) * v j) =
        (f i).eval₂ (Int.castRingHom (ZMod q)) z := by
    intro i
    have hi := (ZMod.intCast_eq_intCast_iff ((f i).eval x) ((f i).eval y) q).2 (hval i)
    have hi' : (f i).eval₂ (Int.castRingHom (ZMod q)) w =
        (f i).eval₂ (Int.castRingHom (ZMod q)) z := by
      simpa [z, w, eval_intCast_zmod] using hi.symm
    have hfun : (fun j => z j + (p ^ r : ZMod q) * v j) = w := by
      funext j
      exact (hv j).symm
    rw [hfun]
    exact hi'
  have hstep := unique_prime_power_lift hp hr f z v hvalZ hdet
  intro i
  have hi := congrFun hstep i
  have hwz : w i = z i := by
    rw [hv i]
    simpa using hi
  exact (ZMod.intCast_eq_intCast_iff (x i) (y i) q).1 hwz.symm

end
end MAPFordHenselStep

#print axioms MAPFordHenselStep.unique_square_zero_lift
#print axioms MAPFordHenselStep.unique_prime_power_lift
