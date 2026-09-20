import JutilaPseudocharacterMollifierSum

/-!
# Literal finite `M(it, chi, psi_r)` from Jutila (2.1)

This module instantiates the abstract mollifier term by the exact Euler-factor
formula on p.48, with Selberg's choice `f(n)=mu(n)phi(n)`.  It proves the
pointwise local envelope used after (2.11), including all character and
imaginary-power factors.
-/

namespace MAPJutilaPseudocharacterMExact

open scoped BigOperators
open Complex ArithmeticFunction
open MAPJutilaPseudocharacterMollifierBound
open MAPJutilaPseudocharacterMollifierSum

noncomputable section

def selbergPseudoCoeff (n : ℕ) : ℂ :=
  (ArithmeticFunction.moebius n : ℂ) * (Nat.totient n : ℂ)

def selbergPseudoAt (r d : ℕ) : ℂ :=
  selbergPseudoCoeff (r.gcd d)

def imaginaryNatPower (n : ℕ) (t : ℝ) : ℂ :=
  (n : ℂ) ^ (-((t : ℂ) * I))

def jutilaLocalEulerFactor {q : ℕ}
    (chi : DirichletCharacter ℂ q) (t : ℝ) (p : ℕ) : ℂ :=
  1 + (selbergPseudoCoeff p - 1) * chi p * imaginaryNatPower p t

def jutilaLocalEulerProduct {q : ℕ}
    (chi : DirichletCharacter ℂ q) (r d : ℕ) (t : ℝ) : ℂ :=
  ∏ p ∈ (r / r.gcd d).primeFactors, jutilaLocalEulerFactor chi t p

/-- Literal summand in Jutila's equation (2.1) on the line `s=it`. -/
def jutilaMTerm {q : ℕ}
    (chi : DirichletCharacter ℂ q) (xi : ℕ → ℂ)
    (r d : ℕ) (t : ℝ) : ℂ :=
  xi d * chi d * selbergPseudoAt r d * imaginaryNatPower d t *
    jutilaLocalEulerProduct chi r d t

/-- Finite version of `M(it,chi,psi_r)`, with `D` containing the support of
the sieve coefficients `xi`. -/
def jutilaMFinite {q : ℕ}
    (chi : DirichletCharacter ℂ q) (xi : ℕ → ℂ)
    (D : Finset ℕ) (r : ℕ) (t : ℝ) : ℂ :=
  ∑ d ∈ D, jutilaMTerm chi xi r d t

theorem norm_imaginaryNatPower_eq_one
    {n : ℕ} (hn : 0 < n) (t : ℝ) :
    ‖imaginaryNatPower n t‖ = 1 := by
  unfold imaginaryNatPower
  rw [Complex.norm_natCast_cpow_of_pos hn]
  simp

theorem selbergPseudoCoeff_prime_sub_one
    {p : ℕ} (hp : p.Prime) :
    selbergPseudoCoeff p - 1 = -(p : ℂ) := by
  rw [selbergPseudoCoeff, ArithmeticFunction.moebius_apply_prime hp,
    Nat.totient_prime hp, Nat.cast_sub hp.one_le]
  push_cast
  ring

theorem norm_selbergPseudoAt_le (r d : ℕ) :
    ‖selbergPseudoAt r d‖ ≤ (Nat.totient (r.gcd d) : ℝ) := by
  have hmu : ‖(ArithmeticFunction.moebius (r.gcd d) : ℂ)‖ ≤ 1 := by
    norm_num
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := r.gcd d)
  unfold selbergPseudoAt selbergPseudoCoeff
  rw [norm_mul]
  have hphiNorm : ‖((Nat.totient (r.gcd d) : ℕ) : ℂ)‖ =
      (Nat.totient (r.gcd d) : ℝ) := by simp
  rw [hphiNorm]
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right hmu (Nat.cast_nonneg _)

theorem norm_jutilaLocalEulerFactor_le
    {q : ℕ} (chi : DirichletCharacter ℂ q) (t : ℝ)
    {p : ℕ} (hp : p.Prime) :
    ‖jutilaLocalEulerFactor chi t p‖ ≤ (p : ℝ) + 1 := by
  have hpower := norm_imaginaryNatPower_eq_one hp.pos t
  have hpowerLe : ‖imaginaryNatPower p t‖ ≤ 1 := hpower.le
  have hchi : ‖chi p‖ ≤ 1 := DirichletCharacter.norm_le_one chi p
  rw [jutilaLocalEulerFactor, selbergPseudoCoeff_prime_sub_one hp]
  calc
    ‖1 + -(p : ℂ) * chi p * imaginaryNatPower p t‖ ≤
        ‖(1 : ℂ)‖ +
          ‖-(p : ℂ) * chi p * imaginaryNatPower p t‖ :=
      norm_add_le _ _
    _ = 1 + (p : ℝ) * ‖chi p‖ * ‖imaginaryNatPower p t‖ := by
      simp only [norm_one, norm_mul, norm_neg, norm_natCast]
    _ ≤ 1 + (p : ℝ) * 1 * 1 := by gcongr
    _ = (p : ℝ) + 1 := by ring

theorem norm_jutilaLocalEulerProduct_le
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    (r d : ℕ) (t : ℝ) :
    ‖jutilaLocalEulerProduct chi r d t‖ ≤
      pseudocharacterEulerProduct (r / r.gcd d) := by
  let n := r / r.gcd d
  have hprodNorm :
      ‖∏ p ∈ n.primeFactors, jutilaLocalEulerFactor chi t p‖ ≤
        ∏ p ∈ n.primeFactors, ‖jutilaLocalEulerFactor chi t p‖ :=
    Finset.norm_prod_le _ _
  calc
    ‖jutilaLocalEulerProduct chi r d t‖ ≤
        ∏ p ∈ n.primeFactors, ‖jutilaLocalEulerFactor chi t p‖ := by
      simpa [jutilaLocalEulerProduct, n] using hprodNorm
    _ ≤ ∏ p ∈ n.primeFactors, ((p : ℝ) + 1) := by
      apply Finset.prod_le_prod
      · intro p hp
        exact norm_nonneg _
      · intro p hp
        exact norm_jutilaLocalEulerFactor_le chi t
          (Nat.prime_of_mem_primeFactors hp)
    _ = pseudocharacterEulerProduct (r / r.gcd d) := by
      rfl

/-- Exact instantiation of the local envelope used below (2.11). -/
theorem norm_jutilaMTerm_le
    {q : ℕ} (chi : DirichletCharacter ℂ q) (xi : ℕ → ℂ)
    {r d : ℕ} (hd : 0 < d) (hxi : ‖xi d‖ ≤ 1) (t : ℝ) :
    ‖jutilaMTerm chi xi r d t‖ ≤
      pseudocharacterLocalEnvelope r d := by
  have hchi : ‖chi d‖ ≤ 1 := DirichletCharacter.norm_le_one chi d
  have hf := norm_selbergPseudoAt_le r d
  have hpower := norm_imaginaryNatPower_eq_one hd t
  have hpowerLe : ‖imaginaryNatPower d t‖ ≤ 1 := hpower.le
  have hEuler := norm_jutilaLocalEulerProduct_le chi r d t
  unfold jutilaMTerm
  simp only [norm_mul]
  calc
    ‖xi d‖ * ‖chi d‖ * ‖selbergPseudoAt r d‖ *
        ‖imaginaryNatPower d t‖ * ‖jutilaLocalEulerProduct chi r d t‖ ≤
      1 * 1 * (Nat.totient (r.gcd d) : ℝ) * 1 *
        pseudocharacterEulerProduct (r / r.gcd d) := by
      gcongr
    _ = pseudocharacterLocalEnvelope r d := by
      unfold pseudocharacterLocalEnvelope
      ring

theorem norm_jutilaMFinite_le
    {q : ℕ} (chi : DirichletCharacter ℂ q) (xi : ℕ → ℂ)
    {D : Finset ℕ} {z2 r : ℕ}
    (hDcard : D.card ≤ z2) (hDpos : ∀ d ∈ D, 0 < d)
    (hxi : ∀ d ∈ D, ‖xi d‖ ≤ 1)
    (hr : 0 < r) (hrsq : Squarefree r) (t : ℝ) :
    ‖jutilaMFinite chi xi D r t‖ ≤
      (z2 : ℝ) * ((r : ℝ) ^ 2 / (Nat.totient r : ℝ)) := by
  change ‖finitePseudocharacterMollifier D
    (fun r d => jutilaMTerm chi xi r d t) r‖ ≤ _
  apply norm_finitePseudocharacterMollifier_le hDcard hr hrsq
  intro d hd
  exact norm_jutilaMTerm_le chi xi (hDpos d hd) (hxi d hd) t

theorem sum_inv_mul_norm_jutilaMFinite_le
    {q : ℕ} (chi : DirichletCharacter ℂ q) (xi : ℕ → ℂ)
    {D : Finset ℕ} {z2 R : ℕ}
    (hDcard : D.card ≤ z2) (hDpos : ∀ d ∈ D, 0 < d)
    (hxi : ∀ d ∈ D, ‖xi d‖ ≤ 1)
    (hrsq : ∀ r ∈ Finset.Icc 1 R, Squarefree r)
    (t : ℝ) :
    (∑ r ∈ Finset.Icc 1 R,
      (r : ℝ)⁻¹ * ‖jutilaMFinite chi xi D r t‖) ≤
      (z2 : ℝ) * (R : ℝ) * (harmonic R : ℝ) ^ 4 := by
  change (∑ r ∈ Finset.Icc 1 R,
      (r : ℝ)⁻¹ * ‖finitePseudocharacterMollifier D
        (fun r d => jutilaMTerm chi xi r d t) r‖) ≤ _
  apply sum_inv_mul_norm_finitePseudocharacterMollifier_le hDcard hrsq
  intro r hrmem d hd
  exact norm_jutilaMTerm_le chi xi (hDpos d hd) (hxi d hd) t

/-- Source-faithful selected `r`-sum.  The selected set records exactly the
squarefree and conductor-coprime convention denoted by the prime on Jutila's
sum. -/
theorem sum_inv_mul_norm_jutilaMFinite_selected_le
    {q : ℕ} (chi : DirichletCharacter ℂ q) (xi : ℕ → ℂ)
    {D S : Finset ℕ} {z2 R : ℕ}
    (hDcard : D.card ≤ z2) (hDpos : ∀ d ∈ D, 0 < d)
    (hxi : ∀ d ∈ D, ‖xi d‖ ≤ 1)
    (hS : S ⊆ Finset.Icc 1 R)
    (hrsq : ∀ r ∈ S, Squarefree r)
    (hrcop : ∀ r ∈ S, r.Coprime q)
    (t : ℝ) :
    (∑ r ∈ S,
      (r : ℝ)⁻¹ * ‖jutilaMFinite chi xi D r t‖) ≤
      (z2 : ℝ) * (R : ℝ) * (harmonic R : ℝ) ^ 4 := by
  change (∑ r ∈ S,
      (r : ℝ)⁻¹ * ‖finitePseudocharacterMollifier D
        (fun r d => jutilaMTerm chi xi r d t) r‖) ≤ _
  apply sum_inv_mul_norm_finitePseudocharacterMollifier_selected_le
    hDcard hS hrsq hrcop
  intro r hrmem d hd
  exact norm_jutilaMTerm_le chi xi (hDpos d hd) (hxi d hd) t

end

end MAPJutilaPseudocharacterMExact

#print axioms MAPJutilaPseudocharacterMExact.norm_jutilaMTerm_le
#print axioms MAPJutilaPseudocharacterMExact.sum_inv_mul_norm_jutilaMFinite_le
#print axioms MAPJutilaPseudocharacterMExact.sum_inv_mul_norm_jutilaMFinite_selected_le
