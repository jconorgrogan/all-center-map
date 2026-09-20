import KoukLemma12TwoSpecializations
import APZeroDensityCertificate
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Conjugation symmetry for real Dirichlet-character L-functions

This is the analytic-continuation step used in Koukoulopoulos, Theorem 12.3:
for a real (equivalently quadratic-or-principal) character, nonreal zeros occur
in conjugate pairs.  The identity is first proved in the half-plane of absolute
convergence, term by term, and then continued by the identity theorem.
-/

namespace MAPRealCharacterLFunctionConjugation

open Complex Filter Topology Set LSeries
open DirichletZeros MAPAPZeroDensityCert
open scoped ComplexConjugate

noncomputable section

/-- Termwise conjugation of a Dirichlet L-series. -/
theorem LSeries_term_inv_conj {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (s : ℂ) (n : ℕ) :
    LSeries.term (fun n : ℕ => chi⁻¹ n) (conj s) n =
      conj (LSeries.term (fun n : ℕ => chi n) s n) := by
  by_cases hn : n = 0
  · subst n
    simp
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
  rw [map_div₀ (starRingEnd ℂ)]
  congr 1
  · exact (MulChar.star_apply' chi n).symm
  · rw [Complex.cpow_conj]
    · simp
    · rw [Complex.natCast_arg]
      exact ne_of_lt Real.pi_pos

/-- Conjugation of the absolutely convergent L-series. -/
theorem LSeries_inv_conj {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (s : ℂ) :
    LSeries (fun n : ℕ => chi⁻¹ n) (conj s) =
      conj (LSeries (fun n : ℕ => chi n) s) := by
  unfold LSeries
  rw [Complex.conj_tsum]
  congr 1
  funext n
  exact LSeries_term_inv_conj chi s n

private theorem chi_inv_ne_one {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) : chi⁻¹ ≠ 1 :=
  inv_ne_one.mpr hchi

/-- Analytic continuation of termwise conjugation from `Re s > 1` to the
entire nonprincipal Dirichlet L-function. -/
theorem LFunction_inv_conj {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) (s : ℂ) :
    DirichletCharacter.LFunction chi⁻¹ (conj s) =
      conj (DirichletCharacter.LFunction chi s) := by
  let f : ℂ → ℂ := DirichletCharacter.LFunction chi⁻¹
  let g : ℂ → ℂ := conj ∘ DirichletCharacter.LFunction chi ∘ conj
  have hf : AnalyticOnNhd ℂ f Set.univ :=
    ((DirichletCharacter.differentiable_LFunction
      (chi_inv_ne_one chi hchi)).differentiableOn).analyticOnNhd isOpen_univ
  have hgdiff : Differentiable ℂ g := by
    intro z
    exact (differentiableAt_conj_conj_iff
      (f := DirichletCharacter.LFunction chi)).2
      ((DirichletCharacter.differentiable_LFunction hchi) (conj z))
  have hg : AnalyticOnNhd ℂ g Set.univ :=
    hgdiff.differentiableOn.analyticOnNhd isOpen_univ
  have hevent : f =ᶠ[nhds (2 : ℂ)] g := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} :=
      isOpen_lt continuous_const continuous_re
    apply eventually_of_mem (hopen.mem_nhds (by norm_num))
    intro z hz
    dsimp [f, g]
    rw [DirichletCharacter.LFunction_eq_LSeries chi⁻¹]
    · rw [DirichletCharacter.LFunction_eq_LSeries chi]
      · simpa using LSeries_inv_conj chi (conj z)
      · exact hz
    · simpa using hz
  have heq : f = g := hf.eq_of_eventuallyEq hg hevent
  simpa [f, g, Function.comp_def] using congrFun heq (conj s)

/-- If `chi^2 = 1`, then `chi` equals its inverse. -/
theorem inv_eq_self_of_sq_eq_one {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hsq : chi ^ 2 = 1) : chi⁻¹ = chi := by
  calc
    chi⁻¹ = chi⁻¹ * (chi * chi) := by rw [← pow_two, hsq, mul_one]
    _ = chi := by group

/-- A nonprincipal real-character L-function is equivariant under complex
conjugation on the whole plane. -/
theorem LFunction_conj_eq_conj_of_sq_eq_one {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (hsq : chi ^ 2 = 1) (s : ℂ) :
    DirichletCharacter.LFunction chi (conj s) =
      conj (DirichletCharacter.LFunction chi s) := by
  have hinv := inv_eq_self_of_sq_eq_one chi hsq
  calc
    DirichletCharacter.LFunction chi (conj s) =
        DirichletCharacter.LFunction chi⁻¹ (conj s) := by rw [hinv]
    _ = conj (DirichletCharacter.LFunction chi s) :=
      LFunction_inv_conj chi hchi s

/-- The divisor support in a rectangle symmetric about the real axis is
closed under conjugation for a nonprincipal real character. -/
theorem conj_mem_zeroSupport_of_sq_eq_one
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hchi : chi ≠ 1) (hsq : chi ^ 2 = 1)
    {sigma T : ℝ} {rho : ℂ} (hrho : rho ∈ zeroSupport chi sigma T) :
    conj rho ∈ zeroSupport chi sigma T := by
  have hdiv : zeroDivisor chi sigma T rho ≠ 0 :=
    (zeroSupport_mem_iff chi sigma T rho).mp hrho
  have hrect : rho ∈ zeroRectangle sigma T :=
    (zeroDivisor chi sigma T).supportWithinDomain hdiv
  have hrectConj : conj rho ∈ zeroRectangle sigma T := by
    rw [zeroRectangle, Complex.mem_reProdIm] at hrect ⊢
    refine ⟨hrect.1, ?_⟩
    constructor <;> simp only [Complex.conj_im] <;> linarith [hrect.2.1, hrect.2.2]
  apply (mem_zeroSupport_iff_eq_zero chi sigma T hrectConj).mpr
  have hzeroReg := regularizedLFunction_eq_zero_of_mem_zeroSupport
    chi sigma T hrho
  have hzero : DirichletCharacter.LFunction chi rho = 0 := by
    simpa [regularizedLFunction, hchi] using hzeroReg
  simpa [regularizedLFunction, hchi,
    LFunction_conj_eq_conj_of_sq_eq_one chi hchi hsq rho, hzero]

#print axioms MAPRealCharacterLFunctionConjugation.LFunction_inv_conj
#print axioms MAPRealCharacterLFunctionConjugation.LFunction_conj_eq_conj_of_sq_eq_one
#print axioms MAPRealCharacterLFunctionConjugation.conj_mem_zeroSupport_of_sq_eq_one

end

end MAPRealCharacterLFunctionConjugation
