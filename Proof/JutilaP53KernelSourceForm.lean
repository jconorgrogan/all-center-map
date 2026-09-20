import JutilaP53KernelExpansion
import Mathlib.NumberTheory.MulChar.Lemmas

/-!
# Source form of the character-pair kernel on Jutila p.53

The positive Halasz energy has already been expanded into pair kernels.  This
file identifies each such kernel with the exact `B(s,chi)` series printed at
the foot of p.52, retaining both character labels and the conjugated zero
shift.  It also certifies that the residue condition `bar chi_i chi_j = chi_0`
is exactly equality of the two row characters.
-/

namespace MAPJutilaP53KernelSourceForm

open scoped BigOperators ComplexConjugate
open Complex
open MAPJutilaP53AggregateCorrelationLeaf
open MAPJutilaP53KernelExpansion

noncomputable section

def jutilaP53PairCharacter {q : ℕ}
    (i j : JutilaP53Row q) : DirichletCharacter ℂ q :=
  i.character⁻¹ * j.character

def jutilaP53PairShift {q : ℕ} (alpha : ℝ)
    (i j : JutilaP53Row q) : ℂ :=
  conj (i.zero - (alpha : ℂ)) + (j.zero - (alpha : ℂ))

@[simp] theorem pairShift_re {q : ℕ} (alpha : ℝ)
    (i j : JutilaP53Row q) :
    (jutilaP53PairShift alpha i j).re =
      (i.zero.re - alpha) + (j.zero.re - alpha) := by
  simp [jutilaP53PairShift]

@[simp] theorem pairShift_im {q : ℕ} (alpha : ℝ)
    (i j : JutilaP53Row q) :
    (jutilaP53PairShift alpha i j).im = j.zero.im - i.zero.im := by
  simp [jutilaP53PairShift]
  ring

theorem pairShift_re_mem_Icc
    {q : ℕ} {alpha epsilon : ℝ} {i j : JutilaP53Row q}
    (hiLo : alpha ≤ i.zero.re) (hiHi : i.zero.re ≤ alpha + epsilon)
    (hjLo : alpha ≤ j.zero.re) (hjHi : j.zero.re ≤ alpha + epsilon) :
    (jutilaP53PairShift alpha i j).re ∈ Set.Icc 0 (2 * epsilon) := by
  simp only [pairShift_re, Set.mem_Icc]
  constructor <;> linarith

/-- Jutila's literal correlation Dirichlet series `B(s,chi)` before Lemma 2
is inserted. -/
def jutilaP53SourceB {q : ℕ} (S : Finset ℕ) (M N : ℝ)
    (s : ℂ) (chi : DirichletCharacter ℂ q) : ℂ :=
  ∑' n : ℕ, (jutilaP53CorrelationWeight S M N n : ℂ) *
    chi n * (n : ℂ) ^ (-s)

theorem conj_character_apply_eq_inv
    {q : ℕ} (chi : DirichletCharacter ℂ q) (n : ℕ) :
    conj (chi n) = chi⁻¹ n := by
  simpa only [RCLike.star_def] using
    (MulChar.star_apply' chi (n : ZMod q))

theorem conj_natCast_cpow
    {n : ℕ} (hn : 0 < n) (s : ℂ) :
    conj ((n : ℂ) ^ (-s)) = (n : ℂ) ^ (-conj s) := by
  have harg : ((n : ℂ)).arg ≠ Real.pi := by
    have hcast : (n : ℂ) = (((n : ℝ) : ℝ) : ℂ) := by norm_cast
    rw [hcast, Complex.arg_ofReal_of_nonneg (by positivity : (0 : ℝ) ≤ n)]
    exact ne_of_lt Real.pi_pos
  have h := Complex.cpow_conj (n : ℂ) (-s) harg
  simpa using h.symm

theorem conj_phase_mul_phase_eq_pairTerm
    {q : ℕ} {alpha : ℝ} (i j : JutilaP53Row q)
    {n : ℕ} (hn : 0 < n) :
    conj (jutilaP53Phase alpha i n) * jutilaP53Phase alpha j n =
      jutilaP53PairCharacter i j n *
        (n : ℂ) ^ (-jutilaP53PairShift alpha i j) := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
  have hconjI := conj_natCast_cpow hn (i.zero - (alpha : ℂ))
  unfold jutilaP53Phase jutilaP53PairCharacter jutilaP53PairShift
  rw [if_neg hn0, if_neg hn0, map_mul, hconjI,
    conj_character_apply_eq_inv]
  rw [MulChar.mul_apply]
  calc
    i.character⁻¹ n * (n : ℂ) ^ (-conj (i.zero - (alpha : ℂ))) *
          (j.character n * (n : ℂ) ^ (-(j.zero - (alpha : ℂ)))) =
        (i.character⁻¹ n * j.character n) *
          ((n : ℂ) ^ (-conj (i.zero - (alpha : ℂ))) *
            (n : ℂ) ^ (-(j.zero - (alpha : ℂ)))) := by ring
    _ = (i.character⁻¹ n * j.character n) *
        (n : ℂ) ^
          ((-conj (i.zero - (alpha : ℂ))) +
            (-(j.zero - (alpha : ℂ)))) := by
      rw [Complex.cpow_add _ _ hnC]
    _ = (i.character⁻¹ n * j.character n) *
        (n : ℂ) ^
          (-(conj (i.zero - (alpha : ℂ)) +
            (j.zero - (alpha : ℂ)))) := by
      congr 1
      ring

/-- Exact identification of the pair kernel with the source `B` series. -/
theorem jutilaP53Kernel_eq_sourceB
    {q : ℕ} (S : Finset ℕ) (alpha M N : ℝ)
    (i j : JutilaP53Row q) :
    jutilaP53Kernel S alpha M N i j =
      jutilaP53SourceB S M N
        (jutilaP53PairShift alpha i j)
        (jutilaP53PairCharacter i j) := by
  unfold jutilaP53Kernel jutilaP53SourceB
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst n
    simp [jutilaP53Phase, jutilaP53CorrelationWeight,
      MAPJutilaHalaszLargeValueFront.jutilaCorrelationWeight]
  · rw [mul_assoc,
      conj_phase_mul_phase_eq_pairTerm i j (Nat.pos_of_ne_zero hn)]
    ring

/-- The principal-character residue condition on p.53 is exactly the
same-character condition. -/
theorem pairCharacter_eq_one_iff
    {q : ℕ} (i j : JutilaP53Row q) :
    jutilaP53PairCharacter i j = 1 ↔ i.character = j.character := by
  unfold jutilaP53PairCharacter
  constructor
  · intro h
    have := congrArg (fun chi : DirichletCharacter ℂ q =>
      i.character * chi) h
    have hji : j.character = i.character := by
      simpa [mul_assoc] using this
    exact hji.symm
  · rintro h
    rw [h, inv_mul_cancel]

end

end MAPJutilaP53KernelSourceForm

#print axioms MAPJutilaP53KernelSourceForm.conj_phase_mul_phase_eq_pairTerm
#print axioms MAPJutilaP53KernelSourceForm.jutilaP53Kernel_eq_sourceB
#print axioms MAPJutilaP53KernelSourceForm.pairCharacter_eq_one_iff
