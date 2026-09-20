import JutilaP53SameCharacterResidueFiberBound
import JutilaP53DivisorKernelAbsoluteMass

/-!
# Principal residue after the actual p.53 divisor expansion
-/

namespace MAPJutilaP53PrincipalDivisorResidueBound

open scoped BigOperators
open Complex
open MAPJutilaP53PairEulerFactorization
open MAPJutilaP53Lemma2Bridge
open MAPJutilaP53TwoScaleContour
open MAPJutilaP53PrincipalResidueEnvelope
open MAPJutilaP53DivisorKernelAbsoluteMass
open MAPJutilaLemma3AbsoluteMass
open CGLProofDAG
open MAPJutilaP53AggregateCorrelationLeaf
open MAPJutilaP53KernelSourceForm
open MAPJutilaOneSeparatedExponentialPacking

noncomputable section

def p53PrincipalDivisorResidue (q : ℕ) [NeZero q]
    (s : ℂ) (M N : ℝ) (r r' : ℕ) : ℂ :=
  ∑ d ∈ (r.lcm r').divisors,
    LSeries.term
        (p53TwistedDivisorKernel (1 : DirichletCharacter ℂ q) r r')
        (1 + s) d *
      p53PrincipalResidue q s (N / (d : ℝ)) (M / (d : ℝ))

theorem norm_twisted_kernel_term_le_kernel
    (q : ℕ) [NeZero q] {r r' d : ℕ} (hd : 0 < d)
    {s : ℂ} (hs : 0 ≤ s.re) :
    ‖LSeries.term
        (p53TwistedDivisorKernel (1 : DirichletCharacter ℂ q) r r')
        (1 + s) d‖ ≤ ‖p53PairDivisorKernel r r' d‖ := by
  have hraw := norm_twisted_kernel_term_le
    (1 : DirichletCharacter ℂ q) (r := r) (r' := r') hd (s := s)
  have hdOne : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hden : 1 ≤ (d : ℝ) ^ (1 + s).re :=
    Real.one_le_rpow hdOne (by simp; linarith)
  have hdenPos : 0 < (d : ℝ) ^ (1 + s).re := zero_lt_one.trans_le hden
  exact hraw.trans (by
    apply (div_le_iff₀ hdenPos).2
    nlinarith [norm_nonneg (p53PairDivisorKernel r r' d)])

/-- The complete finite divisor residue inherits the same exponential
off-diagonal profile, multiplied only by the exact Lemma-3 Euler mass. -/
theorem norm_p53PrincipalDivisorResidue_le_offDiagonal
    (q : ℕ) [NeZero q] {s : ℂ} {M N : ℝ} {r r' : ℕ}
    (hr : Squarefree r) (hr' : Squarefree r')
    (hscale : ((r.lcm r' : ℕ) : ℝ) ≤ M) (hMN : M ≤ N)
    (hsLo : 0 ≤ s.re) (hsHi : s.re ≤ 1 / 2)
    (hsIm : 1 ≤ |s.im|) :
    ‖p53PrincipalDivisorResidue q s M N r r'‖ ≤
      48 * Real.exp (-|s.im|) *
        (lemmaThreeAbsoluteMass r.primeFactors r'.primeFactors : ℝ) := by
  have hrPos : 0 < r := Nat.pos_of_ne_zero (Squarefree.ne_zero hr)
  have hrPos' : 0 < r' := Nat.pos_of_ne_zero (Squarefree.ne_zero hr')
  have hlcmPos : 0 < r.lcm r' := Nat.lcm_pos hrPos hrPos'
  unfold p53PrincipalDivisorResidue
  calc
    _ ≤ ∑ d ∈ (r.lcm r').divisors,
        ‖LSeries.term
            (p53TwistedDivisorKernel (1 : DirichletCharacter ℂ q) r r')
            (1 + s) d *
          p53PrincipalResidue q s (N / (d : ℝ)) (M / (d : ℝ))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ d ∈ (r.lcm r').divisors,
        ‖p53PairDivisorKernel r r' d‖ *
          (48 * Real.exp (-|s.im|)) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdPos := Nat.pos_of_mem_divisors hd
      have hdDvd : d ∣ r.lcm r' := (Nat.mem_divisors.mp hd).1
      have hdLe : d ≤ r.lcm r' := Nat.le_of_dvd hlcmPos hdDvd
      have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hdPos
      have hdLeR : (d : ℝ) ≤ (r.lcm r' : ℕ) := by exact_mod_cast hdLe
      have hdM : (d : ℝ) ≤ M := hdLeR.trans hscale
      have hdN : (d : ℝ) ≤ N := hdM.trans hMN
      rw [norm_mul]
      exact mul_le_mul
        (norm_twisted_kernel_term_le_kernel q hdPos hsLo)
        (norm_p53PrincipalResidue_le_pureExp q
          ((one_le_div₀ hdR).2 hdN) ((one_le_div₀ hdR).2 hdM)
          hsLo hsHi hsIm)
        (norm_nonneg _) (norm_nonneg _)
    _ = 48 * Real.exp (-|s.im|) *
        ∑ d ∈ (r.lcm r').divisors,
          ‖p53PairDivisorKernel r r' d‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ = _ := by
      rw [sum_norm_p53PairDivisorKernel_eq_lemmaThreeAbsoluteMass hr hr']

theorem norm_p53PrincipalDivisorResidue_le_primeProducts
    (q : ℕ) [NeZero q] {s : ℂ} {M N : ℝ} {r r' : ℕ}
    (hr : Squarefree r) (hr' : Squarefree r')
    (hscale : ((r.lcm r' : ℕ) : ℝ) ≤ M) (hMN : M ≤ N)
    (hsLo : 0 ≤ s.re) (hsHi : s.re ≤ 1 / 2)
    (hsIm : 1 ≤ |s.im|) :
    ‖p53PrincipalDivisorResidue q s M N r r'‖ ≤
      48 * Real.exp (-|s.im|) *
        (((∏ p ∈ r.primeFactors, (p + 1)) *
          ∏ p ∈ r'.primeFactors, (p + 1) : ℕ) : ℝ) := by
  have hraw := norm_p53PrincipalDivisorResidue_le_offDiagonal q
    hr hr' hscale hMN hsLo hsHi hsIm
  calc
    _ ≤ 48 * Real.exp (-|s.im|) *
        (lemmaThreeAbsoluteMass r.primeFactors r'.primeFactors : ℝ) := hraw
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact_mod_cast lemmaThreeAbsoluteMass_le r.primeFactors r'.primeFactors
        (fun p hp => by
          rw [Finset.mem_union] at hp
          exact hp.elim
            (fun h => (Nat.prime_of_mem_primeFactors h).two_le)
            (fun h => (Nat.prime_of_mem_primeFactors h).two_le))

/-- One fixed-character fiber of the actual divisor residue costs only one
Euler mass per row, independently of the number of other zeros in the fiber. -/
theorem sum_p53PrincipalDivisorResidue_offDiagonal_le
    (q : ℕ) [NeZero q] (rows : Finset (JutilaP53Row q))
    (chi : DirichletCharacter ℂ q) (i : JutilaP53Row q)
    {alpha epsilon M N : ℝ} {r r' : ℕ}
    (hr : Squarefree r) (hr' : Squarefree r')
    (hscale : ((r.lcm r' : ℕ) : ℝ) ≤ M) (hMN : M ≤ N)
    (heps : 2 * epsilon ≤ 1 / 2)
    (hrows : ∀ row ∈ rows,
      alpha ≤ row.zero.re ∧ row.zero.re ≤ alpha + epsilon)
    (hi : i ∈ rows) (hichar : i.character = chi)
    (hsep : OneSeparated
      ((rows.filter (fun row => row.character = chi)).image
        (fun row => row.zero.im)))
    (hcard : ((rows.filter (fun row => row.character = chi)).image
        (fun row => row.zero.im)).card =
      (rows.filter (fun row => row.character = chi)).card) :
    ∑ j ∈ (rows.filter (fun row => row.character = chi)).filter
        (fun j => j ≠ i),
      ‖p53PrincipalDivisorResidue q
        (jutilaP53PairShift alpha i j) M N r r'‖ ≤
      48 * Real.exp 1 * integerExponentialMass *
        (lemmaThreeAbsoluteMass r.primeFactors r'.primeFactors : ℝ) := by
  let fiber := rows.filter (fun row => row.character = chi)
  let ord : JutilaP53Row q → ℝ := fun row => row.zero.im
  let A : ℝ := (lemmaThreeAbsoluteMass r.primeFactors r'.primeFactors : ℝ)
  have hiFiber : i ∈ fiber := by simp [fiber, hi, hichar]
  have hinj : Set.InjOn ord (↑fiber : Set (JutilaP53Row q)) :=
    Finset.card_image_iff.mp (by simpa [fiber, ord] using hcard)
  have hpoint : ∀ j ∈ fiber.filter (fun j => j ≠ i),
      ‖p53PrincipalDivisorResidue q
          (jutilaP53PairShift alpha i j) M N r r'‖ ≤
        48 * Real.exp (-|ord j - ord i|) * A := by
    intro j hj
    have hjFiber := (Finset.mem_filter.mp hj).1
    have hji := (Finset.mem_filter.mp hj).2
    have hjRows := (Finset.mem_filter.mp hjFiber).1
    have himNe : ord j ≠ ord i := by
      intro heq
      exact hji (hinj (by simpa using hjFiber) (by simpa using hiFiber) heq)
    have himSep : 1 ≤ |ord j - ord i| :=
      hsep (ord j) (Finset.mem_image.mpr ⟨j, hjFiber, rfl⟩)
        (ord i) (Finset.mem_image.mpr ⟨i, hiFiber, rfl⟩) himNe
    have hsMem := pairShift_re_mem_Icc
      (hrows i hi).1 (hrows i hi).2
      (hrows j hjRows).1 (hrows j hjRows).2
    simpa [ord, A] using
      norm_p53PrincipalDivisorResidue_le_offDiagonal q hr hr'
        hscale hMN hsMem.1 (hsMem.2.trans heps)
        (by simpa [ord] using himSep)
  calc
    _ ≤ ∑ j ∈ fiber.filter (fun j => j ≠ i),
        48 * Real.exp (-|ord j - ord i|) * A := Finset.sum_le_sum hpoint
    _ ≤ ∑ j ∈ fiber, 48 * Real.exp (-|ord j - ord i|) * A := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro j hjFiber hjNot
      positivity
    _ = (48 * A) * ∑ u ∈ fiber.image ord,
        Real.exp (-|u - ord i|) := by
      rw [Finset.mul_sum, Finset.sum_image hinj]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ ≤ (48 * A) * (Real.exp 1 * integerExponentialMass) := by
      gcongr
      exact sum_exp_neg_abs_sub_le (fiber.image ord) (ord i)
        (by simpa [fiber, ord] using hsep)
    _ = _ := by ring

end

end MAPJutilaP53PrincipalDivisorResidueBound

#print axioms MAPJutilaP53PrincipalDivisorResidueBound.norm_twisted_kernel_term_le_kernel
#print axioms MAPJutilaP53PrincipalDivisorResidueBound.norm_p53PrincipalDivisorResidue_le_offDiagonal
#print axioms MAPJutilaP53PrincipalDivisorResidueBound.norm_p53PrincipalDivisorResidue_le_primeProducts
#print axioms MAPJutilaP53PrincipalDivisorResidueBound.sum_p53PrincipalDivisorResidue_offDiagonal_le
