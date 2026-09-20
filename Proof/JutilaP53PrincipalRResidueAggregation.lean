import JutilaP53PrincipalDivisorResidueBound

/-!
# Principal residue after the finite normalized pseudocharacter sums
-/

namespace MAPJutilaP53PrincipalRResidueAggregation

open scoped BigOperators
open Complex
open CGLProofDAG
open MAPJutilaP53AggregateCorrelationLeaf
open MAPJutilaP53KernelSourceForm
open MAPJutilaLemma3AbsoluteMass
open MAPJutilaOneSeparatedExponentialPacking
open MAPJutilaP53PrincipalDivisorResidueBound

noncomputable section

def p53NormalizedEulerMass (S : Finset ℕ) : ℝ :=
  ∑ r ∈ S, ∑ r' ∈ S,
    (((r * r' : ℕ) : ℝ)⁻¹) *
      (lemmaThreeAbsoluteMass r.primeFactors r'.primeFactors : ℝ)

def p53PrincipalRResidue (q : ℕ) [NeZero q]
    (S : Finset ℕ) (s : ℂ) (M N : ℝ) : ℂ :=
  ∑ r ∈ S, ∑ r' ∈ S,
    (((r * r' : ℕ) : ℂ)⁻¹) *
      p53PrincipalDivisorResidue q s M N r r'

theorem p53NormalizedEulerMass_nonneg (S : Finset ℕ) :
    0 ≤ p53NormalizedEulerMass S := by
  unfold p53NormalizedEulerMass
  positivity

theorem norm_p53PrincipalRResidue_le_offDiagonal
    (q : ℕ) [NeZero q] {S : Finset ℕ} {s : ℂ} {M N : ℝ}
    (hSq : ∀ r ∈ S, Squarefree r)
    (hscale : ∀ r ∈ S, ∀ r' ∈ S,
      ((r.lcm r' : ℕ) : ℝ) ≤ M)
    (hMN : M ≤ N) (hsLo : 0 ≤ s.re) (hsHi : s.re ≤ 1 / 2)
    (hsIm : 1 ≤ |s.im|) :
    ‖p53PrincipalRResidue q S s M N‖ ≤
      48 * Real.exp (-|s.im|) * p53NormalizedEulerMass S := by
  unfold p53PrincipalRResidue
  calc
    _ ≤ ∑ r ∈ S, ∑ r' ∈ S,
        ‖(((r * r' : ℕ) : ℂ)⁻¹) *
          p53PrincipalDivisorResidue q s M N r r'‖ := by
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun r hr => norm_sum_le _ _)
    _ ≤ ∑ r ∈ S, ∑ r' ∈ S,
        (((r * r' : ℕ) : ℝ)⁻¹) *
          (48 * Real.exp (-|s.im|) *
            (lemmaThreeAbsoluteMass r.primeFactors r'.primeFactors : ℝ)) := by
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro r' hr'
      rw [norm_mul, norm_inv, Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_left
        (norm_p53PrincipalDivisorResidue_le_offDiagonal q
          (hSq r hr) (hSq r' hr') (hscale r hr r' hr') hMN
          hsLo hsHi hsIm) (by positivity)
    _ = 48 * Real.exp (-|s.im|) * p53NormalizedEulerMass S := by
      unfold p53NormalizedEulerMass
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r' hr'
      ring

/-- The complete normalized `r,r'` principal residue has a uniform linear
same-character off-diagonal fiber budget. -/
theorem sum_p53PrincipalRResidue_offDiagonal_le
    (q : ℕ) [NeZero q] (rows : Finset (JutilaP53Row q))
    (chi : DirichletCharacter ℂ q) (i : JutilaP53Row q)
    {S : Finset ℕ} {alpha epsilon M N : ℝ}
    (hSq : ∀ r ∈ S, Squarefree r)
    (hscale : ∀ r ∈ S, ∀ r' ∈ S,
      ((r.lcm r' : ℕ) : ℝ) ≤ M)
    (hMN : M ≤ N) (heps : 2 * epsilon ≤ 1 / 2)
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
      ‖p53PrincipalRResidue q S
        (jutilaP53PairShift alpha i j) M N‖ ≤
      48 * Real.exp 1 * integerExponentialMass *
        p53NormalizedEulerMass S := by
  let fiber := rows.filter (fun row => row.character = chi)
  let ord : JutilaP53Row q → ℝ := fun row => row.zero.im
  let A := p53NormalizedEulerMass S
  have hiFiber : i ∈ fiber := by simp [fiber, hi, hichar]
  have hinj : Set.InjOn ord (↑fiber : Set (JutilaP53Row q)) :=
    Finset.card_image_iff.mp (by simpa [fiber, ord] using hcard)
  have hpoint : ∀ j ∈ fiber.filter (fun j => j ≠ i),
      ‖p53PrincipalRResidue q S
          (jutilaP53PairShift alpha i j) M N‖ ≤
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
    simpa [ord, A] using norm_p53PrincipalRResidue_le_offDiagonal q
      hSq hscale hMN hsMem.1 (hsMem.2.trans heps)
      (by simpa [ord] using himSep)
  calc
    _ ≤ ∑ j ∈ fiber.filter (fun j => j ≠ i),
        48 * Real.exp (-|ord j - ord i|) * A := Finset.sum_le_sum hpoint
    _ ≤ ∑ j ∈ fiber, 48 * Real.exp (-|ord j - ord i|) * A := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro j hj hjnot
      exact mul_nonneg (by positivity) (p53NormalizedEulerMass_nonneg S)
    _ = (48 * A) * ∑ u ∈ fiber.image ord, Real.exp (-|u - ord i|) := by
      rw [Finset.mul_sum, Finset.sum_image hinj]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ ≤ (48 * A) * (Real.exp 1 * integerExponentialMass) := by
      apply mul_le_mul_of_nonneg_left
        (sum_exp_neg_abs_sub_le (fiber.image ord) (ord i)
          (by simpa [fiber, ord] using hsep))
      exact mul_nonneg (by norm_num) (p53NormalizedEulerMass_nonneg S)
    _ = _ := by ring

end

end MAPJutilaP53PrincipalRResidueAggregation

#print axioms MAPJutilaP53PrincipalRResidueAggregation.norm_p53PrincipalRResidue_le_offDiagonal
#print axioms MAPJutilaP53PrincipalRResidueAggregation.sum_p53PrincipalRResidue_offDiagonal_le
