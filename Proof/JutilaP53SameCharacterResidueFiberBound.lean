import JutilaOneSeparatedExponentialPacking
import JutilaP53SameCharacterResidueAggregation

/-!
# Same-character p.53 residue fiber bound

This combines the exact residue envelope with one-dimensional packing.  It
is the source's linear, rather than quadratic, off-diagonal residue budget.
-/

namespace MAPJutilaP53SameCharacterResidueFiberBound

open scoped BigOperators
open Complex
open CGLProofDAG
open MAPJutilaP53AggregateCorrelationLeaf
open MAPJutilaP53KernelSourceForm
open MAPJutilaP53TwoScaleContour
open MAPJutilaP53PrincipalResidueEnvelope
open MAPJutilaOneSeparatedExponentialPacking
open MAPJutilaP53SameCharacterResidueAggregation

noncomputable section

local instance residueCharacterDecidableEq {q : ℕ} :
    DecidableEq (DirichletCharacter ℂ q) :=
  MAPJutilaP53SameCharacterResidueAggregation.instDecidableEqDirichletCharacterComplex_jutilaP53SameCharacterResidueAggregation

theorem sum_p53PrincipalResidue_offDiagonal_le
    {q : ℕ} [NeZero q] (rows : Finset (JutilaP53Row q))
    (chi : DirichletCharacter ℂ q) (i : JutilaP53Row q)
    {alpha epsilon U V : ℝ}
    (hU : 1 ≤ U) (hV : 1 ≤ V) (heps : 2 * epsilon ≤ 1 / 2)
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
      ‖p53PrincipalResidue q (jutilaP53PairShift alpha i j) U V‖ ≤
      48 * Real.exp 1 * integerExponentialMass := by
  let fiber := rows.filter (fun row => row.character = chi)
  let ord : JutilaP53Row q → ℝ := fun row => row.zero.im
  have hiFiber : i ∈ fiber := by simp [fiber, hi, hichar]
  have hinj : Set.InjOn ord (↑fiber : Set (JutilaP53Row q)) := by
    exact Finset.card_image_iff.mp (by simpa [fiber, ord] using hcard)
  have hpoint : ∀ j ∈ fiber.filter (fun j => j ≠ i),
      ‖p53PrincipalResidue q (jutilaP53PairShift alpha i j) U V‖ ≤
        48 * Real.exp (-|ord j - ord i|) := by
    intro j hj
    have hjFiber := (Finset.mem_filter.mp hj).1
    have hji := (Finset.mem_filter.mp hj).2
    have hjRows := (Finset.mem_filter.mp hjFiber).1
    have himNe : ord j ≠ ord i := by
      intro heq
      exact hji (hinj (by simpa using hjFiber) (by simpa using hiFiber) heq)
    have himSep : 1 ≤ |ord j - ord i| := by
      exact hsep (ord j) (Finset.mem_image.mpr ⟨j, hjFiber, rfl⟩)
        (ord i) (Finset.mem_image.mpr ⟨i, hiFiber, rfl⟩) himNe
    have hsMem := pairShift_re_mem_Icc
      (hrows i hi).1 (hrows i hi).2
      (hrows j hjRows).1 (hrows j hjRows).2
    have hpure := norm_p53PrincipalResidue_le_pureExp q hU hV
      hsMem.1 (hsMem.2.trans heps) (by simpa [ord] using himSep)
    simpa [ord] using hpure
  calc
    _ ≤ ∑ j ∈ fiber.filter (fun j => j ≠ i),
        48 * Real.exp (-|ord j - ord i|) := Finset.sum_le_sum hpoint
    _ ≤ ∑ j ∈ fiber, 48 * Real.exp (-|ord j - ord i|) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro j hjFiber hjNot
      positivity
    _ = 48 * ∑ u ∈ fiber.image ord, Real.exp (-|u - ord i|) := by
      rw [Finset.mul_sum, Finset.sum_image hinj]
    _ ≤ 48 * (Real.exp 1 * integerExponentialMass) := by
      gcongr
      exact sum_exp_neg_abs_sub_le (fiber.image ord) (ord i)
        (by simpa [fiber, ord] using hsep)
    _ = _ := by ring

/-- Full principal-residue aggregation: the diagonal is paid once per row,
and every same-character off-diagonal fiber has a universal budget. -/
theorem norm_p53PrincipalPairSum_residue_le_card_mul
    {q : ℕ} [NeZero q] (rows : Finset (JutilaP53Row q))
    {alpha epsilon U V D : ℝ}
    (hU : 1 ≤ U) (hV : 1 ≤ V) (heps : 2 * epsilon ≤ 1 / 2)
    (hrows : ∀ row ∈ rows,
      alpha ≤ row.zero.re ∧ row.zero.re ≤ alpha + epsilon)
    (hfiberSep : ∀ chi : DirichletCharacter ℂ q,
      OneSeparated ((rows.filter (fun row => row.character = chi)).image
        (fun row => row.zero.im)))
    (hfiberCard : ∀ chi : DirichletCharacter ℂ q,
      ((rows.filter (fun row => row.character = chi)).image
        (fun row => row.zero.im)).card =
      (rows.filter (fun row => row.character = chi)).card)
    (hdiag : ∀ i ∈ rows,
      ‖p53PrincipalResidue q (jutilaP53PairShift alpha i i) U V‖ ≤ D) :
    ‖p53PrincipalPairSum rows (fun i j =>
        p53PrincipalResidue q (jutilaP53PairShift alpha i j) U V)‖ ≤
      (rows.card : ℝ) *
        (D + 48 * Real.exp 1 * integerExponentialMass) := by
  apply norm_p53PrincipalPairSum_le_card_mul
  intro i hi
  let fiber := rows.filter (fun row => row.character = i.character)
  let C : JutilaP53Row q → ℂ := fun j =>
    p53PrincipalResidue q (jutilaP53PairShift alpha i j) U V
  have hiFiber : i ∈ fiber := by simp [fiber, hi]
  have hsumEq :
      (∑ j ∈ rows, if i.character = j.character then
        p53PrincipalResidue q (jutilaP53PairShift alpha i j) U V else 0) =
        ∑ j ∈ fiber, C j := by
    rw [← Finset.sum_filter]
    apply Finset.sum_congr
    · ext j
      simp [fiber, eq_comm]
    · intro j hj
      rfl
  have hsplit := Finset.sum_erase_add fiber C hiFiber
  have hoffNorm : ‖∑ j ∈ fiber.erase i, C j‖ ≤
      48 * Real.exp 1 * integerExponentialMass := by
    calc
      _ ≤ ∑ j ∈ fiber.erase i, ‖C j‖ := norm_sum_le _ _
      _ ≤ 48 * Real.exp 1 * integerExponentialMass := by
        have hbound := sum_p53PrincipalResidue_offDiagonal_le
          rows i.character i hU hV heps hrows hi rfl
          (hfiberSep i.character) (hfiberCard i.character)
        have herase : fiber.erase i = fiber.filter (fun j => j ≠ i) := by
          ext j
          simp [and_comm]
        rw [herase]
        simpa [fiber, C] using hbound
  calc
    ‖∑ j ∈ rows, if i.character = j.character then
        p53PrincipalResidue q (jutilaP53PairShift alpha i j) U V else 0‖ =
        ‖∑ j ∈ fiber, C j‖ := congrArg norm hsumEq
    _ = ‖C i + ∑ j ∈ fiber.erase i, C j‖ := by
      congr 1
      rw [add_comm]
      exact hsplit.symm
    _ ≤ ‖C i‖ + ‖∑ j ∈ fiber.erase i, C j‖ := norm_add_le _ _
    _ ≤ D + 48 * Real.exp 1 * integerExponentialMass :=
      add_le_add (hdiag i hi) hoffNorm

end

end MAPJutilaP53SameCharacterResidueFiberBound

#print axioms MAPJutilaP53SameCharacterResidueFiberBound.sum_p53PrincipalResidue_offDiagonal_le
#print axioms MAPJutilaP53SameCharacterResidueFiberBound.norm_p53PrincipalPairSum_residue_le_card_mul
