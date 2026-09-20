import MRTCorollary25Interface
import FarAnnulusSourceToModel
import Mathlib.NumberTheory.DirichletCharacter.Bounds

/-!
# Source-faithful MAP instantiation of MRT Corollary 2.5

MRT Corollary 2.5 is a pointwise truncation-removal theorem.  It applies to
each character-twisted, untruncated convolution separately; it does not create
the Heath--Brown branches, factor a convolution, choose dyadic blocks, pad the
character family, or prove the later stationary-phase estimate.

This file formalizes the largest common part of those operations which is
independent of the unpublished MAP reduction:

* all seven Type-`d` branches and the Type-II branch are enumerated;
* the exact Corollary 2.5 premise is instantiated simultaneously on every
  branch and every character phase, with one constant depending only on `C`;
* arbitrary finite character families are embedded into `Fin q` by literal
  zero padding, with exact preservation of sums whose summand vanishes at zero;
* the remaining source-to-model statement is isolated as a local branchwise
  inequality from the post-Corollary source mass to padded dyadic literal
  Type-`d` cells; and
* that strictly local premise is proved sufficient for the already-certified
  mixed-mean majorant on every block and every branch.

No far-annulus estimate, Heath--Brown identity, character-cardinality theorem,
or analytic bound is declared here.
-/

namespace MAPMRTCorollary25Instantiation

open scoped BigOperators
open MAPMRTCorollary25
open MAPFarAnnulusSourceToModel
open MAPFarAnnulusMRT

noncomputable section

/-! ## Exact branch inventory -/

/-- Precisely the convolution branches on which the MAP proof invokes MRT
Corollary 2.5.  The small-remainder branch and the `q₀ > 1` bad-Euler branch are
handled directly in MRT and do not use cutoff removal. -/
inductive CutoffBranch where
  | typeD1
  | typeD2
  | typeD3
  | typeD4
  | typeD5
  | typeD6
  | typeD7
  | typeII
  deriving DecidableEq, Fintype, Repr

/-- All source branches, including the two branches which are not inputs to
Corollary 2.5. -/
inductive FarSourceBranch where
  | cutoff (branch : CutoffBranch)
  | smallRemainder
  | badEulerFactor
  deriving DecidableEq, Fintype, Repr

@[simp] def usesCorollary25 : FarSourceBranch → Prop
  | .cutoff _ => True
  | .smallRemainder => False
  | .badEulerFactor => False

/-! ## Character twists and the exact Corollary 2.5 application -/

/-- Absorb a Dirichlet-character phase into the arbitrary complex coefficient
allowed by Corollary 2.5. -/
def characterTwist (phase f : ℕ → ℂ) (n : ℕ) : ℂ := phase n * f n

theorem supportedNear_characterTwist
    {X C : ℝ} {phase f : ℕ → ℂ}
    (hf : SupportedNear X C f) : SupportedNear X C (characterTwist phase f) := by
  intro n hn
  rw [characterTwist, hf n hn, mul_zero]

theorem norm_characterTwist_le
    {phase f : ℕ → ℂ} {B : ℝ}
    (hphase : ∀ n, ‖phase n‖ ≤ 1)
    (hf : ∀ n, ‖f n‖ ≤ B) :
    ∀ n, ‖characterTwist phase f n‖ ≤ B := by
  intro n
  rw [characterTwist, norm_mul]
  calc
    ‖phase n‖ * ‖f n‖ ≤ 1 * B :=
      mul_le_mul (hphase n) (hf n) (norm_nonneg _) zero_le_one
    _ = B := one_mul B

/-- Restricting a twisted coefficient is literally the same as twisting the
restricted coefficient. -/
theorem intervalCutoff_characterTwist
    (X1 X2 : ℝ) (phase f : ℕ → ℂ) :
    intervalCutoff X1 X2 (characterTwist phase f) =
      characterTwist phase (intervalCutoff X1 X2 f) := by
  funext n
  simp only [intervalCutoff, characterTwist]
  split_ifs <;> ring

/-- The exact published theorem instantiated with one character phase.  The
untruncated function is `f`; applying the theorem to the already truncated
function would leave the same sharp cutoff on the right and would not license
the later factorization. -/
theorem cutoffRemoval_characterTwist_of_MRTCorollary25
    (hMRT : MRTCorollary25)
    {C : ℝ} (hC : 1 < C) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (X T X1 X2 t B : ℝ) (phase f : ℕ → ℂ),
        1 ≤ X → 1 ≤ T → 0 ≤ B →
        SupportedNear X C f →
        (∀ n, ‖phase n‖ ≤ 1) →
        (∀ n, ‖f n‖ ≤ B) →
        ‖halfLineDirichletPolynomial X C
            (intervalCutoff X1 X2 (characterTwist phase f)) t‖ ≤
          K * ((∫ u in (-T)..T,
              ‖halfLineDirichletPolynomial X C
                (characterTwist phase f) (t + u)‖ / (1 + |u|)) +
            B * Real.sqrt X * Real.log (2 + T) / T) := by
  obtain ⟨K, hK, hbound⟩ := hMRT C hC
  refine ⟨K, hK, ?_⟩
  intro X T X1 X2 t B phase f hX hT hB hs hphase hf
  exact hbound X T X1 X2 t B (characterTwist phase f)
    hX hT hB (supportedNear_characterTwist hs)
    (norm_characterTwist_le hphase hf)

/-- One Corollary 2.5 constant works simultaneously for every cutoff-bearing
MAP branch and every member of an arbitrary finite character family.  The
branch scale may vary (for example it may be `X/q₀`), but `C` is common. -/
theorem cutoffRemoval_all_MAP_convolutionBranches
    (hMRT : MRTCorollary25)
    {Chi : Type*} [Fintype Chi]
    {C : ℝ} (hC : 1 < C)
    (scale height X1 X2 bound : CutoffBranch → ℝ)
    (source : CutoffBranch → ℕ → ℂ)
    (phase : Chi → ℕ → ℂ)
    (hscale : ∀ branch, 1 ≤ scale branch)
    (hheight : ∀ branch, 1 ≤ height branch)
    (hbound0 : ∀ branch, 0 ≤ bound branch)
    (hsupport : ∀ branch, SupportedNear (scale branch) C (source branch))
    (hsource : ∀ branch n, ‖source branch n‖ ≤ bound branch)
    (hphase : ∀ chi n, ‖phase chi n‖ ≤ 1) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (branch : CutoffBranch) (chi : Chi) (t : ℝ),
        ‖halfLineDirichletPolynomial (scale branch) C
            (intervalCutoff (X1 branch) (X2 branch)
              (characterTwist (phase chi) (source branch))) t‖ ≤
          K * ((∫ u in (-(height branch))..(height branch),
              ‖halfLineDirichletPolynomial (scale branch) C
                (characterTwist (phase chi) (source branch)) (t + u)‖ /
                  (1 + |u|)) +
            bound branch * Real.sqrt (scale branch) *
              Real.log (2 + height branch) / height branch) := by
  obtain ⟨K, hK, hcut⟩ := hMRT C hC
  refine ⟨K, hK, ?_⟩
  intro branch chi t
  exact hcut (scale branch) (height branch) (X1 branch) (X2 branch)
    t (bound branch) (characterTwist (phase chi) (source branch))
    (hscale branch) (hheight branch) (hbound0 branch)
    (supportedNear_characterTwist (hsupport branch))
    (norm_characterTwist_le (hphase chi) (hsource branch))

/-- Specialization to the actual family of Dirichlet characters modulo one
fixed modulus.  This proves the character twist required by the source; it does
not identify this character type with `Fin q`, which is the separate padding
problem below. -/
theorem cutoffRemoval_all_MAP_convolutionBranches_dirichletCharacters
    (hMRT : MRTCorollary25)
    {modulus : ℕ} [NeZero modulus]
    {C : ℝ} (hC : 1 < C)
    (scale height X1 X2 bound : CutoffBranch → ℝ)
    (source : CutoffBranch → ℕ → ℂ)
    (hscale : ∀ branch, 1 ≤ scale branch)
    (hheight : ∀ branch, 1 ≤ height branch)
    (hbound0 : ∀ branch, 0 ≤ bound branch)
    (hsupport : ∀ branch, SupportedNear (scale branch) C (source branch))
    (hsource : ∀ branch n, ‖source branch n‖ ≤ bound branch) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (branch : CutoffBranch)
        (chi : DirichletCharacter ℂ modulus) (t : ℝ),
        ‖halfLineDirichletPolynomial (scale branch) C
            (intervalCutoff (X1 branch) (X2 branch)
              (characterTwist (fun n ↦ chi n) (source branch))) t‖ ≤
          K * ((∫ u in (-(height branch))..(height branch),
              ‖halfLineDirichletPolynomial (scale branch) C
                (characterTwist (fun n ↦ chi n) (source branch)) (t + u)‖ /
                  (1 + |u|)) +
            bound branch * Real.sqrt (scale branch) *
              Real.log (2 + height branch) / height branch) := by
  obtain ⟨K, hK, hcut⟩ := hMRT C hC
  refine ⟨K, hK, ?_⟩
  intro branch chi t
  exact hcut (scale branch) (height branch) (X1 branch) (X2 branch)
    t (bound branch) (characterTwist (fun n ↦ chi n) (source branch))
    (hscale branch) (hheight branch) (hbound0 branch)
    (supportedNear_characterTwist (hsupport branch))
    (norm_characterTwist_le (fun n ↦ chi.norm_le_one n) (hsource branch))

/-! ## Exact zero padding of a finite character family -/

/-- Zero-pad a finite family along a supplied embedding into `Fin q`.  The
embedding, rather than a cardinality assertion hidden in the definition, is
the exact datum needed to pass from actual characters to the MAP model. -/
def zeroPad {ι : Type*} [Fintype ι] [DecidableEq ι]
    {q : ℕ} (e : ι ↪ Fin q) (f : ι → ℂ) (j : Fin q) : ℂ :=
  ∑ i : ι, if e i = j then f i else 0

@[simp] theorem zeroPad_apply_embedding
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {q : ℕ} (e : ι ↪ Fin q) (f : ι → ℂ) (i : ι) :
    zeroPad e f (e i) = f i := by
  classical
  simp only [zeroPad]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    simp [e.injective.ne hji]
  · simp

@[simp] theorem zeroPad_eq_zero_of_not_mem
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {q : ℕ} (e : ι ↪ Fin q) (f : ι → ℂ) (j : Fin q)
    (hj : j ∉ Finset.univ.map e) : zeroPad e f j = 0 := by
  classical
  unfold zeroPad
  apply Finset.sum_eq_zero
  intro i hi
  simp only [ite_eq_right_iff]
  intro hij
  subst j
  exact (hj (Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩)).elim

/-- Any transformed character sum is unchanged by zero padding, provided the
transformed zero coefficient contributes zero. -/
theorem sum_transform_zeroPad
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {q : ℕ} (e : ι ↪ Fin q) (f : ι → ℂ)
    (Phi : ℂ → ℝ) (hzero : Phi 0 = 0) :
    (∑ j : Fin q, Phi (zeroPad e f j)) = ∑ i : ι, Phi (f i) := by
  classical
  rw [← Finset.sum_subset (s₁ := Finset.univ.map e) (s₂ := Finset.univ)
    (by intro x hx; simp) (by
      intro j hjuniv hjnot
      rw [zeroPad_eq_zero_of_not_mem e f j hjnot, hzero])]
  rw [Finset.sum_map]
  simp

/-- Function-valued zero padding used for coefficient families. -/
def zeroPadFamily
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {q : ℕ} (e : ι ↪ Fin q) (f : ι → ℕ → ℂ) : Fin q → ℕ → ℂ :=
  fun j n ↦ zeroPad e (fun i ↦ f i n) j

@[simp] theorem zeroPadFamily_apply_embedding
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {q : ℕ} (e : ι ↪ Fin q) (f : ι → ℕ → ℂ) (i : ι) (n : ℕ) :
    zeroPadFamily e f (e i) n = f i n := by
  simp [zeroPadFamily]

theorem zeroPadFamily_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {q : ℕ} (e : ι ↪ Fin q) (f : ι → ℕ → ℂ) (B : ℕ → ℝ)
    (hB : ∀ n, 0 ≤ B n)
    (hf : ∀ i n, ‖f i n‖ ≤ B n) :
    ∀ j n, ‖zeroPadFamily e f j n‖ ≤ B n := by
  classical
  intro j n
  by_cases hj : j ∈ Finset.univ.map e
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hj
    simpa using hf i n
  · rw [zeroPadFamily, zeroPad_eq_zero_of_not_mem e (fun i ↦ f i n) j hj,
      norm_zero]
    exact hB n

/-! ## The first remaining source-to-model proposition -/

/-- The local post-Corollary source statement which is still required from the
actual `m = 8` decomposition.  It says only that each cutoff-bearing branch is
bounded by its accumulated cutoff error plus its explicitly padded, dyadic
literal Type-`d` cells.  This is strictly earlier and weaker than a far-annulus
bound or `CanonicalNearFarEstimates`.

The block count, block lengths, coefficients, character padding, and integration
ranges remain visible data. -/
def SourceToPaddedDyadicCells
    (sourceMass error : CutoffBranch → ℝ)
    (blockCount q shortLength : CutoffBranch → ℕ)
    (longLength : (branch : CutoffBranch) → Fin (blockCount branch) → ℕ)
    (beta : (branch : CutoffBranch) → Fin (q branch) → ℕ → ℂ)
    (g : (branch : CutoffBranch) → Fin (blockCount branch) →
      Fin (q branch) → ℕ → ℂ)
    (a b U : CutoffBranch → ℝ) : Prop :=
  ∀ branch,
    sourceMass branch ≤ error branch +
      ∑ i : Fin (blockCount branch),
        literalFactoredTypeDCell (q branch) (shortLength branch)
          (longLength branch i) (beta branch) (g branch i)
          (a branch) (b branch) (U branch)

/-- The already-certified Cauchy--Fubini and mixed-mean bridge consumes exactly
`SourceToPaddedDyadicCells`.  Thus the unresolved theorem need not assume any
far-annulus estimate: this local branchwise reduction is sufficient. -/
theorem sourceToPaddedDyadicCells_implies_mixedMassMajorant
    {sourceMass error : CutoffBranch → ℝ}
    {blockCount q shortLength : CutoffBranch → ℕ}
    {longLength : (branch : CutoffBranch) → Fin (blockCount branch) → ℕ}
    {beta : (branch : CutoffBranch) → Fin (q branch) → ℕ → ℂ}
    {g : (branch : CutoffBranch) → Fin (blockCount branch) →
      Fin (q branch) → ℕ → ℂ}
    {a b U : CutoffBranch → ℝ}
    (hsource : SourceToPaddedDyadicCells sourceMass error blockCount q
      shortLength longLength beta g a b U)
    (hab : ∀ branch, a branch ≤ b branch)
    (hU : ∀ branch, 0 ≤ U branch) :
    (∑ branch : CutoffBranch, sourceMass branch) ≤
      ∑ branch : CutoffBranch,
        (error branch +
          2 * blockwiseCharacterPairMixedMass
            (M := shortLength branch) (longLength branch) (beta branch)
              (g branch) ((a branch + b branch) / 2)
              ((b branch - a branch) + 2 * U branch) (U branch)) := by
  apply Finset.sum_le_sum
  intro branch hbranch
  calc
    sourceMass branch ≤ error branch +
        ∑ i : Fin (blockCount branch),
          literalFactoredTypeDCell (q branch) (shortLength branch)
            (longLength branch i) (beta branch) (g branch i)
            (a branch) (b branch) (U branch) := hsource branch
    _ ≤ error branch +
        ∑ i : Fin (blockCount branch),
          2 * characterPairMixedMass (q branch) (shortLength branch)
            (longLength branch i) (pairShortFamily (beta branch))
            (pairLongFamily (g branch i))
            ((a branch + b branch) / 2)
            ((b branch - a branch) + 2 * U branch) (U branch) := by
      exact add_le_add le_rfl
        (Finset.sum_le_sum fun i hi ↦
          literalFactoredTypeDCell_le_two_characterPairMixedMass
            (q branch) (shortLength branch) (longLength branch i)
            (beta branch) (g branch i) (hab branch) (hU branch))
    _ = error branch +
        2 * blockwiseCharacterPairMixedMass
          (M := shortLength branch) (longLength branch) (beta branch)
            (g branch) ((a branch + b branch) / 2)
            ((b branch - a branch) + 2 * U branch) (U branch) := by
      unfold blockwiseCharacterPairMixedMass
      rw [Finset.mul_sum]

end
end MAPMRTCorollary25Instantiation

#print axioms MAPMRTCorollary25Instantiation.cutoffRemoval_characterTwist_of_MRTCorollary25
#print axioms MAPMRTCorollary25Instantiation.cutoffRemoval_all_MAP_convolutionBranches
#print axioms MAPMRTCorollary25Instantiation.cutoffRemoval_all_MAP_convolutionBranches_dirichletCharacters
#print axioms MAPMRTCorollary25Instantiation.sum_transform_zeroPad
#print axioms MAPMRTCorollary25Instantiation.sourceToPaddedDyadicCells_implies_mixedMassMajorant
