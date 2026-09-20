import Mathlib

/-!
# Chen--Gupta--Li v2 proof-DAG certificate

This file deliberately contains no theorem asserting the zero-density estimate
of Chen--Gupta--Li.  It certifies finite deductions at the first problematic
transition in the printed proof: passage from a zero-dependent factor
`n ^ (-beta)` to a polynomial common to all zeros.

The source line cannot be justified by simply deleting the weights.  The
correct elementary repair is discrete Abel summation: a large weighted sum
forces a large prefix of the common polynomial when the weights are
nonnegative and decreasing.
-/

namespace CGLProofDAG

open scoped BigOperators
open ArithmeticFunction
open scoped ArithmeticFunction.zeta

/-! ## A source-independent discrete Abel certificate -/

/-- Exact finite summation by parts.  This is the algebraic identity needed to
remove a zero-dependent decreasing weight without pretending that the full
unweighted sum has the same size. -/
theorem sum_range_mul_eq_last_mul_prefix_add_variation
    (a : ℕ → ℂ) (w : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), (w k : ℂ) * a k) =
      (w n : ℂ) * (∑ k ∈ Finset.range (n + 1), a k) +
        ∑ k ∈ Finset.range n,
          ((w k - w (k + 1) : ℝ) : ℂ) *
            (∑ j ∈ Finset.range (k + 1), a j) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hweighted := Finset.sum_range_succ
        (fun k => (w k : ℂ) * a k) (n + 1)
      have hprefix := Finset.sum_range_succ a (n + 1)
      have hvariation := Finset.sum_range_succ
        (fun k => ((w k - w (k + 1) : ℝ) : ℂ) *
          (∑ j ∈ Finset.range (k + 1), a j)) n
      rw [hweighted, hprefix, hvariation, ih]
      push_cast
      ring

/-- A decreasing nonnegative weight costs only its first value when every
prefix of the common polynomial is bounded. -/
theorem norm_sum_range_mul_le_first_mul_prefix_bound
    (a : ℕ → ℂ) (w : ℕ → ℝ) (n : ℕ) (E : ℝ)
    (hw0 : 0 ≤ w n)
    (hmono : ∀ k ∈ Finset.range n, w (k + 1) ≤ w k)
    (hprefix : ∀ k ∈ Finset.range (n + 1),
      ‖∑ j ∈ Finset.range (k + 1), a j‖ ≤ E) :
    ‖∑ k ∈ Finset.range (n + 1), (w k : ℂ) * a k‖ ≤ w 0 * E := by
  rw [sum_range_mul_eq_last_mul_prefix_add_variation]
  calc
    ‖(w n : ℂ) * (∑ k ∈ Finset.range (n + 1), a k) +
        ∑ k ∈ Finset.range n,
          ((w k - w (k + 1) : ℝ) : ℂ) *
            (∑ j ∈ Finset.range (k + 1), a j)‖
        ≤ ‖(w n : ℂ) * (∑ k ∈ Finset.range (n + 1), a k)‖ +
          ‖∑ k ∈ Finset.range n,
            ((w k - w (k + 1) : ℝ) : ℂ) *
              (∑ j ∈ Finset.range (k + 1), a j)‖ := norm_add_le _ _
    _ ≤ w n * E + ∑ k ∈ Finset.range n, (w k - w (k + 1)) * E := by
      apply add_le_add
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hw0]
        exact mul_le_mul_of_nonneg_left
          (hprefix n (Finset.mem_range_succ_iff.mpr le_rfl)) hw0
      · calc
          ‖∑ k ∈ Finset.range n,
              ((w k - w (k + 1) : ℝ) : ℂ) *
                (∑ j ∈ Finset.range (k + 1), a j)‖
              ≤ ∑ k ∈ Finset.range n,
                ‖((w k - w (k + 1) : ℝ) : ℂ) *
                  (∑ j ∈ Finset.range (k + 1), a j)‖ := norm_sum_le _ _
          _ ≤ ∑ k ∈ Finset.range n, (w k - w (k + 1)) * E := by
            apply Finset.sum_le_sum
            intro k hk
            have hdiff : 0 ≤ w k - w (k + 1) := sub_nonneg.mpr (hmono k hk)
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg hdiff]
            exact mul_le_mul_of_nonneg_left
              (hprefix k (Finset.mem_range.mpr (Nat.lt_succ_of_lt
                (Finset.mem_range.mp hk)))) hdiff
    _ = w 0 * E := by
      rw [← Finset.sum_mul, Finset.sum_range_sub']
      ring

/-- Detector form: if the weighted polynomial is at least `V`, then for every
threshold `E` with `w 0 * E < V`, some prefix of the common polynomial is
larger than `E`.  The prefix endpoint may depend on the zero, but the
coefficient sequence does not. -/
theorem exists_large_common_prefix_of_large_weighted_sum
    (a : ℕ → ℂ) (w : ℕ → ℝ) (n : ℕ) (E V : ℝ)
    (hwn : 0 ≤ w n)
    (hmono : ∀ k ∈ Finset.range n, w (k + 1) ≤ w k)
    (hthreshold : w 0 * E < V)
    (hlarge : V ≤ ‖∑ k ∈ Finset.range (n + 1), (w k : ℂ) * a k‖) :
    ∃ k ∈ Finset.range (n + 1),
      E < ‖∑ j ∈ Finset.range (k + 1), a j‖ := by
  by_contra h
  have hall : ∀ k ∈ Finset.range (n + 1),
      ‖∑ j ∈ Finset.range (k + 1), a j‖ ≤ E := by
    intro k hk
    exact le_of_not_gt (fun hklarge => h ⟨k, hk, hklarge⟩)
  have hbound := norm_sum_range_mul_le_first_mul_prefix_bound
    a w n E hwn hmono hall
  exact (not_lt_of_ge (hlarge.trans hbound)) hthreshold

/-! ## A literal death test for the printed weight deletion -/

/-- Deleting a varying positive weight can annihilate the full sum.  Thus the
printed inference from a large `n^(-beta)`-weighted sum to the same full
unweighted sum is false without an Abel/Fourier transfer. -/
theorem dropping_a_varying_weight_is_not_value_preserving :
    ((1 : ℂ) + (-1 : ℂ) = 0) ∧
      ‖(1 : ℂ) * (1 : ℂ) + ((1 / 2 : ℝ) : ℂ) * (-1 : ℂ)‖ = 1 / 2 := by
  norm_num

/-! ## Exact powered-polynomial coefficient majorant

This is the coefficient-specific step suppressed in CGL lines 2220--2256.
Arithmetic-function multiplication is Dirichlet convolution, so its `k`-th
power is exactly the coefficient sequence obtained after collecting equal
products in the `k`-th power of a Dirichlet polynomial.
-/

/-- The ordered `k`-fold divisor function.  Its value at `m` is the number of
ordered factorizations of `m` into `k` positive factors. -/
def orderedDivisorCount (k : ℕ) : ArithmeticFunction ℕ :=
  (ζ : ArithmeticFunction ℕ) ^ k

/-- Every `k`-fold Dirichlet-convolution coefficient formed from a unit-bounded
sequence is bounded by the ordered divisor function.  This is the exact
coefficient majorant needed before normalizing a powered block for the
Guth--Maynard theorem. -/
theorem norm_convolution_power_apply_le_orderedDivisorCount
    (f : ArithmeticFunction ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (k n : ℕ) :
    ‖(f ^ k) n‖ ≤ orderedDivisorCount k n := by
  induction k generalizing n with
  | zero =>
      by_cases hn : n = 1 <;> simp [orderedDivisorCount, hn]
  | succ k ih =>
      rw [pow_succ, ArithmeticFunction.mul_apply, orderedDivisorCount,
        pow_succ, ArithmeticFunction.mul_apply]
      calc
        ‖∑ x ∈ n.divisorsAntidiagonal, (f ^ k) x.1 * f x.2‖ ≤
            ∑ x ∈ n.divisorsAntidiagonal,
              ‖(f ^ k) x.1 * f x.2‖ := norm_sum_le _ _
        _ ≤ ∑ x ∈ n.divisorsAntidiagonal,
            ((orderedDivisorCount k x.1 : ℕ) : ℝ) * 1 := by
          apply Finset.sum_le_sum
          intro x hx
          rw [norm_mul]
          exact mul_le_mul (ih x.1) (hf x.2) (norm_nonneg _) (by positivity)
        _ = ((∑ x ∈ n.divisorsAntidiagonal,
            orderedDivisorCount k x.1 * 1 : ℕ) : ℝ) := by
          norm_cast
        _ = ((∑ x ∈ n.divisorsAntidiagonal,
            ((ζ : ArithmeticFunction ℕ) ^ k) x.1 * ζ x.2 : ℕ) : ℝ) := by
          congr 1
          apply Finset.sum_congr rfl
          intro x hx
          have hmem := Nat.mem_divisorsAntidiagonal.mp hx
          have hn0 := hmem.2
          have hx20 : x.2 ≠ 0 := by
            intro h
            apply hn0
            have hprod := hmem.1
            simp [h] at hprod
            exact hprod.symm
          simp [orderedDivisorCount, ArithmeticFunction.zeta_apply, hx20]

/-- A coefficient sequence supported on the literal CGL dyadic interval
`(N,2N]`. -/
def dyadicCoefficient (N : ℕ) (a : ℕ → ℂ) : ArithmeticFunction ℂ where
  toFun n := if n ∈ Finset.Ioc N (2 * N) then a n else 0
  map_zero' := by simp [Finset.mem_Ioc]

theorem norm_dyadicCoefficient_le_one
    {N : ℕ} {a : ℕ → ℂ}
    (ha : ∀ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ≤ 1) (n : ℕ) :
    ‖dyadicCoefficient N a n‖ ≤ 1 := by
  change ‖if n ∈ Finset.Ioc N (2 * N) then a n else 0‖ ≤ 1
  split_ifs with hn
  · exact ha n hn
  · simp

/-- Source-facing specialization: every collected coefficient of the powered
dyadic polynomial is bounded by `d_k`. -/
theorem norm_dyadic_powered_coefficient_le
    {N : ℕ} {a : ℕ → ℂ}
    (ha : ∀ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ≤ 1) (k m : ℕ) :
    ‖(dyadicCoefficient N a ^ k) m‖ ≤ orderedDivisorCount k m :=
  norm_convolution_power_apply_le_orderedDivisorCount
    (dyadicCoefficient N a) (norm_dyadicCoefficient_le_one ha) k m

/-- Multiplication of an arithmetic coefficient by a Dirichlet character. -/
noncomputable def characterTwist {q : ℕ} (χ : DirichletCharacter ℂ q)
    (f : ArithmeticFunction ℂ) : ArithmeticFunction ℂ where
  toFun n := χ n * f n
  map_zero' := by simp

theorem characterTwist_mul {q : ℕ} (χ : DirichletCharacter ℂ q)
    (f g : ArithmeticFunction ℂ) :
    characterTwist χ (f * g) = characterTwist χ f * characterTwist χ g := by
  apply ArithmeticFunction.ext
  intro n
  have h := congrFun (DirichletCharacter.mul_convolution_distrib χ f g) n
  simpa [characterTwist, Pi.mul_apply, ArithmeticFunction.mul_apply,
    LSeries.convolution_def, mul_assoc, mul_comm, mul_left_comm] using h.symm

theorem characterTwist_one {q : ℕ} (χ : DirichletCharacter ℂ q) :
    characterTwist χ 1 = 1 := by
  apply ArithmeticFunction.ext
  intro n
  by_cases hn : n = 1
  · subst n
    simp [characterTwist]
  · simp [characterTwist, ArithmeticFunction.one_apply_ne hn]

/-- After collecting products, a bounded power still carries exactly one
character twist.  No extra character power occurs. -/
theorem characterTwist_pow {q : ℕ} (χ : DirichletCharacter ℂ q)
    (f : ArithmeticFunction ℂ) (k : ℕ) :
    characterTwist χ (f ^ k) = (characterTwist χ f) ^ k := by
  induction k with
  | zero => exact characterTwist_one χ
  | succ k ih =>
      rw [pow_succ, characterTwist_mul, ih, pow_succ]

theorem powered_dyadic_twist_coefficient
    {q N k m : ℕ} (χ : DirichletCharacter ℂ q) (a : ℕ → ℂ) :
    ((characterTwist χ (dyadicCoefficient N a)) ^ k) m =
      χ m * (dyadicCoefficient N a ^ k) m := by
  have h := congrArg (fun f : ArithmeticFunction ℂ => f m)
    (characterTwist_pow χ (dyadicCoefficient N a) k)
  exact h.symm

/-! ## Exact handoff to the refereed Guth--Maynard theorem -/

noncomputable def dirichletPolynomial (b : ℕ → ℂ) (N : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc N (2 * N),
    b n * Complex.exp (Complex.I * (t * Real.log n))

def OneSeparated (W : Finset ℝ) : Prop :=
  ∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t - u|

/-- Exact epsilon-form interface of Guth--Maynard, Annals of Mathematics 203
(2026), Theorem 1.1.  This proposition is data: it is not asserted here. -/
def GuthMaynardTheorem11 : Prop :=
  ∀ η : ℝ, 0 < η →
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (T V : ℝ) (N : ℕ) (b : ℕ → ℂ) (W : Finset ℝ),
        T₀ ≤ T → 1 ≤ N → 0 < V →
        (∀ n, ‖b n‖ ≤ 1) →
        OneSeparated W →
        (∀ t ∈ W, 0 ≤ t ∧ t ≤ T) →
        (∀ t ∈ W, V ≤ ‖dirichletPolynomial b N t‖) →
        (W.card : ℝ) ≤
          C * Real.rpow T η *
            ((N : ℝ) ^ 2 / V ^ 2 +
              Real.rpow N (18 / 5 : ℝ) / V ^ 4 +
              T * Real.rpow N (12 / 5 : ℝ) / V ^ 4)

/-- The selected dyadic block of the collected `k`-fold coefficient,
normalized by a positive uniform divisor bound. -/
noncomputable def normalizedPoweredBlock (baseN k blockN : ℕ) (a : ℕ → ℂ)
    (C : ℝ) (m : ℕ) : ℂ :=
  if m ∈ Finset.Ioc blockN (2 * blockN) then
    (dyadicCoefficient baseN a ^ k) m / (C : ℂ)
  else 0

theorem norm_normalizedPoweredBlock_le_one
    {baseN k blockN : ℕ} {a : ℕ → ℂ} {C : ℝ}
    (ha : ∀ n ∈ Finset.Ioc baseN (2 * baseN), ‖a n‖ ≤ 1)
    (hC : 0 < C)
    (hdiv : ∀ m ∈ Finset.Ioc blockN (2 * blockN),
      (orderedDivisorCount k m : ℝ) ≤ C) (m : ℕ) :
    ‖normalizedPoweredBlock baseN k blockN a C m‖ ≤ 1 := by
  unfold normalizedPoweredBlock
  split_ifs with hm
  · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hC]
    apply (div_le_iff₀ hC).2
    simpa using (norm_dyadic_powered_coefficient_le ha k m).trans (hdiv m hm)
  · simp

/-- Normalization scales the entire selected polynomial by exactly `1/C`.
This is the deterministic bridge required before applying Theorem 1.1. -/
theorem dirichletPolynomial_normalizedPoweredBlock
    (baseN k blockN : ℕ) (a : ℕ → ℂ) (C : ℝ) (t : ℝ) :
    dirichletPolynomial
        (normalizedPoweredBlock baseN k blockN a C) blockN t =
      dirichletPolynomial (fun m => (dyadicCoefficient baseN a ^ k) m)
        blockN t / (C : ℂ) := by
  unfold dirichletPolynomial
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro m hm
  rw [normalizedPoweredBlock, if_pos hm]
  field_simp

/-- Premise-free transfer from the exact powered coefficient majorant to the
literal published large-values inequality.  The only deep input is the exact
refereed theorem interface `GuthMaynardTheorem11`; the divisor majorant and
normalization are proved above.

The remaining manuscript work needed for (A.13) is to choose `k`, select one
common dyadic block, provide the standard uniform `d_k(m) ≤ T^eta` bound, and
combine this branch with the separate discrete mean-value theorem. -/
theorem guthMaynard_powered_block_transfer
    (hGM : GuthMaynardTheorem11) (η : ℝ) (hη : 0 < η) :
    ∃ K T₀ : ℝ, 0 < K ∧ 2 ≤ T₀ ∧
      ∀ (T V C : ℝ) (baseN k blockN : ℕ) (a : ℕ → ℂ) (W : Finset ℝ),
        T₀ ≤ T → 1 ≤ blockN → 0 < V → 0 < C →
        (∀ n ∈ Finset.Ioc baseN (2 * baseN), ‖a n‖ ≤ 1) →
        (∀ m ∈ Finset.Ioc blockN (2 * blockN),
          (orderedDivisorCount k m : ℝ) ≤ C) →
        OneSeparated W →
        (∀ t ∈ W, 0 ≤ t ∧ t ≤ T) →
        (∀ t ∈ W, V ≤
          ‖dirichletPolynomial
            (fun m => (dyadicCoefficient baseN a ^ k) m) blockN t‖) →
        (W.card : ℝ) ≤
          K * Real.rpow T η *
            ((blockN : ℝ) ^ 2 / (V / C) ^ 2 +
              Real.rpow blockN (18 / 5 : ℝ) / (V / C) ^ 4 +
              T * Real.rpow blockN (12 / 5 : ℝ) / (V / C) ^ 4) := by
  obtain ⟨K, T₀, hK, hT₀, hbound⟩ := hGM η hη
  refine ⟨K, T₀, hK, hT₀, ?_⟩
  intro T V C baseN k blockN a W hT hblock hV hC ha hdiv hsep hheight hlarge
  apply hbound T (V / C) blockN
    (normalizedPoweredBlock baseN k blockN a C) W hT hblock
    (div_pos hV hC)
    (norm_normalizedPoweredBlock_le_one ha hC hdiv) hsep hheight
  intro t ht
  rw [dirichletPolynomial_normalizedPoweredBlock baseN k blockN a C t,
    norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hC]
  exact (div_le_div_iff_of_pos_right hC).2 (hlarge t ht)

/-- Exact uninhabited interface for the first `30/13`-specific theorem still
missing from the local development: the fixed-character bounded-power lemma
behind Appendix (A.13).  A fixed Dirichlet-character twist is already allowed
inside the arbitrary coefficients `b`.

The small `T^eta` factors explicitly represent the uniform subpower losses
from Fourier truncation, the divisor majorant, block selection, and the two
published large-value branches. -/
@[deprecated "The same-eta threshold is not stable under powering; use CGLProofDAG.BudgetedFixedCharacterPoweredLargeValueBridge from BudgetedFixedCharacterPoweredLargeValueBridge." (since := "2026-08-29")]
def FixedCharacterPoweredLargeValueBridge : Prop :=
  ∀ κ η : ℝ, 0 < κ → 0 < η →
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (T σ : ℝ) (N : ℕ) (b : ℕ → ℂ) (W : Finset ℝ),
        T₀ ≤ T → 7 / 10 ≤ σ → σ ≤ 4 / 5 →
        Real.rpow T κ ≤ N →
        (N : ℝ) ≤ Real.rpow T (1 / 2) * (Real.log T) ^ 2 →
        (∀ n, ‖b n‖ ≤ 1) →
        OneSeparated W →
        (∀ t ∈ W, 0 ≤ t ∧ t ≤ T) →
        (∀ t ∈ W,
          Real.rpow N σ * Real.rpow T (-η) ≤
            ‖dirichletPolynomial b N t‖) →
        (W.card : ℝ) ≤
          C * Real.rpow T
            (15 * (1 - σ) / (3 + 5 * σ) + η)

/-! ## Executable proof-DAG metadata

The records below are data, not assumptions.  They make the certification
boundary machine-checkable while the detailed source citations and module map
live in the accompanying report.
-/

inductive CertificationStatus where
  | locallyProved
  | existingProjectProof
  | refereedSourceInput
  | unrefereedSourceClaim
  | missingFullProof
  deriving DecidableEq, Repr

structure ProofNode where
  id : String
  dependencies : List String
  status : CertificationStatus
  deriving DecidableEq, Repr

def proofDAG : List ProofNode :=
  [ { id := "mollifier-coefficient-identity"
      dependencies := []
      status := .existingProjectProof }
  , { id := "gamma-mellin-strip-holomorphy"
      dependencies := []
      status := .existingProjectProof }
  , { id := "primitive-L-fixed-strip-polynomial-growth"
      dependencies := ["Dirichlet-L-functional-equation", "Phragmen-Lindelof"]
      status := .existingProjectProof }
  , { id := "uniform-mellin-detector-contour-shift"
      dependencies :=
        ["mollifier-coefficient-identity", "gamma-mellin-strip-holomorphy",
          "primitive-L-fixed-strip-polynomial-growth"]
      status := .missingFullProof }
  , { id := "multiplicity-aware-local-zero-count"
      dependencies := ["primitive-L-fixed-strip-polynomial-growth", "Jensen"]
      status := .existingProjectProof }
  , { id := "class-II-fourth-moment-bound"
      dependencies :=
        ["uniform-mellin-detector-contour-shift",
          "multiplicity-aware-local-zero-count"]
      status := .refereedSourceInput }
  , { id := "common-polynomial-Fourier-transfer"
      dependencies := ["uniform-mellin-detector-contour-shift"]
      status := .existingProjectProof }
  , { id := "common-prefix-Abel-diagnostic"
      dependencies := []
      status := .locallyProved }
  , { id := "powered-convolution-coefficient-majorant"
      dependencies := []
      status := .locallyProved }
  , { id := "Guth-Maynard-Theorem-1.1"
      dependencies := []
      status := .refereedSourceInput }
  , { id := "discrete-Dirichlet-polynomial-mean-value"
      dependencies := []
      status := .refereedSourceInput }
  , { id := "budgeted-fixed-character-powered-large-value-bridge"
      dependencies :=
        ["common-polynomial-Fourier-transfer",
          "powered-convolution-coefficient-majorant",
          "Guth-Maynard-Theorem-1.1",
          "discrete-Dirichlet-polynomial-mean-value"]
      status := .missingFullProof }
  , { id := "CGL-character-large-values-theorem"
      dependencies := ["CGL-auxiliary-large-values-proposition"]
      status := .unrefereedSourceClaim }
  , { id := "CGL-auxiliary-large-values-proposition"
      dependencies :=
        ["character-subdivision", "trace-expansion", "S1-bound", "S2-bound",
          "S3-energy-bound"]
      status := .unrefereedSourceClaim }
  , { id := "CGL-v2-Theorem-1.2"
      dependencies :=
        ["class-II-fourth-moment-bound", "common-polynomial-Fourier-transfer",
          "CGL-character-large-values-theorem"]
      status := .unrefereedSourceClaim }
  ]

def firstMissingNode : Option ProofNode :=
  proofDAG.find? (fun n => n.status = .missingFullProof)

theorem first_missing_node_is_uniform_detector :
    firstMissingNode = some
      { id := "uniform-mellin-detector-contour-shift"
        dependencies :=
          ["mollifier-coefficient-identity", "gamma-mellin-strip-holomorphy",
            "primitive-L-fixed-strip-polynomial-growth"]
        status := .missingFullProof } := by
  decide

def firstThirtyThirteenMissingNode : Option ProofNode :=
  proofDAG.find? (fun n => n.id = "budgeted-fixed-character-powered-large-value-bridge")

theorem first_thirty_thirteen_specific_missing_node :
    firstThirtyThirteenMissingNode = some
      { id := "budgeted-fixed-character-powered-large-value-bridge"
        dependencies :=
          ["common-polynomial-Fourier-transfer",
            "powered-convolution-coefficient-majorant",
            "Guth-Maynard-Theorem-1.1",
            "discrete-Dirichlet-polynomial-mean-value"]
        status := .missingFullProof } := by
  decide

def cglTheoremNode : Option ProofNode :=
  proofDAG.find? (fun n => n.id = "CGL-v2-Theorem-1.2")

theorem cgl_theorem_is_not_marked_locally_proved :
    cglTheoremNode.map ProofNode.status =
      some CertificationStatus.unrefereedSourceClaim := by
  decide

/-! ## Exact arithmetic for the classical-reference bypass test -/

/-- Montgomery's coefficient `3 / (2 - sigma)` is at most `30/13` exactly
up to `sigma = 7/10` (in the range where the denominator is positive). -/
theorem montgomery_reaches_thirty_thirteenths_iff
    {σ : ℝ} (hσ : σ < 2) :
    3 / (2 - σ) ≤ 30 / 13 ↔ σ ≤ 7 / 10 := by
  constructor <;> intro h
  · have hpos : 0 < 2 - σ := sub_pos.mpr hσ
    rw [div_le_iff₀ hpos] at h
    norm_num at h ⊢
    nlinarith
  · have hpos : 0 < 2 - σ := sub_pos.mpr hσ
    rw [div_le_iff₀ hpos]
    have := h
    norm_num at this ⊢
    nlinarith

/-- The Huxley bridge misses `30/13` by the exact positive amount `6/65`. -/
theorem huxley_bridge_excess :
    (12 / 5 : ℝ) - 30 / 13 = 6 / 65 := by
  norm_num

/-- Heath--Brown's coefficient `2` is strictly stronger than `30/13`; the
obstruction is the published range, which starts at `11/14`. -/
theorem heath_brown_coefficient_is_stronger :
    (2 : ℝ) < 30 / 13 := by
  norm_num

/-- The gap between the endpoint reached by Montgomery and the starting point
of Heath--Brown's sharp range is nonempty. -/
theorem classical_reference_gap_nonempty :
    (7 / 10 : ℝ) < 11 / 14 := by
  norm_num

end CGLProofDAG
