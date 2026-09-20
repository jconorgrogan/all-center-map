import MontgomeryTheorem83Halasz

/-!
# Montgomery Theorem 8.3 with the source's smooth Halasz majorant

The hard dyadic row kernel in `MontgomeryTheorem83Halasz` is deliberately
not used here.  Montgomery inserts a positive smooth weight `b` which is at
least one on the original coefficient interval.  The coefficient sequence
is zero-padded to the (larger) carrier of `b`; the weighted coefficient
energy can only decrease, while the weighted Gram kernel is the object to
which the Mellin/L-function argument applies.

This file certifies that deterministic passage.  The absolute weighted
row-kernel implications are retained as conditional Schur lemmas.  Their
one-spaced specialization fails by near-diagonal accumulation; see
`MONTGOMERY_SMOOTH_ABSOLUTE_ROW_DEATH_CERTIFICATE.md`.  The published 1969
large-value route instead first thins to spacing `2(log N)^2`, uses the
equation-(30) weight, and controls the maximum of the pair kernels; that
source-faithful route is formalized in `MontgomeryEquation30SourceHalasz`.
The signed Hermitian/operator form below remains a valid alternate interface.
-/

namespace MAPMontgomeryTheorem83SmoothHalasz

open scoped BigOperators ComplexConjugate
open Complex
open CGLProofDAG MontgomeryVaughanFiniteReduction
open MAPJutilaDeterministicCore MAPHuxleyHalaszFront
open MAPMontgomeryTheorem83Halasz
open MAPMRTLemma210DyadicMeanSquare

noncomputable section

/-! ## Zero padding and weighted energy -/

/-- Extend a dyadic coefficient sequence by zero to a larger smooth carrier. -/
def paddedDyadicCoefficient (N : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n ∈ dyadicSupport N then a n else 0

/-- A convenient finite carrier which always contains the hard dyadic block. -/
def smoothCarrier (N : ℕ) (tail : Finset ℕ) : Finset ℕ :=
  dyadicSupport N ∪ tail

theorem dyadicSupport_subset_smoothCarrier (N : ℕ) (tail : Finset ℕ) :
    dyadicSupport N ⊆ smoothCarrier N tail := by
  intro n hn
  exact Finset.mem_union_left _ hn

/-- Zero padding does not change the original character polynomial. -/
theorem finitePolynomial_paddedDyadicCoefficient
    {q N : ℕ} (tail : Finset ℕ) (a : ℕ → ℂ)
    (row : (chi : DirichletCharacter ℂ q) × ℝ) :
    finitePolynomial (smoothCarrier N tail)
        (paddedDyadicCoefficient N a) characterRowVector row =
      characterPacketPolynomial q (dyadicSupport N) a row.1 row.2 := by
  unfold finitePolynomial characterPacketPolynomial
  symm
  apply Finset.sum_subset_zero_on_sdiff
      (dyadicSupport_subset_smoothCarrier N tail)
  · intro n hn
    have hnDyadic : n ∉ dyadicSupport N := (Finset.mem_sdiff.mp hn).2
    simp [paddedDyadicCoefficient, hnDyadic]
  · intro n hn
    simp only [paddedDyadicCoefficient, if_pos hn, characterRowVector]
    ring

/-- On a carrier where `b>0`, a majorant `b>=1` on the hard block makes the
weighted zero-padded coefficient energy no larger than the original energy. -/
theorem padded_weightedCoefficientEnergy_le
    {N : ℕ} (tail : Finset ℕ) (a : ℕ → ℂ) (b : ℕ → ℝ)
    (hbpos : ∀ n ∈ smoothCarrier N tail, 0 < b n)
    (hbmajor : ∀ n ∈ dyadicSupport N, 1 ≤ b n) :
    (∑ n ∈ smoothCarrier N tail,
        ‖paddedDyadicCoefficient N a n‖ ^ 2 / b n) ≤
      MontgomeryVaughanFiniteReduction.coefficientEnergy a N := by
  have heq :
      (∑ n ∈ smoothCarrier N tail,
          ‖paddedDyadicCoefficient N a n‖ ^ 2 / b n) =
        ∑ n ∈ dyadicSupport N,
          ‖paddedDyadicCoefficient N a n‖ ^ 2 / b n := by
    symm
    apply Finset.sum_subset_zero_on_sdiff
        (dyadicSupport_subset_smoothCarrier N tail)
    · intro n hn
      have hnDyadic : n ∉ dyadicSupport N := (Finset.mem_sdiff.mp hn).2
      simp [paddedDyadicCoefficient, hnDyadic]
    · intro n hn
      rfl
  rw [heq]
  unfold MontgomeryVaughanFiniteReduction.coefficientEnergy
  apply Finset.sum_le_sum
  intro n hn
  rw [paddedDyadicCoefficient, if_pos hn]
  exact div_le_self (sq_nonneg ‖a n‖) (hbmajor n hn)

/-! ## The source-faithful diagonal/off-diagonal split -/

/-- The diagonal of the weighted character Gram kernel costs only the total
mass of the positive majorant.  This is the deterministic `F` term in
Montgomery's Lemma 1. -/
theorem weighted_characterRow_diagonal_le_mass
    {q : ℕ} (cols : Finset ℕ) (b : ℕ → ℝ)
    (hb : ∀ n ∈ cols, 0 ≤ b n)
    (row : (chi : DirichletCharacter ℂ q) × ℝ) :
    ‖∑ n ∈ cols, (b n : ℂ) * conj (characterRowVector row n) *
        characterRowVector row n‖ ≤
      ∑ n ∈ cols, b n := by
  calc
    ‖∑ n ∈ cols, (b n : ℂ) * conj (characterRowVector row n) *
        characterRowVector row n‖ ≤
        ∑ n ∈ cols, ‖(b n : ℂ) * conj (characterRowVector row n) *
          characterRowVector row n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ cols, b n := by
      apply Finset.sum_le_sum
      intro n hn
      have hb0 := hb n hn
      have hv := norm_characterRowVector_le_one row n
      have hv0 := norm_nonneg (characterRowVector row n)
      have hvSq : ‖characterRowVector row n‖ *
          ‖characterRowVector row n‖ ≤ 1 := by nlinarith
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hb0, Complex.norm_conj]
      calc
        b n * ‖characterRowVector row n‖ * ‖characterRowVector row n‖ =
            b n * (‖characterRowVector row n‖ *
              ‖characterRowVector row n‖) := by ring
        _ ≤ b n * 1 := mul_le_mul_of_nonneg_left hvSq hb0
        _ = b n := mul_one _

/-- Reassemble the full weighted row sum from its smooth diagonal mass and
the *rowwise sum* of off-diagonal kernels.  No uniform pairwise estimate is
introduced: `hoff` is precisely the source's Halasz `K`-sector after the
Mellin/L-function argument has summed the relevant rows.

This lemma is correct conditionally, but the target-size `hoff` is not the
published Theorem-8.3 mechanism; its absolute-row specialization is rejected
by `MONTGOMERY_SMOOTH_ABSOLUTE_ROW_DEATH_CERTIFICATE.md`. -/
theorem weighted_characterRowKernel_le_of_mass_and_offDiagonalRowSum
    {q : ℕ} [DecidableEq ((chi : DirichletCharacter ℂ q) × ℝ)]
    (rows : Finset ((chi : DirichletCharacter ℂ q) × ℝ))
    (cols : Finset ℕ) (b : ℕ → ℝ) {F K : ℝ}
    (hb : ∀ n ∈ cols, 0 ≤ b n)
    (hmass : (∑ n ∈ cols, b n) ≤ F)
    (hoff : ∀ row ∈ rows,
      ∑ row' ∈ rows.erase row,
          ‖∑ n ∈ cols, (b n : ℂ) * conj (characterRowVector row n) *
            characterRowVector row' n‖ ≤ K) :
    ∀ row ∈ rows,
      ∑ row' ∈ rows,
          ‖∑ n ∈ cols, (b n : ℂ) * conj (characterRowVector row n) *
            characterRowVector row' n‖ ≤ F + K := by
  intro row hrow
  let kernelNorm : ((chi : DirichletCharacter ℂ q) × ℝ) → ℝ := fun row' =>
    ‖∑ n ∈ cols, (b n : ℂ) * conj (characterRowVector row n) *
      characterRowVector row' n‖
  have hsplit :
      (∑ row' ∈ rows, kernelNorm row') =
        kernelNorm row + ∑ row' ∈ rows.erase row, kernelNorm row' := by
    rw [add_comm]
    exact (Finset.sum_erase_add rows kernelNorm hrow).symm
  rw [hsplit]
  exact add_le_add
    ((weighted_characterRow_diagonal_le_mass cols b hb row).trans hmass)
    (hoff row hrow)

/-! ## Exact arithmetic form of the smooth Gram kernel -/

/-- The character quotient and ordinate difference occurring in one smooth
Gram entry.  This is the finite Dirichlet sum to which Montgomery applies
equation (35). -/
def smoothTwistedCharacterKernel {q : ℕ}
    (cols : Finset ℕ) (b : ℕ → ℝ)
    (row row' : (chi : DirichletCharacter ℂ q) × ℝ) : ℂ :=
  ∑ n ∈ cols, (b n : ℂ) * conj (row.1 n) * row'.1 n *
    phase n (row'.2 - row.2)

theorem conj_phase_mul_phase (n : ℕ) (t u : ℝ) :
    conj (phase n t) * phase n u = phase n (u - t) := by
  unfold phase
  rw [← Complex.exp_conj]
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The weighted Hilbert-space Gram entry is exactly the smooth character
quotient Dirichlet sum.  Hence the remaining analytic task is genuinely the
Mellin/L-function bound for this object, rather than another abstract
large-value assumption. -/
theorem weighted_characterGram_eq_smoothTwistedCharacterKernel
    {q : ℕ} (cols : Finset ℕ) (b : ℕ → ℝ)
    (row row' : (chi : DirichletCharacter ℂ q) × ℝ) :
    (∑ n ∈ cols, (b n : ℂ) * conj (characterRowVector row n) *
        characterRowVector row' n) =
      smoothTwistedCharacterKernel cols b row row' := by
  unfold smoothTwistedCharacterKernel characterRowVector
  apply Finset.sum_congr rfl
  intro n hn
  rw [map_mul]
  calc
    (b n : ℂ) * (conj (row.1 n) * conj (phase n row.2)) *
          (row'.1 n * phase n row'.2) =
        (b n : ℂ) * conj (row.1 n) * row'.1 n *
          (conj (phase n row.2) * phase n row'.2) := by ring
    _ = (b n : ℂ) * conj (row.1 n) * row'.1 n *
          phase n (row'.2 - row.2) := by rw [conj_phase_mul_phase]

/-! ## Weighted finite Halasz reduction -/

/-- An exact signed Hermitian/operator-form alternate interface.  It bounds
the positive Gram quadratic form without taking absolute values entry by
entry.  This is the form compatible with the dual large sieve and with
Montgomery (8.16). -/
def WeightedGramOperatorBound
    {I J : Type*} [DecidableEq I] [DecidableEq J]
    (rows : Finset I) (cols : Finset J) (b : J → ℝ)
    (v : I → J → ℂ) (M : ℝ) : Prop :=
  ∀ eta : I → ℂ,
    correlationEnergy rows cols b eta v ≤
      M * ∑ i ∈ rows, ‖eta i‖ ^ 2

/-- The signed operator bound is literally the weighted dual large-sieve
quadratic form.  This theorem performs the finite Hilbert-space duality step
from that bound to the primal mean square, with no Schur or absolute-row
loss. -/
theorem finite_weighted_mean_square_le_of_operatorBound
    {I J : Type*} [DecidableEq I] [DecidableEq J]
    (rows : Finset I) (cols : Finset J)
    (a : J → ℂ) (b : J → ℝ) (v : I → J → ℂ)
    {E M : ℝ}
    (hE : 0 ≤ E) (hM : 0 ≤ M)
    (hb : ∀ k ∈ cols, 0 < b k)
    (hcoeff : (∑ k ∈ cols, ‖a k‖ ^ 2 / b k) ≤ E)
    (hoperator : WeightedGramOperatorBound rows cols b v M) :
    (∑ i ∈ rows, ‖finitePolynomial cols a v i‖ ^ 2) ≤ E * M := by
  let D : I → ℂ := finitePolynomial cols a v
  let S : ℝ := ∑ i ∈ rows, ‖D i‖ ^ 2
  have hS : 0 ≤ S := by
    dsimp [S]
    positivity
  have hidentity :
      ∑ k ∈ cols, a k * (∑ i ∈ rows, conj (D i) * v i k) = (S : ℂ) := by
    calc
      ∑ k ∈ cols, a k * (∑ i ∈ rows, conj (D i) * v i k) =
          ∑ i ∈ rows, ∑ k ∈ cols, a k * (conj (D i) * v i k) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
      _ = ∑ i ∈ rows, conj (D i) * D i := by
        apply Finset.sum_congr rfl
        intro i hi
        dsimp [D, finitePolynomial]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ = ∑ i ∈ rows, (‖D i‖ ^ 2 : ℂ) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact Complex.conj_mul' (D i)
      _ = (S : ℂ) := by
        dsimp [S]
        norm_cast
  have hweighted := weighted_norm_sum_sq_le cols a
    (fun k => ∑ i ∈ rows, conj (D i) * v i k) b hb
  have hcorr :
      correlationEnergy rows cols b (fun i => conj (D i)) v ≤ M * S := by
    simpa [S, Complex.norm_conj] using hoperator (fun i => conj (D i))
  have hcorr0 :
      0 ≤ correlationEnergy rows cols b (fun i => conj (D i)) v := by
    unfold correlationEnergy
    apply Finset.sum_nonneg
    intro k hk
    exact mul_nonneg (hb k hk).le (sq_nonneg _)
  have hpre : S ^ 2 ≤ E * (M * S) := by
    calc
      S ^ 2 = ‖(S : ℂ)‖ ^ 2 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hS]
      _ = ‖∑ k ∈ cols, a k *
          (∑ i ∈ rows, conj (D i) * v i k)‖ ^ 2 := by rw [hidentity]
      _ ≤ (∑ k ∈ cols, ‖a k‖ ^ 2 / b k) *
          correlationEnergy rows cols b (fun i => conj (D i)) v := by
        simpa [correlationEnergy] using hweighted
      _ ≤ E * (M * S) := mul_le_mul hcoeff hcorr hcorr0 hE
  change S ≤ E * M
  by_cases hSzero : S = 0
  · rw [hSzero]
    positivity
  · have hSpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hSzero)
    nlinarith

/-- Large-value absorption performed directly from the signed operator
bound.  No absolute Gram row is introduced. -/
theorem finite_weighted_large_values_absorbed_of_operatorBound
    {I J : Type*} [DecidableEq I] [DecidableEq J]
    (rows : Finset I) (cols : Finset J)
    (a : J → ℂ) (b : J → ℝ) (v : I → J → ℂ)
    {V E C N K : ℝ}
    (hV : 0 ≤ V) (hE : 0 ≤ E) (hC : 0 ≤ C)
    (hN : 0 ≤ N) (hK : 0 ≤ K)
    (hb : ∀ k ∈ cols, 0 < b k)
    (hlarge : ∀ i ∈ rows, V ≤ ‖finitePolynomial cols a v i‖)
    (hcoeff : (∑ k ∈ cols, ‖a k‖ ^ 2 / b k) ≤ E)
    (hoperator : WeightedGramOperatorBound rows cols b v
      (C * (N + (rows.card : ℝ) * K)))
    (hthreshold : 2 * C * E * K ≤ V ^ 2) :
    (rows.card : ℝ) * V ^ 2 ≤ 2 * C * E * N := by
  have hlower : (rows.card : ℝ) * V ^ 2 ≤
      ∑ i ∈ rows, ‖finitePolynomial cols a v i‖ ^ 2 := by
    calc
      (rows.card : ℝ) * V ^ 2 = ∑ _i ∈ rows, V ^ 2 := by simp
      _ ≤ ∑ i ∈ rows, ‖finitePolynomial cols a v i‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        exact pow_le_pow_left₀ hV (hlarge i hi) 2
  have hupper := finite_weighted_mean_square_le_of_operatorBound
    rows cols a b v hE
      (mul_nonneg hC (add_nonneg hN (mul_nonneg (by positivity) hK)))
      hb hcoeff hoperator
  let R : ℝ := rows.card
  have hR : 0 ≤ R := by positivity
  have hraw : R * V ^ 2 ≤ C * E * N + R * C * E * K := by
    calc
      R * V ^ 2 ≤ ∑ i ∈ rows, ‖finitePolynomial cols a v i‖ ^ 2 := hlower
      _ ≤ E * (C * (N + R * K)) := hupper
      _ = C * E * N + R * C * E * K := by ring
  have habsorb : 2 * R * C * E * K ≤ R * V ^ 2 := by
    have := mul_le_mul_of_nonneg_left hthreshold hR
    nlinarith
  nlinarith

/-- Legacy Schur implication.  Correct conditionally, but not the
Montgomery-(8.16) source route; the target-size absolute-row hypothesis is
false even for the smooth majorant. -/
theorem correlationEnergy_le_of_weighted_rowKernel
    {I J : Type*} [DecidableEq I] [DecidableEq J]
    (rows : Finset I) (cols : Finset J) (b : J → ℝ)
    (v : I → J → ℂ) (eta : I → ℂ) {M : ℝ}
    (hb : ∀ k ∈ cols, 0 ≤ b k)
    (heta : ∀ i ∈ rows, ‖eta i‖ = 1)
    (hrowKernel : ∀ i ∈ rows,
      ∑ j ∈ rows,
          ‖∑ k ∈ cols, (b k : ℂ) * conj (v i k) * v j k‖ ≤ M) :
    correlationEnergy rows cols b eta v ≤ (rows.card : ℝ) * M := by
  let B : I → I → ℂ := fun i j =>
    ∑ k ∈ cols, (b k : ℂ) * conj (v i k) * v j k
  let F : I → I → ℂ := fun i j =>
    conj (eta i) * eta j * B i j
  have hcorrNonneg : 0 ≤ correlationEnergy rows cols b eta v := by
    unfold correlationEnergy
    apply Finset.sum_nonneg
    intro k hk
    exact mul_nonneg (hb k hk) (sq_nonneg _)
  have hcorrExpanded :
      (correlationEnergy rows cols b eta v : ℂ) =
        ∑ i ∈ rows, ∑ j ∈ rows, F i j := by
    simpa [F, B] using correlationEnergy_eq_doubleSum rows cols b eta v
  calc
    correlationEnergy rows cols b eta v =
        ‖(correlationEnergy rows cols b eta v : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcorrNonneg]
    _ = ‖∑ i ∈ rows, ∑ j ∈ rows, F i j‖ := by rw [hcorrExpanded]
    _ ≤ ∑ i ∈ rows, ∑ j ∈ rows, ‖F i j‖ := by
      exact (norm_sum_le _ _).trans <| Finset.sum_le_sum fun i hi => norm_sum_le _ _
    _ = ∑ i ∈ rows, ∑ j ∈ rows, ‖B i j‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      simp [F, norm_mul, Complex.norm_conj, heta i hi, heta j hj]
    _ ≤ ∑ _i ∈ rows, M := by
      apply Finset.sum_le_sum
      intro i hi
      simpa [B] using hrowKernel i hi
    _ = (rows.card : ℝ) * M := by simp

/-- Finite Schur test for the Hermitian weighted Gram kernel.  Unlike the
unit-phase Halasz corollary, this controls an arbitrary coefficient vector
and is the deterministic step behind Montgomery (8.16). -/
theorem correlationEnergy_le_mul_sum_norm_sq_of_weighted_rowKernel
    {I J : Type*} [DecidableEq I] [DecidableEq J]
    (rows : Finset I) (cols : Finset J) (b : J → ℝ)
    (v : I → J → ℂ) (eta : I → ℂ) {M : ℝ}
    (hb : ∀ k ∈ cols, 0 ≤ b k)
    (hM : 0 ≤ M)
    (hrowKernel : ∀ i ∈ rows,
      ∑ j ∈ rows,
          ‖∑ k ∈ cols, (b k : ℂ) * conj (v i k) * v j k‖ ≤ M) :
    correlationEnergy rows cols b eta v ≤
      M * ∑ i ∈ rows, ‖eta i‖ ^ 2 := by
  let B : I → I → ℂ := fun i j =>
    ∑ k ∈ cols, (b k : ℂ) * conj (v i k) * v j k
  have hBsymm (i j : I) : ‖B j i‖ = ‖B i j‖ := by
    have hconj : conj (B i j) = B j i := by
      dsimp [B]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [map_mul, Complex.conj_ofReal, Complex.conj_conj]
      ring
    rw [← hconj, Complex.norm_conj]
  have hcorrNonneg : 0 ≤ correlationEnergy rows cols b eta v := by
    unfold correlationEnergy
    apply Finset.sum_nonneg
    intro k hk
    exact mul_nonneg (hb k hk) (sq_nonneg _)
  have hcorrExpanded :
      (correlationEnergy rows cols b eta v : ℂ) =
        ∑ i ∈ rows, ∑ j ∈ rows,
          conj (eta i) * eta j * B i j := by
    simpa [B] using correlationEnergy_eq_doubleSum rows cols b eta v
  have htriangle :
      correlationEnergy rows cols b eta v ≤
        ∑ i ∈ rows, ∑ j ∈ rows,
          (‖eta i‖ * ‖eta j‖) * ‖B i j‖ := by
    calc
      correlationEnergy rows cols b eta v =
          ‖(correlationEnergy rows cols b eta v : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcorrNonneg]
      _ = ‖∑ i ∈ rows, ∑ j ∈ rows,
          conj (eta i) * eta j * B i j‖ := by rw [hcorrExpanded]
      _ ≤ ∑ i ∈ rows, ∑ j ∈ rows,
          ‖conj (eta i) * eta j * B i j‖ := by
        exact (norm_sum_le _ _).trans <| Finset.sum_le_sum fun i hi => norm_sum_le _ _
      _ = ∑ i ∈ rows, ∑ j ∈ rows,
          (‖eta i‖ * ‖eta j‖) * ‖B i j‖ := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rw [norm_mul, norm_mul, Complex.norm_conj]
  have hpair :
      2 * (∑ i ∈ rows, ∑ j ∈ rows,
          (‖eta i‖ * ‖eta j‖) * ‖B i j‖) ≤
        ∑ i ∈ rows, ∑ j ∈ rows,
          (‖eta i‖ ^ 2 + ‖eta j‖ ^ 2) * ‖B i j‖ := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hab : 2 * ‖eta i‖ * ‖eta j‖ ≤
        ‖eta i‖ ^ 2 + ‖eta j‖ ^ 2 := by
      nlinarith [sq_nonneg (‖eta i‖ - ‖eta j‖)]
    calc
      2 * ((‖eta i‖ * ‖eta j‖) * ‖B i j‖) =
          (2 * ‖eta i‖ * ‖eta j‖) * ‖B i j‖ := by ring
      _ ≤ (‖eta i‖ ^ 2 + ‖eta j‖ ^ 2) * ‖B i j‖ :=
        mul_le_mul_of_nonneg_right hab (norm_nonneg _)
  have hfirst :
      (∑ i ∈ rows, ∑ j ∈ rows, ‖eta i‖ ^ 2 * ‖B i j‖) ≤
        M * ∑ i ∈ rows, ‖eta i‖ ^ 2 := by
    calc
      (∑ i ∈ rows, ∑ j ∈ rows, ‖eta i‖ ^ 2 * ‖B i j‖) =
          ∑ i ∈ rows, ‖eta i‖ ^ 2 * (∑ j ∈ rows, ‖B i j‖) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
      _ ≤ ∑ i ∈ rows, ‖eta i‖ ^ 2 * M := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (by simpa [B] using hrowKernel i hi)
          (sq_nonneg _)
      _ = M * ∑ i ∈ rows, ‖eta i‖ ^ 2 := by
        rw [← Finset.sum_mul]
        ring
  have hsecond :
      (∑ i ∈ rows, ∑ j ∈ rows, ‖eta j‖ ^ 2 * ‖B i j‖) ≤
        M * ∑ j ∈ rows, ‖eta j‖ ^ 2 := by
    rw [Finset.sum_comm]
    calc
      (∑ j ∈ rows, ∑ i ∈ rows, ‖eta j‖ ^ 2 * ‖B i j‖) =
          ∑ j ∈ rows, ‖eta j‖ ^ 2 * (∑ i ∈ rows, ‖B i j‖) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.mul_sum]
      _ = ∑ j ∈ rows, ‖eta j‖ ^ 2 * (∑ i ∈ rows, ‖B j i‖) := by
        apply Finset.sum_congr rfl
        intro j hj
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        exact (hBsymm i j).symm
      _ ≤ ∑ j ∈ rows, ‖eta j‖ ^ 2 * M := by
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left (by simpa [B] using hrowKernel j hj)
          (sq_nonneg _)
      _ = M * ∑ j ∈ rows, ‖eta j‖ ^ 2 := by
        rw [← Finset.sum_mul]
        ring
  have hsplit :
      (∑ i ∈ rows, ∑ j ∈ rows,
          (‖eta i‖ ^ 2 + ‖eta j‖ ^ 2) * ‖B i j‖) =
        (∑ i ∈ rows, ∑ j ∈ rows, ‖eta i‖ ^ 2 * ‖B i j‖) +
        (∑ i ∈ rows, ∑ j ∈ rows, ‖eta j‖ ^ 2 * ‖B i j‖) := by
    simp_rw [add_mul, Finset.sum_add_distrib]
  have htwice :
      2 * correlationEnergy rows cols b eta v ≤
        2 * (M * ∑ i ∈ rows, ‖eta i‖ ^ 2) := by
    calc
      2 * correlationEnergy rows cols b eta v ≤
          2 * (∑ i ∈ rows, ∑ j ∈ rows,
            (‖eta i‖ * ‖eta j‖) * ‖B i j‖) :=
        mul_le_mul_of_nonneg_left htriangle (by norm_num)
      _ ≤ ∑ i ∈ rows, ∑ j ∈ rows,
          (‖eta i‖ ^ 2 + ‖eta j‖ ^ 2) * ‖B i j‖ := hpair
      _ = (∑ i ∈ rows, ∑ j ∈ rows, ‖eta i‖ ^ 2 * ‖B i j‖) +
          (∑ i ∈ rows, ∑ j ∈ rows, ‖eta j‖ ^ 2 * ‖B i j‖) := hsplit
      _ ≤ M * (∑ i ∈ rows, ‖eta i‖ ^ 2) +
          M * (∑ i ∈ rows, ‖eta i‖ ^ 2) := add_le_add hfirst hsecond
      _ = 2 * (M * ∑ i ∈ rows, ‖eta i‖ ^ 2) := by ring
  linarith

/-- Weighted finite mean-square theorem obtained from the Schur bound.  This
is the exact finite Hilbert-space content of Montgomery (8.16): no
large-value theorem is assumed. -/
theorem finite_weighted_mean_square_le_of_rowKernel
    {I J : Type*} [DecidableEq I] [DecidableEq J]
    (rows : Finset I) (cols : Finset J)
    (a : J → ℂ) (b : J → ℝ) (v : I → J → ℂ)
    {E M : ℝ}
    (hE : 0 ≤ E) (hM : 0 ≤ M)
    (hb : ∀ k ∈ cols, 0 < b k)
    (hcoeff : (∑ k ∈ cols, ‖a k‖ ^ 2 / b k) ≤ E)
    (hrowKernel : ∀ i ∈ rows,
      ∑ j ∈ rows,
          ‖∑ k ∈ cols, (b k : ℂ) * conj (v i k) * v j k‖ ≤ M) :
    (∑ i ∈ rows, ‖finitePolynomial cols a v i‖ ^ 2) ≤ E * M := by
  let D : I → ℂ := finitePolynomial cols a v
  let S : ℝ := ∑ i ∈ rows, ‖D i‖ ^ 2
  have hS : 0 ≤ S := by
    dsimp [S]
    positivity
  have hidentity :
      ∑ k ∈ cols, a k * (∑ i ∈ rows, conj (D i) * v i k) = (S : ℂ) := by
    calc
      ∑ k ∈ cols, a k * (∑ i ∈ rows, conj (D i) * v i k) =
          ∑ i ∈ rows, ∑ k ∈ cols, a k * (conj (D i) * v i k) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
      _ = ∑ i ∈ rows, conj (D i) * D i := by
        apply Finset.sum_congr rfl
        intro i hi
        dsimp [D, finitePolynomial]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ = ∑ i ∈ rows, (‖D i‖ ^ 2 : ℂ) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact Complex.conj_mul' (D i)
      _ = (S : ℂ) := by
        dsimp [S]
        norm_cast
  have hweighted := weighted_norm_sum_sq_le cols a
    (fun k => ∑ i ∈ rows, conj (D i) * v i k) b hb
  have hcorr :
      correlationEnergy rows cols b (fun i => conj (D i)) v ≤ M * S := by
    simpa [S, Complex.norm_conj] using
      correlationEnergy_le_mul_sum_norm_sq_of_weighted_rowKernel
        rows cols b v (fun i => conj (D i))
        (fun k hk => (hb k hk).le) hM hrowKernel
  have hcorr0 :
      0 ≤ correlationEnergy rows cols b (fun i => conj (D i)) v := by
    unfold correlationEnergy
    apply Finset.sum_nonneg
    intro k hk
    exact mul_nonneg (hb k hk).le (sq_nonneg _)
  have hpre : S ^ 2 ≤ E * (M * S) := by
    calc
      S ^ 2 = ‖(S : ℂ)‖ ^ 2 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hS]
      _ = ‖∑ k ∈ cols, a k *
          (∑ i ∈ rows, conj (D i) * v i k)‖ ^ 2 := by rw [hidentity]
      _ ≤ (∑ k ∈ cols, ‖a k‖ ^ 2 / b k) *
          correlationEnergy rows cols b (fun i => conj (D i)) v := by
        simpa [correlationEnergy] using hweighted
      _ ≤ E * (M * S) := mul_le_mul hcoeff hcorr hcorr0 hE
  change S ≤ E * M
  by_cases hSzero : S = 0
  · rw [hSzero]
    positivity
  · have hSpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hSzero)
    nlinarith

/-- Weighted Halasz before Montgomery's absorption. -/
theorem finite_weighted_halasz_before_absorption
    {I J : Type*} [DecidableEq I] [DecidableEq J]
    (rows : Finset I) (cols : Finset J)
    (a : J → ℂ) (b : J → ℝ) (v : I → J → ℂ)
    {V E C N K : ℝ}
    (hV : 0 ≤ V) (hE : 0 ≤ E) (hC : 0 ≤ C)
    (hN : 0 ≤ N) (hK : 0 ≤ K)
    (hb : ∀ k ∈ cols, 0 < b k)
    (hlarge : ∀ i ∈ rows, V ≤ ‖finitePolynomial cols a v i‖)
    (hcoeff : (∑ k ∈ cols, ‖a k‖ ^ 2 / b k) ≤ E)
    (hrowKernel : ∀ i ∈ rows,
      ∑ j ∈ rows,
          ‖∑ k ∈ cols, (b k : ℂ) * conj (v i k) * v j k‖ ≤
        C * (N + (rows.card : ℝ) * K)) :
    (((rows.card : ℝ) * V) ^ 2) ≤
      E * ((rows.card : ℝ) * C *
        (N + (rows.card : ℝ) * K)) := by
  obtain ⟨eta, heta, hhalasz⟩ :=
    finite_halasz_inequality rows cols a b v hb
  have hcard : (rows.card : ℝ) * V ≤
      ∑ i ∈ rows, ‖finitePolynomial cols a v i‖ := by
    calc
      (rows.card : ℝ) * V = ∑ _i ∈ rows, V := by simp
      _ ≤ ∑ i ∈ rows, ‖finitePolynomial cols a v i‖ := by
        exact Finset.sum_le_sum fun i hi => hlarge i hi
  have hsquare := pow_le_pow_left₀
    (mul_nonneg (Nat.cast_nonneg _) hV) hcard 2
  have hcorr := correlationEnergy_le_of_weighted_rowKernel
    rows cols b v eta (fun k hk => (hb k hk).le) heta hrowKernel
  have hweightedEnergy : 0 ≤ ∑ k ∈ cols, ‖a k‖ ^ 2 / b k := by
    apply Finset.sum_nonneg
    intro k hk
    exact div_nonneg (sq_nonneg _) (hb k hk).le
  have hcorr0 : 0 ≤ correlationEnergy rows cols b eta v := by
    unfold correlationEnergy
    apply Finset.sum_nonneg
    intro k hk
    exact mul_nonneg (hb k hk).le (sq_nonneg _)
  calc
    (((rows.card : ℝ) * V) ^ 2) ≤
        (∑ i ∈ rows, ‖finitePolynomial cols a v i‖) ^ 2 := hsquare
    _ ≤ (∑ k ∈ cols, ‖a k‖ ^ 2 / b k) *
          correlationEnergy rows cols b eta v := hhalasz
    _ ≤ E * ((rows.card : ℝ) * C *
          (N + (rows.card : ℝ) * K)) := by
      apply mul_le_mul hcoeff _ hcorr0 hE
      convert hcorr using 1 <;> ring

/-- Montgomery's absorption with an arbitrary certified upper bound `E` for
the weighted coefficient energy. -/
theorem finite_weighted_halasz_absorbed
    {I J : Type*} [DecidableEq I] [DecidableEq J]
    (rows : Finset I) (cols : Finset J)
    (a : J → ℂ) (b : J → ℝ) (v : I → J → ℂ)
    {V E C N K : ℝ}
    (hV : 0 ≤ V) (hE : 0 ≤ E) (hC : 0 ≤ C)
    (hN : 0 ≤ N) (hK : 0 ≤ K)
    (hb : ∀ k ∈ cols, 0 < b k)
    (hlarge : ∀ i ∈ rows, V ≤ ‖finitePolynomial cols a v i‖)
    (hcoeff : (∑ k ∈ cols, ‖a k‖ ^ 2 / b k) ≤ E)
    (hrowKernel : ∀ i ∈ rows,
      ∑ j ∈ rows,
          ‖∑ k ∈ cols, (b k : ℂ) * conj (v i k) * v j k‖ ≤
        C * (N + (rows.card : ℝ) * K))
    (hthreshold : 2 * C * E * K ≤ V ^ 2) :
    (rows.card : ℝ) * V ^ 2 ≤ 2 * C * E * N := by
  let R : ℝ := rows.card
  have hR : 0 ≤ R := by positivity
  by_cases hRzero : R = 0
  · change R * V ^ 2 ≤ 2 * C * E * N
    rw [hRzero, zero_mul]
    positivity
  · have hRpos : 0 < R := lt_of_le_of_ne hR (Ne.symm hRzero)
    have hpre := finite_weighted_halasz_before_absorption
      rows cols a b v hV hE hC hN hK hb hlarge hcoeff hrowKernel
    change (R * V) ^ 2 ≤ E * (R * C * (N + R * K)) at hpre
    have hcancelled :
        R * V ^ 2 ≤ C * E * N + R * C * E * K := by
      apply (mul_le_mul_iff_of_pos_left hRpos).mp
      calc
        R * (R * V ^ 2) = (R * V) ^ 2 := by ring
        _ ≤ E * (R * C * (N + R * K)) := hpre
        _ = R * (C * E * N + R * C * E * K) := by ring
    have habsorb : 2 * R * C * E * K ≤ R * V ^ 2 := by
      have := mul_le_mul_of_nonneg_left hthreshold hR
      nlinarith
    linarith

/-! ## Source-faithful fixed-modulus specialization -/

/-- Signed/operator-form alternative to Montgomery (8.16), fixed modulus and
unit ordinate spacing.  Its analytic premise is the dual hybrid large-sieve
quadratic form itself; the published long-spaced pairwise route is in
`MontgomeryEquation30SourceHalasz`. -/
theorem character_smooth_mean_square_of_operatorBound
    {q N : ℕ} [NeZero q] (hN : 1 ≤ N)
    (tail : Finset ℕ) (a : ℕ → ℂ) (b : ℕ → ℝ)
    {T C : ℝ}
    (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hscale : 1 ≤ (q : ℝ) * T)
    (hbpos : ∀ n ∈ smoothCarrier N tail, 0 < b n)
    (hbmajor : ∀ n ∈ dyadicSupport N, 1 ≤ b n)
    (W : DirichletCharacter ℂ q → Finset ℝ)
    (hsep : ∀ chi, OneSeparated (W chi))
    (hheight : ∀ chi, ∀ t ∈ W chi, |t| ≤ T)
    (hoperator : WeightedGramOperatorBound
      (characterRows W) (smoothCarrier N tail) b characterRowVector
      (C * ((N : ℝ) + ((characterRows W).card : ℝ) *
        theorem83KernelScale q T))) :
    (∑ chi : DirichletCharacter ℂ q, ∑ t ∈ W chi,
        ‖characterPacketPolynomial q (dyadicSupport N) a chi t‖ ^ 2) ≤
      MontgomeryVaughanFiniteReduction.coefficientEnergy a N *
        (C * ((N : ℝ) +
          (∑ chi : DirichletCharacter ℂ q, ((W chi).card : ℝ)) *
            theorem83KernelScale q T)) := by
  have _ := hN
  have _ := hT
  have _ := hsep
  have _ := hheight
  let M : ℝ := C * ((N : ℝ) + ((characterRows W).card : ℝ) *
    theorem83KernelScale q T)
  have hM : 0 ≤ M := by
    dsimp [M]
    exact mul_nonneg hC (add_nonneg (by positivity)
      (mul_nonneg (by positivity) (theorem83KernelScale_nonneg hscale)))
  have h := finite_weighted_mean_square_le_of_operatorBound
    (characterRows W) (smoothCarrier N tail)
    (paddedDyadicCoefficient N a) b characterRowVector
    (by
      unfold MontgomeryVaughanFiniteReduction.coefficientEnergy
      positivity) hM hbpos
    (padded_weightedCoefficientEnergy_le tail a b hbpos hbmajor)
    hoperator
  change (∑ row ∈ characterRows W,
      ‖finitePolynomial (smoothCarrier N tail)
        (paddedDyadicCoefficient N a) characterRowVector row‖ ^ 2) ≤
      MontgomeryVaughanFiniteReduction.coefficientEnergy a N * M at h
  simp_rw [finitePolynomial_paddedDyadicCoefficient] at h
  have hsumSigma : (∑ row ∈ characterRows W,
      ‖characterPacketPolynomial q (dyadicSupport N) a row.1 row.2‖ ^ 2) =
        ∑ chi : DirichletCharacter ℂ q, ∑ t ∈ W chi,
          ‖characterPacketPolynomial q (dyadicSupport N) a chi t‖ ^ 2 := by
    simpa [characterRows] using
      (Finset.sum_sigma
        (Finset.univ : Finset (DirichletCharacter ℂ q)) W
        (fun row =>
          ‖characterPacketPolynomial q (dyadicSupport N) a row.1 row.2‖ ^ 2))
  rw [hsumSigma] at h
  dsimp [M] at h
  rw [card_characterRows] at h
  push_cast at h
  simpa using h

/-- Large-value absorption from the signed/operator-form alternative. -/
theorem character_smooth_large_values_absorbed_of_operatorBound
    {q N : ℕ} [NeZero q] (hN : 1 ≤ N)
    (tail : Finset ℕ) (a : ℕ → ℂ) (b : ℕ → ℝ)
    {T V C : ℝ}
    (hT : 0 ≤ T) (hV : 0 ≤ V) (hC : 0 ≤ C)
    (hscale : 1 ≤ (q : ℝ) * T)
    (hbpos : ∀ n ∈ smoothCarrier N tail, 0 < b n)
    (hbmajor : ∀ n ∈ dyadicSupport N, 1 ≤ b n)
    (W : DirichletCharacter ℂ q → Finset ℝ)
    (hsep : ∀ chi, OneSeparated (W chi))
    (hheight : ∀ chi, ∀ t ∈ W chi, |t| ≤ T)
    (hlarge : ∀ chi, ∀ t ∈ W chi,
      V ≤ ‖characterPacketPolynomial q (dyadicSupport N) a chi t‖)
    (hoperator : WeightedGramOperatorBound
      (characterRows W) (smoothCarrier N tail) b characterRowVector
      (C * ((N : ℝ) + ((characterRows W).card : ℝ) *
        theorem83KernelScale q T)))
    (hthreshold :
      2 * C * MontgomeryVaughanFiniteReduction.coefficientEnergy a N *
          theorem83KernelScale q T ≤ V ^ 2) :
    (∑ chi : DirichletCharacter ℂ q, ((W chi).card : ℝ)) * V ^ 2 ≤
      2 * C * MontgomeryVaughanFiniteReduction.coefficientEnergy a N * N := by
  have hlargeRows : ∀ row ∈ characterRows W,
      V ≤ ‖finitePolynomial (smoothCarrier N tail)
        (paddedDyadicCoefficient N a) characterRowVector row‖ := by
    intro row hrow
    rw [finitePolynomial_paddedDyadicCoefficient]
    exact hlarge row.1 row.2 (Finset.mem_sigma.mp hrow).2
  have h := finite_weighted_large_values_absorbed_of_operatorBound
    (characterRows W) (smoothCarrier N tail)
    (paddedDyadicCoefficient N a) b characterRowVector
    hV (by
      unfold MontgomeryVaughanFiniteReduction.coefficientEnergy
      positivity) hC (by positivity : 0 ≤ (N : ℝ))
    (theorem83KernelScale_nonneg hscale) hbpos hlargeRows
    (padded_weightedCoefficientEnergy_le tail a b hbpos hbmajor)
    hoperator hthreshold
  rw [card_characterRows] at h
  push_cast at h
  simpa using h

/-- Legacy absolute-row/Schur conditional.  Its advertised source-scale
premise is false; use `character_smooth_mean_square_of_operatorBound`. -/
theorem character_smooth_mean_square_sourceScale
    {q N : ℕ} [NeZero q] (hN : 1 ≤ N)
    (tail : Finset ℕ) (a : ℕ → ℂ) (b : ℕ → ℝ)
    {T C : ℝ}
    (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hscale : 1 ≤ (q : ℝ) * T)
    (hbpos : ∀ n ∈ smoothCarrier N tail, 0 < b n)
    (hbmajor : ∀ n ∈ dyadicSupport N, 1 ≤ b n)
    (W : DirichletCharacter ℂ q → Finset ℝ)
    (hsep : ∀ chi, OneSeparated (W chi))
    (hheight : ∀ chi, ∀ t ∈ W chi, |t| ≤ T)
    (hrowKernel : ∀ row ∈ characterRows W,
      ∑ row' ∈ characterRows W,
          ‖∑ n ∈ smoothCarrier N tail,
              (b n : ℂ) * conj (characterRowVector row n) *
                characterRowVector row' n‖ ≤
        C * ((N : ℝ) + ((characterRows W).card : ℝ) *
          theorem83KernelScale q T)) :
    (∑ chi : DirichletCharacter ℂ q, ∑ t ∈ W chi,
        ‖characterPacketPolynomial q (dyadicSupport N) a chi t‖ ^ 2) ≤
      MontgomeryVaughanFiniteReduction.coefficientEnergy a N *
        (C * ((N : ℝ) +
          (∑ chi : DirichletCharacter ℂ q, ((W chi).card : ℝ)) *
            theorem83KernelScale q T)) := by
  have _ := hN
  have _ := hT
  have _ := hsep
  have _ := hheight
  let M : ℝ := C * ((N : ℝ) + ((characterRows W).card : ℝ) *
    theorem83KernelScale q T)
  have hM : 0 ≤ M := by
    dsimp [M]
    exact mul_nonneg hC (add_nonneg (by positivity)
      (mul_nonneg (by positivity) (theorem83KernelScale_nonneg hscale)))
  have h := finite_weighted_mean_square_le_of_rowKernel
    (characterRows W) (smoothCarrier N tail)
    (paddedDyadicCoefficient N a) b characterRowVector
    (by
      unfold MontgomeryVaughanFiniteReduction.coefficientEnergy
      positivity) hM hbpos
    (padded_weightedCoefficientEnergy_le tail a b hbpos hbmajor)
    hrowKernel
  change (∑ row ∈ characterRows W,
      ‖finitePolynomial (smoothCarrier N tail)
        (paddedDyadicCoefficient N a) characterRowVector row‖ ^ 2) ≤
      MontgomeryVaughanFiniteReduction.coefficientEnergy a N * M at h
  simp_rw [finitePolynomial_paddedDyadicCoefficient] at h
  have hsumSigma : (∑ row ∈ characterRows W,
      ‖characterPacketPolynomial q (dyadicSupport N) a row.1 row.2‖ ^ 2) =
        ∑ chi : DirichletCharacter ℂ q, ∑ t ∈ W chi,
          ‖characterPacketPolynomial q (dyadicSupport N) a chi t‖ ^ 2 := by
    simpa [characterRows] using
      (Finset.sum_sigma
        (Finset.univ : Finset (DirichletCharacter ℂ q)) W
        (fun row =>
          ‖characterPacketPolynomial q (dyadicSupport N) a row.1 row.2‖ ^ 2))
  rw [hsumSigma] at h
  dsimp [M] at h
  rw [card_characterRows] at h
  push_cast at h
  simpa using h

/-- Legacy absolute-row/Schur large-value conditional.  Its advertised
source-scale premise is false; use
`character_smooth_large_values_absorbed_of_operatorBound`. -/
theorem character_smooth_halasz_large_values_absorbed_sourceScale
    {q N : ℕ} [NeZero q] (hN : 1 ≤ N)
    (tail : Finset ℕ) (a : ℕ → ℂ) (b : ℕ → ℝ)
    {T V C : ℝ}
    (hT : 0 ≤ T) (hV : 0 ≤ V) (hC : 0 ≤ C)
    (hscale : 1 ≤ (q : ℝ) * T)
    (hbpos : ∀ n ∈ smoothCarrier N tail, 0 < b n)
    (hbmajor : ∀ n ∈ dyadicSupport N, 1 ≤ b n)
    (W : DirichletCharacter ℂ q → Finset ℝ)
    (hsep : ∀ chi, OneSeparated (W chi))
    (hheight : ∀ chi, ∀ t ∈ W chi, |t| ≤ T)
    (hlarge : ∀ chi, ∀ t ∈ W chi,
      V ≤ ‖characterPacketPolynomial q (dyadicSupport N) a chi t‖)
    (hrowKernel : ∀ row ∈ characterRows W,
      ∑ row' ∈ characterRows W,
          ‖∑ n ∈ smoothCarrier N tail,
              (b n : ℂ) * conj (characterRowVector row n) *
                characterRowVector row' n‖ ≤
        C * ((N : ℝ) + ((characterRows W).card : ℝ) *
          theorem83KernelScale q T))
    (hthreshold :
      2 * C * MontgomeryVaughanFiniteReduction.coefficientEnergy a N *
          theorem83KernelScale q T ≤ V ^ 2) :
    (∑ chi : DirichletCharacter ℂ q, ((W chi).card : ℝ)) * V ^ 2 ≤
      2 * C * MontgomeryVaughanFiniteReduction.coefficientEnergy a N * N := by
  have hlargeRows : ∀ row ∈ characterRows W,
      V ≤ ‖finitePolynomial (smoothCarrier N tail)
        (paddedDyadicCoefficient N a) characterRowVector row‖ := by
    intro row hrow
    rw [finitePolynomial_paddedDyadicCoefficient]
    exact hlarge row.1 row.2 (Finset.mem_sigma.mp hrow).2
  have h := finite_weighted_halasz_absorbed
    (characterRows W) (smoothCarrier N tail)
    (paddedDyadicCoefficient N a) b characterRowVector
    hV (by
      unfold MontgomeryVaughanFiniteReduction.coefficientEnergy
      positivity) hC (by positivity : 0 ≤ (N : ℝ))
    (theorem83KernelScale_nonneg hscale) hbpos hlargeRows
    (padded_weightedCoefficientEnergy_le tail a b hbpos hbmajor)
    hrowKernel hthreshold
  rw [card_characterRows] at h
  push_cast at h
  simpa using h

/-- Conditional smooth Schur route with the remaining analytic premise
written in
its exact arithmetic form: a row sum of smooth character-quotient Dirichlet
sums.  The theorem is algebraically valid, but the premise at the advertised
source scale is an overstrong absolute-row surrogate; it must not be cited as
Montgomery (8.16). -/
theorem character_smooth_halasz_large_values_absorbed_of_twistedKernel
    {q N : ℕ} [NeZero q] (hN : 1 ≤ N)
    (tail : Finset ℕ) (a : ℕ → ℂ) (b : ℕ → ℝ)
    {T V C : ℝ}
    (hT : 0 ≤ T) (hV : 0 ≤ V) (hC : 0 ≤ C)
    (hscale : 1 ≤ (q : ℝ) * T)
    (hbpos : ∀ n ∈ smoothCarrier N tail, 0 < b n)
    (hbmajor : ∀ n ∈ dyadicSupport N, 1 ≤ b n)
    (W : DirichletCharacter ℂ q → Finset ℝ)
    (hsep : ∀ chi, OneSeparated (W chi))
    (hheight : ∀ chi, ∀ t ∈ W chi, |t| ≤ T)
    (hlarge : ∀ chi, ∀ t ∈ W chi,
      V ≤ ‖characterPacketPolynomial q (dyadicSupport N) a chi t‖)
    (htwistedKernel : ∀ row ∈ characterRows W,
      ∑ row' ∈ characterRows W,
          ‖smoothTwistedCharacterKernel (smoothCarrier N tail) b row row'‖ ≤
        C * ((N : ℝ) + ((characterRows W).card : ℝ) *
          theorem83KernelScale q T))
    (hthreshold :
      2 * C * MontgomeryVaughanFiniteReduction.coefficientEnergy a N *
          theorem83KernelScale q T ≤ V ^ 2) :
    (∑ chi : DirichletCharacter ℂ q, ((W chi).card : ℝ)) * V ^ 2 ≤
      2 * C * MontgomeryVaughanFiniteReduction.coefficientEnergy a N * N := by
  apply character_smooth_halasz_large_values_absorbed_sourceScale
    hN tail a b hT hV hC hscale hbpos hbmajor W hsep hheight hlarge
  · intro row hrow
    simpa only [weighted_characterGram_eq_smoothTwistedCharacterKernel] using
      htwistedKernel row hrow
  · exact hthreshold

end
end MAPMontgomeryTheorem83SmoothHalasz

#print axioms MAPMontgomeryTheorem83SmoothHalasz.finitePolynomial_paddedDyadicCoefficient
#print axioms MAPMontgomeryTheorem83SmoothHalasz.padded_weightedCoefficientEnergy_le
#print axioms MAPMontgomeryTheorem83SmoothHalasz.weighted_characterRow_diagonal_le_mass
#print axioms MAPMontgomeryTheorem83SmoothHalasz.weighted_characterRowKernel_le_of_mass_and_offDiagonalRowSum
#print axioms MAPMontgomeryTheorem83SmoothHalasz.finite_weighted_mean_square_le_of_operatorBound
#print axioms MAPMontgomeryTheorem83SmoothHalasz.finite_weighted_large_values_absorbed_of_operatorBound
#print axioms MAPMontgomeryTheorem83SmoothHalasz.correlationEnergy_le_of_weighted_rowKernel
#print axioms MAPMontgomeryTheorem83SmoothHalasz.correlationEnergy_le_mul_sum_norm_sq_of_weighted_rowKernel
#print axioms MAPMontgomeryTheorem83SmoothHalasz.finite_weighted_mean_square_le_of_rowKernel
#print axioms MAPMontgomeryTheorem83SmoothHalasz.finite_weighted_halasz_absorbed
#print axioms MAPMontgomeryTheorem83SmoothHalasz.character_smooth_mean_square_of_operatorBound
#print axioms MAPMontgomeryTheorem83SmoothHalasz.character_smooth_large_values_absorbed_of_operatorBound
#print axioms MAPMontgomeryTheorem83SmoothHalasz.character_smooth_mean_square_sourceScale
#print axioms MAPMontgomeryTheorem83SmoothHalasz.character_smooth_halasz_large_values_absorbed_sourceScale
