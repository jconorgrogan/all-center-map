import JutilaP53AggregateCorrelationLeaf
import MontgomeryInfiniteHalasz

/-!
# Common-phase infinite Halasz weld for Jutila p.53

The smoothing scales `M,N` vary in Jutila's integrations, but the phase used
in Lemma 7 is determined only by the detected Dirichlet polynomial.  This
module chooses that phase once and proves the finite-to-infinite correlation
passage uniformly for every positive summable weight.  No correlation-kernel
estimate is asserted.
-/

namespace MAPJutilaP53InfiniteHalaszWeld

open scoped BigOperators
open MAPJutilaDeterministicCore
open MAPMontgomeryInfiniteHalasz
open MAPJutilaP53AggregateCorrelationLeaf

noncomputable section

/-- The p.53 energy is definitionally the generic infinite Halasz energy. -/
theorem jutilaP53CorrelationEnergy_eq_infiniteCorrelationEnergy
    {q : ℕ} (rows : Finset (JutilaP53Row q)) (S : Finset ℕ)
    (alpha M N : ℝ) (eta : JutilaP53Row q → ℂ) :
    jutilaP53CorrelationEnergy rows S alpha M N eta =
      infiniteCorrelationEnergy rows
        (jutilaP53CorrelationWeight S M N) eta
        (jutilaP53Phase alpha) := rfl

/-- Absolute summability of the literal infinite p.53 energy. -/
theorem summable_jutilaP53CorrelationEnergy
    {q R : ℕ} (rows : Finset (JutilaP53Row q))
    {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 R)
    {alpha M N : ℝ} (hM : 0 < M) (hMN : M < N)
    (eta : JutilaP53Row q → ℂ)
    (hrow : ∀ row ∈ rows, alpha ≤ row.zero.re)
    (heta : ∀ row ∈ rows, ‖eta row‖ = 1) :
    Summable (fun n : ℕ =>
      jutilaP53CorrelationWeight S M N n *
        ‖∑ row ∈ rows,
          eta row * jutilaP53Phase alpha row n‖ ^ 2) := by
  let J : ℝ := rows.card
  apply Summable.of_nonneg_of_le
    (f := fun n : ℕ => jutilaP53CorrelationWeight S M N n * J ^ 2)
  · intro n
    exact mul_nonneg (jutilaP53CorrelationWeight_nonneg S hM hMN n)
      (sq_nonneg _)
  · intro n
    have hsum : ‖∑ row ∈ rows,
        eta row * jutilaP53Phase alpha row n‖ ≤ J := by
      calc
        ‖∑ row ∈ rows, eta row * jutilaP53Phase alpha row n‖ ≤
            ∑ row ∈ rows,
              ‖eta row * jutilaP53Phase alpha row n‖ := norm_sum_le _ _
        _ ≤ ∑ _row ∈ rows, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro row hr
          rw [norm_mul, heta row hr, one_mul]
          exact norm_jutilaP53Phase_le_one (hrow row hr) n
        _ = J := by simp [J]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) hsum 2)
      (jutilaP53CorrelationWeight_nonneg S hM hMN n)
  · exact (summable_jutilaP53CorrelationWeight hS hM hMN).mul_right (J ^ 2)

/-- Source-form Halasz with one phase choice valid for every admissible
weight.  This is the quantifier order needed before integrating in `M,N`. -/
theorem finite_halasz_common_phase
    {I K P : Type*} [DecidableEq I] [DecidableEq K]
    (rows : Finset I) (cols : Finset K)
    (a : K → ℂ) (v : I → K → ℂ) (weight : P → K → ℝ) (V : ℝ)
    (hV : 0 ≤ V)
    (hlarge : ∀ i ∈ rows, V ≤ ‖finitePolynomial cols a v i‖)
    (hweight : ∀ p k, k ∈ cols → 0 < weight p k) :
    ∃ eta : I → ℂ,
      (∀ i ∈ rows, ‖eta i‖ = 1) ∧
      ∀ p : P,
        ((rows.card : ℝ) * V) ^ 2 ≤
          (∑ k ∈ cols, ‖a k‖ ^ 2 / weight p k) *
            correlationEnergy rows cols (weight p) eta v := by
  let F : I → ℂ := finitePolynomial cols a v
  let eta : I → ℂ := fun i => alignPhase (F i)
  refine ⟨eta, (fun i _hi => norm_alignPhase (F i)), ?_⟩
  intro p
  have hcard : (rows.card : ℝ) * V ≤ ∑ i ∈ rows, ‖F i‖ := by
    calc
      (rows.card : ℝ) * V = ∑ _i ∈ rows, V := by simp
      _ ≤ ∑ i ∈ rows, ‖F i‖ := by
        apply Finset.sum_le_sum
        intro i hi
        exact hlarge i hi
  have hcardSq := pow_le_pow_left₀
    (mul_nonneg (Nat.cast_nonneg _) hV) hcard 2
  have halign : ((∑ i ∈ rows, ‖F i‖ : ℝ) : ℂ) =
      ∑ i ∈ rows, eta i * F i := by
    push_cast
    apply Finset.sum_congr rfl
    intro i hi
    exact (alignPhase_mul (F i)).symm
  have hinterchange : (∑ i ∈ rows, eta i * F i) =
      ∑ k ∈ cols, a k * (∑ i ∈ rows, eta i * v i k) := by
    dsimp [F, finitePolynomial]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hweighted := weighted_norm_sum_sq_le cols a
    (fun k => ∑ i ∈ rows, eta i * v i k) (weight p)
    (fun k hk => hweight p k hk)
  rw [← hinterchange, ← halign] at hweighted
  have hsum0 : 0 ≤ ∑ i ∈ rows, ‖F i‖ := by positivity
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsum0] at hweighted
  exact hcardSq.trans (by
    simpa [correlationEnergy, F] using hweighted)

/-- The common finite phase also controls the full infinite smooth energy.
The only inputs beyond finite Halasz are positivity, summability, and the
unit row-vector bound. -/
theorem finite_halasz_common_phase_to_infinite
    {I K P : Type*} [DecidableEq I] [DecidableEq K]
    (rows : Finset I) (cols : Finset K)
    (a : K → ℂ) (v : I → K → ℂ) (weight : P → K → ℝ)
    (V Q : ℝ)
    (hV : 0 ≤ V) (hQ : 0 ≤ Q)
    (hlarge : ∀ i ∈ rows, V ≤ ‖finitePolynomial cols a v i‖)
    (hweightPos : ∀ p k, k ∈ cols → 0 < weight p k)
    (hweight0 : ∀ p k, 0 ≤ weight p k)
    (hweightSummable : ∀ p, Summable (weight p))
    (hv : ∀ i k, ‖v i k‖ ≤ 1)
    (hquotient : ∀ p,
      (∑ k ∈ cols, ‖a k‖ ^ 2 / weight p k) ≤ Q) :
    ∃ eta : I → ℂ,
      (∀ i ∈ rows, ‖eta i‖ = 1) ∧
      ∀ p : P,
        ((rows.card : ℝ) * V) ^ 2 ≤
          Q * infiniteCorrelationEnergy rows (weight p) eta v := by
  obtain ⟨eta, heta, hfinite⟩ := finite_halasz_common_phase
    rows cols a v weight V hV hlarge hweightPos
  refine ⟨eta, heta, ?_⟩
  intro p
  have hfinite0 : 0 ≤ correlationEnergy rows cols (weight p) eta v := by
    unfold correlationEnergy
    exact Finset.sum_nonneg (fun k hk =>
      mul_nonneg (hweight0 p k) (sq_nonneg _))
  have hfiniteToInfinite :
      correlationEnergy rows cols (weight p) eta v ≤
        infiniteCorrelationEnergy rows (weight p) eta v := by
    exact (summable_infiniteCorrelationEnergy rows (weight p) eta v
      (hweight0 p) (hweightSummable p) heta hv).sum_le_tsum cols
        (fun k hk => mul_nonneg (hweight0 p k) (sq_nonneg _))
  calc
    ((rows.card : ℝ) * V) ^ 2 ≤
        (∑ k ∈ cols, ‖a k‖ ^ 2 / weight p k) *
          correlationEnergy rows cols (weight p) eta v := hfinite p
    _ ≤ Q * correlationEnergy rows cols (weight p) eta v :=
      mul_le_mul_of_nonneg_right (hquotient p) hfinite0
    _ ≤ Q * infiniteCorrelationEnergy rows (weight p) eta v :=
      mul_le_mul_of_nonneg_left hfiniteToInfinite hQ

end

end MAPJutilaP53InfiniteHalaszWeld

#print axioms MAPJutilaP53InfiniteHalaszWeld.finite_halasz_common_phase
#print axioms MAPJutilaP53InfiniteHalaszWeld.finite_halasz_common_phase_to_infinite
#print axioms MAPJutilaP53InfiniteHalaszWeld.summable_jutilaP53CorrelationEnergy
