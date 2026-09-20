import JutilaP53PseudocharacterSquareExpansion

/-!
# The finite `r,r'` expansion before Jutila's Lemma 2

Each character-pair kernel is expanded into the literal selected
pseudocharacter pairs.  Every component series is proved absolutely
summable from the exponential smoothing, so the finite sums may be moved
through the infinite Dirichlet series without a hidden convergence premise.
-/

namespace MAPJutilaP53PairRExpansion

open scoped BigOperators
open Complex
open MAPJutilaP53AggregateCorrelationLeaf
open MAPJutilaP53KernelSourceForm
open MAPJutilaP53PseudocharacterSquareExpansion

noncomputable section

private theorem summable_finset_sum
    {ι : Type*} [DecidableEq ι] (T : Finset ι)
    (f : ι → ℕ → ℂ) (hf : ∀ i ∈ T, Summable (f i)) :
    Summable (fun n : ℕ => ∑ i ∈ T, f i n) := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert a T ha ih =>
      simp_rw [Finset.sum_insert ha]
      exact (hf a (Finset.mem_insert_self a T)).add
        (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

def jutilaP53PairRTerm {q : ℕ}
    (M N : ℝ) (s : ℂ) (chi : DirichletCharacter ℂ q)
    (r r' n : ℕ) : ℂ :=
  ((n : ℝ)⁻¹ : ℂ) * normalizedP53PseudoAt r n *
    normalizedP53PseudoAt r' n *
    ((Real.exp (-((n : ℝ) / N)) -
      Real.exp (-((n : ℝ) / M))) : ℂ) *
    chi n * (n : ℂ) ^ (-s)

def jutilaP53PairRB {q : ℕ}
    (M N : ℝ) (s : ℂ) (chi : DirichletCharacter ℂ q)
    (r r' : ℕ) : ℂ :=
  ∑' n : ℕ, jutilaP53PairRTerm M N s chi r r' n

theorem sourceB_term_eq_pairR_doubleSum
    {q : ℕ} (S : Finset ℕ) (M N : ℝ) (s : ℂ)
    (chi : DirichletCharacter ℂ q) (n : ℕ) :
    (jutilaP53CorrelationWeight S M N n : ℂ) *
        chi n * (n : ℂ) ^ (-s) =
      ∑ r ∈ S, ∑ r' ∈ S,
        jutilaP53PairRTerm M N s chi r r' n := by
  unfold jutilaP53CorrelationWeight
  unfold MAPJutilaHalaszLargeValueFront.jutilaCorrelationWeight
  unfold jutilaP53PairRTerm
  push_cast
  rw [show ((jutilaP53PseudoReal S n) ^ 2 : ℂ) =
      ∑ r ∈ S, ∑ r' ∈ S,
        normalizedP53PseudoAt r n * normalizedP53PseudoAt r' n by
    exact pseudoReal_sq_eq_doubleSum S n]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro r' hr'
  ring

theorem norm_natCast_cpow_neg_le_one
    {n : ℕ} (hn : 0 < n) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖(n : ℂ) ^ (-s)‖ ≤ 1 := by
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [Complex.norm_natCast_cpow_of_pos hn]
  exact Real.rpow_le_one_of_one_le_of_nonpos hnOne (by simp; linarith)

theorem norm_pairRTerm_le_geometric
    {q : ℕ} {M N : ℝ} (hM : 0 < M) (hMN : M < N)
    {s : ℂ} (hs : 0 ≤ s.re) (chi : DirichletCharacter ℂ q)
    {r r' : ℕ} (hr : 0 < r) (hr' : 0 < r') (n : ℕ) :
    ‖jutilaP53PairRTerm M N s chi r r' n‖ ≤
      (Real.exp (-(1 / N))) ^ n := by
  by_cases hn0 : n = 0
  · subst n
    simp [jutilaP53PairRTerm]
  have hn : 0 < n := Nat.pos_of_ne_zero hn0
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hinv : (n : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hnOne
  have hN : 0 < N := hM.trans hMN
  have hquot : (n : ℝ) / N < (n : ℝ) / M :=
    (div_lt_div_iff_of_pos_left hnR hN hM).2 hMN
  have hdiff0 : 0 ≤ Real.exp (-((n : ℝ) / N)) -
      Real.exp (-((n : ℝ) / M)) :=
    sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith))
  have hdiff : Real.exp (-((n : ℝ) / N)) -
      Real.exp (-((n : ℝ) / M)) ≤ Real.exp (-((n : ℝ) / N)) := by
    linarith [Real.exp_nonneg (-((n : ℝ) / M))]
  have hrNorm := norm_normalizedP53PseudoAt_le_one (n := n) hr
  have hr'Norm := norm_normalizedP53PseudoAt_le_one (n := n) hr'
  have hchi := DirichletCharacter.norm_le_one chi n
  have hpow := norm_natCast_cpow_neg_le_one hn hs
  have hnonneg : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr hnR.le
  unfold jutilaP53PairRTerm
  simp only [norm_mul]
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hnR]
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hdiff0]
  calc
    (n : ℝ)⁻¹ * ‖normalizedP53PseudoAt r n‖ *
          ‖normalizedP53PseudoAt r' n‖ *
          (Real.exp (-((n : ℝ) / N)) - Real.exp (-((n : ℝ) / M))) *
          ‖chi n‖ * ‖(n : ℂ) ^ (-s)‖ ≤
        1 * 1 * 1 * Real.exp (-((n : ℝ) / N)) * 1 * 1 := by
      gcongr
    _ = (Real.exp (-(1 / N))) ^ n := by
      rw [← Real.exp_nat_mul]
      ring

theorem summable_jutilaP53PairRTerm
    {q : ℕ} {M N : ℝ} (hM : 0 < M) (hMN : M < N)
    {s : ℂ} (hs : 0 ≤ s.re) (chi : DirichletCharacter ℂ q)
    {r r' : ℕ} (hr : 0 < r) (hr' : 0 < r') :
    Summable (jutilaP53PairRTerm M N s chi r r') := by
  let a : ℝ := Real.exp (-(1 / N))
  have hN : 0 < N := hM.trans hMN
  have haPos : 0 < a := by dsimp [a]; positivity
  have haLt : a < 1 := by
    dsimp [a]
    have hinv : 0 < 1 / N := one_div_pos.mpr hN
    have : -(1 / N) < 0 := by linarith
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr this
  have hgeo : Summable (fun n : ℕ => a ^ n) :=
    summable_geometric_of_norm_lt_one
      (show ‖a‖ < 1 by
        simpa [Real.norm_eq_abs, abs_of_pos haPos] using haLt)
  exact Summable.of_norm_bounded hgeo (fun n => by
    simpa [a] using norm_pairRTerm_le_geometric hM hMN hs chi hr hr' n)

/-- The complete source `B` series is the finite double sum of selected
`r,r'` components. -/
theorem jutilaP53SourceB_eq_pairR_doubleSum
    {q R : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 R)
    {M N : ℝ} (hM : 0 < M) (hMN : M < N)
    {s : ℂ} (hs : 0 ≤ s.re) (chi : DirichletCharacter ℂ q) :
    jutilaP53SourceB S M N s chi =
      ∑ r ∈ S, ∑ r' ∈ S,
        jutilaP53PairRB M N s chi r r' := by
  have hpos : ∀ r ∈ S, 0 < r := by
    intro r hr
    exact (Finset.mem_Icc.mp (hS hr)).1
  have hsummable : ∀ r ∈ S, ∀ r' ∈ S,
      Summable (jutilaP53PairRTerm M N s chi r r') := by
    intro r hr r' hr'
    exact summable_jutilaP53PairRTerm hM hMN hs chi
      (hpos r hr) (hpos r' hr')
  have hinner : ∀ r ∈ S,
      Summable (fun n : ℕ => ∑ r' ∈ S,
        jutilaP53PairRTerm M N s chi r r' n) := by
    intro r hr
    exact summable_finset_sum S
      (fun r' n => jutilaP53PairRTerm M N s chi r r' n)
      (fun r' hr' => hsummable r hr r' hr')
  unfold jutilaP53SourceB jutilaP53PairRB
  calc
    (∑' n : ℕ, (jutilaP53CorrelationWeight S M N n : ℂ) *
        chi n * (n : ℂ) ^ (-s)) =
        ∑' n : ℕ, ∑ r ∈ S, ∑ r' ∈ S,
          jutilaP53PairRTerm M N s chi r r' n := by
      apply tsum_congr
      exact sourceB_term_eq_pairR_doubleSum S M N s chi
    _ = ∑ r ∈ S, ∑ r' ∈ S,
        ∑' n : ℕ, jutilaP53PairRTerm M N s chi r r' n := by
      rw [Summable.tsum_finsetSum hinner]
      apply Finset.sum_congr rfl
      intro r hr
      rw [Summable.tsum_finsetSum (fun r' hr' => hsummable r hr r' hr')]

end

end MAPJutilaP53PairRExpansion

#print axioms MAPJutilaP53PairRExpansion.sourceB_term_eq_pairR_doubleSum
#print axioms MAPJutilaP53PairRExpansion.summable_jutilaP53PairRTerm
#print axioms MAPJutilaP53PairRExpansion.jutilaP53SourceB_eq_pairR_doubleSum
