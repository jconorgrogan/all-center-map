import GoldfeldConditionalDirichletContinuation

/-!
# The `j = 1`, `t = 0` derivative form of Lemma 11.2

This module welds the analytic complete-block continuation to the finite
Pólya--Vinogradov/Abel estimate.
-/

namespace MAPGoldfeldSiegel

open Complex Set LSeries Filter Topology
open scoped BigOperators

noncomputable section

/-- A finite initial interval is the disjoint union of its complete residue
blocks. -/
theorem sum_range_mul_eq_sum_blocks
    {N : ℕ} [NeZero N] {E : Type*} [AddCommMonoid E]
    (f : ℕ → E) (R : ℕ) :
    (∑ m ∈ Finset.range R, ∑ j : ZMod N, f (j.val + N * m)) =
      ∑ n ∈ Finset.range (N * R), f n := by
  have hblock (m : ℕ) :
      (∑ j : ZMod N, f (j.val + N * m)) =
        ∑ k ∈ Finset.range N, f (N * m + k) := by
    apply Finset.sum_bij (fun j _ => j.val)
    · intro j hj
      exact Finset.mem_range.mpr j.val_lt
    · intro a ha b hb hab
      exact ZMod.val_injective N hab
    · intro k hk
      have hklt := Finset.mem_range.mp hk
      refine ⟨(k : ZMod N), Finset.mem_univ _, ?_⟩
      exact ZMod.val_natCast_of_lt hklt
    · intro j hj
      congr 1
      omega
  induction R with
  | zero => simp
  | succ R ih =>
      rw [Finset.sum_range_succ, ih]
      rw [show N * (R + 1) = N * R + N by ring, Finset.sum_range_add]
      rw [hblock R]

/-- Shifted form: positive complete blocks cover the interval beginning at
the modulus. -/
theorem sum_positive_blocks_eq_sum_Ico
    {N : ℕ} [NeZero N] {E : Type*} [AddCommMonoid E]
    (f : ℕ → E) (R : ℕ) :
    (∑ m ∈ Finset.range R, ∑ j : ZMod N, f (j.val + N * (m + 1))) =
      ∑ n ∈ Finset.Ico N (N * (R + 1)), f n := by
  have h := sum_range_mul_eq_sum_blocks (N := N) (fun n => f (n + N)) R
  rw [Finset.sum_Ico_eq_sum_range]
  simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- The derivative term on the real axis is exactly the source weight times
the character coefficient. -/
theorem term_logMul_eq_firstDerivativeWeight_mul
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N)
    {sigma : ℝ} {n : ℕ} (hn : n ≠ 0) :
    LSeries.term (LSeries.logMul (fun k : ℕ => chi k)) (sigma : ℂ) n =
      (firstDerivativeWeight sigma n : ℂ) * chi (n : ZMod N) := by
  rw [LSeries.term_of_ne_zero hn]
  change (Complex.log (n : ℂ) * chi (n : ZMod N)) / (n : ℂ) ^ (sigma : ℂ) = _
  rw [firstDerivativeWeight]
  push_cast
  rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
  have hcast : (((n : ℝ) : ℂ)) = (n : ℂ) := by norm_cast
  rw [hcast]
  ring

/-- Derivative of one positive complete block at a real point. -/
theorem deriv_characterLBlock_eq_neg_weight_sum
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N)
    {sigma : ℝ} (r : ℕ) :
    deriv (characterLBlock chi r) (sigma : ℂ) =
      -(∑ j : ZMod N,
        (firstDerivativeWeight sigma (j.val + N * r) : ℂ) *
          chi ((j.val + N * r : ℕ) : ZMod N)) := by
  unfold characterLBlock
  rw [deriv_fun_sum]
  · rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [(LSeries.hasDerivAt_term (fun n : ℕ => chi n)
      (j.val + N * r) (sigma : ℂ)).deriv]
    congr 1
    by_cases hn : j.val + N * r = 0
    · simp [hn, LSeries.term, firstDerivativeWeight]
    · exact term_logMul_eq_firstDerivativeWeight_mul chi hn
  · intro j hj
    exact (LSeries.hasDerivAt_term (fun n : ℕ => chi n)
      (j.val + N * r) (sigma : ℂ)).differentiableAt

/-- Finite sums of centered block derivatives are exactly the differentiated
ordered Dirichlet sum over the corresponding positive interval. -/
theorem sum_deriv_centeredCharacterLBlock_eq_neg_sum_Ico
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1)
    (sigma : ℝ) (R : ℕ) :
    (∑ m ∈ Finset.range R, deriv (centeredCharacterLBlock chi m) (sigma : ℂ)) =
      -(∑ n ∈ Finset.Ico N (N * (R + 1)),
        (firstDerivativeWeight sigma n : ℂ) * chi (n : ZMod N)) := by
  calc
    (∑ m ∈ Finset.range R, deriv (centeredCharacterLBlock chi m) (sigma : ℂ)) =
        ∑ m ∈ Finset.range R, deriv (characterLBlock chi (m + 1)) (sigma : ℂ) := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Filter.EventuallyEq.deriv_eq
      exact Filter.Eventually.of_forall fun z => centeredCharacterLBlock_eq chi hchi m z
    _ = ∑ m ∈ Finset.range R,
        -(∑ j : ZMod N,
          (firstDerivativeWeight sigma (j.val + N * (m + 1)) : ℂ) *
            chi ((j.val + N * (m + 1) : ℕ) : ZMod N)) := by
      apply Finset.sum_congr rfl
      intro m hm
      exact deriv_characterLBlock_eq_neg_weight_sum chi (m + 1)
    _ = -(∑ m ∈ Finset.range R, ∑ j : ZMod N,
          (firstDerivativeWeight sigma (j.val + N * (m + 1)) : ℂ) *
            chi ((j.val + N * (m + 1) : ℕ) : ZMod N)) := by
      rw [Finset.sum_neg_distrib]
    _ = -(∑ n ∈ Finset.Ico N (N * (R + 1)),
        (firstDerivativeWeight sigma n : ℂ) * chi (n : ZMod N)) := by
      congr 1
      exact sum_positive_blocks_eq_sum_Ico
        (N := N) (fun n => (firstDerivativeWeight sigma n : ℂ) * chi (n : ZMod N)) R

/-- The ordered differentiated Dirichlet sums at complete-block endpoints
converge to the derivative of Mathlib's analytically continued L-function. -/
theorem tendsto_neg_firstDerivativeWeight_sum_blocks
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1)
    {sigma : ℝ} (hsigma : 0 < sigma) :
    Filter.Tendsto
      (fun R : ℕ => -(∑ n ∈ Finset.range (N * (R + 1)),
        (firstDerivativeWeight sigma n : ℂ) * chi (n : ZMod N)))
      Filter.atTop
      (nhds (deriv (DirichletCharacter.LFunction chi) (sigma : ℂ))) := by
  let q : ℕ → ℂ := fun n =>
    (firstDerivativeWeight sigma n : ℂ) * chi (n : ZMod N)
  have hHas := hasSum_deriv_centeredCharacterLBlock_of_pos_re
    chi (s := (sigma : ℂ)) (by simpa using hsigma)
  have ht := hHas.tendsto_sum_nat
  have htadd := (tendsto_const_nhds.add ht :
    Filter.Tendsto
      (fun R : ℕ => deriv (characterLBlock chi 0) (sigma : ℂ) +
        ∑ m ∈ Finset.range R, deriv (centeredCharacterLBlock chi m) (sigma : ℂ))
      Filter.atTop
      (nhds (deriv (characterLBlock chi 0) (sigma : ℂ) +
        deriv (fun w : ℂ => ∑' m : ℕ, centeredCharacterLBlock chi m w) (sigma : ℂ))))
  have hblock0 : (∑ j : ZMod N, q j.val) = ∑ n ∈ Finset.range N, q n := by
    have h := sum_range_mul_eq_sum_blocks (N := N) q 1
    simpa [q] using h
  have hfinite : ∀ R : ℕ,
      deriv (characterLBlock chi 0) (sigma : ℂ) +
          ∑ m ∈ Finset.range R, deriv (centeredCharacterLBlock chi m) (sigma : ℂ) =
        -(∑ n ∈ Finset.range (N * (R + 1)), q n) := by
    intro R
    rw [deriv_characterLBlock_eq_neg_weight_sum chi 0]
    rw [sum_deriv_centeredCharacterLBlock_eq_neg_sum_Ico chi hchi sigma R]
    change -(∑ j : ZMod N, q j.val) -
        ∑ n ∈ Finset.Ico N (N * (R + 1)), q n = _
    rw [hblock0]
    have hNend : N ≤ N * (R + 1) := by
      have hN0 : 0 < N := NeZero.pos N
      nlinarith
    calc
      -(∑ n ∈ Finset.range N, q n) -
          ∑ n ∈ Finset.Ico N (N * (R + 1)), q n =
          -((∑ n ∈ Finset.range N, q n) +
            ∑ n ∈ Finset.Ico N (N * (R + 1)), q n) := by ring
      _ = -(∑ n ∈ Finset.range (N * (R + 1)), q n) := by
        rw [Finset.sum_range_add_sum_Ico q hNend]
  have ht' : Filter.Tendsto
      (fun R : ℕ => -(∑ n ∈ Finset.range (N * (R + 1)), q n))
      Filter.atTop
      (nhds (deriv (characterLBlock chi 0) (sigma : ℂ) +
        deriv (fun w : ℂ => ∑' m : ℕ, centeredCharacterLBlock chi m w) (sigma : ℂ))) := by
    exact htadd.congr' (Filter.Eventually.of_forall hfinite)
  have hfirst : DifferentiableAt ℂ (characterLBlock chi 0) (sigma : ℂ) := by
    unfold characterLBlock
    apply DifferentiableAt.fun_sum
    intro j hj
    exact (LSeries.hasDerivAt_term (fun n : ℕ => chi n) j.val (sigma : ℂ)).differentiableAt
  have hcond := differentiableAt_conditionalCharacterLSeries_of_pos_re
    chi (s := (sigma : ℂ)) (by simpa using hsigma)
  have htail : DifferentiableAt ℂ
      (fun w : ℂ => ∑' m : ℕ, centeredCharacterLBlock chi m w) (sigma : ℂ) := by
    rw [show (fun w : ℂ => ∑' m : ℕ, centeredCharacterLBlock chi m w) =
        conditionalCharacterLSeries chi - characterLBlock chi 0 by
      funext w
      simp [conditionalCharacterLSeries]]
    exact hcond.sub hfirst
  have hsplit :
      deriv (conditionalCharacterLSeries chi) (sigma : ℂ) =
        deriv (characterLBlock chi 0) (sigma : ℂ) +
          deriv (fun w : ℂ => ∑' m : ℕ, centeredCharacterLBlock chi m w) (sigma : ℂ) := by
    unfold conditionalCharacterLSeries
    exact deriv_add hfirst htail
  have hident := deriv_conditionalCharacterLSeries_eq_deriv_LFunction_of_pos_re
    chi hchi (s := (sigma : ℂ)) (by simpa using hsigma)
  change Filter.Tendsto (fun R : ℕ => -(∑ n ∈ Finset.range (N * (R + 1)), q n))
      Filter.atTop (nhds (deriv (DirichletCharacter.LFunction chi) (sigma : ℂ)))
  rw [← hident, hsplit]
  exact ht'

/-- Exact `t = 0` derivative estimate after the source cutoff, before the
elementary small-sum bound and the choice `K ≍ √N`. -/
theorem norm_deriv_LFunction_le_initial_add_PV_tail
    {N : ℕ} [NeZero N] (hN : 2 ≤ N)
    (chi : DirichletCharacter ℂ N) (hprim : chi.IsPrimitive)
    (hchi : chi ≠ 1) (hreal : chi ^ 2 = 1)
    {sigma : ℝ} (hsigma : 1 / 2 ≤ sigma)
    {K : ℕ} (hK : 9 ≤ K) :
    ‖deriv (DirichletCharacter.LFunction chi) (sigma : ℂ)‖ ≤
      ‖∑ n ∈ Finset.range (K + 1),
        (firstDerivativeWeight sigma n : ℂ) * chi (n : ZMod N)‖ +
      2 * (Real.sqrt N * (1 + Real.log N)) *
        firstDerivativeWeight sigma (K + 1) := by
  let q : ℕ → ℂ := fun n =>
    (firstDerivativeWeight sigma n : ℂ) * chi (n : ZMod N)
  let D : ℂ := deriv (DirichletCharacter.LFunction chi) (sigma : ℂ)
  let I : ℂ := ∑ n ∈ Finset.range (K + 1), q n
  have hsigmaPos : 0 < sigma := lt_of_lt_of_le (by norm_num) hsigma
  have hneg := tendsto_neg_firstDerivativeWeight_sum_blocks chi hchi hsigmaPos
  have htotal : Filter.Tendsto
      (fun R : ℕ => ∑ n ∈ Finset.range (N * (R + 1)), q n)
      Filter.atTop (nhds (-D)) := by
    have ht := hneg.neg
    simpa [q, D] using ht
  have hsub : Filter.Tendsto
      (fun R : ℕ => (∑ n ∈ Finset.range (N * (R + 1)), q n) - I)
      Filter.atTop (nhds ((-D) - I)) :=
    htotal.sub tendsto_const_nhds
  have heq :
      (fun R : ℕ => (∑ n ∈ Finset.range (N * (R + 1)), q n) - I) =ᶠ[Filter.atTop]
        (fun R : ℕ => ∑ n ∈ Finset.Ioc K (N * (R + 1) - 1), q n) := by
    filter_upwards [Filter.eventually_gt_atTop K] with R hR
    have hNpos : 0 < N := NeZero.pos N
    let E : ℕ := N * (R + 1)
    have hKE : K + 1 ≤ E := by
      dsimp [E]
      have hNone : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
      nlinarith
    have hEpos : 0 < E := Nat.mul_pos hNpos (Nat.succ_pos R)
    have hset : Finset.Ioc K (E - 1) = Finset.Ico (K + 1) E := by
      ext n
      simp only [Finset.mem_Ioc, Finset.mem_Ico]
      omega
    rw [hset]
    have hsplit := Finset.sum_range_add_sum_Ico q hKE
    dsimp [I, E]
    rw [← hsplit]
    ring
  have htail : Filter.Tendsto
      (fun R : ℕ => ∑ n ∈ Finset.Ioc K (N * (R + 1) - 1), q n)
      Filter.atTop (nhds ((-D) - I)) := hsub.congr' heq
  have htailBound : ‖(-D) - I‖ ≤
      2 * (Real.sqrt N * (1 + Real.log N)) *
        firstDerivativeWeight sigma (K + 1) := by
    apply le_of_tendsto htail.norm
    filter_upwards [Filter.eventually_gt_atTop K] with R hR
    have hNpos : 0 < N := NeZero.pos N
    have hKM : K < N * (R + 1) - 1 := by
      have hscale : R + 1 ≤ N * (R + 1) :=
        Nat.le_mul_of_pos_left (R + 1) hNpos
      omega
    change ‖∑ n ∈ Finset.Ioc K (N * (R + 1) - 1),
      (firstDerivativeWeight sigma n : ℂ) * chi (n : ZMod N)‖ ≤ _
    exact primitive_quadratic_firstDerivative_tail_finite hN chi hprim hreal
      hsigma hK hKM
  have htriangle : ‖D‖ ≤ ‖I‖ + ‖(-D) - I‖ := by
    calc
      ‖D‖ = ‖-(((-D) - I) + I)‖ := by congr 1 <;> ring
      _ = ‖((-D) - I) + I‖ := norm_neg _
      _ ≤ ‖(-D) - I‖ + ‖I‖ := norm_add_le _ _
      _ = ‖I‖ + ‖(-D) - I‖ := add_comm _ _
  exact htriangle.trans (by
    simpa [I, add_comm] using add_le_add_left htailBound ‖I‖)

/-- Source small-sum estimate for one differentiated term below a cutoff. -/
theorem firstDerivativeWeight_le_cutoff
    {sigma : ℝ} (hsigmaHalf : 1 / 2 ≤ sigma) (hsigmaOne : sigma ≤ 1)
    {n K : ℕ} (hn : 1 ≤ n) (hnK : n ≤ K) :
    firstDerivativeWeight sigma n ≤
      Real.rpow (K : ℝ) (1 - sigma) * Real.log K * (n : ℝ)⁻¹ := by
  have hnPos : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hKPos : (0 : ℝ) < K := hnPos.trans_le (by exact_mod_cast hnK)
  have hexp : 0 ≤ 1 - sigma := sub_nonneg.mpr hsigmaOne
  have hpow : Real.rpow (n : ℝ) (1 - sigma) ≤
      Real.rpow (K : ℝ) (1 - sigma) :=
    Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast hnK) hexp
  have hlog : Real.log n ≤ Real.log K :=
    Real.log_le_log hnPos (by exact_mod_cast hnK)
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hKlog0 : 0 ≤ Real.log K := Real.log_nonneg (by exact_mod_cast hn.trans hnK)
  have hinv0 : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg n)
  have hrewrite : firstDerivativeWeight sigma n =
      Real.log n * Real.rpow (n : ℝ) (1 - sigma) * (n : ℝ)⁻¹ := by
    rw [firstDerivativeWeight, div_eq_mul_inv]
    rw [← Real.rpow_neg hnPos.le]
    rw [show -sigma = (1 - sigma) + (-1) by ring,
      Real.rpow_add hnPos]
    rw [Real.rpow_neg_one]
    simp only [Real.rpow_eq_pow, mul_comm, mul_assoc]
  rw [hrewrite]
  calc
    Real.log n * Real.rpow (n : ℝ) (1 - sigma) * (n : ℝ)⁻¹ ≤
        Real.log K * Real.rpow (K : ℝ) (1 - sigma) * (n : ℝ)⁻¹ := by
      gcongr
      exact Real.rpow_nonneg (Nat.cast_nonneg n) _
    _ = Real.rpow (K : ℝ) (1 - sigma) * Real.log K * (n : ℝ)⁻¹ := by ring

/-- Trivial estimation of the differentiated Dirichlet sum below the source
cutoff, retaining the exponent `K^(1-sigma)`. -/
theorem norm_firstDerivative_initialSum_le
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N)
    {sigma : ℝ} (hsigmaHalf : 1 / 2 ≤ sigma) (hsigmaOne : sigma ≤ 1)
    {K : ℕ} (hK : 1 ≤ K) :
    ‖∑ n ∈ Finset.range (K + 1),
        (firstDerivativeWeight sigma n : ℂ) * chi (n : ZMod N)‖ ≤
      Real.rpow (K : ℝ) (1 - sigma) * Real.log K *
        (1 + Real.log K) := by
  let C : ℝ := Real.rpow (K : ℝ) (1 - sigma) * Real.log K
  have hKPos : (0 : ℝ) < K := by exact_mod_cast (Nat.zero_lt_of_lt hK)
  have hC : 0 ≤ C := mul_nonneg
    (Real.rpow_nonneg (Nat.cast_nonneg K) _) (Real.log_nonneg (by exact_mod_cast hK))
  have hsumNorm :
      (∑ n ∈ Finset.range (K + 1),
        ‖(firstDerivativeWeight sigma n : ℂ) * chi (n : ZMod N)‖) ≤
      C * ∑ n ∈ Finset.Icc 1 K, ((n : ℝ)⁻¹) := by
    rw [show Finset.range (K + 1) = {0} ∪ Finset.Icc 1 K by
      ext n
      simp
      omega]
    rw [Finset.sum_union]
    · simp only [Finset.sum_singleton, firstDerivativeWeight, Nat.cast_zero,
        Real.log_zero, zero_div, Complex.ofReal_zero, zero_mul, norm_zero, zero_add]
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro n hnFin
      have hnI := Finset.mem_Icc.mp hnFin
      rw [norm_mul, norm_real, Real.norm_eq_abs]
      change |firstDerivativeWeight sigma n| * ‖chi (n : ZMod N)‖ ≤ _
      rw [abs_of_nonneg (firstDerivativeWeight_nonneg hnI.1)]
      calc
        firstDerivativeWeight sigma n * ‖chi (n : ZMod N)‖ ≤
            firstDerivativeWeight sigma n * 1 :=
          mul_le_mul_of_nonneg_left (chi.norm_le_one n)
            (firstDerivativeWeight_nonneg hnI.1)
        _ ≤ C * (n : ℝ)⁻¹ := by
          simpa [C] using
            (firstDerivativeWeight_le_cutoff hsigmaHalf hsigmaOne hnI.1 hnI.2)
    · simp
  calc
    ‖∑ n ∈ Finset.range (K + 1),
        (firstDerivativeWeight sigma n : ℂ) * chi (n : ZMod N)‖
        ≤ ∑ n ∈ Finset.range (K + 1),
          ‖(firstDerivativeWeight sigma n : ℂ) * chi (n : ZMod N)‖ := norm_sum_le _ _
    _ ≤ C * ∑ n ∈ Finset.Icc 1 K, ((n : ℝ)⁻¹) := hsumNorm
    _ = C * (harmonic K : ℝ) := by rw [sum_Icc_inv_eq_harmonic_real]
    _ ≤ C * (1 + Real.log K) := by
      exact mul_le_mul_of_nonneg_left (harmonic_le_one_add_log K) hC
    _ = Real.rpow (K : ℝ) (1 - sigma) * Real.log K *
        (1 + Real.log K) := by rfl

/-- The exact `t = 0`, `j = 1` cutoff form of Koukoulopoulos, Lemma 11.2,
specialized to primitive quadratic characters.  The source cutoff is chosen at
`9 * ceil (sqrt N)`; the two displayed terms are respectively the trivial
initial segment and the Pólya--Vinogradov/Abel tail. -/
theorem primitive_quadratic_deriv_LFunction_t0_cutoff
    {N : ℕ} [NeZero N] (hN : 2 ≤ N)
    (chi : DirichletCharacter ℂ N)
    (hprim : chi.IsPrimitive) (hchi : chi ≠ 1) (hreal : chi ^ 2 = 1)
    {sigma : ℝ} (hsigmaHalf : 1 / 2 ≤ sigma) (hsigmaOne : sigma ≤ 1) :
    let K := 9 * Nat.ceil (Real.sqrt N)
    ‖deriv (DirichletCharacter.LFunction chi) (sigma : ℂ)‖ ≤
      Real.rpow (K : ℝ) (1 - sigma) * Real.log K *
          (1 + Real.log K) +
        2 * (Real.sqrt N * (1 + Real.log N)) *
          firstDerivativeWeight sigma (K + 1) := by
  let K := 9 * Nat.ceil (Real.sqrt N)
  have hsqrtPos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 (by
    exact_mod_cast (Nat.zero_lt_of_lt hN))
  have hceil : 1 ≤ Nat.ceil (Real.sqrt N) :=
    (Nat.one_le_iff_ne_zero).2 (ne_of_gt (Nat.ceil_pos.2 hsqrtPos))
  have hK9 : 9 ≤ K := by
    dsimp [K]
    omega
  have hraw := norm_deriv_LFunction_le_initial_add_PV_tail
    hN chi hprim hchi hreal hsigmaHalf hK9
  have hinitial := norm_firstDerivative_initialSum_le chi hsigmaHalf hsigmaOne
    (show 1 ≤ K by omega)
  exact hraw.trans (add_le_add hinitial (le_refl _))

/-- Elementary location of the integer cutoff used above. -/
theorem goldfeldCutoff_bounds
    {N : ℕ} (hN : 2 ≤ N) :
    let K := 9 * Nat.ceil (Real.sqrt N)
    Real.sqrt N ≤ (K : ℝ) ∧
      (K : ℝ) ≤ 18 * Real.sqrt N ∧
      ((K + 1 : ℕ) : ℝ) ≤ 19 * (N : ℝ) := by
  let K := 9 * Nat.ceil (Real.sqrt N)
  have hNreal : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hRone : (1 : ℝ) ≤ Real.sqrt N := Real.one_le_sqrt.2 (by linarith)
  have hceilLower : Real.sqrt (N : ℝ) ≤ (Nat.ceil (Real.sqrt N) : ℝ) :=
    Nat.le_ceil _
  have hceilUpper : (Nat.ceil (Real.sqrt N) : ℝ) ≤ 2 * Real.sqrt N :=
    Nat.ceil_le_two_mul (by linarith)
  have hRnonneg : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  have hRsq : (Real.sqrt (N : ℝ)) ^ 2 = N :=
    Real.sq_sqrt (by positivity)
  have hRleN : Real.sqrt (N : ℝ) ≤ N := by
    nlinarith [mul_nonneg hRnonneg (sub_nonneg.mpr hRone)]
  have hKlower : Real.sqrt (N : ℝ) ≤ (K : ℝ) := by
    rw [show (K : ℝ) = 9 * (Nat.ceil (Real.sqrt N) : ℝ) by
      norm_num [K]]
    nlinarith [show 0 ≤ (Nat.ceil (Real.sqrt N) : ℝ) by positivity]
  have hKupper : (K : ℝ) ≤ 18 * Real.sqrt N := by
    rw [show (K : ℝ) = 9 * (Nat.ceil (Real.sqrt N) : ℝ) by
      norm_num [K]]
    nlinarith
  refine ⟨hKlower, hKupper, ?_⟩
  rw [show (((K + 1 : ℕ) : ℝ)) = (K : ℝ) + 1 by norm_num]
  nlinarith

/-- The two cutoff logarithms cost only fixed multiples of `1 + log N`. -/
theorem goldfeldCutoff_log_bounds
    {N : ℕ} (hN : 2 ≤ N) :
    let K := 9 * Nat.ceil (Real.sqrt N)
    Real.log K ≤ 17 * (1 + Real.log N) ∧
      Real.log ((K + 1 : ℕ) : ℝ) ≤ 18 * (1 + Real.log N) := by
  let K := 9 * Nat.ceil (Real.sqrt N)
  obtain ⟨_, hKupper, hKsuccUpper⟩ := goldfeldCutoff_bounds hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hNlog0 : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hRleN : Real.sqrt (N : ℝ) ≤ N := by
    have hRone : (1 : ℝ) ≤ Real.sqrt N := Real.one_le_sqrt.2 (by
      exact_mod_cast (show 1 ≤ N by omega))
    have hRsq := Real.sq_sqrt (show (0 : ℝ) ≤ N by positivity)
    nlinarith [mul_nonneg (Real.sqrt_nonneg (N : ℝ)) (sub_nonneg.mpr hRone)]
  have hKpos : (0 : ℝ) < K := by
    have : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.2 hNpos
    exact this.trans_le (goldfeldCutoff_bounds hN).1
  have hlog18 : Real.log (18 : ℝ) ≤ 17 := by
    nlinarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 18 by norm_num)]
  have hlog19 : Real.log (19 : ℝ) ≤ 18 := by
    nlinarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 19 by norm_num)]
  constructor
  · calc
      Real.log (K : ℝ) ≤ Real.log (18 * (N : ℝ)) :=
        Real.log_le_log hKpos (hKupper.trans (by nlinarith))
      _ = Real.log 18 + Real.log (N : ℝ) := by
        rw [Real.log_mul (by norm_num : (18 : ℝ) ≠ 0) hNpos.ne']
      _ ≤ 17 * (1 + Real.log (N : ℝ)) := by nlinarith
  · have hKsuccPos : (0 : ℝ) < ((K + 1 : ℕ) : ℝ) := by positivity
    calc
      Real.log ((K + 1 : ℕ) : ℝ) ≤ Real.log (19 * (N : ℝ)) :=
        Real.log_le_log hKsuccPos hKsuccUpper
      _ = Real.log 19 + Real.log (N : ℝ) := by
        rw [Real.log_mul (by norm_num : (19 : ℝ) ≠ 0) hNpos.ne']
      _ ≤ 18 * (1 + Real.log (N : ℝ)) := by nlinarith

/-- The power of the integer cutoff has the source conductor exponent. -/
theorem goldfeldCutoff_rpow_le
    {N : ℕ} (hN : 2 ≤ N)
    {sigma : ℝ} (hsigmaHalf : 1 / 2 ≤ sigma) (hsigmaOne : sigma ≤ 1) :
    let K := 9 * Nat.ceil (Real.sqrt N)
    Real.rpow (K : ℝ) (1 - sigma) ≤
      18 * Real.rpow (Real.sqrt N) (1 - sigma) := by
  let K := 9 * Nat.ceil (Real.sqrt N)
  have hKupper := (goldfeldCutoff_bounds hN).2.1
  have hexp0 : 0 ≤ 1 - sigma := sub_nonneg.mpr hsigmaOne
  have hexp1 : 1 - sigma ≤ 1 := by linarith
  have h18pow : Real.rpow (18 : ℝ) (1 - sigma) ≤ 18 := by
    have := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 18 by norm_num) hexp1
    simpa [Real.rpow_one, Real.rpow_eq_pow] using this
  calc
    Real.rpow (K : ℝ) (1 - sigma) ≤
        Real.rpow (18 * Real.sqrt N) (1 - sigma) :=
      Real.rpow_le_rpow (by positivity) hKupper hexp0
    _ = Real.rpow (18 : ℝ) (1 - sigma) *
        Real.rpow (Real.sqrt N) (1 - sigma) := by
      simp only [Real.rpow_eq_pow]
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 18) (Real.sqrt_nonneg _)]
    _ ≤ 18 * Real.rpow (Real.sqrt N) (1 - sigma) :=
      mul_le_mul_of_nonneg_right h18pow (Real.rpow_nonneg (Real.sqrt_nonneg _) _)

/-- The Abel-tail weight at the source cutoff, with its negative conductor
power made explicit. -/
theorem firstDerivativeWeight_goldfeldCutoff_le
    {N : ℕ} (hN : 2 ≤ N)
    {sigma : ℝ} (hsigmaHalf : 1 / 2 ≤ sigma) :
    let K := 9 * Nat.ceil (Real.sqrt N)
    firstDerivativeWeight sigma (K + 1) ≤
      18 * (1 + Real.log N) *
        Real.rpow (Real.sqrt N) (-sigma) := by
  dsimp only
  let K := 9 * Nat.ceil (Real.sqrt N)
  have hRlower := (goldfeldCutoff_bounds hN).1
  change Real.sqrt (N : ℝ) ≤ (K : ℝ) at hRlower
  have hlog := (goldfeldCutoff_log_bounds hN).2
  change Real.log ((K + 1 : ℕ) : ℝ) ≤
    18 * (1 + Real.log (N : ℝ)) at hlog
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hRpos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hNpos
  have hXpos : (0 : ℝ) < ((K + 1 : ℕ) : ℝ) := by positivity
  have hRlower' : Real.sqrt (N : ℝ) ≤ ((K + 1 : ℕ) : ℝ) :=
    hRlower.trans (by exact_mod_cast (Nat.le_succ K))
  have hpow : Real.rpow ((K + 1 : ℕ) : ℝ) (-sigma) ≤
      Real.rpow (Real.sqrt N) (-sigma) :=
    Real.rpow_le_rpow_of_nonpos hRpos hRlower' (by linarith)
  have hlog0 : 0 ≤ Real.log ((K + 1 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ K + 1 by omega))
  have hNone : (1 : ℝ) ≤ N := by
    exact_mod_cast (show 1 ≤ N by omega)
  have hL0 : 0 ≤ 18 * (1 + Real.log (N : ℝ)) := by
    have : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hNone
    positivity
  have hrewrite : firstDerivativeWeight sigma (K + 1) =
      Real.log ((K + 1 : ℕ) : ℝ) *
        Real.rpow ((K + 1 : ℕ) : ℝ) (-sigma) := by
    rw [firstDerivativeWeight, div_eq_mul_inv]
    rw [← Real.rpow_neg hXpos.le]
    simp only [Real.rpow_eq_pow]
  rw [hrewrite]
  exact mul_le_mul hlog hpow
    (Real.rpow_nonneg (by positivity) _) hL0

end
end MAPGoldfeldSiegel

#print axioms MAPGoldfeldSiegel.sum_range_mul_eq_sum_blocks
#print axioms MAPGoldfeldSiegel.sum_positive_blocks_eq_sum_Ico
#print axioms MAPGoldfeldSiegel.term_logMul_eq_firstDerivativeWeight_mul
#print axioms MAPGoldfeldSiegel.deriv_characterLBlock_eq_neg_weight_sum
#print axioms MAPGoldfeldSiegel.sum_deriv_centeredCharacterLBlock_eq_neg_sum_Ico
#print axioms MAPGoldfeldSiegel.tendsto_neg_firstDerivativeWeight_sum_blocks
#print axioms MAPGoldfeldSiegel.norm_deriv_LFunction_le_initial_add_PV_tail
#print axioms MAPGoldfeldSiegel.firstDerivativeWeight_le_cutoff
#print axioms MAPGoldfeldSiegel.norm_firstDerivative_initialSum_le
#print axioms MAPGoldfeldSiegel.primitive_quadratic_deriv_LFunction_t0_cutoff
