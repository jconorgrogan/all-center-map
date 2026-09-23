import GoldfeldLemma11TwoLValue

/-!
# Lemma 11.2 derivative bound at an imprimitive level

For the common-level Goldfeld lift, complete-period cancellation gives the
partial-sum bound `N`.  Taking cutoff `9N` retains the conductor exponent
`N^(1-sigma)`, which is still proportional to the exceptional zero gap.
-/

namespace MAPGoldfeldSiegel

open Complex Set LSeries Filter Topology
open scoped BigOperators

noncomputable section

theorem nonprincipal_firstDerivative_tail_finite
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1)
    {sigma : ℝ} (hsigma : 1 / 2 ≤ sigma)
    {K M : ℕ} (hK : 9 ≤ K) (hKM : K < M) :
    ‖∑ n ∈ Finset.Ioc K M,
        (firstDerivativeWeight sigma n : ℂ) * chi (n : ZMod N)‖ ≤
      2 * (N : ℝ) * firstDerivativeWeight sigma (K + 1) := by
  apply norm_sum_Ioc_mul_le_two_mul_of_antitone
  · exact hKM
  · intro n
    exact nonprincipal_initialSum_norm_le_level chi hchi n
  · intro n hKn _
    exact firstDerivativeWeight_nonneg (by omega)
  · intro i hKi _
    exact firstDerivativeWeight_antitone_of_nine_le hsigma (by omega)
      (Nat.le_succ i)

theorem norm_deriv_LFunction_le_initial_add_level_tail
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1)
    {sigma : ℝ} (hsigma : 1 / 2 ≤ sigma)
    {K : ℕ} (hK : 9 ≤ K) :
    ‖deriv (DirichletCharacter.LFunction chi) (sigma : ℂ)‖ ≤
      ‖∑ n ∈ Finset.range (K + 1),
        (firstDerivativeWeight sigma n : ℂ) * chi (n : ZMod N)‖ +
      2 * (N : ℝ) * firstDerivativeWeight sigma (K + 1) := by
  let q : ℕ → ℂ := fun n =>
    (firstDerivativeWeight sigma n : ℂ) * chi (n : ZMod N)
  let D : ℂ := deriv (DirichletCharacter.LFunction chi) (sigma : ℂ)
  let I : ℂ := ∑ n ∈ Finset.range (K + 1), q n
  have hsigmaPos : 0 < sigma := lt_of_lt_of_le (by norm_num) hsigma
  have hneg := tendsto_neg_firstDerivativeWeight_sum_blocks chi hchi hsigmaPos
  have htotal : Tendsto
      (fun R : ℕ => ∑ n ∈ Finset.range (N * (R + 1)), q n)
      atTop (nhds (-D)) := by
    have ht := hneg.neg
    simpa [q, D] using ht
  have hsub : Tendsto
      (fun R : ℕ => (∑ n ∈ Finset.range (N * (R + 1)), q n) - I)
      atTop (nhds ((-D) - I)) := htotal.sub tendsto_const_nhds
  have heq :
      (fun R : ℕ => (∑ n ∈ Finset.range (N * (R + 1)), q n) - I) =ᶠ[atTop]
        (fun R : ℕ => ∑ n ∈ Finset.Ioc K (N * (R + 1) - 1), q n) := by
    filter_upwards [eventually_gt_atTop K] with R hR
    have hNpos : 0 < N := NeZero.pos N
    let E : ℕ := N * (R + 1)
    have hKE : K + 1 ≤ E := by
      dsimp [E]
      have hNone : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
      nlinarith
    have hset : Finset.Ioc K (E - 1) = Finset.Ico (K + 1) E := by
      ext n
      simp only [Finset.mem_Ioc, Finset.mem_Ico]
      omega
    rw [hset]
    have hsplit := Finset.sum_range_add_sum_Ico q hKE
    dsimp [I, E]
    rw [← hsplit]
    ring
  have htail : Tendsto
      (fun R : ℕ => ∑ n ∈ Finset.Ioc K (N * (R + 1) - 1), q n)
      atTop (nhds ((-D) - I)) := hsub.congr' heq
  have htailBound : ‖(-D) - I‖ ≤
      2 * (N : ℝ) * firstDerivativeWeight sigma (K + 1) := by
    apply le_of_tendsto htail.norm
    filter_upwards [eventually_gt_atTop K] with R hR
    have hNpos : 0 < N := NeZero.pos N
    have hKM : K < N * (R + 1) - 1 := by
      have hscale : R + 1 ≤ N * (R + 1) :=
        Nat.le_mul_of_pos_left (R + 1) hNpos
      omega
    change ‖∑ n ∈ Finset.Ioc K (N * (R + 1) - 1),
      (firstDerivativeWeight sigma n : ℂ) * chi (n : ZMod N)‖ ≤ _
    exact nonprincipal_firstDerivative_tail_finite chi hchi hsigma hK hKM
  have htriangle : ‖D‖ ≤ ‖I‖ + ‖(-D) - I‖ := by
    calc
      ‖D‖ = ‖-(((-D) - I) + I)‖ := by congr 1 <;> ring
      _ = ‖((-D) - I) + I‖ := norm_neg _
      _ ≤ ‖(-D) - I‖ + ‖I‖ := norm_add_le _ _
      _ = ‖I‖ + ‖(-D) - I‖ := add_comm _ _
  exact htriangle.trans (by
    simpa [I, add_comm] using add_le_add_left htailBound ‖I‖)

/-- Lemma 11.2 at `t=0`, `j=1`, for a nonprincipal character at its
possibly imprimitive current level. -/
theorem nonprincipal_deriv_LFunction_t0_le
    {N : ℕ} [NeZero N] (hN : 2 ≤ N)
    (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1)
    {sigma : ℝ} (hsigmaHalf : 1 / 2 ≤ sigma) (hsigmaOne : sigma ≤ 1) :
    ‖deriv (DirichletCharacter.LFunction chi) (sigma : ℂ)‖ ≤
      2000 * Real.rpow (N : ℝ) (1 - sigma) *
        (1 + Real.log N) ^ 2 := by
  let K := 9 * N
  have hK9 : 9 ≤ K := by
    dsimp [K]
    have : 1 ≤ N := by omega
    nlinarith
  have hraw := norm_deriv_LFunction_le_initial_add_level_tail
    chi hchi hsigmaHalf hK9
  have hinit := norm_firstDerivative_initialSum_le chi hsigmaHalf hsigmaOne
    (show 1 ≤ K by omega)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (NeZero.pos N)
  have hNlog0 : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hL0 : 0 ≤ 1 + Real.log (N : ℝ) := by linarith
  have hKpow : Real.rpow (K : ℝ) (1 - sigma) ≤
      9 * Real.rpow (N : ℝ) (1 - sigma) := by
    have hexp0 : 0 ≤ 1 - sigma := sub_nonneg.mpr hsigmaOne
    have hexp1 : 1 - sigma ≤ 1 := by linarith
    have h9pow : Real.rpow (9 : ℝ) (1 - sigma) ≤ 9 := by
      have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 9) hexp1
      simpa [Real.rpow_one, Real.rpow_eq_pow] using this
    rw [show (K : ℝ) = 9 * (N : ℝ) by norm_num [K]]
    simp only [Real.rpow_eq_pow]
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 9) hNpos.le]
    exact mul_le_mul_of_nonneg_right h9pow
      (Real.rpow_nonneg hNpos.le _)
  have hKlog : Real.log (K : ℝ) ≤ 8 * (1 + Real.log N) := by
    have hlog9 : Real.log (9 : ℝ) ≤ 8 := by
      nlinarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 9)]
    rw [show (K : ℝ) = 9 * (N : ℝ) by norm_num [K],
      Real.log_mul (by norm_num : (9 : ℝ) ≠ 0) hNpos.ne']
    nlinarith
  have hKlogPlus : 1 + Real.log (K : ℝ) ≤
      9 * (1 + Real.log N) := by linarith
  have hinitBound :
      Real.rpow (K : ℝ) (1 - sigma) * Real.log K * (1 + Real.log K) ≤
        648 * Real.rpow (N : ℝ) (1 - sigma) *
          (1 + Real.log N) ^ 2 := by
    have hlogK0 : 0 ≤ Real.log (K : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ K by omega))
    have hpowRight0 : 0 ≤ 9 * Real.rpow (N : ℝ) (1 - sigma) :=
      mul_nonneg (by norm_num) (Real.rpow_nonneg hNpos.le _)
    have hprod : Real.rpow (K : ℝ) (1 - sigma) * Real.log K ≤
        (9 * Real.rpow (N : ℝ) (1 - sigma)) *
          (8 * (1 + Real.log N)) :=
      mul_le_mul hKpow hKlog hlogK0 hpowRight0
    have hprodRight0 : 0 ≤
        (9 * Real.rpow (N : ℝ) (1 - sigma)) *
          (8 * (1 + Real.log N)) := by positivity
    calc
      Real.rpow (K : ℝ) (1 - sigma) * Real.log K * (1 + Real.log K) ≤
          (9 * Real.rpow (N : ℝ) (1 - sigma)) *
            (8 * (1 + Real.log N)) * (9 * (1 + Real.log N)) :=
        mul_le_mul hprod hKlogPlus (by linarith) hprodRight0
      _ = 648 * Real.rpow (N : ℝ) (1 - sigma) *
          (1 + Real.log N) ^ 2 := by ring
  have hNlower : (N : ℝ) ≤ ((K + 1 : ℕ) : ℝ) := by
    norm_num [K]
    nlinarith
  have hXpos : (0 : ℝ) < ((K + 1 : ℕ) : ℝ) := by positivity
  have hpowNeg : Real.rpow ((K + 1 : ℕ) : ℝ) (-sigma) ≤
      Real.rpow (N : ℝ) (-sigma) :=
    Real.rpow_le_rpow_of_nonpos hNpos hNlower (by linarith)
  have hlogSucc : Real.log ((K + 1 : ℕ) : ℝ) ≤
      9 * (1 + Real.log N) := by
    have hupper : (((K + 1 : ℕ) : ℝ)) ≤ 10 * (N : ℝ) := by
      have hNoneR : (1 : ℝ) ≤ N := by
        exact_mod_cast (show 1 ≤ N by omega)
      norm_num [K]
      nlinarith
    have hlog10 : Real.log (10 : ℝ) ≤ 9 := by
      nlinarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 10)]
    calc
      Real.log ((K + 1 : ℕ) : ℝ) ≤ Real.log (10 * (N : ℝ)) :=
        Real.log_le_log hXpos hupper
      _ = Real.log 10 + Real.log (N : ℝ) := by
        rw [Real.log_mul (by norm_num : (10 : ℝ) ≠ 0) hNpos.ne']
      _ ≤ 9 * (1 + Real.log (N : ℝ)) := by nlinarith
  have hweight : firstDerivativeWeight sigma (K + 1) ≤
      9 * (1 + Real.log N) * Real.rpow (N : ℝ) (-sigma) := by
    have hre : firstDerivativeWeight sigma (K + 1) =
        Real.log ((K + 1 : ℕ) : ℝ) *
          Real.rpow ((K + 1 : ℕ) : ℝ) (-sigma) := by
      rw [firstDerivativeWeight, div_eq_mul_inv, ← Real.rpow_neg hXpos.le]
      simp only [Real.rpow_eq_pow]
    rw [hre]
    exact mul_le_mul hlogSucc hpowNeg
      (Real.rpow_nonneg (by positivity) _)
      (mul_nonneg (by norm_num) hL0)
  have hcombine : (N : ℝ) * Real.rpow (N : ℝ) (-sigma) =
      Real.rpow (N : ℝ) (1 - sigma) := by
    calc
      (N : ℝ) * Real.rpow (N : ℝ) (-sigma) =
          Real.rpow (N : ℝ) 1 * Real.rpow (N : ℝ) (-sigma) := by
        rw [show Real.rpow (N : ℝ) 1 = N by simp [Real.rpow_eq_pow]]
      _ = Real.rpow (N : ℝ) (1 + -sigma) := by
        simpa only [Real.rpow_eq_pow] using
          (Real.rpow_add hNpos 1 (-sigma)).symm
      _ = Real.rpow (N : ℝ) (1 - sigma) := by ring_nf
  have htailBound :
      2 * (N : ℝ) * firstDerivativeWeight sigma (K + 1) ≤
        18 * Real.rpow (N : ℝ) (1 - sigma) *
          (1 + Real.log N) := by
    calc
      2 * (N : ℝ) * firstDerivativeWeight sigma (K + 1) ≤
          2 * (N : ℝ) *
            (9 * (1 + Real.log N) * Real.rpow (N : ℝ) (-sigma)) := by
        gcongr
      _ = 18 * ((N : ℝ) * Real.rpow (N : ℝ) (-sigma)) *
          (1 + Real.log N) := by ring
      _ = 18 * Real.rpow (N : ℝ) (1 - sigma) *
          (1 + Real.log N) := by rw [hcombine]
  have hinitRaw := hinit
  have hraw' := hraw.trans (add_le_add hinitRaw (le_refl _))
  have hpow0 := Real.rpow_nonneg hNpos.le (1 - sigma)
  have hLone : 1 ≤ 1 + Real.log (N : ℝ) := by linarith
  have hLleSq : 1 + Real.log (N : ℝ) ≤ (1 + Real.log N) ^ 2 := by
    nlinarith [sq_nonneg (Real.log N)]
  have htailCoarse :
      18 * Real.rpow (N : ℝ) (1 - sigma) * (1 + Real.log N) ≤
        18 * Real.rpow (N : ℝ) (1 - sigma) *
          (1 + Real.log N) ^ 2 :=
    mul_le_mul_of_nonneg_left hLleSq (mul_nonneg (by norm_num) hpow0)
  have hZ0 : 0 ≤ Real.rpow (N : ℝ) (1 - sigma) *
      (1 + Real.log N) ^ 2 := mul_nonneg hpow0 (sq_nonneg _)
  calc
    ‖deriv (DirichletCharacter.LFunction chi) (sigma : ℂ)‖ ≤
        Real.rpow (K : ℝ) (1 - sigma) * Real.log K *
          (1 + Real.log K) +
        2 * (N : ℝ) * firstDerivativeWeight sigma (K + 1) := hraw'
    _ ≤ 648 * Real.rpow (N : ℝ) (1 - sigma) *
          (1 + Real.log N) ^ 2 +
        18 * Real.rpow (N : ℝ) (1 - sigma) *
          (1 + Real.log N) := add_le_add hinitBound htailBound
    _ ≤ 648 * Real.rpow (N : ℝ) (1 - sigma) *
          (1 + Real.log N) ^ 2 +
        18 * Real.rpow (N : ℝ) (1 - sigma) *
          (1 + Real.log N) ^ 2 := add_le_add (le_refl _) htailCoarse
    _ ≤ 2000 * Real.rpow (N : ℝ) (1 - sigma) *
        (1 + Real.log N) ^ 2 := by nlinarith

end
end MAPGoldfeldSiegel

#print axioms MAPGoldfeldSiegel.nonprincipal_firstDerivative_tail_finite
#print axioms MAPGoldfeldSiegel.norm_deriv_LFunction_le_initial_add_level_tail
#print axioms MAPGoldfeldSiegel.nonprincipal_deriv_LFunction_t0_le
