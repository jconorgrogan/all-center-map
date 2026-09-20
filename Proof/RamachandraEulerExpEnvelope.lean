import RamachandraTheorem6SourceProofChain

/-!
# Elementary finite Euler-product envelope for Ramachandra Theorem 6

This file proves the scalar arithmetic estimate behind the published
`exp (sqrt (log q))` loss.  The proof uses only distinct prime factors, a
small/large split at `log q / 10000`, and the elementary telescoping bound
`sum_{n ≤ N} n⁻¹/² ≤ 2 sqrt N`.
-/

namespace RamachandraEulerExpEnvelope

open scoped BigOperators
open RamachandraTheorem6SourceProofChain

noncomputable section

lemma invSqrt_succ_le_two_mul_sqrt_sub (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤
      2 * (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (n : ℝ)) := by
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hn1 : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hs0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hs1 : 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) := Real.sqrt_pos.2 hn1
  have hle : Real.sqrt (n : ℝ) ≤ Real.sqrt ((n + 1 : ℕ) : ℝ) := by
    exact Real.sqrt_le_sqrt (by norm_num)
  have hsum : 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) + Real.sqrt (n : ℝ) := by positivity
  have hid :
      Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (n : ℝ) =
        1 / (Real.sqrt ((n + 1 : ℕ) : ℝ) + Real.sqrt (n : ℝ)) := by
    apply (eq_div_iff hsum.ne').2
    have hsq0 := Real.sq_sqrt hn0
    have hsq1 := Real.sq_sqrt hn1.le
    norm_num at hsq1 ⊢
    nlinarith
  rw [show (-(1/2 : ℝ)) = -(1/2 : ℝ) by rfl,
    Real.rpow_neg hn1.le, ← Real.sqrt_eq_rpow, hid]
  rw [← one_div]
  have hfrac :
      1 / Real.sqrt ((n + 1 : ℕ) : ℝ) ≤
        2 / (Real.sqrt ((n + 1 : ℕ) : ℝ) + Real.sqrt (n : ℝ)) := by
    rw [div_le_div_iff₀ hs1 hsum]
    linarith
  simpa [div_eq_mul_inv] using hfrac

lemma sum_invSqrt_range_le (N : ℕ) :
    (Finset.sum (Finset.range N) (fun n => (((n + 1 : ℕ) : ℝ) ^ (-(1/2 : ℝ))))) ≤
      2 * Real.sqrt (N : ℝ) := by
  calc
    _ ≤ Finset.sum (Finset.range N) (fun n =>
        2 * (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (n : ℝ))) := by
      apply Finset.sum_le_sum
      intro n hn
      exact invSqrt_succ_le_two_mul_sqrt_sub n
    _ = 2 * Real.sqrt (N : ℝ) := by
      rw [← Finset.mul_sum]
      have htel := Finset.sum_range_sub (fun n : ℕ => Real.sqrt (n : ℝ)) N
      rw [htel]
      norm_num


lemma sum_Icc_invSqrt_le (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, ((n : ℝ) ^ (-(1/2 : ℝ)))) ≤
      2 * Real.sqrt (N : ℝ) := by
  have hfin : Finset.Icc 1 N = Finset.Ico 1 (N + 1) := by
    ext n
    simp
  rw [hfin, Finset.sum_Ico_eq_sum_range]
  simpa [add_comm] using sum_invSqrt_range_le N

lemma sum_subset_invSqrt_le {s : Finset ℕ} {y : ℝ}
    (hy : 0 ≤ y)
    (hpos : ∀ n ∈ s, 1 ≤ n)
    (hle : ∀ n ∈ s, (n : ℝ) ≤ y) :
    (∑ n ∈ s, ((n : ℝ) ^ (-(1/2 : ℝ)))) ≤ 2 * Real.sqrt y := by
  let N := ⌊y⌋₊
  have hsub : s ⊆ Finset.Icc 1 N := by
    intro n hn
    rw [Finset.mem_Icc]
    exact ⟨hpos n hn, Nat.le_floor (hle n hn)⟩
  calc
    (∑ n ∈ s, ((n : ℝ) ^ (-(1/2 : ℝ)))) ≤
      ∑ n ∈ Finset.Icc 1 N, ((n : ℝ) ^ (-(1/2 : ℝ))) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro n hn hns
        positivity
    _ ≤ 2 * Real.sqrt (N : ℝ) := sum_Icc_invSqrt_le N
    _ ≤ 2 * Real.sqrt y := by
      gcongr
      exact Nat.floor_le hy

lemma sum_log_primeFactors_le_log (q : ℕ) [NeZero q] :
    (∑ p ∈ q.primeFactors, Real.log (p : ℝ)) ≤ Real.log (q : ℝ) := by
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hprodpos : 0 < ∏ p ∈ q.primeFactors, p := by
    apply Finset.prod_pos
    intro p hp
    exact Nat.prime_of_mem_primeFactors hp |>.pos
  have hproddvd : (∏ p ∈ q.primeFactors, p) ∣ q := Nat.prod_primeFactors_dvd q
  have hprodle : (∏ p ∈ q.primeFactors, p) ≤ q := Nat.le_of_dvd hqpos hproddvd
  rw [← Real.log_prod]
  · have hqposR : 0 < (q : ℝ) := by exact_mod_cast hqpos
    have hprodposR : 0 < ∏ p ∈ q.primeFactors, (p : ℝ) := by
      apply Finset.prod_pos
      intro p hp
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
    apply Real.strictMonoOn_log.monotoneOn hprodposR hqposR
    rw [← Nat.cast_prod]
    exact_mod_cast hprodle
  · intro p hp
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero

noncomputable def primeFactorHalfMass (q : ℕ) : ℝ :=
  ∑ p ∈ q.primeFactors, (p : ℝ) ^ (-(1/2 : ℝ))

lemma invSqrt_le_log_div_of_lt {y x : ℝ} (hy : 1 < y) (hyx : y < x) :
    x ^ (-(1/2 : ℝ)) ≤ Real.log x / (Real.sqrt y * Real.log y) := by
  have hy0 : 0 < y := lt_trans zero_lt_one hy
  have hx0 : 0 < x := lt_trans hy0 hyx
  have hlogy : 0 < Real.log y := Real.log_pos hy
  have hlogmono : Real.log y ≤ Real.log x :=
    Real.strictMonoOn_log.monotoneOn hy0 hx0 hyx.le
  have hone : 1 ≤ Real.log x / Real.log y :=
    (le_div_iff₀ hlogy).2 (by simpa using hlogmono)
  have hbase : x ^ (-(1/2 : ℝ)) ≤ y ^ (-(1/2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hy0 hyx.le (by norm_num)
  calc
    x ^ (-(1/2 : ℝ)) ≤ y ^ (-(1/2 : ℝ)) := hbase
    _ ≤ y ^ (-(1/2 : ℝ)) * (Real.log x / Real.log y) := by
      exact le_mul_of_one_le_right (Real.rpow_nonneg hy0.le _) hone
    _ = Real.log x / (Real.sqrt y * Real.log y) := by
      rw [Real.rpow_neg hy0.le, ← Real.sqrt_eq_rpow]
      field_simp

lemma primeFactorHalfMass_split (q : ℕ) [NeZero q] {y : ℝ} (hy : 1 < y) :
    primeFactorHalfMass q ≤
      2 * Real.sqrt y + Real.log (q : ℝ) / (Real.sqrt y * Real.log y) := by
  classical
  let small : Finset ℕ := q.primeFactors.filter (fun p => (p : ℝ) ≤ y)
  let large : Finset ℕ := q.primeFactors.filter (fun p => ¬ (p : ℝ) ≤ y)
  have hsplit := Finset.sum_filter_add_sum_filter_not q.primeFactors
    (fun p => (p : ℝ) ≤ y) (fun p => (p : ℝ) ^ (-(1/2 : ℝ)))
  have hsmall :
      (∑ p ∈ small, (p : ℝ) ^ (-(1/2 : ℝ))) ≤ 2 * Real.sqrt y := by
    apply sum_subset_invSqrt_le (zero_le_one.trans hy.le)
    · intro p hp
      have hpq : p ∈ q.primeFactors := (Finset.mem_filter.1 hp).1
      exact (Nat.prime_of_mem_primeFactors hpq).one_le
    · intro p hp
      exact (Finset.mem_filter.1 hp).2
  have hlarge :
      (∑ p ∈ large, (p : ℝ) ^ (-(1/2 : ℝ))) ≤
        Real.log (q : ℝ) / (Real.sqrt y * Real.log y) := by
    calc
      (∑ p ∈ large, (p : ℝ) ^ (-(1/2 : ℝ))) ≤
          ∑ p ∈ large, Real.log (p : ℝ) / (Real.sqrt y * Real.log y) := by
        apply Finset.sum_le_sum
        intro p hp
        have hnot := (Finset.mem_filter.1 hp).2
        exact invSqrt_le_log_div_of_lt hy (lt_of_not_ge hnot)
      _ = (Real.sqrt y * Real.log y)⁻¹ *
          (∑ p ∈ large, Real.log (p : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        field_simp
      _ ≤ (Real.sqrt y * Real.log y)⁻¹ * Real.log (q : ℝ) := by
        have hsumlog :
            (∑ p ∈ large, Real.log (p : ℝ)) ≤ Real.log (q : ℝ) := by
          calc
            (∑ p ∈ large, Real.log (p : ℝ)) ≤
                ∑ p ∈ q.primeFactors, Real.log (p : ℝ) := by
              apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              intro p hp hpl
              exact Real.log_nonneg (by
                exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le)
            _ ≤ Real.log (q : ℝ) := sum_log_primeFactors_le_log q
        apply mul_le_mul_of_nonneg_left hsumlog
        exact inv_nonneg.mpr (mul_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg hy.le))
      _ = Real.log (q : ℝ) / (Real.sqrt y * Real.log y) := by
        ring
  unfold primeFactorHalfMass
  rw [← hsplit]
  exact add_le_add hsmall hlarge

lemma primeFactorHalfMass_le_three_fiftieth_sqrt_log
    (q : ℕ) [NeZero q]
    (hlarge : 10000 * Real.exp 2500 ≤ Real.log (q : ℝ)) :
    primeFactorHalfMass q ≤ (3/50 : ℝ) * Real.sqrt (Real.log (q : ℝ)) := by
  let L := Real.log (q : ℝ)
  let y := L / 10000
  have hLpos : 0 < L := lt_of_lt_of_le (by positivity) hlarge
  have hyExp : Real.exp 2500 ≤ y := by
    dsimp [y]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 10000)).2
    simpa [mul_comm] using hlarge
  have hy1 : 1 < y := by
    calc
      1 = Real.exp 0 := by simp
      _ < Real.exp 2500 := Real.exp_lt_exp.mpr (by norm_num)
      _ ≤ y := hyExp
  have hlogy : 2500 ≤ Real.log y := by
    rw [← Real.log_exp 2500]
    exact Real.log_le_log (Real.exp_pos _) hyExp
  have hsqrty : Real.sqrt y = Real.sqrt L / 100 := by
    dsimp [y]
    rw [Real.sqrt_div hLpos.le]
    norm_num
  have hsqrtLpos : 0 < Real.sqrt L := Real.sqrt_pos.2 hLpos
  have hsecond :
      L / (Real.sqrt y * Real.log y) ≤ Real.sqrt L / 25 := by
    rw [hsqrty]
    apply (div_le_iff₀ (mul_pos (div_pos hsqrtLpos (by norm_num))
      (Real.log_pos hy1))).2
    have hmul : (Real.sqrt L / 100) * 2500 ≤
        (Real.sqrt L / 100) * Real.log y :=
      mul_le_mul_of_nonneg_left hlogy (by positivity)
    calc
      L = (Real.sqrt L) ^ 2 := (Real.sq_sqrt hLpos.le).symm
      _ = (Real.sqrt L / 25) * ((Real.sqrt L / 100) * 2500) := by ring
      _ ≤ (Real.sqrt L / 25) * ((Real.sqrt L / 100) * Real.log y) :=
        mul_le_mul_of_nonneg_left hmul (by positivity)
  calc
    primeFactorHalfMass q ≤ 2 * Real.sqrt y +
        L / (Real.sqrt y * Real.log y) := primeFactorHalfMass_split q hy1
    _ ≤ 2 * (Real.sqrt L / 100) + Real.sqrt L / 25 := by
      rw [hsqrty] at hsecond ⊢
      exact add_le_add_right hsecond _
    _ = (3/50 : ℝ) * Real.sqrt L := by ring

noncomputable def primeFactorShiftMass (q : ℕ) (sigma : ℝ) : ℝ :=
  ∑ p ∈ q.primeFactors, (p : ℝ) ^ (-sigma)

lemma primeFactor_rpow_shift_le
    {q : ℕ} [NeZero q] {T sigma : ℝ} (hT : 3 ≤ T)
    (hstrip : |sigma - (1/2 : ℝ)| ≤
      (100 * Real.log ((q : ℝ) * T))⁻¹)
    {p : ℕ} (hpq : p ∈ q.primeFactors) :
    (p : ℝ) ^ (-sigma) ≤
      Real.exp (1/100 : ℝ) * (p : ℝ) ^ (-(1/2 : ℝ)) := by
  have hqposN : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hqone : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q))
  have hqT3 : 3 ≤ (q : ℝ) * T := by nlinarith
  have hlogpos : 0 < Real.log ((q : ℝ) * T) :=
    Real.log_pos (lt_of_lt_of_le (by norm_num) hqT3)
  have hdelta : (1/2 : ℝ) - sigma ≤
      (100 * Real.log ((q : ℝ) * T))⁻¹ := by
    have habs := (abs_le.mp hstrip).1
    linarith
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hpq
  have hpPos : 0 < (p : ℝ) := by exact_mod_cast hpPrime.pos
  have hp_le_q : p ≤ q := Nat.le_of_dvd hqposN (Nat.dvd_of_mem_primeFactors hpq)
  have hp_le_qT : (p : ℝ) ≤ (q : ℝ) * T := by
    have hpqR : (p : ℝ) ≤ (q : ℝ) := by exact_mod_cast hp_le_q
    nlinarith
  have hlogp_nonneg : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hpPrime.one_le)
  have hlog_le : Real.log (p : ℝ) ≤ Real.log ((q : ℝ) * T) :=
    Real.log_le_log hpPos hp_le_qT
  have hlogdelta : Real.log (p : ℝ) * ((1/2 : ℝ) - sigma) ≤ 1/100 := by
    by_cases hd : 0 ≤ (1/2 : ℝ) - sigma
    · have hmul := mul_le_mul hlog_le hdelta hd hlogpos.le
      have hden : 0 < 100 * Real.log ((q : ℝ) * T) := mul_pos (by norm_num) hlogpos
      calc
        Real.log (p : ℝ) * ((1/2 : ℝ) - sigma) ≤
            Real.log ((q : ℝ) * T) *
              (100 * Real.log ((q : ℝ) * T))⁻¹ := hmul
        _ = 1/100 := by field_simp
    · have hd' : (1/2 : ℝ) - sigma < 0 := lt_of_not_ge hd
      have : Real.log (p : ℝ) * ((1/2 : ℝ) - sigma) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hlogp_nonneg hd'.le
      linarith
  have hrpowDelta :
      (p : ℝ) ^ ((1/2 : ℝ) - sigma) ≤ Real.exp (1/100 : ℝ) := by
    rw [Real.rpow_def_of_pos hpPos]
    exact Real.exp_le_exp.mpr hlogdelta
  rw [show -sigma = (-(1/2 : ℝ)) + ((1/2 : ℝ) - sigma) by ring,
    Real.rpow_add hpPos]
  nlinarith [Real.rpow_nonneg hpPos.le (-(1/2 : ℝ))]

lemma primeFactorShiftMass_le_exp_mul_halfMass
    (q : ℕ) [NeZero q] {T sigma : ℝ} (hT : 3 ≤ T)
    (hstrip : |sigma - (1/2 : ℝ)| ≤
      (100 * Real.log ((q : ℝ) * T))⁻¹) :
    primeFactorShiftMass q sigma ≤
      Real.exp (1/100 : ℝ) * primeFactorHalfMass q := by
  unfold primeFactorShiftMass primeFactorHalfMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  exact primeFactor_rpow_shift_le hT hstrip hp

lemma primeFactorHalfMass_le_q_add_one (q : ℕ) [NeZero q] :
    primeFactorHalfMass q ≤ (q : ℝ) + 1 := by
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hsub : q.primeFactors ⊆ Finset.range (q + 1) := by
    intro p hp
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (Nat.le_of_dvd hqpos (Nat.dvd_of_mem_primeFactors hp))
  unfold primeFactorHalfMass
  calc
    (∑ p ∈ q.primeFactors, (p : ℝ) ^ (-(1/2 : ℝ))) ≤
        ∑ p ∈ q.primeFactors, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      exact Real.rpow_le_one_of_one_le_of_nonpos
        (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le) (by norm_num)
    _ = (q.primeFactors.card : ℝ) := by simp
    _ ≤ ((Finset.range (q + 1)).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    _ = (q : ℝ) + 1 := by simp

lemma four_mul_primeFactorShiftMass_le_sqrt_log_of_large
    (q : ℕ) [NeZero q] {T sigma : ℝ} (hT : 3 ≤ T)
    (hstrip : |sigma - (1/2 : ℝ)| ≤
      (100 * Real.log ((q : ℝ) * T))⁻¹)
    (hlarge : 10000 * Real.exp 2500 ≤ Real.log (q : ℝ)) :
    4 * primeFactorShiftMass q sigma ≤ Real.sqrt (Real.log (q : ℝ)) := by
  have hshift := primeFactorShiftMass_le_exp_mul_halfMass q hT hstrip
  have hhalf := primeFactorHalfMass_le_three_fiftieth_sqrt_log q hlarge
  have hexp : Real.exp (1/100 : ℝ) ≤ 100/99 := by
    have h := Real.exp_bound_div_one_sub_of_interval
      (show 0 ≤ (1/100 : ℝ) by norm_num)
      (show (1/100 : ℝ) < 1 by norm_num)
    norm_num at h ⊢
    exact h
  have hnonneg : 0 ≤ primeFactorHalfMass q := by
    unfold primeFactorHalfMass
    positivity
  have hsqrtnonneg : 0 ≤ Real.sqrt (Real.log (q : ℝ)) := Real.sqrt_nonneg _
  calc
    4 * primeFactorShiftMass q sigma ≤
        4 * (Real.exp (1/100 : ℝ) * primeFactorHalfMass q) := by gcongr
    _ ≤ 4 * ((100/99 : ℝ) * primeFactorHalfMass q) := by
      gcongr
    _ ≤ 4 * ((100/99 : ℝ) * ((3/50 : ℝ) *
        Real.sqrt (Real.log (q : ℝ)))) := by
      gcongr
    _ ≤ Real.sqrt (Real.log (q : ℝ)) := by nlinarith

noncomputable def ramachandraEulerScalarConstant : ℝ :=
  Real.exp (4 * (Real.exp (1/100 : ℝ) *
    (Real.exp (10000 * Real.exp 2500) + 1)))

lemma ramachandraEulerScalarConstant_pos : 0 < ramachandraEulerScalarConstant := by
  unfold ramachandraEulerScalarConstant
  positivity

lemma primeFactorExpBound_full :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ) [NeZero q] (T sigma : ℝ), 3 ≤ T →
        |sigma - (1/2 : ℝ)| ≤
          (100 * Real.log ((q : ℝ) * T))⁻¹ →
        Real.exp (4 * primeFactorShiftMass q sigma) ≤
          C * Real.exp (Real.sqrt (Real.log (q : ℝ))) := by
  refine ⟨ramachandraEulerScalarConstant, ramachandraEulerScalarConstant_pos, ?_⟩
  intro q _inst T sigma hT hstrip
  have hqpos : 0 < (q : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q))
  have hsqrtnonneg : 0 ≤ Real.sqrt (Real.log (q : ℝ)) := Real.sqrt_nonneg _
  have hCgeOne : 1 ≤ ramachandraEulerScalarConstant := by
    unfold ramachandraEulerScalarConstant
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    positivity
  by_cases hlarge : 10000 * Real.exp 2500 ≤ Real.log (q : ℝ)
  · have hexp := Real.exp_le_exp.mpr
      (four_mul_primeFactorShiftMass_le_sqrt_log_of_large q hT hstrip hlarge)
    calc
      Real.exp (4 * primeFactorShiftMass q sigma) ≤
          Real.exp (Real.sqrt (Real.log (q : ℝ))) := hexp
      _ ≤ ramachandraEulerScalarConstant *
          Real.exp (Real.sqrt (Real.log (q : ℝ))) := by
        nlinarith [Real.exp_pos (Real.sqrt (Real.log (q : ℝ)))]
  · have hloglt : Real.log (q : ℝ) < 10000 * Real.exp 2500 := lt_of_not_ge hlarge
    have hqbound : (q : ℝ) ≤ Real.exp (10000 * Real.exp 2500) := by
      calc
        (q : ℝ) = Real.exp (Real.log (q : ℝ)) := (Real.exp_log hqpos).symm
        _ ≤ Real.exp (10000 * Real.exp 2500) := Real.exp_le_exp.mpr hloglt.le
    have hshift := primeFactorShiftMass_le_exp_mul_halfMass q hT hstrip
    have hhalf := primeFactorHalfMass_le_q_add_one q
    have hmass : primeFactorShiftMass q sigma ≤
        Real.exp (1/100 : ℝ) * (Real.exp (10000 * Real.exp 2500) + 1) := by
      calc
        primeFactorShiftMass q sigma ≤
            Real.exp (1/100 : ℝ) * primeFactorHalfMass q := hshift
        _ ≤ Real.exp (1/100 : ℝ) * ((q : ℝ) + 1) := by gcongr
        _ ≤ Real.exp (1/100 : ℝ) *
            (Real.exp (10000 * Real.exp 2500) + 1) := by gcongr
    have hexpC : Real.exp (4 * primeFactorShiftMass q sigma) ≤
        ramachandraEulerScalarConstant := by
      unfold ramachandraEulerScalarConstant
      exact Real.exp_le_exp.mpr (by nlinarith)
    calc
      Real.exp (4 * primeFactorShiftMass q sigma) ≤
          ramachandraEulerScalarConstant := hexpC
      _ ≤ ramachandraEulerScalarConstant *
          Real.exp (Real.sqrt (Real.log (q : ℝ))) := by
        have hexpone : 1 ≤ Real.exp (Real.sqrt (Real.log (q : ℝ))) := by
          rw [← Real.exp_zero]
          exact Real.exp_le_exp.mpr hsqrtnonneg
        nlinarith [ramachandraEulerScalarConstant_pos]


/-- Triangle inequality and the finite-product exponential majorant reduce the
missing Euler factors to the scalar prime-factor mass. -/
theorem norm_eulerCorrection_le_exp_mass
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (sigma t : ℝ) :
    ‖PrimitiveEulerZeroTransport.eulerCorrection chi
      ((sigma : ℂ) + t * Complex.I)‖ ≤
      Real.exp (primeFactorShiftMass q sigma) := by
  unfold PrimitiveEulerZeroTransport.eulerCorrection primeFactorShiftMass
  rw [norm_prod]
  calc
    (∏ p ∈ q.primeFactors,
        ‖1 - chi.primitiveCharacter p *
          (p : ℂ) ^ (-((sigma : ℂ) + t * Complex.I))‖) ≤
      ∏ p ∈ q.primeFactors, (1 + (p : ℝ) ^ (-sigma)) := by
      apply Finset.prod_le_prod
      · intro p hp
        positivity
      · intro p hp
        have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
        have hpPos : 0 < (p : ℝ) := by exact_mod_cast hpPrime.pos
        have hpow :
            ‖(p : ℂ) ^ (-((sigma : ℂ) + t * Complex.I))‖ =
              (p : ℝ) ^ (-sigma) := by
          change ‖((p : ℝ) : ℂ) ^ (-((sigma : ℂ) + t * Complex.I))‖ =
            (p : ℝ) ^ (-sigma)
          rw [Complex.norm_cpow_eq_rpow_re_of_pos hpPos]
          congr 1
          norm_num
        calc
          ‖1 - chi.primitiveCharacter p *
              (p : ℂ) ^ (-((sigma : ℂ) + t * Complex.I))‖ ≤
              ‖(1 : ℂ)‖ + ‖chi.primitiveCharacter p *
                (p : ℂ) ^ (-((sigma : ℂ) + t * Complex.I))‖ :=
            norm_sub_le _ _
          _ = 1 + ‖chi.primitiveCharacter p‖ *
              (p : ℝ) ^ (-sigma) := by rw [norm_one, norm_mul, hpow]
          _ ≤ 1 + (p : ℝ) ^ (-sigma) := by
            gcongr
            exact mul_le_of_le_one_left
              (Real.rpow_nonneg hpPos.le _)
              (chi.primitiveCharacter.norm_le_one p)
    _ ≤ Real.exp (∑ p ∈ q.primeFactors, (p : ℝ) ^ (-sigma)) := by
      exact Real.prod_one_add_le_exp_sum _
        (fun p => Real.rpow_nonneg (Nat.cast_nonneg p) _)

/-- The exact local finite Euler-product envelope used by the source proof
chain, now with no analytic or arithmetic hypothesis left. -/
theorem ramachandraEulerProductEnvelopeK2 :
    RamachandraEulerProductEnvelopeK2 := by
  obtain ⟨C, hC, hsource⟩ := primeFactorExpBound_full
  refine ⟨C, hC, ?_⟩
  intro q _inst T sigma hT hstrip chi t ht
  have hnorm := norm_eulerCorrection_le_exp_mass chi sigma t
  have hpow := pow_le_pow_left₀ (norm_nonneg _) hnorm 4
  calc
    ‖PrimitiveEulerZeroTransport.eulerCorrection chi
        ((sigma : ℂ) + t * Complex.I)‖ ^ 4 ≤
      Real.exp (primeFactorShiftMass q sigma) ^ 4 := hpow
    _ = Real.exp (4 * primeFactorShiftMass q sigma) := by
      rw [← Real.exp_nat_mul]
      norm_num
    _ ≤ C * Real.exp (Real.sqrt (Real.log (q : ℝ))) :=
      hsource q T sigma hT hstrip

/-- With the deterministic conductor partition and the Euler envelope closed,
the all-character source theorem has exactly one remaining input: the shifted
primitive fourth moment stated in the proof of Ramachandra's Theorem 6. -/
theorem ramachandraTheorem6K2Source_of_primitive
    (hprim : RamachandraPrimitiveShiftedFourthK2) :
    RamachandraTheorem6ShiftedStripSource.RamachandraTheorem6K2Source :=
  ramachandraTheorem6K2Source_of_primitive_partition_eulerEnvelope
    hprim ramachandraConductorPartitionIdentity
    ramachandraEulerProductEnvelopeK2

end
end RamachandraEulerExpEnvelope

#print axioms RamachandraEulerExpEnvelope.primeFactorExpBound_full
#print axioms RamachandraEulerExpEnvelope.norm_eulerCorrection_le_exp_mass
#print axioms RamachandraEulerExpEnvelope.ramachandraEulerProductEnvelopeK2
#print axioms RamachandraEulerExpEnvelope.ramachandraTheorem6K2Source_of_primitive
