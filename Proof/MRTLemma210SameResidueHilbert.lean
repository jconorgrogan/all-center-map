import FiniteHilbertInequality

/-!
# MRT Lemma 2.10: the same-residue logarithmic Hilbert estimate

The character orthogonality reduction leaves pairs of integers in one residue
class modulo `q`.  Applying the dyadic logarithmic Hilbert bound without
remembering that residue class loses the essential factor `q`.  This file
retains it: the arithmetic progression is reindexed by `n / q`, the integer
Hilbert inequality is applied there, and the logarithmic change of variables
costs only `N / q`.
-/

namespace MAPMRTLemma210SameResidueHilbert

open scoped BigOperators ComplexConjugate Interval Real
open MeasureTheory intervalIntegral Complex
open MontgomeryVaughanFiniteReduction

noncomputable section

/-- An integer embedding which is `n / q` on the residue class `r`, while
sending all other naturals to distinct negative integers.  The negative branch
is only present to make a global embedding; every application below lies in the
positive branch. -/
def residueEmbedding (q r : ℕ) (hq : 0 < q) : ℕ ↪ ℤ where
  toFun n := if n % q = r then ((n / q : ℕ) : ℤ) else -((n + 1 : ℕ) : ℤ)
  inj' := by
    intro n m h
    by_cases hn : n % q = r
    · by_cases hm : m % q = r
      · simp only [hn, hm, if_true, Int.ofNat_inj] at h
        have hdiv : n / q = m / q := by exact_mod_cast h
        calc
          n = n % q + q * (n / q) := (Nat.mod_add_div n q).symm
          _ = m % q + q * (m / q) := by rw [hn, hm, hdiv]
          _ = m := Nat.mod_add_div m q
      · simp only [hn, hm, if_true, if_false] at h
        have hnq : (0 : ℤ) ≤ ((n / q : ℕ) : ℤ) := Int.ofNat_nonneg _
        have hmpos : (0 : ℤ) < ((m + 1 : ℕ) : ℤ) := by exact_mod_cast Nat.succ_pos m
        have hmneg : -((m + 1 : ℕ) : ℤ) < 0 := neg_neg_of_pos hmpos
        linarith
    · by_cases hm : m % q = r
      · simp only [hn, hm, if_true, if_false] at h
        have hmq : (0 : ℤ) ≤ ((m / q : ℕ) : ℤ) := Int.ofNat_nonneg _
        have hnpos : (0 : ℤ) < ((n + 1 : ℕ) : ℤ) := by exact_mod_cast Nat.succ_pos n
        have hnneg : -((n + 1 : ℕ) : ℤ) < 0 := neg_neg_of_pos hnpos
        linarith
      · simp only [hn, hm, if_false] at h
        have hs : n + 1 = m + 1 := by exact_mod_cast (neg_inj.mp h)
        omega

@[simp] theorem residueEmbedding_apply_of_mod
    {q r n : ℕ} (hq : 0 < q) (hn : n % q = r) :
    residueEmbedding q r hq n = ((n / q : ℕ) : ℤ) := by
  simp [residueEmbedding, hn]

/-- Integer Hilbert form after quotienting one residue class by its modulus. -/
def residueQuotientHilbertForm
    (q : ℕ) (S : Finset ℕ) (a b : ℕ → ℂ) : ℂ :=
  ∑ n ∈ S, ∑ m ∈ S.erase n,
    (a n * star (b m)) /
      ((((n / q : ℕ) : ℤ) - ((m / q : ℕ) : ℤ) : ℤ) : ℂ)

/-- The certified integer Hilbert inequality, transported to a single residue
class.  No estimate is used in this transport. -/
theorem norm_residueQuotientHilbertForm_le
    {q r : ℕ} (hq : 0 < q) (S : Finset ℕ)
    (hres : ∀ n ∈ S, n % q = r) (a b : ℕ → ℂ) :
    ‖residueQuotientHilbertForm q S a b‖ ≤
      Real.pi * Real.sqrt (∑ n ∈ S, ‖a n‖ ^ 2) *
        Real.sqrt (∑ n ∈ S, ‖b n‖ ^ 2) := by
  classical
  let e : ℕ ↪ ℤ := residueEmbedding q r hq
  let A : ℤ → ℂ := fun z ↦ a (r + q * z.natAbs)
  let B : ℤ → ℂ := fun z ↦ b (r + q * z.natAbs)
  have hA (n : ℕ) (hn : n ∈ S) : A (e n) = a n := by
    have hnmod := hres n hn
    have hnrec := Nat.mod_add_div n q
    simp only [A, e, residueEmbedding_apply_of_mod hq hnmod]
    rw [← hnmod]
    exact congrArg a hnrec
  have hB (n : ℕ) (hn : n ∈ S) : B (e n) = b n := by
    have hnmod := hres n hn
    have hnrec := Nat.mod_add_div n q
    simp only [B, e, residueEmbedding_apply_of_mod hq hnmod]
    rw [← hnmod]
    exact congrArg b hnrec
  have hform :
      discreteHilbertForm (S.map e) A B =
        residueQuotientHilbertForm q S a b := by
    unfold discreteHilbertForm residueQuotientHilbertForm
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro n hn
    rw [← Finset.map_erase, Finset.sum_map]
    apply Finset.sum_congr rfl
    intro m hm
    have hmS : m ∈ S := (Finset.mem_erase.mp hm).2
    rw [hA n hn, hB m hmS]
    simp only [e, residueEmbedding_apply_of_mod hq (hres n hn),
      residueEmbedding_apply_of_mod hq (hres m hmS)]
  have henergyA :
      (∑ z ∈ S.map e, ‖A z‖ ^ 2) = ∑ n ∈ S, ‖a n‖ ^ 2 := by
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro n hn
    rw [hA n hn]
  have henergyB :
      (∑ z ∈ S.map e, ‖B z‖ ^ 2) = ∑ n ∈ S, ‖b n‖ ^ 2 := by
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro n hn
    rw [hB n hn]
  have h := finiteDiscreteHilbertBilinear (S.map e) A B
  rw [hform, henergyA, henergyB] at h
  exact h

/-- Equal residues identify the ordinary integer gap with `q` times the gap
between quotient indices. -/
theorem int_gap_eq_modulus_mul_quotient_gap
    {q r n m : ℕ} (hn : n % q = r) (hm : m % q = r) :
    (n : ℤ) - (m : ℤ) =
      (q : ℤ) * (((n / q : ℕ) : ℤ) - ((m / q : ℕ) : ℤ)) := by
  have hnrec : (n : ℤ) = (r : ℤ) + (q : ℤ) * ((n / q : ℕ) : ℤ) := by
    exact_mod_cast (show n = r + q * (n / q) by
      rw [← hn]
      exact (Nat.mod_add_div n q).symm)
  have hmrec : (m : ℤ) = (r : ℤ) + (q : ℤ) * ((m / q : ℕ) : ℤ) := by
    exact_mod_cast (show m = r + q * (m / q) by
      rw [← hm]
      exact (Nat.mod_add_div m q).symm)
  rw [hnrec, hmrec]
  ring

theorem quotient_ne_of_ne_of_same_residue
    {q r n m : ℕ} (hn : n % q = r) (hm : m % q = r) (hne : n ≠ m) :
    n / q ≠ m / q := by
  intro hdiv
  apply hne
  calc
    n = n % q + q * (n / q) := (Nat.mod_add_div n q).symm
    _ = m % q + q * (m / q) := by rw [hn, hm, hdiv]
    _ = m := Nat.mod_add_div m q

/-- Exact logarithmic mean identity with the arithmetic progression scale
made explicit.  This is the point where `N/q`, rather than `N`, appears. -/
theorem inv_logGap_eq_sameResidue_normalizedMean
    {N q r n m : ℕ} (hN : 1 ≤ N) (hq : 0 < q)
    (hnpos : 0 < n) (hmpos : 0 < m)
    (hnres : n % q = r) (hmres : m % q = r) (hne : n ≠ m) :
    (1 : ℂ) / (logGap n m : ℂ) =
      ((N : ℂ) / (q : ℂ)) * ∫ t in (0 : ℝ)..1,
        (normalizedLogWeight N n t *
          star (normalizedLogWeight N m (1 - t))) /
            (((((n / q : ℕ) : ℤ) - ((m / q : ℕ) : ℤ) : ℤ) : ℂ)) := by
  have hNpos : 0 < N := Nat.zero_lt_of_lt hN
  have hmean := inv_log_sub_eq_logMeanIntegral
    (x := (n : ℝ)) (y := (m : ℝ))
    (by exact_mod_cast hnpos) (by exact_mod_cast hmpos)
    (by exact_mod_cast hne)
  change (1 : ℂ) / (logGap n m : ℂ) = _
  rw [logGap, hmean]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  have hNexp : Complex.exp ((Real.log N : ℝ) : ℂ) = (N : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log (by exact_mod_cast hNpos)]
    norm_cast
  have hstar : star (normalizedLogWeight N m (1 - t)) =
      normalizedLogWeight N m (1 - t) := by
    unfold normalizedLogWeight
    change conj (Complex.exp (Complex.ofReal
      ((1 - t) * (Real.log m - Real.log N)))) =
        Complex.exp (Complex.ofReal
          ((1 - t) * (Real.log m - Real.log N)))
    rw [← Complex.ofReal_exp]
    exact conj_ofReal _
  have hnum :
      Complex.exp
          (((t * Real.log n + (1 - t) * Real.log m : ℝ) : ℂ)) =
        (N : ℂ) *
          (normalizedLogWeight N n t * normalizedLogWeight N m (1 - t)) := by
    rw [← hNexp]
    unfold normalizedLogWeight
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hdenInt := int_gap_eq_modulus_mul_quotient_gap hnres hmres
  have hden : ((((n : ℝ) - (m : ℝ) : ℝ) : ℂ)) =
      (q : ℂ) *
        (((((n / q : ℕ) : ℤ) - ((m / q : ℕ) : ℤ) : ℤ) : ℂ)) := by
    exact_mod_cast hdenInt
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hquot :
      (((((n / q : ℕ) : ℤ) - ((m / q : ℕ) : ℤ) : ℤ) : ℂ)) ≠ 0 := by
    have hquotNat := quotient_ne_of_ne_of_same_residue hnres hmres hne
    have hquotInt : ((n / q : ℕ) : ℤ) - ((m / q : ℕ) : ℤ) ≠ 0 := by
      exact sub_ne_zero.mpr (by exact_mod_cast hquotNat)
    exact_mod_cast hquotInt
  dsimp only
  rw [hnum, hden, hstar]
  field_simp [hqC, hquot]

/-- The logarithmic Hilbert form on one finite residue-class packet. -/
def sameResidueLogHilbertForm (S : Finset ℕ) (a : ℕ → ℂ) : ℂ :=
  ∑ n ∈ S, ∑ m ∈ S.erase n,
    (a n * star (a m)) / (logGap n m : ℂ)

/-- Exact passage from logarithmic frequencies to the quotient-index Hilbert
form. -/
theorem sameResidueLogHilbertForm_eq_normalizedIntegral
    {N q r : ℕ} (hN : 1 ≤ N) (hq : 0 < q)
    (S : Finset ℕ) (hpos : ∀ n ∈ S, 0 < n)
    (hres : ∀ n ∈ S, n % q = r) (a : ℕ → ℂ) :
    sameResidueLogHilbertForm S a =
      ((N : ℂ) / (q : ℂ)) * ∫ t in (0 : ℝ)..1,
        residueQuotientHilbertForm q S
          (fun n ↦ normalizedLogWeight N n t * a n)
          (fun m ↦ normalizedLogWeight N m (1 - t) * a m) := by
  classical
  unfold sameResidueLogHilbertForm residueQuotientHilbertForm
  rw [intervalIntegral.integral_finsetSum]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [intervalIntegral.integral_finsetSum]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      have hmS : m ∈ S := (Finset.mem_erase.mp hm).2
      have hne : n ≠ m := fun h ↦ (Finset.mem_erase.mp hm).1 h.symm
      have hinv := inv_logGap_eq_sameResidue_normalizedMean
        hN hq (hpos n hn) (hpos m hmS) (hres n hn) (hres m hmS) hne
      calc
        (a n * star (a m)) / (logGap n m : ℂ) =
            (a n * star (a m)) * ((1 : ℂ) / (logGap n m : ℂ)) := by ring
        _ = (a n * star (a m)) *
            (((N : ℂ) / (q : ℂ)) * ∫ t in (0 : ℝ)..1,
              (normalizedLogWeight N n t *
                star (normalizedLogWeight N m (1 - t))) /
                  (((((n / q : ℕ) : ℤ) - ((m / q : ℕ) : ℤ) : ℤ) : ℂ))) := by
              rw [hinv]
        _ = ((N : ℂ) / (q : ℂ)) * ∫ t in (0 : ℝ)..1,
            ((normalizedLogWeight N n t * a n) *
              star (normalizedLogWeight N m (1 - t) * a m)) /
                (((((n / q : ℕ) : ℤ) - ((m / q : ℕ) : ℤ) : ℤ) : ℂ)) := by
          rw [show (a n * star (a m)) *
              (((N : ℂ) / (q : ℂ)) * ∫ t in (0 : ℝ)..1,
                (normalizedLogWeight N n t *
                  star (normalizedLogWeight N m (1 - t))) /
                    (((((n / q : ℕ) : ℤ) - ((m / q : ℕ) : ℤ) : ℤ) : ℂ))) =
              ((N : ℂ) / (q : ℂ)) *
                ((a n * star (a m)) * ∫ t in (0 : ℝ)..1,
                  (normalizedLogWeight N n t *
                    star (normalizedLogWeight N m (1 - t))) /
                      (((((n / q : ℕ) : ℤ) - ((m / q : ℕ) : ℤ) : ℤ) : ℂ))) by ring]
          congr 1
          rw [← intervalIntegral.integral_const_mul]
          apply intervalIntegral.integral_congr
          intro t ht
          simp_rw [star_mul]
          ring
    · intro m hm
      apply Continuous.intervalIntegrable
      unfold normalizedLogWeight
      fun_prop
  · intro n hn
    apply Continuous.intervalIntegrable
    unfold normalizedLogWeight
    fun_prop

theorem normalizedLogWeight_norm_le_two_of_mem_dyadic
    {N n : ℕ} (hN : 1 ≤ N) (hn : n ∈ dyadicSupport N)
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    ‖normalizedLogWeight N n u‖ ≤ 2 := by
  have hNpos : 0 < N := Nat.zero_lt_of_lt hN
  have hnIoc := Finset.mem_Ioc.mp hn
  have hnpos : 0 < n := lt_trans hNpos hnIoc.1
  have hNposR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hnposR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hNnR : (N : ℝ) ≤ n := by exact_mod_cast hnIoc.1.le
  have hnupperR : (n : ℝ) ≤ 2 * N := by exact_mod_cast hnIoc.2
  have hlog_nonneg : 0 ≤ Real.log n - Real.log N := by
    exact sub_nonneg.mpr (Real.log_le_log hNposR hNnR)
  have hlog_le : Real.log n - Real.log N ≤ Real.log 2 := by
    have h := Real.log_le_log hnposR hnupperR
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hNposR.ne'] at h
    linarith
  have hexponent : u * (Real.log n - Real.log N) ≤ Real.log 2 := by
    calc
      u * (Real.log n - Real.log N) ≤
          1 * (Real.log n - Real.log N) := by
            exact mul_le_mul_of_nonneg_right hu.2 hlog_nonneg
      _ ≤ Real.log 2 := by simpa using hlog_le
  unfold normalizedLogWeight
  rw [Complex.norm_exp, Complex.ofReal_re]
  rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  exact Real.exp_le_exp.mpr hexponent

theorem normalizedWeightedEnergyOn_le
    (N : ℕ) (S : Finset ℕ) (a : ℕ → ℂ) (hN : 1 ≤ N)
    (hsub : ∀ n ∈ S, n ∈ dyadicSupport N)
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    (∑ n ∈ S, ‖normalizedLogWeight N n u * a n‖ ^ 2) ≤
      4 * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  calc
    (∑ n ∈ S, ‖normalizedLogWeight N n u * a n‖ ^ 2) ≤
        ∑ n ∈ S, 4 * ‖a n‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      have hw := normalizedLogWeight_norm_le_two_of_mem_dyadic
        hN (hsub n hn) hu
      rw [norm_mul]
      nlinarith [norm_nonneg (normalizedLogWeight N n u), norm_nonneg (a n),
        sq_nonneg (2 * ‖a n‖ - ‖normalizedLogWeight N n u‖ * ‖a n‖)]
    _ = 4 * ∑ n ∈ S, ‖a n‖ ^ 2 := by rw [Finset.mul_sum]

/-- The same-residue logarithmic Hilbert estimate with the source-critical
`N/q` saving.  This closes the first formal leaf identified after character
orthogonality in MRT Lemma 2.10. -/
theorem norm_sameResidueLogHilbertForm_le
    {N q r : ℕ} (hN : 1 ≤ N) (hq : 0 < q)
    (S : Finset ℕ) (hsub : ∀ n ∈ S, n ∈ dyadicSupport N)
    (hres : ∀ n ∈ S, n % q = r) (a : ℕ → ℂ) :
    ‖sameResidueLogHilbertForm S a‖ ≤
      4 * Real.pi * ((N : ℝ) / (q : ℝ)) *
        ∑ n ∈ S, ‖a n‖ ^ 2 := by
  have hpos : ∀ n ∈ S, 0 < n := by
    intro n hn
    have hnIoc := Finset.mem_Ioc.mp (hsub n hn)
    omega
  rw [sameResidueLogHilbertForm_eq_normalizedIntegral hN hq S hpos hres a]
  let E : ℝ := ∑ n ∈ S, ‖a n‖ ^ 2
  have hE : 0 ≤ E := by
    unfold E
    positivity
  have hint :
      ‖∫ t in (0 : ℝ)..1,
        residueQuotientHilbertForm q S
          (fun n ↦ normalizedLogWeight N n t * a n)
          (fun m ↦ normalizedLogWeight N m (1 - t) * a m)‖ ≤
        4 * Real.pi * E := by
    calc
      _ ≤ ∫ _t in (0 : ℝ)..1, 4 * Real.pi * E := by
        apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
        · filter_upwards with t ht
          have hut : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
          have hu1t : 1 - t ∈ Set.Icc (0 : ℝ) 1 := by
            constructor <;> linarith [ht.1, ht.2]
          have hleft := normalizedWeightedEnergyOn_le N S a hN hsub hut
          have hright := normalizedWeightedEnergyOn_le N S a hN hsub hu1t
          have hbase := norm_residueQuotientHilbertForm_le hq S hres
            (fun n ↦ normalizedLogWeight N n t * a n)
            (fun m ↦ normalizedLogWeight N m (1 - t) * a m)
          have hsqrt : Real.sqrt (4 * E) = 2 * Real.sqrt E := by
            rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
            norm_num
          calc
            _ ≤ Real.pi *
                Real.sqrt (∑ n ∈ S,
                  ‖normalizedLogWeight N n t * a n‖ ^ 2) *
                Real.sqrt (∑ n ∈ S,
                  ‖normalizedLogWeight N n (1 - t) * a n‖ ^ 2) := hbase
            _ ≤ Real.pi * Real.sqrt (4 * E) * Real.sqrt (4 * E) := by
              gcongr
            _ = 4 * Real.pi * E := by
              rw [hsqrt]
              calc
                Real.pi * (2 * Real.sqrt E) * (2 * Real.sqrt E) =
                    4 * Real.pi * Real.sqrt E ^ 2 := by ring
                _ = 4 * Real.pi * E := by rw [Real.sq_sqrt hE]
        · exact intervalIntegral.intervalIntegrable_const
      _ = 4 * Real.pi * E := by simp
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hscale : ‖(N : ℂ) / (q : ℂ)‖ = (N : ℝ) / (q : ℝ) := by
    rw [norm_div, Complex.norm_natCast, Complex.norm_natCast]
  calc
    ‖((N : ℂ) / (q : ℂ)) * ∫ t in (0 : ℝ)..1,
        residueQuotientHilbertForm q S
          (fun n ↦ normalizedLogWeight N n t * a n)
          (fun m ↦ normalizedLogWeight N m (1 - t) * a m)‖ =
        ((N : ℝ) / (q : ℝ)) *
          ‖∫ t in (0 : ℝ)..1,
            residueQuotientHilbertForm q S
              (fun n ↦ normalizedLogWeight N n t * a n)
              (fun m ↦ normalizedLogWeight N m (1 - t) * a m)‖ := by
      rw [norm_mul, hscale]
    _ ≤ ((N : ℝ) / (q : ℝ)) * (4 * Real.pi * E) := by
      exact mul_le_mul_of_nonneg_left hint (by positivity)
    _ = 4 * Real.pi * ((N : ℝ) / (q : ℝ)) *
        ∑ n ∈ S, ‖a n‖ ^ 2 := by
      unfold E
      ring

/-! ## Continuous mean square on one residue packet -/

def residuePacketPolynomial (S : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ S, a n * phase n t

def residuePacketEnergy (S : Finset ℕ) (a : ℕ → ℂ) : ℝ :=
  ∑ n ∈ S, ‖a n‖ ^ 2

def residuePacketOffDiagonal (S : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ S, ∑ m ∈ S.erase n, pairTerm a n m t

def integratedResiduePacketOffDiagonal
    (S : Finset ℕ) (a : ℕ → ℂ) (T : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..T, residuePacketOffDiagonal S a t

theorem residuePacket_square_eq_diagonal_add_offDiagonal
    (S : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) :
    residuePacketPolynomial S a t * star (residuePacketPolynomial S a t) =
      (residuePacketEnergy S a : ℂ) + residuePacketOffDiagonal S a t := by
  classical
  unfold residuePacketPolynomial residuePacketEnergy residuePacketOffDiagonal
  rw [MontgomeryVaughanFiniteReduction.finite_square_expansion]
  calc
    (∑ n ∈ S, ∑ m ∈ S, a n * phase n t * star (a m * phase m t)) =
        ∑ n ∈ S, (pairTerm a n n t +
          ∑ m ∈ S.erase n, pairTerm a n m t) := by
      apply Finset.sum_congr rfl
      intro n hn
      have herase := Finset.sum_erase_add S (fun m ↦ pairTerm a n m t) hn
      rw [add_comm] at herase
      exact herase.symm
    _ = ∑ n ∈ S, ((‖a n‖ ^ 2 : ℝ) +
          ∑ m ∈ S.erase n, pairTerm a n m t) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [pairTerm_self]
    _ = (↑(∑ n ∈ S, ‖a n‖ ^ 2) : ℂ) +
        ∑ n ∈ S, ∑ m ∈ S.erase n, pairTerm a n m t := by
      rw [Finset.sum_add_distrib]
      push_cast
      rfl

theorem integral_residuePacket_square_eq
    (S : Finset ℕ) (a : ℕ → ℂ) (T : ℝ) :
    (∫ t in (0 : ℝ)..T,
      residuePacketPolynomial S a t * star (residuePacketPolynomial S a t)) =
      (T : ℂ) * residuePacketEnergy S a +
        integratedResiduePacketOffDiagonal S a T := by
  calc
    _ = ∫ t in (0 : ℝ)..T,
        ((residuePacketEnergy S a : ℂ) + residuePacketOffDiagonal S a t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact residuePacket_square_eq_diagonal_add_offDiagonal S a t
    _ = (∫ _t in (0 : ℝ)..T, (residuePacketEnergy S a : ℂ)) +
        ∫ t in (0 : ℝ)..T, residuePacketOffDiagonal S a t := by
      rw [intervalIntegral.integral_add]
      · exact (continuous_const.intervalIntegrable _ _)
      · apply Continuous.intervalIntegrable
        unfold residuePacketOffDiagonal pairTerm phase
        fun_prop
    _ = _ := by
      rw [intervalIntegral.integral_const]
      simp [integratedResiduePacketOffDiagonal]

theorem integratedResiduePacketOffDiagonal_eq_hilbertDifference
    (S : Finset ℕ) (a : ℕ → ℂ)
    (hpos : ∀ n ∈ S, 0 < n) (T : ℝ) :
    integratedResiduePacketOffDiagonal S a T =
      -Complex.I *
        (sameResidueLogHilbertForm S (modulatedCoefficient a T) -
          sameResidueLogHilbertForm S a) := by
  classical
  unfold integratedResiduePacketOffDiagonal residuePacketOffDiagonal
  rw [intervalIntegral.integral_finsetSum]
  · unfold sameResidueLogHilbertForm
    rw [mul_sub]
    rw [Finset.mul_sum]
    rw [Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    rw [intervalIntegral.integral_finsetSum]
    · rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro m hm
      have hmS : m ∈ S := (Finset.mem_erase.mp hm).2
      have hne : n ≠ m := fun h ↦ (Finset.mem_erase.mp hm).1 h.symm
      rw [MontgomeryVaughanFiniteReduction.integral_pairTerm_offDiagonal
        a (hpos n hn) (hpos m hmS) hne T]
      simpa [hilbertPair, mul_sub] using
        (MontgomeryVaughanFiniteReduction.explicitKernelPair_eq_hilbertDifference
          a (hpos n hn) (hpos m hmS) hne T)
    · intro m hm
      exact MontgomeryVaughanFiniteReduction.intervalIntegrable_pairTerm a n m 0 T
  · intro n hn
    apply Continuous.intervalIntegrable
    unfold pairTerm phase
    fun_prop

theorem residuePacketEnergy_modulated
    (S : Finset ℕ) (a : ℕ → ℂ) (T : ℝ) :
    residuePacketEnergy S (modulatedCoefficient a T) =
      residuePacketEnergy S a := by
  unfold residuePacketEnergy modulatedCoefficient
  apply Finset.sum_congr rfl
  intro n hn
  rw [norm_mul]
  have hnorm : ‖phase n T‖ = 1 := by
    unfold phase
    exact Complex.norm_exp_ofReal_mul_I _
  rw [hnorm, mul_one]

theorem norm_integratedResiduePacketOffDiagonal_le
    {N q r : ℕ} (hN : 1 ≤ N) (hq : 0 < q)
    (S : Finset ℕ) (hsub : ∀ n ∈ S, n ∈ dyadicSupport N)
    (hres : ∀ n ∈ S, n % q = r) (a : ℕ → ℂ) (T : ℝ) :
    ‖integratedResiduePacketOffDiagonal S a T‖ ≤
      8 * Real.pi * ((N : ℝ) / (q : ℝ)) * residuePacketEnergy S a := by
  have hpos : ∀ n ∈ S, 0 < n := by
    intro n hn
    have hnIoc := Finset.mem_Ioc.mp (hsub n hn)
    omega
  rw [integratedResiduePacketOffDiagonal_eq_hilbertDifference S a hpos T,
    norm_mul, norm_neg, Complex.norm_I, one_mul]
  have hmod := norm_sameResidueLogHilbertForm_le hN hq S hsub hres
    (modulatedCoefficient a T)
  have hbase := norm_sameResidueLogHilbertForm_le hN hq S hsub hres a
  calc
    ‖sameResidueLogHilbertForm S (modulatedCoefficient a T) -
        sameResidueLogHilbertForm S a‖ ≤
      ‖sameResidueLogHilbertForm S (modulatedCoefficient a T)‖ +
        ‖sameResidueLogHilbertForm S a‖ := norm_sub_le _ _
    _ ≤ 4 * Real.pi * ((N : ℝ) / (q : ℝ)) *
          ∑ n ∈ S, ‖modulatedCoefficient a T n‖ ^ 2 +
        4 * Real.pi * ((N : ℝ) / (q : ℝ)) *
          ∑ n ∈ S, ‖a n‖ ^ 2 := add_le_add hmod hbase
    _ = 8 * Real.pi * ((N : ℝ) / (q : ℝ)) * residuePacketEnergy S a := by
      have henergy := residuePacketEnergy_modulated S a T
      unfold residuePacketEnergy at henergy ⊢
      rw [henergy]
      ring

/-- Continuous mean square for one arithmetic-progression packet. -/
theorem integral_norm_sq_residuePacketPolynomial_le
    {N q r : ℕ} (hN : 1 ≤ N) (hq : 0 < q)
    (S : Finset ℕ) (hsub : ∀ n ∈ S, n ∈ dyadicSupport N)
    (hres : ∀ n ∈ S, n % q = r) (a : ℕ → ℂ)
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, ‖residuePacketPolynomial S a t‖ ^ 2) ≤
      (T + 8 * Real.pi * ((N : ℝ) / (q : ℝ))) *
        residuePacketEnergy S a := by
  have heqC := integral_residuePacket_square_eq S a T
  have hleft :
      (∫ t in (0 : ℝ)..T,
        residuePacketPolynomial S a t * star (residuePacketPolynomial S a t)) =
      ((∫ t in (0 : ℝ)..T, ‖residuePacketPolynomial S a t‖ ^ 2 : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro t ht
    change residuePacketPolynomial S a t * conj (residuePacketPolynomial S a t) = _
    rw [Complex.mul_conj, ← Complex.sq_norm]
  rw [hleft] at heqC
  have heqR := congrArg Complex.re heqC
  simp only [Complex.ofReal_re, Complex.add_re, Complex.mul_re,
    Complex.ofReal_im, mul_zero, sub_zero] at heqR
  have hoff := norm_integratedResiduePacketOffDiagonal_le
    hN hq S hsub hres a T
  have hre := Complex.re_le_norm (integratedResiduePacketOffDiagonal S a T)
  rw [heqR]
  calc
    T * residuePacketEnergy S a +
        (integratedResiduePacketOffDiagonal S a T).re ≤
      T * residuePacketEnergy S a +
        ‖integratedResiduePacketOffDiagonal S a T‖ :=
      add_le_add (le_refl _) hre
    _ ≤ T * residuePacketEnergy S a +
        8 * Real.pi * ((N : ℝ) / (q : ℝ)) * residuePacketEnergy S a :=
      add_le_add (le_refl _) hoff
    _ = (T + 8 * Real.pi * ((N : ℝ) / (q : ℝ))) *
        residuePacketEnergy S a := by ring

end
end MAPMRTLemma210SameResidueHilbert

#print axioms MAPMRTLemma210SameResidueHilbert.norm_residueQuotientHilbertForm_le
#print axioms MAPMRTLemma210SameResidueHilbert.norm_sameResidueLogHilbertForm_le
