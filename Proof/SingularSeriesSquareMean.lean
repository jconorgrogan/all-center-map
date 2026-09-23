import SingularSeriesFiniteFactors
import MertensAnalyticLeaf
import SupportBoundaryQuantitative

/-!
# Translated singular-series square mean

This file proves the singular-series input used by the MAP variance-to-Q4 weld.
It does not mention the prime-pair variance target.  The proof is pointwise:
the finite product over prime divisors is bounded using the certified
coefficient-one Mertens estimate, and the exact closed real translated-window
cardinality is then applied.
-/

namespace SingularSeriesSquareMean

open scoped BigOperators

open PrimePairEndpoints

noncomputable section

def primeExponentialFactor (p : ℕ) : ℝ :=
  if p.Prime then Real.exp (3 * (p : ℝ)⁻¹) else 1

theorem one_le_primeExponentialFactor (p : ℕ) :
    1 ≤ primeExponentialFactor p := by
  unfold primeExponentialFactor
  split_ifs
  · exact Real.one_le_exp (by positivity)
  · exact le_rfl

theorem singularLocalFactor_le_primeExponentialFactor
    (h : {z : ℤ // z ≠ 0}) (p : ℕ) :
    singularLocalFactor h p ≤ primeExponentialFactor p := by
  by_cases hprime : p.Prime
  · rw [primeExponentialFactor, if_pos hprime]
    by_cases hfactor : p.Prime ∧ 2 < p ∧ (p : ℤ) ∣ h.1
    · rw [singularLocalFactor, if_pos hfactor]
      have hpR : (2 : ℝ) < p := by exact_mod_cast hfactor.2.1
      have hpPos : (0 : ℝ) < p := by linarith
      have hdenPos : 0 < (p : ℝ) - 2 := by linarith
      have hrewrite : ((p : ℝ) - 1) / ((p : ℝ) - 2) =
          1 + (((p : ℝ) - 2)⁻¹) := by
        field_simp
        ring
      rw [hrewrite]
      have hexp := Real.add_one_le_exp (((p : ℝ) - 2)⁻¹)
      have hinv : (((p : ℝ) - 2)⁻¹) ≤ 3 * (p : ℝ)⁻¹ := by
        have hp3N : 3 ≤ p := by omega
        have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hp3N
        have hfrac : 1 / ((p : ℝ) - 2) ≤ 3 / (p : ℝ) := by
          rw [div_le_div_iff₀ hdenPos hpPos]
          nlinarith
        simpa [one_div, div_eq_mul_inv] using hfrac
      calc
        1 + (((p : ℝ) - 2)⁻¹) = (((p : ℝ) - 2)⁻¹) + 1 := by ring
        _ ≤ Real.exp (((p : ℝ) - 2)⁻¹) := hexp
        _ ≤ Real.exp (3 * (p : ℝ)⁻¹) := Real.exp_le_exp.mpr hinv
    · rw [singularLocalFactor, if_neg hfactor]
      exact Real.one_le_exp (by positivity)
  · rw [primeExponentialFactor, if_neg hprime, singularLocalFactor]
    split_ifs with hfactor
    · exact (hprime hfactor.1).elim
    · exact le_rfl

theorem singularLocalProduct_le_primeExponentialProduct
    (h : {z : ℤ // z ≠ 0}) :
    (∏ p ∈ h.1.natAbs.divisors, singularLocalFactor h p) ≤
      ∏ p ∈ h.1.natAbs.divisors, primeExponentialFactor p := by
  exact Finset.prod_le_prod₀ (fun p hp => (singularLocalFactor_pos h p).le)
    (fun p hp => singularLocalFactor_le_primeExponentialFactor h p)

theorem primeExponentialProduct_eq_exp_primeDivisorSum
    (h : {z : ℤ // z ≠ 0}) :
    (∏ p ∈ h.1.natAbs.divisors, primeExponentialFactor p) =
      Real.exp (3 * ∑ p ∈ h.1.natAbs.divisors.filter Nat.Prime,
        (p : ℝ)⁻¹) := by
  classical
  simp only [primeExponentialFactor]
  rw [← Finset.prod_filter, ← Real.exp_sum, Finset.mul_sum]

theorem primeDivisorReciprocalSum_le
    (h : {z : ℤ // z ≠ 0}) :
    (∑ p ∈ h.1.natAbs.divisors.filter Nat.Prime, (p : ℝ)⁻¹) ≤
      ShiuAnalyticLayer.primeReciprocalSum h.1.natAbs := by
  unfold ShiuAnalyticLayer.primeReciprocalSum
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    simp only [Finset.mem_filter] at hp ⊢
    refine ⟨?_, hp.2⟩
    have hdiv : p ∣ h.1.natAbs := (Nat.mem_divisors.mp hp.1).1
    have hle : p ≤ h.1.natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr h.2) hdiv
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hle)
  · intro p hp hnot
    positivity

theorem singularLocalProduct_le_exp_primeReciprocalSum
    (h : {z : ℤ // z ≠ 0}) :
    (∏ p ∈ h.1.natAbs.divisors, singularLocalFactor h p) ≤
      Real.exp (3 * ShiuAnalyticLayer.primeReciprocalSum h.1.natAbs) := by
  calc
    (∏ p ∈ h.1.natAbs.divisors, singularLocalFactor h p) ≤
        ∏ p ∈ h.1.natAbs.divisors, primeExponentialFactor p :=
      singularLocalProduct_le_primeExponentialProduct h
    _ = Real.exp (3 * ∑ p ∈ h.1.natAbs.divisors.filter Nat.Prime,
          (p : ℝ)⁻¹) := primeExponentialProduct_eq_exp_primeDivisorSum h
    _ ≤ Real.exp (3 * ShiuAnalyticLayer.primeReciprocalSum h.1.natAbs) := by
      apply Real.exp_le_exp.mpr
      gcongr
      exact primeDivisorReciprocalSum_le h

def singularSquareConstant : ℝ :=
  (2 * twinPrimeConstant) ^ 2 *
    Real.exp (6 * (1 + 2 * Real.log 4))

theorem singularSquareConstant_pos : 0 < singularSquareConstant := by
  unfold singularSquareConstant
  exact mul_pos (sq_pos_of_pos (mul_pos (by norm_num) twinPrimeConstant_pos))
    (Real.exp_pos _)

theorem singularSeries_sq_le_log_pow
    {X : ℝ} (hX : 3 ≤ X) (h : {z : ℤ // z ≠ 0})
    (hhX : (h.1.natAbs : ℝ) < X) :
    singularSeries h ^ 2 ≤ singularSquareConstant * (Real.log X) ^ 6 := by
  let N : ℕ := max 3 h.1.natAbs
  have hN3 : 3 ≤ N := Nat.le_max_left _ _
  have hNleX : (N : ℝ) ≤ X := by
    dsimp [N]
    rw [Nat.cast_max]
    exact max_le hX hhX.le
  have hXpos : 0 < X := by linarith
  have hNpos : (0 : ℝ) < N := by positivity
  have hlogNpos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 3) hN3))
  have hlogmono : Real.log (N : ℝ) ≤ Real.log X :=
    Real.log_le_log hNpos hNleX
  by_cases heven : (2 : ℤ) ∣ h.1
  · rw [singularSeries_eq_finite_divisor_product h, if_pos heven]
    have hprod0 : 0 ≤ ∏ p ∈ h.1.natAbs.divisors, singularLocalFactor h p :=
      (Finset.prod_pos fun p hp => singularLocalFactor_pos h p).le
    have hprimeMono :
        ShiuAnalyticLayer.primeReciprocalSum h.1.natAbs ≤
          ShiuAnalyticLayer.primeReciprocalSum N := by
      unfold ShiuAnalyticLayer.primeReciprocalSum
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        simp only [Finset.mem_filter] at hp ⊢
        refine ⟨?_, hp.2⟩
        have hpLt : p < h.1.natAbs + 1 := Finset.mem_range.mp hp.1
        exact Finset.mem_range.mpr (lt_of_lt_of_le hpLt (Nat.succ_le_succ (Nat.le_max_right 3 h.1.natAbs)))
      · intro p hp hnot
        positivity
    have hprod := (singularLocalProduct_le_exp_primeReciprocalSum h).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hprimeMono (by norm_num)))
    have hmertens := MAPMertensAnalyticLeaf.primeReciprocalSum_le_loglog_add_explicit hN3
    have hexp :
        Real.exp (6 * ShiuAnalyticLayer.primeReciprocalSum N) ≤
          Real.exp (6 * (1 + 2 * Real.log 4)) * (Real.log (N : ℝ)) ^ 6 := by
      calc
        Real.exp (6 * ShiuAnalyticLayer.primeReciprocalSum N) ≤
            Real.exp (6 * (Real.log (Real.log (N : ℝ)) +
              (1 + 2 * Real.log 4))) := by
          apply Real.exp_le_exp.mpr
          gcongr
        _ = Real.exp (6 * (1 + 2 * Real.log 4)) *
              (Real.log (N : ℝ)) ^ 6 := by
          rw [mul_add, Real.exp_add]
          rw [show 6 * Real.log (Real.log (N : ℝ)) =
              (6 : ℕ) * Real.log (Real.log (N : ℝ)) by norm_num,
            Real.exp_nat_mul, Real.exp_log hlogNpos]
          ring
    have hprodsq :
        (∏ p ∈ h.1.natAbs.divisors, singularLocalFactor h p) ^ 2 ≤
          Real.exp (6 * ShiuAnalyticLayer.primeReciprocalSum N) := by
      calc
        (∏ p ∈ h.1.natAbs.divisors, singularLocalFactor h p) ^ 2 ≤
            (Real.exp (3 * ShiuAnalyticLayer.primeReciprocalSum N)) ^ 2 := by
          nlinarith [hprod, Real.exp_pos (3 * ShiuAnalyticLayer.primeReciprocalSum N)]
        _ = Real.exp (6 * ShiuAnalyticLayer.primeReciprocalSum N) := by
          rw [pow_two, ← Real.exp_add]
          ring_nf
    calc
      (2 * twinPrimeConstant *
          ∏ p ∈ h.1.natAbs.divisors, singularLocalFactor h p) ^ 2 =
          (2 * twinPrimeConstant) ^ 2 *
            (∏ p ∈ h.1.natAbs.divisors, singularLocalFactor h p) ^ 2 := by ring
      _ ≤ (2 * twinPrimeConstant) ^ 2 *
          Real.exp (6 * ShiuAnalyticLayer.primeReciprocalSum N) := by gcongr
      _ ≤ (2 * twinPrimeConstant) ^ 2 *
          (Real.exp (6 * (1 + 2 * Real.log 4)) *
            (Real.log (N : ℝ)) ^ 6) := by gcongr
      _ ≤ singularSquareConstant * (Real.log X) ^ 6 := by
        unfold singularSquareConstant
        have hlog0 : 0 ≤ Real.log (N : ℝ) := hlogNpos.le
        have hlogX0 : 0 ≤ Real.log X := (Real.log_pos (by linarith)).le
        have hpow : (Real.log (N : ℝ)) ^ 6 ≤ (Real.log X) ^ 6 := by gcongr
        have hfactor0 : 0 ≤ (2 * twinPrimeConstant) ^ 2 *
            Real.exp (6 * (1 + 2 * Real.log 4)) := by positivity
        calc
          (2 * twinPrimeConstant) ^ 2 *
              (Real.exp (6 * (1 + 2 * Real.log 4)) *
                (Real.log (N : ℝ)) ^ 6) =
              ((2 * twinPrimeConstant) ^ 2 *
                Real.exp (6 * (1 + 2 * Real.log 4))) *
                  (Real.log (N : ℝ)) ^ 6 := by ring
          _ ≤ ((2 * twinPrimeConstant) ^ 2 *
                Real.exp (6 * (1 + 2 * Real.log 4))) *
                  (Real.log X) ^ 6 :=
            mul_le_mul_of_nonneg_left hpow hfactor0
          _ = ((2 * twinPrimeConstant) ^ 2 *
                Real.exp (6 * (1 + 2 * Real.log 4))) *
                  (Real.log X) ^ 6 := rfl
  · rw [singularSeries_eq_finite_divisor_product h, if_neg heven]
    simpa using mul_nonneg singularSquareConstant_pos.le
      (pow_nonneg (Real.log_pos (by linarith : 1 < X)).le 6)

/-- The source-faithful all-center translated singular-series square mean.
The exponent `6` is explicit and deliberately unoptimized. -/
theorem translated_singularSquareMain_le :
    ∀ ε : ℝ, 0 < ε →
      ∃ C X₀ : ℝ, 0 < C ∧ 2 ≤ X₀ ∧
        ∀ X H h₀ : ℝ, X₀ ≤ X →
          LegalParameters ε X H h₀ →
          singularSquareMain H h₀ ≤ C * H * (Real.log X) ^ 6 := by
  intro ε hε
  have hevent := SupportBoundaryQuantitative.eventually_two_rpow_one_sub_lt hε
  rw [Filter.eventually_atTop] at hevent
  obtain ⟨Xshift, hXshift⟩ := hevent
  let C : ℝ := 3 * singularSquareConstant
  let X₀ : ℝ := max 3 Xshift
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos (by norm_num) singularSquareConstant_pos
  have hX₀ : 2 ≤ X₀ := by
    dsimp [X₀]
    linarith [le_max_left (3 : ℝ) Xshift]
  refine ⟨C, X₀, hC, hX₀, ?_⟩
  intro X H h₀ hXX₀ hlegal
  have hX3 : 3 ≤ X :=
    (le_max_left (3 : ℝ) Xshift).trans hXX₀
  have hXXshift : Xshift ≤ X :=
    (le_max_right (3 : ℝ) Xshift).trans hXX₀
  have hshiftX : 2 * Real.rpow X (1 - ε) < X := hXshift X hXXshift
  have hH1 := SupportBoundaryQuantitative.one_le_H_of_legal
    (by linarith : 1 ≤ X) hε hlegal
  have hcard := SupportBoundaryQuantitative.translatedWindow_card_real_le
    (h₀ := h₀) (show 0 ≤ H by linarith)
  have hcard3 : ((translatedWindow H h₀).card : ℝ) ≤ 3 * H :=
    hcard.trans (by linarith)
  have hpoint : ∀ h ∈ translatedWindow H h₀,
      (singularSeriesTotal h) ^ 2 ≤
        singularSquareConstant * (Real.log X) ^ 6 := by
    intro h hh
    by_cases hh0 : h = 0
    · subst h
      simp [singularSeriesTotal]
      exact mul_nonneg singularSquareConstant_pos.le
        (pow_nonneg (Real.log_pos (by linarith : 1 < X)).le 6)
    · rw [singularSeriesTotal, dif_pos hh0]
      apply singularSeries_sq_le_log_pow hX3
      exact (SupportBoundaryQuantitative.natAbs_shift_le_two_rpow hlegal hh).trans_lt hshiftX
  have hconst0 : 0 ≤ singularSquareConstant * (Real.log X) ^ 6 :=
    mul_nonneg singularSquareConstant_pos.le
      (pow_nonneg (Real.log_pos (by linarith : 1 < X)).le 6)
  unfold singularSquareMain
  calc
    (∑ h ∈ translatedWindow H h₀, (singularSeriesTotal h) ^ 2) ≤
        ∑ _h ∈ translatedWindow H h₀,
          singularSquareConstant * (Real.log X) ^ 6 :=
      Finset.sum_le_sum hpoint
    _ = ((translatedWindow H h₀).card : ℝ) *
        (singularSquareConstant * (Real.log X) ^ 6) := by simp
    _ ≤ (3 * H) * (singularSquareConstant * (Real.log X) ^ 6) :=
      mul_le_mul_of_nonneg_right hcard3 hconst0
    _ = C * H * (Real.log X) ^ 6 := by
      dsimp [C]
      ring

/-- Exact adapter for `MAPVarianceTransferWeld` and its cutoff-faithful
endpoint.  No variance proposition occurs in the statement or proof. -/
theorem translated_singularSquare_input :
    ∀ ε : ℝ, 0 < ε →
      ∃ k : ℕ, ∃ C X₀ : ℝ,
        0 < C ∧ 2 ≤ X₀ ∧
          ∀ X H h₀ : ℝ, X₀ ≤ X →
            LegalParameters ε X H h₀ →
            singularSquareMain H h₀ ≤
              C * H * (Real.log X) ^ k := by
  intro ε hε
  obtain ⟨C, X₀, hC, hX₀, hbound⟩ := translated_singularSquareMain_le ε hε
  exact ⟨6, C, X₀, hC, hX₀, hbound⟩

end

end SingularSeriesSquareMean
