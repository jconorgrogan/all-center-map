import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Gamma

/-!
# Polynomial times two-sided exponential envelopes

This is the real-variable integration leaf needed after Jutila's vertical
contour has been reduced to an explicit polynomial-exponential majorant.
-/

namespace JutilaPolynomialExponentialIntegral

open Real Set MeasureTheory

noncomputable section

def absPowExp (k : ℕ) (c : ℝ) (v : ℝ) : ℝ :=
  |v| ^ k * Real.exp (-c * |v|)

def shiftedAbsPowExp (A : ℝ) (k : ℕ) (c : ℝ) (v : ℝ) : ℝ :=
  (A + |v|) ^ k * Real.exp (-c * |v|)

theorem integrable_absPowExp (k : ℕ) {c : ℝ} (hc : 0 < c) :
    Integrable (absPowExp k c) := by
  have hposR : IntegrableOn
      (fun x : ℝ => x ^ (k : ℝ) * Real.exp (-c * x ^ (1 : ℝ)))
      (Set.Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow
      (by have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
      (by norm_num) hc
  have hpos : IntegrableOn (absPowExp k c) (Set.Ioi 0) := by
    apply hposR.congr_fun _ measurableSet_Ioi
    intro x hx
    have hx0 : 0 < x := hx
    simp [absPowExp, abs_of_pos hx0, Real.rpow_natCast]
  have hici : IntegrableOn (absPowExp k c) (Set.Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).2 hpos
  have hnegRaw := hpos.comp_neg
  have hneg : IntegrableOn (absPowExp k c) (Set.Iio 0) := by
    have hset : -(Set.Ioi (0 : ℝ)) = Set.Iio 0 := by simp
    rw [hset] at hnegRaw
    apply hnegRaw.congr_fun _ measurableSet_Iio
    intro x hx
    simp [absPowExp]
  rw [← integrableOn_univ, ← Set.Iio_union_Ici]
  exact hneg.union hici

theorem integral_absPowExp (k : ℕ) {c : ℝ} (hc : 0 < c) :
    ∫ v : ℝ, absPowExp k c v =
      2 * (1 / c) ^ ((k : ℝ) + 1) * (k.factorial : ℝ) := by
  have hgamma := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (k : ℝ) + 1) (r := c)
    (by positivity) hc
  have heq : (∫ x : ℝ in Set.Ioi 0,
      x ^ k * Real.exp (-c * x)) =
      (1 / c) ^ ((k : ℝ) + 1) * (k.factorial : ℝ) := by
    calc
      (∫ x : ℝ in Set.Ioi 0, x ^ k * Real.exp (-c * x)) =
          ∫ x : ℝ in Set.Ioi 0,
            x ^ (((k : ℝ) + 1) - 1) * Real.exp (-(c * x)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        simp [Real.rpow_natCast]
      _ = (1 / c) ^ ((k : ℝ) + 1) * Real.Gamma ((k : ℝ) + 1) := hgamma
      _ = (1 / c) ^ ((k : ℝ) + 1) * (k.factorial : ℝ) := by
        rw [Real.Gamma_nat_eq_factorial]
  calc
    (∫ v : ℝ, absPowExp k c v) =
        ∫ v : ℝ, (fun x : ℝ => x ^ k * Real.exp (-c * x)) |v| := by rfl
    _ = 2 * ∫ x : ℝ in Set.Ioi 0,
        x ^ k * Real.exp (-c * x) :=
      integral_comp_abs (f := fun x : ℝ => x ^ k * Real.exp (-c * x))
    _ = 2 * (1 / c) ^ ((k : ℝ) + 1) * (k.factorial : ℝ) := by
      rw [heq]
      ring

theorem integrableOn_Ioi_pow_exp (k : ℕ) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun x : ℝ => x ^ k * Real.exp (-c * x)) (Set.Ioi 0) := by
  have hposR : IntegrableOn
      (fun x : ℝ => x ^ (k : ℝ) * Real.exp (-c * x ^ (1 : ℝ)))
      (Set.Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow
      (by have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
      (by norm_num) hc
  apply hposR.congr_fun _ measurableSet_Ioi
  intro x hx
  have hx0 : 0 < x := hx
  simp [Real.rpow_natCast]

theorem integral_Ioi_pow_exp (k : ℕ) {c : ℝ} (hc : 0 < c) :
    ∫ x : ℝ in Set.Ioi 0, x ^ k * Real.exp (-c * x) =
      (1 / c) ^ ((k : ℝ) + 1) * (k.factorial : ℝ) := by
  have hgamma := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (k : ℝ) + 1) (r := c) (by positivity) hc
  calc
    (∫ x : ℝ in Set.Ioi 0, x ^ k * Real.exp (-c * x)) =
        ∫ x : ℝ in Set.Ioi 0,
          x ^ (((k : ℝ) + 1) - 1) * Real.exp (-(c * x)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      simp [Real.rpow_natCast]
    _ = (1 / c) ^ ((k : ℝ) + 1) * Real.Gamma ((k : ℝ) + 1) := hgamma
    _ = (1 / c) ^ ((k : ℝ) + 1) * (k.factorial : ℝ) := by
      rw [Real.Gamma_nat_eq_factorial]

/-- Exact binomial evaluation, avoiding the exponentially wasteful `2^k`
majorant.  This sharp form is required by the source `M` ledger. -/
theorem integral_shiftedAbsPowExp_eq
    (A : ℝ) (k : ℕ) {c : ℝ} (hc : 0 < c) :
    ∫ v : ℝ, shiftedAbsPowExp A k c v =
      2 * ∑ m ∈ Finset.range (k + 1),
        A ^ m * (1 / c) ^ (((k - m : ℕ) : ℝ) + 1) *
          ((k - m).factorial : ℝ) * (k.choose m : ℝ) := by
  calc
    (∫ v : ℝ, shiftedAbsPowExp A k c v) =
        2 * ∫ x : ℝ in Set.Ioi 0,
          (A + x) ^ k * Real.exp (-c * x) := by
      simpa [shiftedAbsPowExp] using
        (integral_comp_abs
          (f := fun x : ℝ => (A + x) ^ k * Real.exp (-c * x)))
    _ = 2 * ∫ x : ℝ in Set.Ioi 0,
        ∑ m ∈ Finset.range (k + 1),
          (A ^ m * (k.choose m : ℝ)) *
            (x ^ (k - m) * Real.exp (-c * x)) := by
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      change (A + x) ^ k * Real.exp (-c * x) =
        ∑ m ∈ Finset.range (k + 1),
          (A ^ m * (k.choose m : ℝ)) *
            (x ^ (k - m) * Real.exp (-c * x))
      rw [add_pow]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro m hm
      ring
    _ = 2 * ∑ m ∈ Finset.range (k + 1),
        ∫ x : ℝ in Set.Ioi 0,
          (A ^ m * (k.choose m : ℝ)) *
            (x ^ (k - m) * Real.exp (-c * x)) := by
      congr 1
      rw [integral_finset_sum]
      intro m hm
      exact (integrableOn_Ioi_pow_exp (k - m) hc).const_mul _
    _ = 2 * ∑ m ∈ Finset.range (k + 1),
        A ^ m * (1 / c) ^ (((k - m : ℕ) : ℝ) + 1) *
          ((k - m).factorial : ℝ) * (k.choose m : ℝ) := by
      congr 1
      apply Finset.sum_congr rfl
      intro m hm
      rw [integral_const_mul, integral_Ioi_pow_exp (k - m) hc]
      ring

theorem choose_mul_sub_factorial_le_pow
    {k m : ℕ} (hm : m ≤ k) :
    k.choose m * (k - m).factorial ≤ k ^ (k - m) := by
  calc
    k.choose m * (k - m).factorial =
        (k - m).factorial * k.choose (k - m) := by
      rw [Nat.choose_symm hm]
      exact Nat.mul_comm _ _
    _ = k.descFactorial (k - m) :=
      (Nat.descFactorial_eq_factorial_mul_choose k (k - m)).symm
    _ ≤ k ^ (k - m) := Nat.descFactorial_le_pow _ _

/-- Sharp elementary bound for the exact binomial integral.  Its effective
base is `A+k*d`, with no extraneous `2^k` loss. -/
theorem exactBinomialBudget_le
    {A d : ℝ} (hA : 0 ≤ A) (hd : 0 < d) (k : ℕ) :
    2 * ∑ m ∈ Finset.range (k + 1),
        A ^ m * d ^ (((k - m : ℕ) : ℝ) + 1) *
          ((k - m).factorial : ℝ) * (k.choose m : ℝ) ≤
      2 * d * (A + (k : ℝ) * d) ^ k := by
  have hd0 : 0 ≤ d := hd.le
  have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  rw [show 2 * d * (A + (k : ℝ) * d) ^ k =
      2 * (d * (A + (k : ℝ) * d) ^ k) by ring]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  calc
    (∑ m ∈ Finset.range (k + 1),
        A ^ m * d ^ (((k - m : ℕ) : ℝ) + 1) *
          ((k - m).factorial : ℝ) * (k.choose m : ℝ)) ≤
        ∑ m ∈ Finset.range (k + 1),
          d * (A ^ m * (((k : ℝ) * d) ^ (k - m)) *
            (k.choose m : ℝ)) := by
      apply Finset.sum_le_sum
      intro m hmrange
      have hm : m ≤ k := by
        have : m < k + 1 := Finset.mem_range.mp hmrange
        omega
      have hcoeffNat := choose_mul_sub_factorial_le_pow hm
      have hcoeff :
          ((k - m).factorial : ℝ) * (k.choose m : ℝ) ≤
            (k : ℝ) ^ (k - m) := by
        exact_mod_cast (by simpa [Nat.mul_comm] using hcoeffNat)
      have hchoose : (1 : ℝ) ≤ (k.choose m : ℝ) := by
        exact_mod_cast Nat.choose_pos hm
      have hdPow : 0 ≤ d ^ (k - m) := pow_nonneg hd0 _
      have hAPow : 0 ≤ A ^ m := pow_nonneg hA _
      have hkPow : 0 ≤ (k : ℝ) ^ (k - m) := pow_nonneg hk0 _
      have hcoeff0 : 0 ≤ ((k - m).factorial : ℝ) *
          (k.choose m : ℝ) := by positivity
      have hrpow : d ^ (((k - m : ℕ) : ℝ) + 1) =
          d ^ (k - m) * d := by
        rw [Real.rpow_add hd, Real.rpow_natCast, Real.rpow_one]
      rw [hrpow]
      have hfirst :
          A ^ m * (d ^ (k - m) * d) *
              (((k - m).factorial : ℝ) * (k.choose m : ℝ)) ≤
            d * (A ^ m * (d ^ (k - m) * (k : ℝ) ^ (k - m))) := by
        calc
          A ^ m * (d ^ (k - m) * d) *
                (((k - m).factorial : ℝ) * (k.choose m : ℝ)) =
              d * (A ^ m * d ^ (k - m) *
                (((k - m).factorial : ℝ) * (k.choose m : ℝ))) := by ring
          _ ≤ d * (A ^ m * d ^ (k - m) *
                (k : ℝ) ^ (k - m)) := by
            gcongr
          _ = d * (A ^ m *
                (d ^ (k - m) * (k : ℝ) ^ (k - m))) := by ring
      calc
        A ^ m * (d ^ (k - m) * d) *
            ((k - m).factorial : ℝ) * (k.choose m : ℝ) =
          A ^ m * (d ^ (k - m) * d) *
            (((k - m).factorial : ℝ) * (k.choose m : ℝ)) := by ring
        _ ≤ d * (A ^ m * (d ^ (k - m) * (k : ℝ) ^ (k - m))) := hfirst
        _ = d * (A ^ m * (((k : ℝ) * d) ^ (k - m))) := by
          rw [mul_pow]
          ring
        _ ≤ d * (A ^ m * (((k : ℝ) * d) ^ (k - m)) *
            (k.choose m : ℝ)) := by
          have hterm : 0 ≤ A ^ m * (((k : ℝ) * d) ^ (k - m)) := by
            positivity
          apply mul_le_mul_of_nonneg_left _ hd0
          calc
            A ^ m * (((k : ℝ) * d) ^ (k - m)) =
                A ^ m * (((k : ℝ) * d) ^ (k - m)) * 1 := by ring
            _ ≤ A ^ m * (((k : ℝ) * d) ^ (k - m)) *
                (k.choose m : ℝ) :=
              mul_le_mul_of_nonneg_left hchoose hterm
    _ = d * ∑ m ∈ Finset.range (k + 1),
          A ^ m * (((k : ℝ) * d) ^ (k - m)) *
            (k.choose m : ℝ) := by rw [Finset.mul_sum]
    _ = d * (A + (k : ℝ) * d) ^ k := by rw [add_pow]

theorem shiftedAbsPowExp_le
    {A c : ℝ} (hA : 0 ≤ A) (k : ℕ) (v : ℝ) :
    shiftedAbsPowExp A k c v ≤
      (2 : ℝ) ^ k *
        (A ^ k * absPowExp 0 c v + absPowExp k c v) := by
  let u := |v|
  have hu : 0 ≤ u := abs_nonneg v
  have hsum : A + u ≤ 2 * max A u := by
    have hAmax := le_max_left A u
    have humax := le_max_right A u
    linarith
  have hpow : (A + u) ^ k ≤ (2 * max A u) ^ k :=
    pow_le_pow_left₀ (add_nonneg hA hu) hsum k
  have hmaxpow : (max A u) ^ k ≤ A ^ k + u ^ k := by
    rcases max_cases A u with h | h
    · rw [h.1]
      exact le_add_of_nonneg_right (pow_nonneg hu k)
    · rw [h.1]
      exact le_add_of_nonneg_left (pow_nonneg hA k)
  have hexp : 0 ≤ Real.exp (-c * u) := (Real.exp_pos _).le
  unfold shiftedAbsPowExp absPowExp
  change (A + u) ^ k * Real.exp (-c * u) ≤
    2 ^ k * (A ^ k * (u ^ 0 * Real.exp (-c * u)) +
      u ^ k * Real.exp (-c * u))
  calc
    (A + u) ^ k * Real.exp (-c * u) ≤
        (2 * max A u) ^ k * Real.exp (-c * u) :=
      mul_le_mul_of_nonneg_right hpow hexp
    _ = 2 ^ k * ((max A u) ^ k * Real.exp (-c * u)) := by ring
    _ ≤ 2 ^ k * ((A ^ k + u ^ k) * Real.exp (-c * u)) := by
      gcongr
    _ = 2 ^ k * (A ^ k * (u ^ 0 * Real.exp (-c * u)) +
        u ^ k * Real.exp (-c * u)) := by ring

theorem integrable_shiftedAbsPowExp
    {A c : ℝ} (hA : 0 ≤ A) (k : ℕ) (hc : 0 < c) :
    Integrable (shiftedAbsPowExp A k c) := by
  have h0 := integrable_absPowExp 0 hc
  have hk := integrable_absPowExp k hc
  have hmajor : Integrable (fun v : ℝ =>
      (2 : ℝ) ^ k * (A ^ k * absPowExp 0 c v + absPowExp k c v)) :=
    ((h0.const_mul (A ^ k)).add hk).const_mul ((2 : ℝ) ^ k)
  apply hmajor.mono'
  · unfold shiftedAbsPowExp
    fun_prop
  · filter_upwards [] with v
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact shiftedAbsPowExp_le hA k v
    · unfold shiftedAbsPowExp
      exact mul_nonneg (pow_nonneg (add_nonneg hA (abs_nonneg v)) k)
        (Real.exp_pos _).le

theorem integral_shiftedAbsPowExp_le
    {A c : ℝ} (hA : 0 ≤ A) (k : ℕ) (hc : 0 < c) :
    ∫ v : ℝ, shiftedAbsPowExp A k c v ≤
      (2 : ℝ) ^ k *
        (A ^ k * (2 / c) +
          2 * (1 / c) ^ ((k : ℝ) + 1) * (k.factorial : ℝ)) := by
  have hshift := integrable_shiftedAbsPowExp hA k hc
  have h0 := integrable_absPowExp 0 hc
  have hk := integrable_absPowExp k hc
  have hmajor : Integrable (fun v : ℝ =>
      (2 : ℝ) ^ k * (A ^ k * absPowExp 0 c v + absPowExp k c v)) :=
    ((h0.const_mul (A ^ k)).add hk).const_mul ((2 : ℝ) ^ k)
  have hzero : (∫ v : ℝ, absPowExp 0 c v) = 2 / c := by
    rw [integral_absPowExp 0 hc]
    simp only [Nat.cast_zero, zero_add, Real.rpow_one, Nat.factorial_zero,
      Nat.cast_one]
    field_simp
  calc
    (∫ v : ℝ, shiftedAbsPowExp A k c v) ≤
        ∫ v : ℝ, (2 : ℝ) ^ k *
          (A ^ k * absPowExp 0 c v + absPowExp k c v) := by
      apply integral_mono hshift hmajor
      intro v
      exact shiftedAbsPowExp_le hA k v
    _ = (2 : ℝ) ^ k *
        (A ^ k * (2 / c) +
          2 * (1 / c) ^ ((k : ℝ) + 1) * (k.factorial : ℝ)) := by
      rw [integral_const_mul,
        integral_add (h0.const_mul (A ^ k)) hk,
        integral_const_mul, hzero, integral_absPowExp k hc]

end

end JutilaPolynomialExponentialIntegral

#print axioms JutilaPolynomialExponentialIntegral.integrable_absPowExp
#print axioms JutilaPolynomialExponentialIntegral.integral_absPowExp
#print axioms JutilaPolynomialExponentialIntegral.integral_shiftedAbsPowExp_eq
#print axioms JutilaPolynomialExponentialIntegral.integrable_shiftedAbsPowExp
#print axioms JutilaPolynomialExponentialIntegral.integral_shiftedAbsPowExp_le
