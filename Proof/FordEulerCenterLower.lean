import DirichletLQuantitativeFoundation
import FordEulerPowerTail

open scoped BigOperators
noncomputable section
namespace FordEulerCenterLower

open FordEulerPowerTail

private def inverseCoeff {N : ℕ} (χ : DirichletCharacter ℂ N) : ℕ → ℂ :=
  (fun n : ℕ => χ n) * (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ))

private lemma inverseCoeff_norm_le_one {N : ℕ} (χ : DirichletCharacter ℂ N)
    {n : ℕ} (hn : n ≠ 0) : ‖inverseCoeff χ n‖ ≤ 1 := by
  simp only [inverseCoeff, Pi.mul_apply, norm_mul]
  have hχ := χ.norm_le_one n
  have hμ := ArithmeticFunction.abs_moebius_le_one (n := n)
  have hμR : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
    exact_mod_cast hμ
  have hμC : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
    simpa [Complex.norm_intCast] using hμR
  exact mul_le_one₀ hχ (norm_nonneg _) hμC

private lemma shifted_power_sum_bound {σ : ℝ} (hσ : 1 < σ) :
    (∑' n : ℕ, (1 + n : ℝ) ^ (-σ)) ≤ 1 + 1 / (σ - 1) := by
  have hp := FordEulerPowerTail.tsum_power_le (a := (1 : ℝ))
    (sigma := σ - 1) (by norm_num) (by linarith)
  simpa [show -(σ - 1 : ℝ) - 1 = -σ by ring] using hp

private lemma inverseCoeff_lseries_norm_le {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    ‖LSeries (inverseCoeff χ) s‖ ≤ 1 + 1 / (s.re - 1) := by
  have hsum : Summable (LSeries.term (inverseCoeff χ) s) :=
    LSeriesSummable_of_bounded_of_one_lt_re
      (fun n hn => inverseCoeff_norm_le_one χ hn) hs
  let p : ℕ → ℝ := fun n => if n = 0 then 0 else (n : ℝ) ^ (-s.re)
  have hp_shift : Summable (fun n : ℕ => p (n + 1)) := by
    have hb := Real.summable_nat_rpow.mpr (by linarith : -s.re < -1)
    simpa [p, Nat.cast_add, Nat.cast_one, add_comm] using
      (summable_nat_add_iff 1).2 hb
  have hp : Summable p := (summable_nat_add_iff 1).mp hp_shift
  have hpsum : (∑' n : ℕ, p n) = ∑' n : ℕ, (1 + n : ℝ) ^ (-s.re) := by
    have hsplit := hp.sum_add_tsum_nat_add 1
    simpa [p, add_comm] using hsplit.symm
  have hnorm : ‖LSeries (inverseCoeff χ) s‖ ≤ ∑' n : ℕ, p n := by
    change ‖∑' n : ℕ, LSeries.term (inverseCoeff χ) s n‖ ≤ ∑' n : ℕ, p n
    calc
      _ ≤ ∑' n : ℕ, ‖LSeries.term (inverseCoeff χ) s n‖ :=
        norm_tsum_le_tsum_norm hsum.norm
      _ ≤ ∑' n : ℕ, p n := by
        apply Summable.tsum_le_tsum _ hsum.norm hp
        intro n
        rw [LSeries.norm_term_eq]
        split_ifs with hn
        · simp [p, hn]
        · have hcoeff := inverseCoeff_norm_le_one χ hn
          have hden : 0 ≤ (n : ℝ) ^ s.re := by positivity
          have hterm : ‖inverseCoeff χ n‖ / (n : ℝ) ^ s.re ≤
              1 / (n : ℝ) ^ s.re :=
            div_le_div_of_nonneg_right hcoeff hden
          simpa [p, hn, Real.rpow_neg] using hterm
  rw [hpsum] at hnorm
  exact hnorm.trans (shifted_power_sum_bound hs)

theorem norm_LFunction_lower {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    (s.re - 1) / s.re ≤ ‖DirichletCharacter.LFunction χ s‖ := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  have hginv : LSeries (fun n : ℕ => χ n) s *
      LSeries (inverseCoeff χ) s = 1 := by
    simpa [inverseCoeff] using DirichletCharacter.LSeries.mul_mu_eq_one χ hs
  have hg := inverseCoeff_lseries_norm_le χ hs
  have hnorm_nonneg : 0 ≤ ‖LSeries (fun n : ℕ => χ n) s‖ := norm_nonneg _
  have hone : 1 ≤ (1 + 1 / (s.re - 1)) *
      ‖LSeries (fun n : ℕ => χ n) s‖ := by
    calc
      1 = ‖LSeries (fun n : ℕ => χ n) s * LSeries (inverseCoeff χ) s‖ := by
        rw [hginv, norm_one]
      _ = ‖LSeries (inverseCoeff χ) s‖ *
          ‖LSeries (fun n : ℕ => χ n) s‖ := by
        rw [norm_mul, mul_comm]
      _ ≤ (1 + 1 / (s.re - 1)) *
          ‖LSeries (fun n : ℕ => χ n) s‖ := by
        gcongr
  have hsigpos : 0 < s.re := by linarith
  have hdenpos : 0 < s.re - 1 := by linarith
  have hineq : s.re - 1 ≤ s.re *
      ‖LSeries (fun n : ℕ => χ n) s‖ := by
    have hm := mul_le_mul_of_nonneg_left hone (le_of_lt hdenpos)
    calc
      s.re - 1 = (s.re - 1) * 1 := by ring
      _ ≤ (s.re - 1) * ((1 + 1 / (s.re - 1)) *
          ‖LSeries (fun n : ℕ => χ n) s‖) := hm
      _ = s.re * ‖LSeries (fun n : ℕ => χ n) s‖ := by
        field_simp [ne_of_gt hdenpos]
        ring
  apply (div_le_iff₀ hsigpos).2
  simpa [mul_comm] using hineq

theorem norm_LFunction_one_add_delta_lower {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {δ t : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    δ / 2 ≤ ‖DirichletCharacter.LFunction χ
      (((1 + δ : ℝ) : ℂ) + Complex.I * (t : ℂ))‖ := by
  have hs : 1 < (((1 + δ : ℝ) : ℂ) + Complex.I * (t : ℂ)).re := by
    simp
    linarith
  have hmain := norm_LFunction_lower χ hs
  have hden : 0 < 1 + δ := by linarith
  have hdelta : δ / 2 ≤ δ / (1 + δ) := by
    apply (div_le_div_iff₀ (by positivity) hden).2
    nlinarith
  have hmain' : δ / (1 + δ) ≤ ‖DirichletCharacter.LFunction χ
      (((1 + δ : ℝ) : ℂ) + Complex.I * (t : ℂ))‖ := by
    simpa using hmain
  exact hdelta.trans hmain'

end FordEulerCenterLower

#print axioms FordEulerCenterLower.norm_LFunction_lower
#print axioms FordEulerCenterLower.norm_LFunction_one_add_delta_lower
