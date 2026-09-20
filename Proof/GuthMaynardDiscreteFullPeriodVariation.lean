import GuthMaynardDiscreteFirstDerivative
import GuthMaynardDiscreteInverseVariation
import GuthMaynardDiscreteImagVariation
import GuthMaynardDiscreteFullPeriod

namespace GuthMaynardDiscreteFullPeriodVariation

open GuthMaynardDiscreteFirstDerivative
open GuthMaynardDiscreteInverseVariation
open GuthMaynardDiscreteImagVariation
open GuthMaynardDiscreteFullPeriod

noncomputable section

theorem sum_norm_inverseCoeff_diff
    (k : ℕ) (d : ℕ → ℝ)
    (hd0 : ∀ n, 0 < d n) (hd1 : ∀ n, d n < 2 * Real.pi)
    (hdanti : Antitone d) :
    ∑ n ∈ Finset.range k,
        ‖inverseCoeff (d (n + 1)) - inverseCoeff (d n)‖ =
      (Real.cot (d k / 2) - Real.cot (d 0 / 2)) / 2 := by
  let b : ℕ → ℝ := fun n => Real.cot (d n / 2) / 2
  have hb : Monotone b := by
    intro n m hnm
    unfold b
    have hdnm : d m ≤ d n := hdanti hnm
    have hnmem : d n / 2 ∈ Set.Ioo (0 : ℝ) Real.pi := by
      constructor
      · nlinarith [hd0 n]
      · nlinarith [hd1 n]
    have hmmem : d m / 2 ∈ Set.Ioo (0 : ℝ) Real.pi := by
      constructor
      · nlinarith [hd0 m]
      · nlinarith [hd1 m]
    have hhalf : d m / 2 ≤ d n / 2 := by linarith
    have hc := cot_antitone_on_pi hmmem hnmem hhalf
    linarith
  calc
    ∑ n ∈ Finset.range k,
        ‖inverseCoeff (d (n + 1)) - inverseCoeff (d n)‖ =
      ∑ n ∈ Finset.range k,
        ‖imagCoeff (b (n + 1)) - imagCoeff (b n)‖ := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [inverseCoeff_halfAngle (hd0 (n + 1)) (hd1 (n + 1)),
            inverseCoeff_halfAngle (hd0 n) (hd1 n)]
          simp [imagCoeff, b]
    _ = b k - b 0 := sum_norm_imagCoeff_diff_of_monotone k b hb
    _ = (Real.cot (d k / 2) - Real.cot (d 0 / 2)) / 2 := by
      unfold b
      ring


theorem norm_sum_le_margin
    (k : ℕ) (d : ℕ → ℝ) (z : ℕ → ℂ) {δ : ℝ}
    (hδ : 0 < δ) (hdlo : ∀ n, δ ≤ d n)
    (hdhi : ∀ n, d n ≤ 2 * Real.pi - δ) (hdanti : Antitone d)
    (hrec : ∀ n < k + 1, z (n + 1) = z n * Complex.exp (Complex.I * (d n : ℂ)))
    (hz : ∀ n ≤ k + 1, ‖z n‖ = 1) :
    ‖∑ n ∈ Finset.range (k + 1), z n‖ ≤ 3 * Real.pi / δ := by
  have hd0 : ∀ n, 0 < d n := fun n => lt_of_lt_of_le hδ (hdlo n)
  have hd2 : ∀ n, d n < 2 * Real.pi := by intro n; linarith [hdhi n]
  let a : ℕ → ℂ := fun n => inverseCoeff (d n)
  have ha : ∀ n < k + 1, a n * (z (n + 1) - z n) = z n := by
    intro n hn
    rw [hrec n hn]
    calc
      a n * (z n * Complex.exp (Complex.I * (d n : ℂ)) - z n) =
          (a n * (Complex.exp (Complex.I * (d n : ℂ)) - 1)) * z n := by ring
      _ = z n := by
        rw [show a n = inverseCoeff (d n) by rfl,
          inverseCoeff_mul_increment (exp_sub_one_ne_zero (hd0 n) (hd2 n))]
        simp
  have hvar_eq := sum_norm_inverseCoeff_diff k d hd0 hd2 hdanti
  have hcK := abs_le.mp (abs_cot_half_le_pi_div_margin hδ (hdlo k) (hdhi k))
  have hc0 := abs_le.mp (abs_cot_half_le_pi_div_margin hδ (hdlo 0) (hdhi 0))
  have hvar : ∑ n ∈ Finset.range k, ‖a (n + 1) - a n‖ ≤ Real.pi / δ := by
    change (∑ n ∈ Finset.range k,
      ‖inverseCoeff (d (n + 1)) - inverseCoeff (d n)‖) ≤ Real.pi / δ
    rw [hvar_eq]
    linarith
  have hmain := norm_sum_range_le_boundary_add_variation k z a ha hz hvar
  have hk := inverseCoeff_norm_le_pi_div_margin hδ (hdlo k) (hdhi k)
  have h0 := inverseCoeff_norm_le_pi_div_margin hδ (hdlo 0) (hdhi 0)
  dsimp [a] at hmain
  rw [show 3 * Real.pi / δ = 3 * (Real.pi / δ) by ring]
  linarith

theorem norm_sum_le_margin_finite
    (k : ℕ) (d : ℕ → ℝ) (z : ℕ → ℂ) {δ : ℝ}
    (hδ : 0 < δ) (hdlo : ∀ n ≤ k, δ ≤ d n)
    (hdhi : ∀ n ≤ k, d n ≤ 2 * Real.pi - δ)
    (hdanti : AntitoneOn d (Set.Iic k))
    (hrec : ∀ n < k + 1, z (n + 1) = z n * Complex.exp (Complex.I * (d n : ℂ)))
    (hz : ∀ n ≤ k + 1, ‖z n‖ = 1) :
    ‖∑ n ∈ Finset.range (k + 1), z n‖ ≤ 3 * Real.pi / δ := by
  let e : ℕ → ℝ := fun n => d (min n k)
  apply norm_sum_le_margin k e z hδ
  · intro n; exact hdlo _ (min_le_right _ _)
  · intro n; exact hdhi _ (min_le_right _ _)
  · intro n m hnm
    exact hdanti (show min n k ∈ Set.Iic k from min_le_right n k)
      (show min m k ∈ Set.Iic k from min_le_right m k) (min_le_min_right k hnm)
  · intro n hn
    simpa [e, min_eq_left (show n ≤ k by omega)] using hrec n hn
  · exact hz

end
end GuthMaynardDiscreteFullPeriodVariation
#print axioms GuthMaynardDiscreteFullPeriodVariation.sum_norm_inverseCoeff_diff
#print axioms GuthMaynardDiscreteFullPeriodVariation.norm_sum_le_margin_finite
