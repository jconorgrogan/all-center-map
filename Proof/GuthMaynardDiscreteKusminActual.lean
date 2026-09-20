import GuthMaynardDiscreteFirstDerivative
import GuthMaynardDiscreteInverseVariationActual
import GuthMaynardDiscreteCotBound

namespace GuthMaynardDiscreteKusminActual

open scoped BigOperators
open GuthMaynardDiscreteFirstDerivative
open GuthMaynardDiscreteInverseVariationActual
open GuthMaynardDiscreteCotBound

noncomputable section

def cumulativePhase (d : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, d j

def cumulativePhaseExp (d : ℕ → ℝ) (n : ℕ) : ℂ :=
  Complex.exp (Complex.I * (cumulativePhase d n : ℂ))

theorem cumulativePhase_succ (d : ℕ → ℝ) (n : ℕ) :
    cumulativePhase d (n + 1) = cumulativePhase d n + d n := by
  simp [cumulativePhase, Finset.sum_range_succ]

theorem cumulativePhaseExp_unit (d : ℕ → ℝ) (n : ℕ) :
    ‖cumulativePhaseExp d n‖ = 1 := by
  unfold cumulativePhaseExp
  have h := Complex.norm_exp_ofReal_mul_I (cumulativePhase d n)
  simpa [mul_comm] using h

theorem inverseCoeff_norm_le_pi_div {d : ℝ} (hd0 : 0 < d) (hd1 : d ≤ 1) :
    ‖inverseCoeff d‖ ≤ Real.pi / d := by
  have hcot := cot_half_le_pi_div hd0 hd1
  have hnorm : ‖inverseCoeff d‖ ≤ (1 + Real.cot (d / 2)) / 2 := by
    rw [GuthMaynardDiscreteHalfAngle.inverseCoeff_halfAngle hd0 hd1]
    calc
      ‖((-1 / 2 : ℝ) : ℂ) - ((Real.cot (d / 2) / 2 : ℝ) : ℂ) * Complex.I‖ ≤
          ‖((-1 / 2 : ℝ) : ℂ)‖ +
            ‖((Real.cot (d / 2) / 2 : ℝ) : ℂ) * Complex.I‖ :=
        norm_sub_le _ _
      _ = (1 + Real.cot (d / 2)) / 2 := by
        have hcot0 : 0 ≤ Real.cot (d / 2) := by
          apply GuthMaynardDiscreteInverseVariation.cot_nonneg_on_unit
          constructor
          · linarith [hd0]
          · nlinarith [hd1]
        have hnormneg : ‖((-1 / 2 : ℝ) : ℂ)‖ = (1 / 2 : ℝ) := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by norm_num)]
          norm_num
        have hnormmul :
            ‖((Real.cot (d / 2) / 2 : ℝ) : ℂ) * Complex.I‖ =
              Real.cot (d / 2) / 2 := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (by linarith), Complex.norm_I, mul_one]
        rw [hnormneg, hnormmul]
        ring
  have hratio : 1 ≤ Real.pi / d := by
    apply (le_div_iff₀ hd0).2
    nlinarith [Real.pi_gt_three, hd1]
  linarith

theorem norm_sum_cumulativePhaseExp_le
    (k : ℕ) (d : ℕ → ℝ)
    (hd0 : ∀ n, 0 < d n) (hd1 : ∀ n, d n ≤ 1)
    (hdanti : Antitone d) :
    ‖∑ n ∈ Finset.range (k + 1), cumulativePhaseExp d n‖ ≤
      ‖inverseCoeff (d k)‖ + ‖inverseCoeff (d 0)‖ +
        (Real.cot (d k / 2) - Real.cot (d 0 / 2)) / 2 := by
  let z : ℕ → ℂ := cumulativePhaseExp d
  let a : ℕ → ℂ := fun n => inverseCoeff (d n)
  have hrec : ∀ n < k + 1, a n * (z (n + 1) - z n) = z n := by
    intro n hn
    have hstep := exp_mul_I_sub_one_ne_zero_of_unit_interval (hd0 n) (hd1 n)
    have hexp : z (n + 1) = z n * Complex.exp (Complex.I * (d n : ℂ)) := by
      unfold z cumulativePhaseExp
      rw [cumulativePhase_succ]
      rw [show Complex.I * ((cumulativePhase d n + d n : ℝ) : ℂ) =
          Complex.I * (cumulativePhase d n : ℂ) + Complex.I * (d n : ℂ) by
            push_cast; ring, Complex.exp_add]
    rw [hexp]
    calc
      a n * (z n * Complex.exp (Complex.I * (d n : ℂ)) - z n) =
          (a n * (Complex.exp (Complex.I * (d n : ℂ)) - 1)) * z n := by ring
      _ = z n := by
        rw [show a n = inverseCoeff (d n) by rfl,
          inverseCoeff_mul_increment hstep]
        simp
  have hz : ∀ n ≤ k + 1, ‖z n‖ = 1 := by
    intro n hn
    exact cumulativePhaseExp_unit d n
  have hvar_eq := sum_norm_inverseCoeff_diff k d hd0 hd1 hdanti
  have hvar : ∑ n ∈ Finset.range k, ‖a (n + 1) - a n‖ ≤
      (Real.cot (d k / 2) - Real.cot (d 0 / 2)) / 2 := by
    rw [show a = fun n => inverseCoeff (d n) by rfl]
    rw [hvar_eq]
  simpa [z, cumulativePhaseExp] using
    (norm_sum_range_le_boundary_add_variation k z a hrec hz hvar)

theorem norm_sum_cumulativePhaseExp_le_pi
    (k : ℕ) (d : ℕ → ℝ)
    (hd0 : ∀ n, 0 < d n) (hd1 : ∀ n, d n ≤ 1)
    (hdanti : Antitone d) :
    ‖∑ n ∈ Finset.range (k + 1), cumulativePhaseExp d n‖ ≤
      3 * Real.pi / d k := by
  have hmain := norm_sum_cumulativePhaseExp_le k d hd0 hd1 hdanti
  have hdk := inverseCoeff_norm_le_pi_div (hd0 k) (hd1 k)
  have hd0b := inverseCoeff_norm_le_pi_div (hd0 0) (hd1 0)
  have hdk0 : d k ≤ d 0 := hdanti (Nat.zero_le k)
  have hratio : Real.pi / d 0 ≤ Real.pi / d k := by
    apply (div_le_div_iff_of_pos_left Real.pi_pos (hd0 0) (hd0 k)).2
    exact hdk0
  have hcot := cot_half_le_pi_div (hd0 k) (hd1 k)
  have hcot0 : 0 ≤ Real.cot (d 0 / 2) := by
    apply GuthMaynardDiscreteInverseVariation.cot_nonneg_on_unit
    constructor
    · linarith [hd0 0]
    · nlinarith [hd1 0]
  have hvar : (Real.cot (d k / 2) - Real.cot (d 0 / 2)) / 2 ≤
      Real.pi / d k / 2 := by
    have hdiff : Real.cot (d k / 2) - Real.cot (d 0 / 2) ≤
        Real.cot (d k / 2) := by linarith
    linarith
  have hpi_dk : 0 ≤ Real.pi / d k := (div_pos Real.pi_pos (hd0 k)).le
  have hbound : ‖∑ n ∈ Finset.range (k + 1), cumulativePhaseExp d n‖ ≤
      Real.pi / d k + Real.pi / d k + Real.pi / d k / 2 := by
    linarith [hmain, hdk, hd0b, hratio, hvar]
  calc
    ‖∑ n ∈ Finset.range (k + 1), cumulativePhaseExp d n‖ ≤
        Real.pi / d k + Real.pi / d k + Real.pi / d k / 2 := hbound
    _ = (5 / 2 : ℝ) * (Real.pi / d k) := by ring
    _ ≤ 3 * (Real.pi / d k) := by nlinarith
    _ = 3 * Real.pi / d k := by ring

end
end GuthMaynardDiscreteKusminActual

#print axioms GuthMaynardDiscreteKusminActual.norm_sum_cumulativePhaseExp_le
#print axioms GuthMaynardDiscreteKusminActual.norm_sum_cumulativePhaseExp_le_pi
