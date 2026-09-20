import Mathlib

open scoped BigOperators Interval
open Interval
noncomputable section

namespace FordLogTaylor

def logTaylor (k : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range k, (-1 : ℝ) ^ j * x ^ (j + 1) / (j + 1)

lemma geom_remainder (k : ℕ) (t : ℝ) (ht : 1 + t ≠ 0) :
    1 / (1 + t) - ∑ j ∈ Finset.range k, (-1 : ℝ) ^ j * t ^ j =
      (-1 : ℝ) ^ k * t ^ k / (1 + t) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ]
      calc
        1 / (1 + t) - (∑ x ∈ Finset.range k, (-1 : ℝ) ^ x * t ^ x +
            (-1 : ℝ) ^ k * t ^ k) =
            (1 / (1 + t) - ∑ x ∈ Finset.range k, (-1 : ℝ) ^ x * t ^ x) -
              (-1 : ℝ) ^ k * t ^ k := by ring
        _ = _ := by rw [ih]; field_simp; ring

lemma hasDerivAt_logTaylor_remainder {k : ℕ} {t : ℝ} (ht : 1 + t ≠ 0) :
    HasDerivAt (fun x : ℝ => Real.log (1 + x) - logTaylor k x)
      ((-1 : ℝ) ^ k * t ^ k / (1 + t)) t := by
  have hlog : HasDerivAt (fun x : ℝ => Real.log (1 + x)) (1 / (1 + t)) t := by
    have h := ((hasDerivAt_id t).add_const 1).log (by simpa [add_comm] using ht)
    convert h using 1 <;> simp [add_comm]
  have hpoly : HasDerivAt (fun x : ℝ => logTaylor k x)
      (∑ j ∈ Finset.range k, (-1 : ℝ) ^ j * t ^ j) t := by
    unfold logTaylor
    have hs : HasDerivAt (∑ j ∈ Finset.range k,
        fun x : ℝ => (-1 : ℝ) ^ j * x ^ (j + 1) / (j + 1))
        (∑ j ∈ Finset.range k, (-1 : ℝ) ^ j * t ^ j) t := by
      apply HasDerivAt.sum
      intro j hj
      convert ((hasDerivAt_pow (j + 1) t).const_mul ((-1 : ℝ) ^ j)).div_const (j + 1) using 1
      · field_simp
        simp only [Nat.add_sub_cancel]
        push_cast
        ring
    convert hs using 1
    funext z
    simp only [Finset.sum_apply]
  convert hlog.sub hpoly using 1
  exact (geom_remainder k t ht).symm

theorem log_taylor_remainder {k : ℕ} {x : ℝ} (hx : 0 ≤ x) :
    |Real.log (1 + x) - logTaylor k x| ≤ x ^ (k + 1) / (k + 1) := by
  by_cases hxeq : x = 0
  · subst x
    simp [logTaylor]
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hxeq)
  let F : ℝ → ℝ := fun t => Real.log (1 + t) - logTaylor k t
  let G : ℝ → ℝ := fun t => (-1 : ℝ) ^ k * t ^ k / (1 + t)
  have hfund : (∫ t in (0 : ℝ)..x, G t) = F x - F 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx
    · apply ContinuousOn.sub
      · apply (continuousOn_const.add continuousOn_id).log
        intro t ht
        have := ht.1
        simp at *
        linarith
      · unfold logTaylor
        fun_prop
    · intro t ht
      exact hasDerivAt_logTaylor_remainder (by
        have := ht.1
        nlinarith)
    · have hGcont : ContinuousOn G (Set.Icc (0 : ℝ) x) := by
        apply ContinuousOn.div
        · fun_prop
        · intro t ht
          fun_prop
        · intro t ht
          have := ht.1
          positivity
      exact hGcont.intervalIntegrable_of_Icc hx
  have hrem : F x - F 0 = ∫ t in (0 : ℝ)..x, G t := hfund.symm
  have hbound : |∫ t in (0 : ℝ)..x, G t| ≤
      ∫ t in (0 : ℝ)..x, t ^ k := by
    calc
      |∫ t in (0 : ℝ)..x, G t| ≤ ∫ t in (0 : ℝ)..x, |G t| := by
        simpa only [Real.norm_eq_abs] using
          (intervalIntegral.norm_integral_le_integral_norm (f := G) hx)
      _ ≤ ∫ t in (0 : ℝ)..x, t ^ k := by
        apply intervalIntegral.integral_mono_on hx
        · exact (by
            have hGc : ContinuousOn G (Set.Icc (0 : ℝ) x) := by
              apply ContinuousOn.div
              · fun_prop
              · fun_prop
              · intro t ht; have := ht.1; positivity
            exact hGc.abs.intervalIntegrable_of_Icc hx)
        · exact (by
            exact (continuousOn_pow k).intervalIntegrable_of_Icc hx)
        · intro t ht
          have ht0 : 0 ≤ t := ht.1
          have hden : 0 < 1 + t := by linarith
          simp only [G, abs_div, abs_mul, abs_pow, abs_neg, abs_one]
          rw [abs_of_nonneg ht0, abs_of_pos hden]
          simp only [one_pow]
          exact (div_le_iff₀ hden).2 (by nlinarith [pow_nonneg ht0 k])
  have hF : F x - F 0 = Real.log (1 + x) - logTaylor k x := by
    simp [F, logTaylor]
  calc
    |Real.log (1 + x) - logTaylor k x| = |∫ t in (0 : ℝ)..x, G t| := by rw [← hF, hrem]
    _ ≤ ∫ t in (0 : ℝ)..x, t ^ k := hbound
    _ = x ^ (k + 1) / (k + 1) := by simp [integral_pow]

end FordLogTaylor

#print axioms FordLogTaylor.log_taylor_remainder
