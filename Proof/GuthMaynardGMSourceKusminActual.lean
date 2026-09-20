import GuthMaynardGMPointwiseHighTPartition
import GuthMaynardDiscreteFirstDerivative
import GuthMaynardDiscreteInverseVariationActual
import GuthMaynardDiscreteKusminActual

namespace GuthMaynardGMSourceKusminActual

open scoped BigOperators
open GuthMaynardSectionFourTrace
open GuthMaynardGMPointwiseHighTPartition
open GuthMaynardDiscreteFirstDerivative
open GuthMaynardDiscreteInverseVariationActual
open GuthMaynardDiscreteKusminActual
open GuthMaynardDiscreteCotBound

noncomputable section

/-- The literal source phase on a translated finite integer interval obeys the
 exact recurrence needed by the finite Abel identity. -/
theorem norm_sum_sourcePhase_shift_le
    (base k : ℕ) (t : ℝ)
    (hbase : 0 < base)
    (hinc0 : ∀ n, 0 < gmIncrement t (base + n))
    (hinc1 : ∀ n, gmIncrement t (base + n) ≤ 1)
    (hanti : Antitone (fun n => gmIncrement t (base + n))) :
    ‖∑ n ∈ Finset.range (k + 1), sourcePhase (base + n) t‖ ≤
      ‖inverseCoeff (gmIncrement t (base + k))‖ +
        ‖inverseCoeff (gmIncrement t base)‖ +
        (Real.cot (gmIncrement t (base + k) / 2) -
          Real.cot (gmIncrement t base / 2)) / 2 := by
  let z : ℕ → ℂ := fun n => sourcePhase (base + n) t
  let a : ℕ → ℂ := fun n => inverseCoeff (gmIncrement t (base + n))
  have hrec : ∀ n < k + 1, a n * (z (n + 1) - z n) = z n := by
    intro n hn
    have hpos : 0 < base + n := by omega
    have hstep := exp_mul_I_sub_one_ne_zero_of_unit_interval (hinc0 n) (hinc1 n)
    have hs := sourcePhase_succ_eq_mul_gmStepPhase (t := t) (n := base + n) hpos
    rw [show z (n + 1) = sourcePhase (base + n + 1) t by
      simp [z, Nat.add_assoc]]
    rw [show base + n + 1 = (base + n) + 1 by omega, hs]
    rw [show gmStepPhase t (base + n) =
      Complex.exp (Complex.I * (gmIncrement t (base + n) : ℂ)) by rfl]
    calc
      a n * (z n * Complex.exp (Complex.I * (gmIncrement t (base + n) : ℂ)) - z n) =
          (a n * (Complex.exp (Complex.I * (gmIncrement t (base + n) : ℂ)) - 1)) * z n := by ring
      _ = z n := by
        rw [show a n = inverseCoeff (gmIncrement t (base + n)) by rfl,
          inverseCoeff_mul_increment hstep]
        simp
  have hz : ∀ n ≤ k + 1, ‖z n‖ = 1 := by
    intro n hn
    dsimp [z, sourcePhase]
    simpa [mul_comm] using Complex.norm_exp_ofReal_mul_I (t * Real.log (base + n))
  have hvar_eq := sum_norm_inverseCoeff_diff k
    (fun n => gmIncrement t (base + n)) hinc0 hinc1 hanti
  have hvar : ∑ n ∈ Finset.range k, ‖a (n + 1) - a n‖ ≤
      (Real.cot (gmIncrement t (base + k) / 2) -
        Real.cot (gmIncrement t base / 2)) / 2 := by
    simpa [a] using (le_of_eq hvar_eq)
  simpa [z] using
    (norm_sum_range_le_boundary_add_variation k z a hrec hz hvar)

/-- Numeric small-step form: the literal source phase is bounded by the
 endpoint minimum increment. -/
theorem norm_sum_sourcePhase_shift_le_pi
    (base k : ℕ) (t : ℝ)
    (hbase : 0 < base)
    (hinc0 : ∀ n, 0 < gmIncrement t (base + n))
    (hinc1 : ∀ n, gmIncrement t (base + n) ≤ 1)
    (hanti : Antitone (fun n => gmIncrement t (base + n))) :
    ‖∑ n ∈ Finset.range (k + 1), sourcePhase (base + n) t‖ ≤
      3 * Real.pi / gmIncrement t (base + k) := by
  have hmain := norm_sum_sourcePhase_shift_le base k t hbase hinc0 hinc1 hanti
  have hdk := inverseCoeff_norm_le_pi_div (hinc0 k) (hinc1 k)
  have hdb := inverseCoeff_norm_le_pi_div (hinc0 0) (hinc1 0)
  have hdb' : ‖inverseCoeff (gmIncrement t base)‖ ≤ Real.pi / gmIncrement t base := by
    simpa using hdb
  have hbaseinc0 : 0 < gmIncrement t base := by simpa using hinc0 0
  have hbaseinc1 : gmIncrement t base ≤ 1 := by simpa using hinc1 0
  have hmono : gmIncrement t (base + k) ≤ gmIncrement t base := hanti (Nat.zero_le k)
  have hratio : Real.pi / gmIncrement t base ≤
      Real.pi / gmIncrement t (base + k) := by
    apply (div_le_div_iff_of_pos_left Real.pi_pos (hinc0 0) (hinc0 k)).2
    exact hmono
  have hcot := cot_half_le_pi_div (hinc0 k) (hinc1 k)
  have hcot0 : 0 ≤ Real.cot (gmIncrement t base / 2) := by
    apply GuthMaynardDiscreteInverseVariation.cot_nonneg_on_unit
    constructor
    · linarith [hbaseinc0]
    · nlinarith [hbaseinc1]
  have hvar : (Real.cot (gmIncrement t (base + k) / 2) -
      Real.cot (gmIncrement t base / 2)) / 2 ≤
      Real.pi / gmIncrement t (base + k) / 2 := by
    have hdiff : Real.cot (gmIncrement t (base + k) / 2) -
        Real.cot (gmIncrement t base / 2) ≤
        Real.cot (gmIncrement t (base + k) / 2) := by linarith
    linarith
  have hq : 0 ≤ Real.pi / gmIncrement t (base + k) :=
    (div_pos Real.pi_pos (hinc0 k)).le
  have hbound : ‖∑ n ∈ Finset.range (k + 1), sourcePhase (base + n) t‖ ≤
      Real.pi / gmIncrement t (base + k) +
        Real.pi / gmIncrement t (base + k) +
        Real.pi / gmIncrement t (base + k) / 2 := by
    linarith [hmain, hdk, hdb', hratio, hvar]
  calc
    ‖∑ n ∈ Finset.range (k + 1), sourcePhase (base + n) t‖ ≤
        Real.pi / gmIncrement t (base + k) +
          Real.pi / gmIncrement t (base + k) +
          Real.pi / gmIncrement t (base + k) / 2 := hbound
    _ = (5 / 2 : ℝ) * (Real.pi / gmIncrement t (base + k)) := by ring
    _ ≤ 3 * (Real.pi / gmIncrement t (base + k)) := by nlinarith
    _ = 3 * Real.pi / gmIncrement t (base + k) := by ring

theorem gmIncrement_shift_antitone
    {base : ℕ} {t : ℝ} (ht : 0 < t) (hbase : 0 < base) :
    Antitone (fun n => gmIncrement t (base + n)) := by
  intro n m hnm
  induction m generalizing n with
  | zero =>
      have hn : n = 0 := by omega
      simp [hn]
  | succ m ih =>
      rcases Nat.eq_or_lt_of_le hnm with hEq | hlt
      · simp [hEq]
      · have hstep : gmIncrement t (base + (m + 1)) ≤
          gmIncrement t (base + m) := by
          have hpos : 0 < base + m := by omega
          have hs := gmIncrement_succ_lt ht hpos
          simpa [Nat.add_assoc] using hs.le
        exact hstep.trans (ih (Nat.le_of_lt_succ hlt))

theorem norm_sum_sourcePhase_small_t
    (base k : ℕ) (t : ℝ)
    (hbase : 0 < base) (ht : 0 < t) (htbase : t ≤ base) :
    ‖∑ n ∈ Finset.range (k + 1), sourcePhase (base + n) t‖ ≤
      3 * Real.pi / gmIncrement t (base + k) := by
  have hinc0 : ∀ n, 0 < gmIncrement t (base + n) := by
    intro n
    unfold gmIncrement
    have hposN : 0 < base + n := by omega
    have hpos : 0 < (base + n : ℝ) := by exact_mod_cast hposN
    have hlog : 0 < Real.log (1 + 1 / (base + n : ℝ)) := by
      apply Real.log_pos
      have : 0 < 1 / (base + n : ℝ) := one_div_pos.mpr hpos
      linarith
    simpa [Nat.cast_add] using (mul_pos ht hlog)
  have hinc1 : ∀ n, gmIncrement t (base + n) ≤ 1 := by
    intro n
    unfold gmIncrement
    have hposN : 0 < base + n := by omega
    have hpos : 0 < (base + n : ℝ) := by exact_mod_cast hposN
    have hlog := Real.log_le_sub_one_of_pos
      (show 0 < 1 + 1 / (base + n : ℝ) by positivity)
    have hlog' : Real.log (1 + 1 / (base + n : ℝ)) ≤
        1 / (base + n : ℝ) := by
      convert hlog using 1 <;> ring
    have hmul := mul_le_mul_of_nonneg_left hlog' ht.le
    have htx : t ≤ (base + n : ℝ) := by
      have hbaseR : (base : ℝ) ≤ (base + n : ℝ) := by
        exact_mod_cast (Nat.le_add_right base n)
      exact htbase.trans hbaseR
    have hquot : t / (base + n : ℝ) ≤ 1 := by
      apply (div_le_iff₀ hpos).2
      simpa using htx
    have hprod : t * Real.log (1 + 1 / (base + n : ℝ)) ≤ 1 := by
      calc
        t * Real.log (1 + 1 / (base + n : ℝ)) ≤
            t * (1 / (base + n : ℝ)) := hmul
        _ = t / (base + n : ℝ) := by ring
        _ ≤ 1 := hquot
    simpa [Nat.cast_add] using hprod
  exact norm_sum_sourcePhase_shift_le_pi base k t hbase hinc0 hinc1
    (gmIncrement_shift_antitone ht hbase)

end
end GuthMaynardGMSourceKusminActual

#print axioms GuthMaynardGMSourceKusminActual.norm_sum_sourcePhase_shift_le
#print axioms GuthMaynardGMSourceKusminActual.norm_sum_sourcePhase_shift_le_pi
