import MRTProposition51FirstAnalytic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

namespace MAPMRTOrdinarySlidingMassBudget
open MeasureTheory Set
open scoped BigOperators
open MAPMRTCorollary53Source MAPMRTProposition51FirstAnalytic
noncomputable section

theorem mapMangoldtCoeff_norm_le_log {X : ℝ} (hX : 2 ≤ X)
    {n : ℕ} (hn : n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊) :
    ‖mapMangoldtCoeff X n‖ ≤ Real.log (2 * X) := by
  rw [mapMangoldtCoeff, if_pos hn, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  have hn' := Finset.mem_Ioc.mp hn
  have hnp : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hne : (n : ℝ) ≤ 2 * X :=
    (by exact_mod_cast hn'.2 : (n : ℝ) ≤ (⌊2 * X⌋₊ : ℝ)).trans
      (Nat.floor_le (by linarith))
  exact ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log hnp hne)

theorem ordinaryWindowSum_map_le {X H : ℝ} (hX : 2 ≤ X)
    (hH : 1 ≤ H) (hHX : H ≤ X) (x : ℝ) :
    ordinaryWindowSum X H (mapMangoldtCoeff X) x ≤
      4 * H * Real.log (2 * X) := by
  have hlog : 0 ≤ Real.log (2 * X) := Real.log_nonneg (by linarith)
  by_cases hx : 0 ≤ x
  · let s := (Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊).filter
      (fun n : ℕ => x ≤ (n : ℝ) ∧ (n : ℝ) ≤ x + H)
    have hsub : s ⊆ Finset.Icc ⌊x⌋₊ ⌊x + H⌋₊ := by
      intro n hn
      have hn' := (Finset.mem_filter.mp hn).2
      apply Finset.mem_Icc.mpr
      exact ⟨(Nat.floor_le hx).trans hn'.1 |> fun h => by exact_mod_cast h,
        (Nat.le_floor_iff (by linarith)).mpr hn'.2⟩
    have hfl : ⌊x⌋₊ ≤ ⌊x + H⌋₊ + 1 := by
      have := Nat.floor_mono (show x ≤ x + H by linarith)
      omega
    have hcard : (s.card : ℝ) ≤ 4 * H := by
      have hc := Nat.cast_le (α := ℝ).mpr (Finset.card_le_card hsub)
      rw [Nat.card_Icc, Nat.cast_sub hfl, Nat.cast_add, Nat.cast_one] at hc
      have hf := Nat.floor_le (show 0 ≤ x + H by linarith)
      have hl := Nat.lt_floor_add_one x
      linarith
    have heq : ordinaryWindowSum X H (mapMangoldtCoeff X) x =
        ∑ n ∈ s, ‖mapMangoldtCoeff X n‖ := by
      simp [ordinaryWindowSum, s, Finset.sum_filter]
    rw [heq]
    calc
      _ ≤ ∑ n ∈ s, Real.log (2 * X) := by
        apply Finset.sum_le_sum
        intro n hn
        exact mapMangoldtCoeff_norm_le_log hX (Finset.mem_filter.mp hn).1
      _ = (s.card : ℝ) * Real.log (2 * X) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard hlog
  · have heq : ordinaryWindowSum X H (mapMangoldtCoeff X) x = 0 := by
      unfold ordinaryWindowSum
      apply Finset.sum_eq_zero
      intro n hn
      have hnlo : X < (n : ℝ) :=
        (Nat.floor_lt (by linarith : 0 ≤ X)).mp (Finset.mem_Ioc.mp hn).1
      rw [if_neg (by intro h; linarith [h.2])]
    rw [heq]
    positivity

theorem integral_ordinaryWindowSum {X H : ℝ} (hH : 0 ≤ H) (f : ℕ → ℂ) :
    (∫ x : ℝ, ordinaryWindowSum X H f x) = H * coefficientMass X f := by
  unfold ordinaryWindowSum coefficientMass
  rw [integral_finset_sum _ (fun n _ => integrable_ordinaryWindowTerm H f n)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have heq : (fun x : ℝ => if x ≤ (n : ℝ) ∧ (n : ℝ) ≤ x + H then ‖f n‖ else 0) =
      (Icc ((n : ℝ) - H) n).indicator (fun _ => ‖f n‖) := by
    funext x
    simp only [Set.indicator, Set.mem_Icc]
    congr 1
    ext
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  rw [heq, integral_indicator measurableSet_Icc, setIntegral_const,
    MeasureTheory.Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
  simp [sub_sub_cancel, smul_eq_mul]

theorem coefficientMass_map_le {X : ℝ} (hX : 2 ≤ X) :
    coefficientMass X (mapMangoldtCoeff X) ≤ 2 * X * Real.log (2 * X) := by
  have hlog : 0 ≤ Real.log (2 * X) := Real.log_nonneg (by linarith)
  unfold coefficientMass
  calc
    _ ≤ ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊, Real.log (2 * X) := by
      apply Finset.sum_le_sum
      exact fun n hn => mapMangoldtCoeff_norm_le_log hX hn
    _ = ((Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊).card : ℝ) * Real.log (2 * X) := by simp
    _ ≤ 2 * X * Real.log (2 * X) := by
      apply mul_le_mul_of_nonneg_right _ hlog
      rw [Nat.card_Ioc]
      exact (by exact_mod_cast (Nat.sub_le ⌊2 * X⌋₊ ⌊X⌋₊) :
        ((⌊2 * X⌋₊ - ⌊X⌋₊ : ℕ) : ℝ) ≤ (⌊2 * X⌋₊ : ℝ)).trans
          (Nat.floor_le (by linarith))

theorem ordinarySlidingMass_map_le {X H : ℝ} (hX : 2 ≤ X)
    (hH : 1 ≤ H) (hHX : H ≤ X) :
    ordinarySlidingMass X H (mapMangoldtCoeff X) ≤
      8 * X * H ^ 2 * Real.log (2 * X) ^ 2 := by
  have hlog : 0 ≤ Real.log (2 * X) := Real.log_nonneg (by linarith)
  rw [ordinarySlidingMass_eq_integral_ordinaryWindowSum]
  calc
    _ ≤ ∫ x : ℝ, (4 * H * Real.log (2 * X)) *
        ordinaryWindowSum X H (mapMangoldtCoeff X) x := by
      apply integral_mono (integrable_sq_ordinaryWindowSum _ _ _)
        ((integrable_ordinaryWindowSum _ _ _).const_mul _)
      intro x
      have hp := ordinaryWindowSum_map_le hX hH hHX x
      have hn := ordinaryWindowSum_nonneg X H (mapMangoldtCoeff X) x
      nlinarith
    _ = (4 * H * Real.log (2 * X)) *
        (H * coefficientMass X (mapMangoldtCoeff X)) := by
      rw [integral_const_mul, integral_ordinaryWindowSum (by linarith)]
    _ ≤ (4 * H * Real.log (2 * X)) *
        (H * (2 * X * Real.log (2 * X))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left (coefficientMass_map_le hX) (by linarith)
    _ = _ := by ring
end
end MAPMRTOrdinarySlidingMassBudget
#print axioms MAPMRTOrdinarySlidingMassBudget.ordinarySlidingMass_map_le
