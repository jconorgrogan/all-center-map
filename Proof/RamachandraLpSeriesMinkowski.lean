import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# A literal infinite-series Minkowski adapter

This file isolates the functional-analytic step used in the Ramachandra
long/short shell assembly.  It does not assume the desired moment bound.
Given pointwise convergence of the literal shell series and summable certified
upper bounds for the individual `L^p` seminorms, it bounds the seminorm of the
literal pointwise sum by the scalar series.
-/

namespace RamachandraLpSeriesMinkowski

open MeasureTheory Filter
open scoped ENNReal Topology BigOperators

noncomputable section

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
  {μ : Measure α} {p : ℝ≥0∞}

private theorem eLpNorm_finset_sum_le_sum
    (hp : 1 ≤ p) {f : ℕ → α → E}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (s : Finset ℕ) :
    eLpNorm (fun x => ∑ n ∈ s, f n x) p μ ≤
      ∑ n ∈ s, eLpNorm (f n) p μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert n s hn ih =>
      simp only [Finset.sum_insert hn]
      have hsumMeas : AEStronglyMeasurable (fun x => ∑ i ∈ s, f i x) μ := by
        fun_prop
      refine (eLpNorm_add_le hp).trans ?_
      exact add_le_add_right ih _

/-- Infinite Minkowski for a literal pointwise series.  The conclusion is
about the supplied pointwise sum `g`, not an abstract representative in `Lp`.
This is the exact form needed to weld the dyadic contour shells. -/
theorem eLpNorm_le_tsum_of_ae_hasSum
    (hp : 1 ≤ p) {f : ℕ → α → E} {g : α → E} {a : ℕ → ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (ha0 : ∀ n, 0 ≤ a n)
    (ha : Summable a)
    (hfa : ∀ n, eLpNorm (f n) p μ ≤ ENNReal.ofReal (a n))
    (hsum : ∀ᵐ x ∂μ, HasSum (fun n => f n x) (g x)) :
    eLpNorm g p μ ≤ ENNReal.ofReal (∑' n, a n) := by
  let F : ℕ → α → E := fun N x => ∑ n ∈ Finset.range N, f n x
  have hFmeas : ∀ N, AEStronglyMeasurable (F N) μ := by
    intro N
    dsimp [F]
    fun_prop
  have hFtendsto : ∀ᵐ x ∂μ, Tendsto (F · x) atTop (𝓝 (g x)) := by
    filter_upwards [hsum] with x hx
    simpa [F] using hx.tendsto_sum_nat
  apply Lp.eLpNorm_le_of_ae_tendsto
      (C := ENNReal.ofReal (∑' n, a n)) (u := atTop)
      (f := F) (g := g)
  · filter_upwards with N
    calc
      eLpNorm (F N) p μ ≤
          ∑ n ∈ Finset.range N, eLpNorm (f n) p μ :=
        eLpNorm_finset_sum_le_sum hp hf (Finset.range N)
      _ ≤ ∑ n ∈ Finset.range N, ENNReal.ofReal (a n) := by
        gcongr with n hn
        exact hfa n
      _ = ENNReal.ofReal (∑ n ∈ Finset.range N, a n) := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro n hn
        exact ha0 n
      _ ≤ ENNReal.ofReal (∑' n, a n) := by
        have htotal0 : 0 ≤ ∑' n, a n := tsum_nonneg ha0
        rw [ENNReal.ofReal_le_ofReal_iff htotal0]
        exact ha.sum_le_tsum (Finset.range N) (fun n hn => ha0 n)
  · exact hFmeas
  · exact aestronglyMeasurable_of_tendsto_ae _ hFmeas hFtendsto
  · exact hFtendsto

/-- Convenience specialization for the square-integrable shell assembly. -/
theorem eLpNorm_two_le_tsum_of_ae_hasSum
    {f : ℕ → α → E} {g : α → E} {a : ℕ → ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (ha0 : ∀ n, 0 ≤ a n)
    (ha : Summable a)
    (hfa : ∀ n, eLpNorm (f n) 2 μ ≤ ENNReal.ofReal (a n))
    (hsum : ∀ᵐ x ∂μ, HasSum (fun n => f n x) (g x)) :
    eLpNorm g 2 μ ≤ ENNReal.ofReal (∑' n, a n) :=
  eLpNorm_le_tsum_of_ae_hasSum (p := 2) (by norm_num) hf ha0 ha hfa hsum

end
end RamachandraLpSeriesMinkowski

#print axioms RamachandraLpSeriesMinkowski.eLpNorm_le_tsum_of_ae_hasSum
#print axioms RamachandraLpSeriesMinkowski.eLpNorm_two_le_tsum_of_ae_hasSum
