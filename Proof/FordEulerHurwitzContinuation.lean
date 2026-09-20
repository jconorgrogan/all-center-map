import FordEulerHurwitzAboveOne
import FordEulerCellAnalytic
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.NumberTheory.LSeries.HurwitzZeta

open Set
open scoped BigOperators Topology
noncomputable section

namespace FordEulerHurwitzContinuation

open FordEulerCellAnalytic

theorem hurwitz_eq_finite_add_cellSeries_upper_right
    {u : ℝ} (hu : u ∈ Icc 0 1) {M : ℕ} (hM : 1 ≤ M)
    {s : ℂ} (hsre : 0 < s.re) (hsim : 0 < s.im) :
    HurwitzZeta.hurwitzZeta (u : UnitAddCircle) s =
      (∑ n ∈ Finset.range M, (((n : ℝ) + u : ℝ) : ℂ) ^ (-s)) +
        ((((M : ℝ) + u : ℝ) : ℂ) ^ (1 - s)) / (s - 1) + cellSeries M u s := by
  let U : Set ℂ := {z : ℂ | 0 < z.re ∧ 0 < z.im}
  let F : ℂ → ℂ := fun z => HurwitzZeta.hurwitzZeta (u : UnitAddCircle) z
  let G : ℂ → ℂ := fun z =>
    (∑ n ∈ Finset.range M, (((n : ℝ) + u : ℝ) : ℂ) ^ (-z)) +
      ((((M : ℝ) + u : ℝ) : ℂ) ^ (1 - z)) / (z - 1) + cellSeries M u z
  have hUopen : IsOpen U := by
    dsimp [U]
    exact (Complex.continuous_re.isOpen_preimage _ isOpen_Ioi).inter
      (Complex.continuous_im.isOpen_preimage _ isOpen_Ioi)
  have hUpre : IsPreconnected U := by
    dsimp [U]
    simpa only [Set.mem_setOf_eq] using
      ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_gt 0)).isPreconnected
  have hF : AnalyticOnNhd ℂ F U := by
    apply DifferentiableOn.analyticOnNhd
    · intro z hz
      have hz1 : z ≠ 1 := by
        intro h
        subst z
        dsimp [U] at hz
        norm_num at hz
      exact (HurwitzZeta.differentiableAt_hurwitzZeta (u : UnitAddCircle) hz1).differentiableWithinAt
    · exact hUopen
  have hG : AnalyticOnNhd ℂ G U := by
    apply DifferentiableOn.analyticOnNhd
    · intro z hz
      have hzre : 0 < z.re := hz.1
      have hzim : 0 < z.im := hz.2
      have hz1 : z ≠ 1 := by
        intro h
        subst z
        norm_num at hzim
      have hfinite : DifferentiableAt ℂ (fun w : ℂ =>
          ∑ n ∈ Finset.range M, (((n : ℝ) + u : ℝ) : ℂ) ^ (-w)) z := by
        refine DifferentiableAt.fun_sum fun n hn => ?_
        have hneg : DifferentiableAt ℂ (fun w : ℂ => -w) z := differentiableAt_id.neg
        by_cases hbase : (((n : ℝ) + u : ℝ) : ℂ) = 0
        · have hexp : -z ≠ 0 := by
            intro he
            have hz0 : z = 0 := neg_eq_zero.mp he
            subst z
            norm_num at hzre
          exact hneg.const_cpow (Or.inr hexp)
        · exact hneg.const_cpow (Or.inl hbase)
      have hMpos : 0 < (M : ℝ) + u := by
        have hMr : (0 : ℝ) < M := by exact_mod_cast Nat.zero_lt_of_lt hM
        linarith [hu.1]
      have hM0 : ((((M : ℝ) + u : ℝ) : ℂ) ≠ 0) := by
        exact_mod_cast (ne_of_gt hMpos)
      have hone_sub : DifferentiableAt ℂ (fun w : ℂ => 1 - w) z :=
        (differentiableAt_const (c := (1 : ℂ))).sub differentiableAt_id
      have hcorr : DifferentiableAt ℂ (fun w : ℂ =>
          ((((M : ℝ) + u : ℝ) : ℂ) ^ (1 - w)) / (w - 1)) z := by
        have hnum := hone_sub.const_cpow (Or.inl hM0)
        have hden : DifferentiableAt ℂ (fun w : ℂ => w - 1) z :=
          differentiableAt_id.sub_const 1
        have hden0 : z - 1 ≠ 0 := by
          intro h
          have hi := congrArg Complex.im h
          simp at hi
          linarith
        exact hnum.div hden hden0
      have hcell : DifferentiableAt ℂ (cellSeries M u) z :=
        differentiableAt_cellSeries hM hu.1 hzre hz1
      exact ((hfinite.add hcorr).add hcell).differentiableWithinAt
    · exact hUopen
  have hbase : (2 + Complex.I : ℂ) ∈ U := by
    dsimp [U]
    norm_num
  have hfg : F =ᶠ[𝓝 (2 + Complex.I : ℂ)] G := by
    refine Filter.eventually_of_mem (U := {z : ℂ | 1 < z.re}) ?_ ?_
    · exact (Complex.continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by norm_num)
    · intro z hz
      dsimp [F, G]
      simpa using
        (FordEulerHurwitzAboveOne.hurwitz_eq_finite_add_cellSeries hu hM hz)
  have hEq : EqOn F G U :=
    AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hF hG hUpre hbase hfg
  have hsU : s ∈ U := by
    dsimp [U]
    exact ⟨hsre, hsim⟩
  exact hEq hsU

end FordEulerHurwitzContinuation

#print axioms FordEulerHurwitzContinuation.hurwitz_eq_finite_add_cellSeries_upper_right
