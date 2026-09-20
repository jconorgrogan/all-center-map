import KhaleAppendixB1ZetaReduction
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.PSeries
import Mathlib.Order.SuccPred.IntervalSucc
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalAverage
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Certified sharp zeta bound for Khale Appendix B

This proves the exact elementary estimate used in Khale's `(lazyzeta)` step.
The key device is a midpoint convexity bound
`ζ(1+η) ≤ 1 + (3/2)^(-η)/η`, followed by exact rational Taylor
bounds on `log(3/2)` and `exp`.
-/

namespace MAPKhaleAppendixBZetaPointwiseCertified

noncomputable section

open Set MeasureTheory intervalIntegral
open scoped Interval Function


lemma convex_neg_rpow {eta : ℝ} (heta : 0 < eta) :
    ConvexOn ℝ (Set.Ici (1/2 : ℝ)) (fun x : ℝ => x ^ (-(1+eta) : ℝ)) := by
  let p : ℝ := -(1 + eta)
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ici _)
  · exact (continuousOn_id.rpow_const (fun x hx => Or.inl (by simp only [id_eq]; change (1/2:ℝ) ≤ x at hx; linarith)))
  · intro x hx
    have hx0 : x ≠ 0 := by rw [interior_Ici] at hx; have := Set.mem_Ioi.mp hx; linarith
    exact (Real.hasDerivAt_rpow_const (p := p) (Or.inl hx0)).hasDerivWithinAt
  · intro x hx
    have hx0 : x ≠ 0 := by rw [interior_Ici] at hx; have := Set.mem_Ioi.mp hx; linarith
    exact ((Real.hasDerivAt_rpow_const (p := p - 1) (Or.inl hx0)).const_mul p).hasDerivWithinAt
  · intro x hx
    dsimp [p]
    have hxpos : 0 < x := by rw [interior_Ici] at hx; have := Set.mem_Ioi.mp hx; linarith
    have hpow : 0 ≤ x ^ (-(1+eta) - 2 : ℝ) := Real.rpow_nonneg hxpos.le _
    have hc : 0 ≤ (-(1+eta)) * (-(1+eta)-1) := by nlinarith
    convert mul_nonneg hc hpow using 1 <;> ring

lemma midpoint_le_interval {eta : ℝ} (heta : 0 < eta) (n : ℕ) :
    ((n:ℝ)+1) ^ (-(1+eta):ℝ) ≤
      ∫ x in ((n:ℝ)+1/2)..((n:ℝ)+3/2), x ^ (-(1+eta):ℝ) := by
  let a : ℝ := (n:ℝ) + 1/2
  let b : ℝ := (n:ℝ) + 3/2
  let g : ℝ → ℝ := fun x => x ^ (-(1+eta):ℝ)
  have hab : a < b := by dsimp [a,b]; linarith
  have ha : (1/2:ℝ) ≤ a := by dsimp [a]; exact le_add_of_nonneg_left (Nat.cast_nonneg n)
  have hconv := convex_neg_rpow heta
  have hgc : ContinuousOn g (Ici (1/2:ℝ)) := by
    dsimp [g]
    exact continuousOn_id.rpow_const (fun x hx => Or.inl (by simp only [id_eq]; change (1/2:ℝ) ≤ x at hx; linarith))
  have hj := hconv.map_set_average_le (μ := volume) (t := Set.Ioc a b)
    (f := fun x : ℝ => x) hgc isClosed_Ici
    (by simpa using hab) (by simp)
    (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx; exact ha.trans hx.1.le)
    (continuousOn_id.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
    ((hgc.mono (fun x hx => ha.trans hx.1)).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
  have havgId : (⨍ x in a..b, x) = (n:ℝ)+1 := by
    rw [interval_average_eq_div, integral_id]
    dsimp [a,b]
    ring
  have havgG : (⨍ x in a..b, g x) = ∫ x in a..b, g x := by
    rw [interval_average_eq_div]
    have : b - a = 1 := by dsimp [a,b]; ring
    rw [this, div_one]
  have hj' : g (⨍ x in a..b, x) ≤ ⨍ x in a..b, g x := by
    simpa only [uIoc_of_le hab.le] using hj
  rw [havgId, havgG] at hj'
  exact hj'

lemma tail_rpow_le_integral {eta : ℝ} (heta : 0 < eta) :
    (∑' n : ℕ, ((n:ℝ)+2) ^ (-(1+eta):ℝ)) ≤
      ∫ x : ℝ in Set.Ioi (3/2:ℝ), x ^ (-(1+eta):ℝ) := by
  let f : ℝ → ℝ := fun x => x ^ (-(1+eta):ℝ)
  let cuts : ℕ → ℝ := fun n => (3/2:ℝ) + n
  let S : ℕ → Set ℝ := fun n => Set.Ioc (cuts n) (cuts (Order.succ n))
  have hcuts : Monotone cuts := by
    intro m n hmn
    dsimp [cuts]
    have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
    linarith
  have hunion : (⋃ n : ℕ, S n) = Set.Ioi (3/2:ℝ) := by
    have hlow : ∀ n : ℕ, cuts 0 ≤ cuts n := fun n => hcuts (Nat.zero_le n)
    have hub : ¬ BddAbove (Set.range cuts) := by
      rw [not_bddAbove_iff]
      intro x
      obtain ⟨n, hn⟩ := exists_nat_gt (x - 3/2)
      refine ⟨cuts n, ⟨n, rfl⟩, ?_⟩
      dsimp [cuts]
      linarith
    simpa [S, cuts] using iUnion_Ioc_map_succ_eq_Ioi hlow hub
  have hpair : Pairwise (Disjoint on S) := by
    simpa [S] using hcuts.pairwise_disjoint_on_Ioc_succ
  have hfint : IntegrableOn f (Set.Ioi (3/2:ℝ)) := by
    dsimp [f]
    exact integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)
  have hsumB : HasSum (fun n : ℕ => ∫ x in S n, f x)
      (∫ x in Set.Ioi (3/2:ℝ), f x) := by
    have h := MeasureTheory.hasSum_integral_iUnion
      (f := f) (μ := volume) (s := S)
      (fun n => by dsimp [S]; exact measurableSet_Ioc) hpair
      (by rw [hunion]; exact hfint)
    rwa [hunion] at h
  have hsumA : Summable (fun n : ℕ => ((n:ℝ)+2) ^ (-(1+eta):ℝ)) := by
    have hall : Summable (fun n : ℕ => 1 / (n:ℝ) ^ (1+eta)) :=
      (Real.summable_one_div_nat_rpow).mpr (by linarith)
    have hshift := (summable_nat_add_iff 2).mpr hall
    convert hshift using 1
    funext n
    rw [Real.rpow_neg (by positivity)]
    simp [one_div]
  have hsumBS : Summable (fun n : ℕ => ∫ x in S n, f x) := hsumB.summable
  have hpoint : ∀ n : ℕ, ((n:ℝ)+2) ^ (-(1+eta):ℝ) ≤ ∫ x in S n, f x := by
    intro n
    have hmid := midpoint_le_interval heta (n+1)
    dsimp [S, cuts, f]
    rw [← intervalIntegral.integral_of_le (by
      have hn : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
      exact (by simpa [add_comm] using add_le_add_left hn (3/2:ℝ)) :
      (3/2:ℝ) + n ≤ 3/2 + (n + 1 : ℕ))]
    convert hmid using 1 <;> push_cast <;> ring
  have hle := hsumA.tsum_le_tsum hpoint hsumBS
  rw [hsumB.tsum_eq] at hle
  exact hle

lemma zeta_re_eq_real_tsum {eta : ℝ} (heta : 0 < eta) :
    Complex.re (riemannZeta (((1+eta:ℝ):ℂ))) =
      ∑' n : ℕ, ((n:ℝ)+1) ^ (-(1+eta):ℝ) := by
  have hs : 1 < (((1+eta:ℝ):ℂ)).re := by simp; linarith
  have hsumC : Summable (fun n : ℕ =>
      1 / ((n + 1 : ℕ) : ℂ) ^ (((1+eta:ℝ):ℂ))) := by
    have h := (Complex.summable_one_div_nat_cpow
      (p := (((1+eta:ℝ):ℂ)))).mpr hs
    exact (summable_nat_add_iff 1).mpr h
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  have hsumC' : Summable (fun n : ℕ =>
      1 / ((n : ℂ) + 1) ^ (((1+eta:ℝ):ℂ))) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hsumC
  rw [Complex.re_tsum hsumC']
  apply tsum_congr
  intro n
  have hn : 0 ≤ ((n:ℝ)+1) := by positivity
  have hbase : ((n : ℂ) + 1) = ((((n:ℝ)+1):ℝ) : ℂ) := by push_cast; rfl
  rw [hbase, ← Complex.ofReal_cpow hn (1+eta)]
  norm_cast
  push_cast
  rw [one_div, ← Real.rpow_neg hn (1+eta)]

lemma zeta_midpoint_upper {eta : ℝ} (heta : 0 < eta) :
    Complex.re (riemannZeta (((1+eta:ℝ):ℂ))) ≤
      1 + (3/2:ℝ) ^ (-eta) / eta := by
  rw [zeta_re_eq_real_tsum heta]
  have hsum : Summable (fun n : ℕ => ((n:ℝ)+1) ^ (-(1+eta):ℝ)) := by
    have hall : Summable (fun n : ℕ => 1 / (n:ℝ) ^ (1+eta)) :=
      (Real.summable_one_div_nat_rpow).mpr (by linarith)
    have hshift := (summable_nat_add_iff 1).mpr hall
    convert hshift using 1
    funext n
    rw [Real.rpow_neg (by positivity)]
    simp [one_div]
  rw [hsum.tsum_eq_zero_add]
  simp only [Nat.cast_zero, zero_add, Real.one_rpow]
  have htail := tail_rpow_le_integral heta
  have hint : (∫ x : ℝ in Set.Ioi (3/2:ℝ), x ^ (-(1+eta):ℝ)) =
      (3/2:ℝ) ^ (-eta) / eta := by
    rw [integral_Ioi_rpow_of_lt (by linarith) (by norm_num)]
    field_simp [heta.ne']
    ring
  rw [hint] at htail
  convert add_le_add_left htail 1 using 1 <;> push_cast <;> ring

lemma log_three_halves_lower : (0.4054:ℝ) < Real.log (3/2:ℝ) := by
  rw [Real.lt_log_iff_exp_lt (by norm_num : (0:ℝ)<3/2)]
  have h := Real.exp_bound' (x := (0.4054:ℝ)) (by norm_num) (by norm_num)
    (n := 8) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith

lemma log_three_halves_upper : Real.log (3/2:ℝ) < (0.4055:ℝ) := by
  rw [Real.log_lt_iff_lt_exp (by norm_num : (0:ℝ)<3/2)]
  have h := Real.sum_le_exp_of_nonneg (x := (0.4055:ℝ)) (by norm_num) 8
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith

lemma rpow_three_halves_numeric {eta : ℝ} (heta : 0 < eta)
    (hetaTop : eta ≤ 0.06) :
    1 + (3/2:ℝ)^(-eta) / eta ≤ 0.6 + 1/eta := by
  let L : ℝ := Real.log (3/2:ℝ)
  have hLlow : (0.4054:ℝ) ≤ L := log_three_halves_lower.le
  have hLtop : L ≤ (0.4055:ℝ) := log_three_halves_upper.le
  have hLpos : 0 < L := (by norm_num : (0:ℝ)<0.4054).trans_le hLlow
  let x : ℝ := eta * L
  have hx0 : 0 ≤ x := mul_nonneg heta.le hLpos.le
  have hxTop : x ≤ 0.02433 := by dsimp [x]; nlinarith
  have habs : |(-x)| ≤ 1 := by rw [abs_neg, abs_of_nonneg hx0]; linarith
  have he := Real.exp_bound (x := -x) habs (n := 3) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_nonneg hx0] at he
  have hexp : Real.exp (-x) ≤ 1 - x + x^2/2 + (2/9:ℝ)*x^3 := by
    rcases abs_le.mp he with ⟨_, hright⟩
    nlinarith
  have hrpow : (3/2:ℝ)^(-eta) = Real.exp (-x) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<3/2)]
    dsimp [x, L]
    congr 1
    ring
  have hpoly : (0.4:ℝ) + eta * L^2 / 2 + (2/9:ℝ) * eta^2 * L^3 ≤ L := by
    have hL0 : 0 ≤ L := hLpos.le
    have hL2 : L^2 ≤ (0.4055:ℝ)^2 := by nlinarith [sq_nonneg (0.4055-L)]
    have hL3 : L^3 ≤ (0.4055:ℝ)^3 := by
      exact pow_le_pow_left₀ hL0 hLtop 3
    have heta2 : eta^2 ≤ (0.06:ℝ)^2 := by nlinarith
    have hterm2 : eta * L^2 / 2 ≤ (0.06:ℝ)*(0.4055:ℝ)^2/2 := by
      gcongr
    have hterm3 : (2/9:ℝ)*eta^2*L^3 ≤
        (2/9:ℝ)*(0.06:ℝ)^2*(0.4055:ℝ)^3 := by
      gcongr
    nlinarith
  rw [hrpow]
  have hmain : Real.exp (-x) ≤ 1 - 0.4*eta := by
    calc
      Real.exp (-x) ≤ 1-x+x^2/2+(2/9:ℝ)*x^3 := hexp
      _ ≤ 1-0.4*eta := by
        dsimp [x]
        have heta0 := heta.le
        nlinarith [mul_nonneg heta0 (sub_nonneg.mpr hpoly)]
  have hetaNe : eta ≠ 0 := heta.ne'
  rw [show 1 + Real.exp (-x) / eta =
      (eta + Real.exp (-x)) / eta by field_simp [hetaNe],
    show (0.6:ℝ) + 1 / eta = (0.6*eta + 1) / eta by
      field_simp [hetaNe],
    div_le_div_iff_of_pos_right heta]
  nlinarith

/-- Premise-free inhabitant of the exact zeta estimate used in Appendix B. -/
theorem appendixBZetaPointwise06 :
    MAPKhaleAppendixB1ZetaReduction.AppendixBZetaPointwise06 := by
  intro eta heta hetaTop
  have hpos : 0 < Complex.re (riemannZeta (((1+eta:ℝ):ℂ))) := by
    simpa using riemannZeta_re_pos_of_one_lt (show (1:ℝ) < 1+eta by linarith)
  refine ⟨hpos, ?_⟩
  exact (zeta_midpoint_upper heta).trans (rpow_three_halves_numeric heta hetaTop)

end
end MAPKhaleAppendixBZetaPointwiseCertified

#print axioms MAPKhaleAppendixBZetaPointwiseCertified.appendixBZetaPointwise06
