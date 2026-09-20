import WideDiskLocalLogDerivative
import FullStripA5Family

/-!
# Certified multiplicity mass in the radius-three Blaschke disk
-/

namespace WideDiskLocalMass

open Complex Set Metric DirichletZeros PrimitiveExplicitFormulaSpine
open WideDiskLFunctionGrowth WideDiskBlaschkeAssembly
open MAPLocalZeroWindow
open scoped BigOperators ZMod

noncomputable section

variable {q : ℕ} [NeZero q]

/-- Primitive nonprincipal Dirichlet L-functions have no zeros in the open
strip `-1 < re s < 0`; the first trivial-zero endpoint is `s = 0`. -/
theorem regularizedLFunction_ne_zero_of_neg_one_lt_re_lt_zero
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    {s : ℂ} (hlo : -1 < s.re) (hhi : s.re < 0) :
    regularizedLFunction χ s ≠ 0 := by
  intro hzero
  have hLzero : χ.LFunction s = 0 := by
    simpa [regularizedLFunction, hχ] using hzero
  have hgamma : χ.gammaFactor s ≠ 0 := by
    rcases χ.even_or_odd with heven | hodd
    · rw [heven.gammaFactor_def]
      intro hz
      rw [Complex.Gammaℝ_eq_zero_iff] at hz
      rcases hz with ⟨n, hn⟩
      have hre := congrArg Complex.re hn
      norm_num at hre
      cases n with
      | zero => norm_num at hre; linarith
      | succ n =>
          have hn1 : (1 : ℝ) ≤ (Nat.succ n : ℕ) := by exact_mod_cast Nat.succ_pos n
          linarith
    · rw [hodd.gammaFactor_def]
      apply Complex.Gammaℝ_ne_zero_of_re_pos
      simp only [Complex.add_re, Complex.one_re]
      linarith
  have hq1 : q ≠ 1 := fun hq => hχ (χ.level_one' hq)
  have heq := χ.LFunction_eq_completed_div_gammaFactor s (Or.inr hq1)
  have hcompleted : χ.completedLFunction s = 0 := by
    rw [heq, div_eq_zero_iff] at hLzero
    exact hLzero.resolve_right hgamma
  let u : ℂ := 1 - s
  have hFE := hprim.completedLFunction_one_sub u
  have hleft : 1 - u = s := by dsimp [u]; ring
  rw [hleft, hcompleted] at hFE
  have hqpow : (q : ℂ) ^ (u - 1 / 2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr <| Or.inl <|
      Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hroot := MAPTrivialZeroEndpoint.rootNumber_ne_zero_of_primitive hprim
  have hucomp : χ⁻¹.completedLFunction u = 0 := by
    rcases mul_eq_zero.mp hFE.symm with h | h
    · rcases mul_eq_zero.mp h with hq | hr
      · exact (hqpow hq).elim
      · exact (hroot hr).elim
    · exact h
  have huRe : 1 < u.re := by
    change 1 < 1 - s.re
    linarith
  have huNeOne : u ≠ 1 := by
    intro hu
    have hre := congrArg Complex.re hu
    simp at hre
    linarith
  have huNeZero : u ≠ 0 := by
    intro hu
    have hre := congrArg Complex.re hu
    simp at hre
    linarith
  have hLne : χ⁻¹.LFunction u ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ⁻¹
      (Or.inr huNeOne) huRe.le
  have heqInv := χ⁻¹.LFunction_eq_completed_div_gammaFactor u
    (Or.inl huNeZero)
  rw [hucomp, zero_div] at heqInv
  exact hLne heqInv

/-- Every zero used by the radius-three product lies in the ordinary full
critical strip `0 ≤ re rho ≤ 1`. -/
theorem re_nonneg_of_mem_wideZeroSupport
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    {t : ℝ} {ρ : ℂ} (hρ : ρ ∈ wideZeroSupport χ t) :
    0 ≤ ρ.re := by
  by_contra hnot
  have hreNeg : ρ.re < 0 := lt_of_not_ge hnot
  have hball := mem_ball_of_mem_wideZeroSupport χ hρ
  have hnorm : ‖ρ - wideCenter t‖ < 3 := by
    simpa [Metric.mem_ball, dist_eq_norm, wideRadius] using hball
  have hreDiff : |ρ.re - 2| < 3 := by
    simpa [wideCenter] using
      (Complex.abs_re_le_norm (ρ - wideCenter t)).trans_lt hnorm
  have hlo : -1 < ρ.re := by
    have := neg_lt_of_abs_lt hreDiff
    linarith
  exact (regularizedLFunction_ne_zero_of_neg_one_lt_re_lt_zero
    χ hprim hχ hlo hreNeg)
      (regularizedLFunction_eq_zero_of_mem_zeroSupport χ (-1) (|t| + 3)
        (mem_baseZeroSupport_of_mem_wideZeroSupport χ hρ))

def wideUnitSlice (χ : DirichletCharacter ℂ q) (t u : ℝ) : Finset ℂ :=
  (wideZeroSupport χ t).filter fun ρ => u ≤ ρ.im ∧ ρ.im ≤ u + 1

/-- A closed unit slice of the radius-three disk is controlled by the
certified full-strip closed unit-window count, with multiplicities transported
between the two literal rectangles. -/
theorem wideUnitSlice_mass_le_closedUnitWindowCount
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    (t u : ℝ) :
    (∑ ρ ∈ wideUnitSlice χ t u, wideZeroMultiplicity χ t ρ) ≤
      closedUnitWindowCount χ 0 u := by
  have hsubset : wideUnitSlice χ t u ⊆ closedUnitWindowSupport χ 0 u := by
    intro ρ hρ
    have hmem := Finset.mem_filter.mp hρ
    have hwide := hmem.1
    have hbase := mem_baseZeroSupport_of_mem_wideZeroSupport χ hwide
    have hzero := regularizedLFunction_eq_zero_of_mem_zeroSupport
      χ (-1) (|t| + 3) hbase
    have hbaseRect : ρ ∈ zeroRectangle (-1) (|t| + 3) :=
      (zeroDivisor χ (-1) (|t| + 3)).supportWithinDomain
        ((zeroSupport_mem_iff χ (-1) (|t| + 3) ρ).mp hbase)
    have himabs : |ρ.im| ≤ windowHeight u := by
      have him := hmem.2
      unfold windowHeight
      rw [abs_le]
      constructor <;> linarith [le_abs_self u, neg_le_abs u]
    have hrect : ρ ∈ zeroRectangle 0 (windowHeight u) := by
      rw [zeroRectangle, Complex.mem_reProdIm]
      exact ⟨⟨re_nonneg_of_mem_wideZeroSupport χ hprim hχ hwide,
        hbaseRect.1.2⟩, abs_le.mp himabs⟩
    rw [closedUnitWindowSupport, Finset.mem_filter]
    exact ⟨(MAPAPZeroDensityCert.mem_zeroSupport_iff_eq_zero
      χ 0 (windowHeight u) hrect).2 hzero, hmem.2⟩
  unfold wideUnitSlice closedUnitWindowCount
  calc
    (∑ ρ ∈ (wideZeroSupport χ t).filter
        (fun ρ => u ≤ ρ.im ∧ ρ.im ≤ u + 1),
        wideZeroMultiplicity χ t ρ) =
      ∑ ρ ∈ (wideZeroSupport χ t).filter
        (fun ρ => u ≤ ρ.im ∧ ρ.im ≤ u + 1),
        zeroMultiplicity χ 0 (windowHeight u) ρ := by
      apply Finset.sum_congr rfl
      intro ρ hρ
      have hwide := (Finset.mem_filter.mp hρ).1
      have hbase := mem_baseZeroSupport_of_mem_wideZeroSupport χ hwide
      have hbaseRect : ρ ∈ zeroRectangle (-1) (|t| + 3) :=
        (zeroDivisor χ (-1) (|t| + 3)).supportWithinDomain
          ((zeroSupport_mem_iff χ (-1) (|t| + 3) ρ).mp hbase)
      have htarget := hsubset hρ
      have htargetBase := (Finset.mem_filter.mp htarget).1
      have htargetRect : ρ ∈ zeroRectangle 0 (windowHeight u) :=
        (zeroDivisor χ 0 (windowHeight u)).supportWithinDomain
          ((zeroSupport_mem_iff χ 0 (windowHeight u) ρ).mp htargetBase)
      exact MAPMellinDetectorLeaf.zeroMultiplicity_eq_of_mem_rectangles
        χ hbaseRect htargetRect
    _ ≤ ∑ ρ ∈ closedUnitWindowSupport χ 0 u,
        zeroMultiplicity χ 0 (windowHeight u) ρ :=
      Finset.sum_le_sum_of_subset hsubset

private theorem exists_window_index_of_mem_wideZeroSupport
    (χ : DirichletCharacter ℂ q) {t : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ wideZeroSupport χ t) :
    ∃ j ∈ Finset.range 6,
      t - 3 + (j : ℝ) ≤ ρ.im ∧ ρ.im ≤ t - 3 + (j : ℝ) + 1 := by
  have hball := mem_ball_of_mem_wideZeroSupport χ hρ
  have hnorm : ‖ρ - wideCenter t‖ < 3 := by
    simpa [Metric.mem_ball, dist_eq_norm, wideRadius] using hball
  have himDiff : |ρ.im - t| < 3 := by
    simpa [wideCenter] using
      (Complex.abs_im_le_norm (ρ - wideCenter t)).trans_lt hnorm
  have hlo : t - 3 < ρ.im := by
    have := neg_lt_of_abs_lt himDiff
    linarith
  have hhi : ρ.im < t + 3 := by
    have := lt_of_abs_lt himDiff
    linarith
  by_cases h0 : ρ.im ≤ t - 2
  · exact ⟨0, by simp, by norm_num; constructor <;> linarith⟩
  by_cases h1 : ρ.im ≤ t - 1
  · exact ⟨1, by simp, by norm_num; constructor <;> linarith⟩
  by_cases h2 : ρ.im ≤ t
  · exact ⟨2, by simp, by norm_num; constructor <;> linarith⟩
  by_cases h3 : ρ.im ≤ t + 1
  · exact ⟨3, by simp, by norm_num; constructor <;> linarith⟩
  by_cases h4 : ρ.im ≤ t + 2
  · exact ⟨4, by simp, by norm_num; constructor <;> linarith⟩
  · exact ⟨5, by simp, by norm_num; constructor <;> linarith⟩

/-- The radius-three multiplicity mass is bounded by six certified closed
unit-window counts. -/
theorem wideZeroMultiplicity_mass_le_six_windows
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    (t : ℝ) :
    (∑ ρ ∈ wideZeroSupport χ t, wideZeroMultiplicity χ t ρ) ≤
      ∑ j ∈ Finset.range 6,
        closedUnitWindowCount χ 0 (t - 3 + (j : ℝ)) := by
  calc
    (∑ ρ ∈ wideZeroSupport χ t, wideZeroMultiplicity χ t ρ) ≤
      ∑ ρ ∈ wideZeroSupport χ t,
        ∑ j ∈ Finset.range 6,
          if t - 3 + (j : ℝ) ≤ ρ.im ∧
              ρ.im ≤ t - 3 + (j : ℝ) + 1 then
            wideZeroMultiplicity χ t ρ else 0 := by
      apply Finset.sum_le_sum
      intro ρ hρ
      obtain ⟨j, hj, hinterval⟩ :=
        exists_window_index_of_mem_wideZeroSupport χ hρ
      calc
        wideZeroMultiplicity χ t ρ =
            if t - 3 + (j : ℝ) ≤ ρ.im ∧
                ρ.im ≤ t - 3 + (j : ℝ) + 1 then
              wideZeroMultiplicity χ t ρ else 0 := by simp [hinterval]
        _ ≤ ∑ k ∈ Finset.range 6,
            if t - 3 + (k : ℝ) ≤ ρ.im ∧
                ρ.im ≤ t - 3 + (k : ℝ) + 1 then
              wideZeroMultiplicity χ t ρ else 0 := by
          apply Finset.single_le_sum (fun k hk => by positivity) hj
    _ = ∑ j ∈ Finset.range 6,
        ∑ ρ ∈ wideUnitSlice χ t (t - 3 + (j : ℝ)),
          wideZeroMultiplicity χ t ρ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      unfold wideUnitSlice
      rw [Finset.sum_filter]
    _ ≤ ∑ j ∈ Finset.range 6,
        closedUnitWindowCount χ 0 (t - 3 + (j : ℝ)) := by
      apply Finset.sum_le_sum
      intro j hj
      exact wideUnitSlice_mass_le_closedUnitWindowCount χ hprim hχ t _

/-- Numerical form using the already certified full-strip A.5 estimate. -/
theorem wideZeroMultiplicity_mass_le_explicit
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    (t : ℝ) :
    (∑ ρ ∈ wideZeroSupport χ t,
        (wideZeroMultiplicity χ t ρ : ℝ)) ≤
      ∑ j ∈ Finset.range 6,
        (1 + 153 * Real.log (arithmeticScale q (t - 3 + (j : ℝ))) +
          153 * Real.log
            (arithmeticScale q (-(t - 3 + (j : ℝ)) - 1))) := by
  have hmass := wideZeroMultiplicity_mass_le_six_windows χ hprim hχ t
  have hcast :
      (∑ ρ ∈ wideZeroSupport χ t,
        (wideZeroMultiplicity χ t ρ : ℝ)) ≤
      ∑ j ∈ Finset.range 6,
        (closedUnitWindowCount χ 0 (t - 3 + (j : ℝ)) : ℝ) := by
    exact_mod_cast hmass
  exact hcast.trans (Finset.sum_le_sum fun j hj =>
    MAPFullStripA5Family.certifiedFullStripClosedLocalZeroCount
      χ hprim hχ (t - 3 + (j : ℝ)))

end

end WideDiskLocalMass
