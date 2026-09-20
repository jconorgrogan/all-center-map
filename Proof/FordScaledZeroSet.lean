import Mathlib.Analysis.Complex.JensenFormula

open scoped BigOperators
noncomputable section
namespace FordScaledZeroSet

open Complex Set Filter Metric

/-- The zeros of an analytic function in the strict inner disk form a finite
set, with their actual analytic multiplicities. -/
theorem exists_finite_zero_set
    {a : ℝ} (ha : 0 < a) {c : ℂ} {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (closedBall c (6 * a)))
    (hfc : f c ≠ 0) :
    ∃ S : Finset ℂ,
      (∀ ρ, ρ ∈ S ↔ ρ ∈ ball c (3 * a) ∧ f ρ = 0) ∧
      (∀ ρ ∈ S,
        analyticOrderAt f ρ ≠ ⊤ ∧ 1 ≤ analyticOrderNatAt f ρ) := by
  classical
  have ha3 : 0 < 3 * a := by positivity
  have ha6 : 0 < 6 * a := by positivity
  let U : Set ℂ := closedBall c (3 * a)
  let V : Set ℂ := closedBall c (6 * a)
  have hUV : U ⊆ V := by
    dsimp [U, V]
    exact closedBall_subset_closedBall (by linarith)
  have hUanalytic : AnalyticOnNhd ℂ f U := hf.mono hUV
  let D : ℂ → ℤ := MeromorphicOn.divisor f U
  have hDfinite : D.support.Finite := by
    dsimp [D]
    exact (MeromorphicOn.divisor f U).finiteSupport (isCompact_closedBall _ _)
  let T : Finset ℂ := hDfinite.toFinset
  let S : Finset ℂ := T.filter (fun z ↦ z ∈ ball c (3 * a))
  have houter (ρ : ℂ) (hρ : ρ ∈ U) : ρ ∈ V := hUV hρ
  have hfinite_order (ρ : ℂ) (hρ : ρ ∈ U) :
      analyticOrderAt f ρ ≠ ⊤ := by
    intro htop
    have hfreq : ∃ᶠ z in nhdsWithin ρ {ρ}ᶜ, f z = 0 :=
      (hf ρ (houter ρ hρ)).frequently_zero_iff_eventually_zero.mpr
        (analyticOrderAt_eq_top.mp htop)
    have hzero := hf.eqOn_zero_of_preconnected_of_frequently_eq_zero
      isPreconnected_closedBall (houter ρ hρ) hfreq
    exact hfc (hzero (mem_closedBall_self (by positivity)))
  have hdiv_apply (ρ : ℂ) (hρ : ρ ∈ U) :
      D ρ = (ENat.map Nat.cast (analyticOrderAt f ρ)).untop₀ := by
    dsimp [D]
    exact MeromorphicOn.AnalyticOnNhd.divisor_apply hUanalytic hρ
  have hzero_to_support (ρ : ℂ) (hρ : ρ ∈ ball c (3 * a))
      (hzero : f ρ = 0) : D ρ ≠ 0 := by
    have hρU : ρ ∈ U := by
      dsimp [U]
      exact ball_subset_closedBall hρ
    have horder : analyticOrderAt f ρ ≠ 0 :=
      (hf ρ (houter ρ hρU)).analyticOrderAt_ne_zero.mpr hzero
    have htop := hfinite_order ρ hρU
    rw [hdiv_apply ρ hρU]
    simp [htop, horder]
  have hsupport_to_zero (ρ : ℂ) (hρ : ρ ∈ U) (hDρ : D ρ ≠ 0) :
      f ρ = 0 := by
    have htop := hfinite_order ρ hρ
    have horder : analyticOrderAt f ρ ≠ 0 := by
      intro hzero
      apply hDρ
      rw [hdiv_apply ρ hρ]
      simp [htop, hzero]
    exact (hf ρ (houter ρ hρ)).analyticOrderAt_ne_zero.mp horder
  refine ⟨S, ?_, ?_⟩
  · intro ρ
    constructor
    · intro hρS
      have hρT : ρ ∈ T := (Finset.mem_filter.mp hρS).1
      have hρball : ρ ∈ ball c (3 * a) := (Finset.mem_filter.mp hρS).2
      have hDρ : D ρ ≠ 0 := (Set.Finite.mem_toFinset hDfinite).mp hρT
      exact ⟨hρball, hsupport_to_zero ρ (ball_subset_closedBall hρball) hDρ⟩
    · rintro ⟨hρball, hzero⟩
      have hDρ := hzero_to_support ρ hρball hzero
      have hρT : ρ ∈ T := (Set.Finite.mem_toFinset hDfinite).mpr hDρ
      exact Finset.mem_filter.mpr ⟨hρT, hρball⟩
  · intro ρ hρS
    have hρball := (Finset.mem_filter.mp hρS).2
    have hρU : ρ ∈ U := ball_subset_closedBall hρball
    have htop := hfinite_order ρ hρU
    have hzero := hsupport_to_zero ρ hρU
      ((Set.Finite.mem_toFinset hDfinite).mp (Finset.mem_filter.mp hρS).1)
    have horder := (hf ρ (houter ρ hρU)).analyticOrderAt_ne_zero.mpr hzero
    have hnat := Nat.cast_analyticOrderNatAt htop
    have hmne : analyticOrderNatAt f ρ ≠ 0 := by
      intro hm
      apply horder
      rw [← hnat, hm]
      simp
    exact ⟨htop, Nat.one_le_iff_ne_zero.mpr hmne⟩

end FordScaledZeroSet

#print axioms FordScaledZeroSet.exists_finite_zero_set
