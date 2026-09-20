import JutilaLemma6CanonicalMellinBound
import JutilaLemma6GenericDeltaLedger
import JutilaLemma6GenericTailAbsorption

/-! Uniform smallness of the actual canonical detector series at source parameters. -/
namespace MAPJutilaLemma6CanonicalSeriesSmall
open Complex Real Filter
open MAPJutilaLemma6CanonicalMellinBound MAPJutilaLemma6GenericDeltaLedger
open MAPJutilaLemma6FiniteContour MAPJutilaLemma6DirectTail
open MAPJutilaPseudocharacterHarmonicLower MAPJutilaLemma6MellinIntegral
open MAPJutilaLemma6GammaKernel MAPJutilaP48ConvexityAdapter
noncomputable section

theorem source_height_power_le_twoPi
    {q : ℕ} {T D t : ℝ} (hT : 1 ≤ T) (hD : (q : ℝ) * T = D) (ht : |t| ≤ T) :
    Real.rpow ((q : ℝ) * (1 + |t|)) p48HeightExponent ≤
      2 * Real.pi * Real.rpow D p48HeightExponent := by
  have hD0 : 0 ≤ D := by rw [← hD]; positivity
  have hh : (q : ℝ) * (1 + |t|) ≤ 2 * D := by
    rw [← hD]
    nlinarith [mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg q),
      mul_le_mul_of_nonneg_left hT (Nat.cast_nonneg q)]
  have htwo : Real.rpow 2 p48HeightExponent ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) p48HeightExponent_le_one
  calc
    _ ≤ Real.rpow (2 * D) p48HeightExponent := Real.rpow_le_rpow (by positivity) hh p48HeightExponent_nonneg
    _ = Real.rpow 2 p48HeightExponent * Real.rpow D p48HeightExponent := Real.mul_rpow (by norm_num) hD0
    _ ≤ 2 * Real.rpow D p48HeightExponent := mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hD0 _)
    _ ≤ _ := mul_le_mul_of_nonneg_right (by nlinarith [Real.pi_gt_three]) (Real.rpow_nonneg hD0 _)

theorem eventually_canonical_directSeries_lt_one
    {δ : ℝ} (hδlo : 1 / 560 ≤ δ) (hδhi : δ ≤ 1 / 280) :
    ∀ᶠ D : ℝ in atTop, ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q)
      (T omega : ℝ) (rho : ℂ), chi.IsPrimitive → chi ≠ 1 →
      1 ≤ T → (q : ℝ) * T = D → 0 < omega →
      Real.log D ≤ Real.rpow D (omega / 140) →
      1 - δ ≤ rho.re → rho.re ≤ 1 - omega → |rho.im| ≤ T →
      DirichletCharacter.LFunction chi rho = 0 →
      ‖∑' n : ℕ, jutilaLemmaSixDirectTerm chi
        (Real.rpow D (1 / 2 + 7 * δ)) (Real.rpow D (1 / 2 + 8 * δ))
        (jutilaPrimedRSet q (Nat.floor (Real.rpow D δ))) rho
        (Real.rpow D (1 + 12 * δ)) n‖ < 1 := by
  have hsmall := eventually_uniform_mellin_numeric_lt_one hδlo hδhi
  filter_upwards [hsmall, eventually_gt_atTop (1 : ℝ)] with D hsmall hD
  intro q _inst chi T omega rho hprim hchi hT hDT homega hgap hrlo hrhi ht hrzero
  have hDp : 0 < D := zero_lt_one.trans hD
  have hδ : 0 < δ := by linarith
  have hz1 : 1 < Real.rpow D (1 / 2 + 7 * δ) := Real.one_lt_rpow hD (by linarith)
  have hz12 : Real.rpow D (1 / 2 + 7 * δ) < Real.rpow D (1 / 2 + 8 * δ) :=
    Real.rpow_lt_rpow_of_exponent_lt hD (by linarith)
  have hX : 1 ≤ Real.rpow D (1 + 12 * δ) := Real.one_le_rpow hD.le (by linarith)
  have hR : 1 ≤ Nat.floor (Real.rpow D δ) := (Nat.one_le_floor_iff _).mpr (Real.one_le_rpow hD.le hδ.le)
  have hRle : (Nat.floor (Real.rpow D δ) : ℝ) ≤ Real.rpow D δ := Nat.floor_le (Real.rpow_nonneg hDp.le _)
  have hzle : (Nat.floor (Real.rpow D (1 / 2 + 8 * δ)) : ℝ) ≤ Real.rpow D (1 / 2 + 8 * δ) :=
    Nat.floor_le (Real.rpow_nonneg hDp.le _)
  have hrpoint : lemmaSixZeroPoint rho.re rho.im = rho := by apply Complex.ext <;> simp [lemmaSixZeroPoint]
  have hbound := norm_selected_directSeries_le_mellinBound chi hprim hchi
    (jutilaPrimedRSet_subset_Icc q (Nat.floor (Real.rpow D δ)))
    (fun r hr => squarefree_of_mem_jutilaPrimedRSet hr)
    (fun r hr => coprime_of_mem_jutilaPrimedRSet hr)
    hz1 hz12 (t := rho.im) homega (by linarith : 4 / 5 ≤ rho.re) hrhi hX
    (by simpa only [hrpoint] using hrzero)
  rw [hrpoint] at hbound
  have hnum := hsmall omega rho.re D
    (Nat.floor (Real.rpow D (1 / 2 + 8 * δ))) (Nat.floor (Real.rpow D δ))
    homega hgap hrlo hDp.le le_rfl hzle hR hRle
  have hh := source_height_power_le_twoPi hT hDT ht
  have hG : 0 ≤ lemmaSixGammaSqConstant omega * p48ConvexityConstant :=
    mul_nonneg (lemmaSixGammaSqConstant_pos homega).le p48ConvexityConstant_pos.le
  have hbase : 0 ≤ Real.rpow (Real.rpow D (1 + 12 * δ)) (-rho.re) *
      ((Nat.floor (Real.rpow D (1 / 2 + 8 * δ)) : ℝ) *
        (Nat.floor (Real.rpow D δ) : ℝ) * (harmonic (Nat.floor (Real.rpow D δ)) : ℝ)^4) := by
    apply mul_nonneg (Real.rpow_nonneg (Real.rpow_nonneg hDp.le _) _)
    positivity
  apply lt_of_le_of_lt hbound
  apply lt_of_le_of_lt _ hnum
  apply mul_le_mul_of_nonneg_left _ hbase
  calc
    _ ≤ (lemmaSixGammaSqConstant omega * p48ConvexityConstant) *
        (2 * Real.pi * Real.rpow D p48HeightExponent) := mul_le_mul_of_nonneg_left hh hG
    _ = _ := by ring

end
end MAPJutilaLemma6CanonicalSeriesSmall
#print axioms MAPJutilaLemma6CanonicalSeriesSmall.eventually_canonical_directSeries_lt_one
