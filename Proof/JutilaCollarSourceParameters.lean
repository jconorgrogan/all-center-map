import JutilaLemma6GenericTailAbsorption
import JutilaTotientSmallLogBound

namespace MAPJutilaCollarSourceParameters
open Real Filter
open MAPJutilaLemma6GenericTailAbsorption
open PostA5HighStripSplitReductionFromFourthMoment
noncomputable section

def sourceR (δ D : ℝ) : ℕ := Nat.floor (Real.rpow D δ)
def sourceZ1 (δ D : ℝ) : ℝ := Real.rpow D (1 / 2 + 7 * δ)
def sourceZ2 (δ D : ℝ) : ℝ := Real.rpow D (1 / 2 + 8 * δ)

structure SourceGeometry (δ D : ℝ) : Prop where
  R_one : 1 ≤ sourceR δ D
  X_two : 2 ≤ lemmaSixSmoothScale δ D
  x_one : 1 ≤ lemmaSixDirectCutoff δ D
  z1_one : 1 < sourceZ1 δ D
  z12 : sourceZ1 δ D < sourceZ2 δ D
  separation : 4 * sourceZ1 δ D ≤ (lemmaSixDirectCutoff δ D : ℝ)
  logR_lower : (δ / 2) * Real.log D ≤ Real.log (sourceR δ D : ℝ)
  R_upper : (sourceR δ D : ℝ) ≤ Real.rpow D δ
  x_upper : (lemmaSixDirectCutoff δ D : ℝ) ≤ lemmaSixSmoothScale δ D * (Real.log D) ^ 2
  harmonic_upper : (harmonic (sourceR δ D) : ℝ) ≤ 1 + Real.log D
  logx_upper : Real.log (lemmaSixDirectCutoff δ D : ℝ) ≤ 3 * Real.log D

theorem eventually_sourceGeometry {δ : ℝ}
    (hlo : 1 / 560 ≤ δ) (hhi : δ ≤ 1 / 280) :
    ∀ᶠ D : ℝ in atTop, SourceGeometry δ D := by
  have hδ : 0 < δ := by linarith
  have hhalf := (tendsto_rpow_atTop (show 0 < δ / 2 by linarith)).eventually
    (eventually_ge_atTop (2 : ℝ))
  have hgap := (tendsto_rpow_atTop (show 0 < 1 / 2 + 5 * δ by linarith)).eventually
    (eventually_ge_atTop (8 : ℝ))
  have hlogpow := eventually_const_mul_polylog_le_rpow 1 2 1 (by norm_num) (by norm_num)
  filter_upwards [hhalf, hgap, hlogpow, eventually_ge_atTop (Real.exp 2),
    eventually_ge_atTop (2 : ℝ)] with D hhalf hgap hlogpow hDe hD2
  change 2 ≤ Real.rpow D (δ / 2) at hhalf
  change 8 ≤ Real.rpow D (1 / 2 + 5 * δ) at hgap
  have hD : 1 < D := by linarith
  have hDp : 0 < D := by linarith
  have hlog : 2 ≤ Real.log D := by
    rw [← Real.log_exp 2]
    exact Real.log_le_log (Real.exp_pos _) hDe
  have hhalfSq : Real.rpow D δ = (Real.rpow D (δ / 2)) ^ 2 := by
    have hh := Real.rpow_mul hDp.le (δ / 2) (2 : ℝ)
    norm_num at hh
    convert hh using 1 <;> ring
  have hfloor := Nat.lt_floor_add_one (Real.rpow D δ)
  have hRlower : Real.rpow D (δ / 2) ≤ (sourceR δ D : ℝ) := by
    change _ ≤ (Nat.floor (Real.rpow D δ) : ℝ)
    have hf : (Real.rpow D (δ / 2)) ^ 2 < (Nat.floor (Real.rpow D δ) : ℝ) + 1 := by
      calc
        _ = Real.rpow D δ := hhalfSq.symm
        _ < _ := hfloor
    nlinarith
  have hR1 : 1 ≤ sourceR δ D := by
    have hh : (1 : ℝ) ≤ (sourceR δ D : ℝ) := by linarith
    exact_mod_cast hh
  have hRp : (0 : ℝ) < sourceR δ D := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hR1)
  have hRup : (sourceR δ D : ℝ) ≤ Real.rpow D δ :=
    Nat.floor_le (Real.rpow_nonneg hDp.le _)
  have hRleD : (sourceR δ D : ℝ) ≤ D := hRup.trans (by
    simpa using Real.rpow_le_rpow_of_exponent_le hD.le (show δ ≤ 1 by linarith))
  have hz1 : 1 < sourceZ1 δ D :=
    Real.one_lt_rpow hD (by linarith : 0 < 1 / 2 + 7 * δ)
  have hz12 : sourceZ1 δ D < sourceZ2 δ D :=
    Real.rpow_lt_rpow_of_exponent_lt hD (by linarith)
  have hXlower : D ≤ lemmaSixSmoothScale δ D := by
    simpa [lemmaSixSmoothScale] using
      Real.rpow_le_rpow_of_exponent_le hD.le (show (1 : ℝ) ≤ 1 + 12 * δ by linarith)
  have hXsep : 8 * sourceZ1 δ D ≤ lemmaSixSmoothScale δ D := by
    have hh := mul_le_mul_of_nonneg_left hgap (show 0 ≤ sourceZ1 δ D by exact hz1.le.trans' zero_le_one)
    have heq : sourceZ1 δ D * Real.rpow D (1 / 2 + 5 * δ) =
        lemmaSixSmoothScale δ D := by
      unfold sourceZ1 lemmaSixSmoothScale
      simp only [Real.rpow_eq_pow]
      rw [← Real.rpow_add hDp]
      congr 1
      ring
    rw [heq] at hh
    linarith
  have hXpos : 0 < lemmaSixSmoothScale δ D := lemmaSixSmoothScale_pos hDp
  have hlogSq : 1 ≤ (Real.log D) ^ 2 := by nlinarith
  have hargX : lemmaSixSmoothScale δ D ≤ lemmaSixSmoothScale δ D * (Real.log D) ^ 2 := by
    nlinarith
  have hxFloor := Nat.lt_floor_add_one (lemmaSixSmoothScale δ D * (Real.log D) ^ 2)
  have hxsep : 4 * sourceZ1 δ D ≤ (lemmaSixDirectCutoff δ D : ℝ) := by
    change _ ≤ (Nat.floor (lemmaSixSmoothScale δ D * (Real.log D) ^ 2) : ℝ)
    nlinarith
  have hx1 : 1 ≤ lemmaSixDirectCutoff δ D := by
    have hh : (1 : ℝ) ≤ (lemmaSixDirectCutoff δ D : ℝ) := by linarith
    exact_mod_cast hh
  have hxup : (lemmaSixDirectCutoff δ D : ℝ) ≤
      lemmaSixSmoothScale δ D * (Real.log D) ^ 2 := Nat.floor_le (by positivity)
  have hlogR : (δ / 2) * Real.log D ≤ Real.log (sourceR δ D : ℝ) := by
    have hh := Real.log_le_log (Real.rpow_pos_of_pos hDp _) hRlower
    simpa only [Real.rpow_eq_pow, Real.log_rpow hDp] using hh
  have hharm : (harmonic (sourceR δ D) : ℝ) ≤ 1 + Real.log D :=
    (harmonic_le_one_add_log _).trans (by linarith [Real.log_le_log hRp hRleD])
  have hXup : lemmaSixSmoothScale δ D ≤ D ^ (2 : ℕ) := by
    have hh := Real.rpow_le_rpow_of_exponent_le hD.le
      (show 1 + 12 * δ ≤ (2 : ℝ) by linarith)
    simpa [lemmaSixSmoothScale] using hh
  have hlogup : (Real.log D) ^ (2 : ℕ) ≤ D := by
    simpa only [one_mul, Real.rpow_eq_pow, Real.rpow_two, Real.rpow_one] using hlogpow
  have hxD : (lemmaSixDirectCutoff δ D : ℝ) ≤ D ^ (3 : ℕ) := by
    calc
      _ ≤ lemmaSixSmoothScale δ D * (Real.log D) ^ 2 := hxup
      _ ≤ D ^ (2 : ℕ) * D := mul_le_mul hXup hlogup (sq_nonneg _) (sq_nonneg _)
      _ = _ := by ring
  have hxlog : Real.log (lemmaSixDirectCutoff δ D : ℝ) ≤ 3 * Real.log D := by
    have hxp : (0 : ℝ) < lemmaSixDirectCutoff δ D := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hx1)
    simpa only [Real.log_pow, Nat.cast_ofNat] using Real.log_le_log hxp hxD
  exact ⟨hR1, hD2.trans hXlower, hx1, hz1, hz12, hxsep, hlogR,
    hRup, hxup, hharm, hxlog⟩

/-- Uniform source-main threshold over every positive q≤D. -/
theorem eventually_source_main_threshold {δ : ℝ}
    (hlo : 1 / 560 ≤ δ) (hhi : δ ≤ 1 / 280) :
    ∀ᶠ D : ℝ in atTop, ∀ q : ℕ, 0 < q → (q : ℝ) ≤ D →
      4 ≤ (1 / 8 : ℝ) * ((Nat.totient q : ℝ) / (q : ℝ)) *
        Real.log (sourceR δ D : ℝ) := by
  have htot := MAPJutilaTotientSmallLogBound.eventually_uniform_div_totient_le_mul_log
    (show 0 < δ / 128 by linarith)
  filter_upwards [eventually_sourceGeometry hlo hhi, htot] with D hgeo htot
  intro q hq hqD
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq
  have hφp : (0 : ℝ) < Nat.totient q := by exact_mod_cast (Nat.totient_pos.mpr hq)
  have hratio : 0 ≤ (Nat.totient q : ℝ) / (q : ℝ) := by positivity
  have hprod := mul_le_mul_of_nonneg_right (htot q hq hqD) hratio
  have hcancel : (q : ℝ) / (Nat.totient q : ℝ) * ((Nat.totient q : ℝ) / (q : ℝ)) = 1 := by
    field_simp
  rw [hcancel] at hprod
  have hlog := mul_le_mul_of_nonneg_left hgeo.logR_lower hratio
  nlinarith

/-- All source legalities and the uniform main-size threshold in one event. -/
theorem eventually_sourceParameters {δ : ℝ}
    (hlo : 1 / 560 ≤ δ) (hhi : δ ≤ 1 / 280) :
    ∀ᶠ D : ℝ in atTop, SourceGeometry δ D ∧
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ D →
        4 ≤ (1 / 8 : ℝ) * ((Nat.totient q : ℝ) / (q : ℝ)) *
          Real.log (sourceR δ D : ℝ) :=
  (eventually_sourceGeometry hlo hhi).and (eventually_source_main_threshold hlo hhi)

end
end MAPJutilaCollarSourceParameters
#print axioms MAPJutilaCollarSourceParameters.eventually_sourceGeometry
#print axioms MAPJutilaCollarSourceParameters.eventually_source_main_threshold

#print axioms MAPJutilaCollarSourceParameters.eventually_sourceParameters
