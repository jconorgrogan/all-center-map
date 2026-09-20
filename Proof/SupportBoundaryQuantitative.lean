import SupportBoundaryWeld
import WindowArcBoundaryWeld

/-!
# Quantitative support-boundary leaf

This file turns the exact collar certificate into the pointwise logarithmic
bound needed by the MAP variance assembly, then absorbs its square over every
legal translated window.
-/

namespace SupportBoundaryQuantitative

open scoped BigOperators ArithmeticFunction
open SupportBoundaryWeld

noncomputable section

theorem boundary_index_le_three_mul_X
    {X : ℝ} (hX : 2 ≤ X) {h : ℤ}
    (hhX : (h.natAbs : ℝ) < X) {n : ℕ}
    (hn : n ∈ boundarySupport X h) :
    (n : ℝ) ≤ 3 * X ∧
      ((((n : ℤ) + h).toNat : ℕ) : ℝ) ≤ 3 * X := by
  simp only [boundarySupport, Finset.mem_filter, dyadicSupport,
    Finset.mem_Ioc] at hn
  rcases hn with ⟨⟨hnlo, hnhi⟩, hshiftpos, _⟩
  have h2X0 : 0 ≤ 2 * X := by positivity
  have hnFloor : (n : ℝ) ≤ (⌊2 * X⌋₊ : ℝ) := by exact_mod_cast hnhi
  have hn2X : (n : ℝ) ≤ 2 * X := hnFloor.trans (Nat.floor_le h2X0)
  constructor
  · linarith
  · have hshiftcast : ((((n : ℤ) + h).toNat : ℕ) : ℤ) =
        (n : ℤ) + h := Int.toNat_of_nonneg (le_of_lt hshiftpos)
    have hhle : (h : ℝ) ≤ (h.natAbs : ℝ) := by
      have hz : h ≤ (h.natAbs : ℤ) := Int.le_natAbs
      have hr : (h : ℝ) ≤ ((h.natAbs : ℤ) : ℝ) := Int.cast_le.mpr hz
      norm_num at hr ⊢
      exact hr
    have hcast : ((((n : ℤ) + h).toNat : ℕ) : ℝ) =
        (n : ℝ) + (h : ℝ) := by
      exact_mod_cast hshiftcast
    rw [hcast]
    linarith

theorem boundary_term_le_log_sq
    {X : ℝ} (hX : 2 ≤ X) {h : ℤ}
    (hhX : (h.natAbs : ℝ) < X) {n : ℕ}
    (hn : n ∈ boundarySupport X h) :
    |ArithmeticFunction.vonMangoldt n *
        PrimePairEndpoints.integerVonMangoldt ((n : ℤ) + h)| ≤
      (Real.log (3 * X)) ^ 2 := by
  have hb := boundary_index_le_three_mul_X hX hhX hn
  have hnmem := hn
  simp only [boundarySupport, Finset.mem_filter] at hnmem
  have hshiftpos := hnmem.2.1
  let k : ℕ := ((n : ℤ) + h).toNat
  have hnpos : 0 < n := pos_of_mem_dyadicSupport hnmem.1
  have hkpos : 0 < k := by
    have hkcast : (k : ℤ) = (n : ℤ) + h :=
      Int.toNat_of_nonneg (le_of_lt hshiftpos)
    have hkne : k ≠ 0 := by
      intro hk
      simp [hk] at hkcast
      omega
    omega
  have h3Xpos : 0 < 3 * X := by positivity
  have hlog0 : 0 ≤ Real.log (3 * X) := by
    apply Real.log_nonneg
    linarith
  have hlogn : Real.log (n : ℝ) ≤ Real.log (3 * X) :=
    Real.log_le_log (Nat.cast_pos.mpr hnpos) hb.1
  have hlogk : Real.log (k : ℝ) ≤ Real.log (3 * X) :=
    Real.log_le_log (Nat.cast_pos.mpr hkpos) hb.2
  have hvmn0 : 0 ≤ ArithmeticFunction.vonMangoldt n :=
    ArithmeticFunction.vonMangoldt_nonneg
  have hvmk0 : 0 ≤ ArithmeticFunction.vonMangoldt k :=
    ArithmeticFunction.vonMangoldt_nonneg
  have hvmn : ArithmeticFunction.vonMangoldt n ≤ Real.log (3 * X) :=
    ArithmeticFunction.vonMangoldt_le_log.trans hlogn
  have hvmk : ArithmeticFunction.vonMangoldt k ≤ Real.log (3 * X) :=
    ArithmeticFunction.vonMangoldt_le_log.trans hlogk
  have hint : PrimePairEndpoints.integerVonMangoldt ((n : ℤ) + h) =
      ArithmeticFunction.vonMangoldt k := by
    simp [PrimePairEndpoints.integerVonMangoldt, hshiftpos, k]
  rw [hint, abs_of_nonneg (mul_nonneg hvmn0 hvmk0), pow_two]
  exact mul_le_mul hvmn hvmk hvmk0 hlog0

/-- Explicit pointwise collar bound, with constant one and no `+1` loss. -/
theorem abs_supportBoundaryCorrection_le
    {X : ℝ} (hX : 2 ≤ X) {h : ℤ}
    (hhX : (h.natAbs : ℝ) < X) :
    |supportBoundaryCorrection X h| ≤
      (h.natAbs : ℝ) * (Real.log (3 * X)) ^ 2 := by
  rw [supportBoundaryCorrection_eq_sum_boundarySupport]
  calc
    |∑ n ∈ boundarySupport X h,
        ArithmeticFunction.vonMangoldt n *
          PrimePairEndpoints.integerVonMangoldt ((n : ℤ) + h)| ≤
        ∑ n ∈ boundarySupport X h,
          |ArithmeticFunction.vonMangoldt n *
            PrimePairEndpoints.integerVonMangoldt ((n : ℤ) + h)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ boundarySupport X h,
          (Real.log (3 * X)) ^ 2 := by
      exact Finset.sum_le_sum (fun n hn ↦ boundary_term_le_log_sq hX hhX hn)
    _ = ((boundarySupport X h).card : ℝ) *
          (Real.log (3 * X)) ^ 2 := by simp
    _ ≤ (h.natAbs : ℝ) * (Real.log (3 * X)) ^ 2 := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast boundarySupport_card_le_natAbs X h
      · positivity

/-- Exact cardinality bound for the closed real translated window. -/
theorem translatedWindow_card_real_le
    {H h₀ : ℝ} (hH : 0 ≤ H) :
    ((PrimePairEndpoints.translatedWindow H h₀).card : ℝ) ≤ 2 * H + 1 := by
  let a : ℤ := ⌈h₀ - H⌉
  let b : ℤ := ⌊h₀ + H⌋
  change ((Finset.Icc a b).card : ℝ) ≤ 2 * H + 1
  by_cases hab : a ≤ b + 1
  · have hcardZ : ((Finset.Icc a b).card : ℤ) = b + 1 - a :=
      Int.card_Icc_of_le a b hab
    have hcardR : ((Finset.Icc a b).card : ℝ) =
        (b : ℝ) + 1 - (a : ℝ) := by exact_mod_cast hcardZ
    rw [hcardR]
    have hb : (b : ℝ) ≤ h₀ + H := Int.floor_le _
    have ha : h₀ - H ≤ (a : ℝ) := Int.le_ceil _
    linarith
  · have hba : ¬ a ≤ b := by omega
    rw [Finset.Icc_eq_empty hba]
    simp
    linarith

/-- Every shift in a legal all-center window has the manuscript's uniform
mesoscopic size bound. -/
theorem natAbs_shift_le_two_rpow
    {X H h₀ ε : ℝ}
    (hlegal : PrimePairEndpoints.LegalParameters ε X H h₀)
    {h : ℤ} (hh : h ∈ PrimePairEndpoints.translatedWindow H h₀) :
    (h.natAbs : ℝ) ≤ 2 * Real.rpow X (1 - ε) := by
  have hbounds :=
    (PrimePairEndpoints.mem_translatedWindow_iff_real_bounds.mp hh)
  rcases hlegal with ⟨_hlower, hHupper, hh₀nonneg, hh₀upper⟩
  have habs : |(h : ℝ)| ≤ h₀ + H := by
    rw [abs_le]
    constructor <;> linarith
  have heq : (h.natAbs : ℝ) = |(h : ℝ)| := by
    rw [← Int.cast_abs]
    norm_num
  rw [heq]
  exact habs.trans (by linarith)

/-- The lower aperture condition forces a legal window to have length at
least one once `X ≥ 1`. -/
theorem one_le_H_of_legal
    {X H h₀ ε : ℝ} (hX : 1 ≤ X) (hε : 0 < ε)
    (hlegal : PrimePairEndpoints.LegalParameters ε X H h₀) :
    1 ≤ H := by
  have hexp : 0 ≤ 2 / 15 + ε := by linarith
  have hrpow : 1 ≤ Real.rpow X (2 / 15 + ε) :=
    Real.one_le_rpow hX hexp
  exact hrpow.trans hlegal.1

/-- Eventually the whole legal translated shift range lies in `|h| < X`,
which is the exact domain of the pointwise collar estimate. -/
theorem eventually_two_rpow_one_sub_lt
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℝ in Filter.atTop,
      2 * Real.rpow X (1 - ε) < X := by
  have hlarge : ∀ᶠ X : ℝ in Filter.atTop, 2 < Real.rpow X ε :=
    (tendsto_rpow_atTop hε).eventually (Filter.eventually_gt_atTop 2)
  filter_upwards [hlarge, Filter.eventually_gt_atTop 0] with X hpow hX
  have hpos : 0 < Real.rpow X (1 - ε) := Real.rpow_pos_of_pos hX _
  have hmul := mul_lt_mul_of_pos_left hpow hpos
  calc
    2 * Real.rpow X (1 - ε) = Real.rpow X (1 - ε) * 2 := by ring
    _ < Real.rpow X (1 - ε) * Real.rpow X ε := hmul
    _ = Real.rpow X ((1 - ε) + ε) := (Real.rpow_add hX _ _).symm
    _ = X := by ring_nf; simp

/-- Every fixed real polylogarithmic power is eventually below a prescribed
positive power of `X`. -/
theorem polylog_absorption (K η : ℝ) (hη : 0 < η) :
    ∀ᶠ X : ℝ in Filter.atTop,
      Real.rpow (Real.log X) K ≤ Real.rpow X η := by
  have hsmall := (isLittleO_log_rpow_rpow_atTop K hη).eventuallyLE
  filter_upwards [hsmall, Filter.eventually_ge_atTop (1 : ℝ)] with X hX hXone
  have hlog : 0 ≤ Real.log X := Real.log_nonneg hXone
  have hXnonneg : 0 ≤ X := zero_le_one.trans hXone
  simpa [Real.norm_of_nonneg (Real.rpow_nonneg hlog K),
    Real.norm_of_nonneg (Real.rpow_nonneg hXnonneg η)] using hX

/-- The supported Fourier correlation with the same zero-shift totalization as
the public prime-pair signal. -/
def dyadicSignal (X : ℝ) (h : ℤ) : ℝ :=
  if h = 0 then 0 else twiceSupportedCorrelation X h

theorem primePairSignal_sub_dyadicSignal
    {X : ℝ} {h : ℤ} (hh : h ≠ 0) :
    PrimePairEndpoints.primePairSignal X h - dyadicSignal X h =
      supportBoundaryCorrection X h := by
  simp only [PrimePairEndpoints.primePairSignal, dyadicSignal, if_neg hh]
  rw [primePairCorrelation_eq_twiceSupported_add_boundary]
  ring

theorem log_three_mul_le_two_log {X : ℝ} (hX : 3 ≤ X) :
    Real.log (3 * X) ≤ 2 * Real.log X := by
  have hXpos : 0 < X := by linarith
  have hlog3 : Real.log 3 ≤ Real.log X :=
    Real.log_le_log (by norm_num) hX
  rw [Real.log_mul (by norm_num) hXpos.ne']
  linarith

/-- Algebraic trade converting the remaining polylog into the exact negative
logarithmic power used by the public variance family. -/
theorem power_log_trade
    {A ε X : ℝ} (hX : 1 < X)
    (hpoly : Real.rpow (Real.log X) (A + 4) ≤
      Real.rpow X (2 * ε)) :
    Real.rpow X (2 - 2 * ε) * (Real.log X) ^ 4 ≤
      X ^ 2 * Real.rpow (Real.log X) (-A) := by
  have hXpos : 0 < X := by linarith
  have hlogpos : 0 < Real.log X := Real.log_pos hX
  have hneg0 : 0 ≤ Real.rpow (Real.log X) (-A) :=
    Real.rpow_nonneg hlogpos.le _
  have hm := mul_le_mul_of_nonneg_right hpoly hneg0
  have hleft : Real.rpow (Real.log X) (A + 4) *
      Real.rpow (Real.log X) (-A) = (Real.log X) ^ 4 := by
    calc
      Real.rpow (Real.log X) (A + 4) *
          Real.rpow (Real.log X) (-A) =
          Real.rpow (Real.log X) ((A + 4) + (-A)) :=
        (Real.rpow_add hlogpos _ _).symm
      _ = Real.rpow (Real.log X) (4 : ℝ) := by ring_nf
      _ = (Real.log X) ^ 4 := Real.rpow_natCast _ 4
  have hlogtrade : (Real.log X) ^ 4 ≤
      Real.rpow X (2 * ε) * Real.rpow (Real.log X) (-A) := by
    rw [← hleft]
    exact hm
  have hmul := mul_le_mul_of_nonneg_left hlogtrade
    (Real.rpow_nonneg hXpos.le (2 - 2 * ε))
  have hxprod : Real.rpow X (2 - 2 * ε) * Real.rpow X (2 * ε) =
      X ^ 2 := by
    calc
      Real.rpow X (2 - 2 * ε) * Real.rpow X (2 * ε) =
          Real.rpow X ((2 - 2 * ε) + (2 * ε)) :=
        (Real.rpow_add hXpos _ _).symm
      _ = Real.rpow X (2 : ℝ) := by ring_nf
      _ = X ^ 2 := Real.rpow_natCast X 2
  calc
    Real.rpow X (2 - 2 * ε) * (Real.log X) ^ 4 ≤
        Real.rpow X (2 - 2 * ε) *
          (Real.rpow X (2 * ε) * Real.rpow (Real.log X) (-A)) := hmul
    _ = (Real.rpow X (2 - 2 * ε) * Real.rpow X (2 * ε)) *
          Real.rpow (Real.log X) (-A) := by ring
    _ = X ^ 2 * Real.rpow (Real.log X) (-A) := by rw [hxprod]

/-- Pointwise squared envelope on every legal shift, after the eventual
`|h|<X` condition has been made explicit. -/
theorem signal_boundary_sq_le
    {X H h₀ ε : ℝ} (hX : 3 ≤ X)
    (hlegal : PrimePairEndpoints.LegalParameters ε X H h₀)
    (hshiftX : 2 * Real.rpow X (1 - ε) < X)
    {h : ℤ} (hhwin : h ∈ PrimePairEndpoints.translatedWindow H h₀) :
    |PrimePairEndpoints.primePairSignal X h - dyadicSignal X h| ^ 2 ≤
      64 * Real.rpow X (2 - 2 * ε) * (Real.log X) ^ 4 := by
  by_cases hh0 : h = 0
  · subst h
    simp [PrimePairEndpoints.primePairSignal, dyadicSignal]
    positivity
  · rw [primePairSignal_sub_dyadicSignal hh0]
    have habs := natAbs_shift_le_two_rpow hlegal hhwin
    have hhX : (h.natAbs : ℝ) < X := habs.trans_lt hshiftX
    have hpoint := abs_supportBoundaryCorrection_le (by linarith) hhX
    have hlog0 : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
    have hlog3 := log_three_mul_le_two_log hX
    have hlog3nonneg : 0 ≤ Real.log (3 * X) := by
      apply Real.log_nonneg
      nlinarith
    have hlogsq : (Real.log (3 * X)) ^ 2 ≤
        4 * (Real.log X) ^ 2 := by
      nlinarith [sq_nonneg (Real.log (3 * X)), sq_nonneg (Real.log X)]
    have hrpow0 : 0 ≤ Real.rpow X (1 - ε) :=
      Real.rpow_nonneg (by linarith) _
    have habs0 : 0 ≤ (h.natAbs : ℝ) := by positivity
    have hcoarse : |supportBoundaryCorrection X h| ≤
        8 * Real.rpow X (1 - ε) * (Real.log X) ^ 2 := by
      calc
        |supportBoundaryCorrection X h| ≤
            (h.natAbs : ℝ) * (Real.log (3 * X)) ^ 2 := hpoint
        _ ≤ (2 * Real.rpow X (1 - ε)) *
            (4 * (Real.log X) ^ 2) :=
          mul_le_mul habs hlogsq (sq_nonneg _) (by positivity)
        _ = 8 * Real.rpow X (1 - ε) * (Real.log X) ^ 2 := by ring
    have hright0 : 0 ≤ 8 * Real.rpow X (1 - ε) *
        (Real.log X) ^ 2 := by positivity
    have hsq := (sq_le_sq₀ (abs_nonneg _) hright0).2 hcoarse
    have hrpowsq : (Real.rpow X (1 - ε)) ^ 2 =
        Real.rpow X (2 - 2 * ε) := by
      calc
        (Real.rpow X (1 - ε)) ^ 2 =
            Real.rpow X (1 - ε) * Real.rpow X (1 - ε) := by ring
        _ = Real.rpow X ((1 - ε) + (1 - ε)) :=
          (Real.rpow_add (by linarith : 0 < X) _ _).symm
        _ = Real.rpow X (2 - 2 * ε) := by ring_nf
    calc
      |supportBoundaryCorrection X h| ^ 2 ≤
          (8 * Real.rpow X (1 - ε) * (Real.log X) ^ 2) ^ 2 := hsq
      _ = 64 * (Real.rpow X (1 - ε)) ^ 2 * (Real.log X) ^ 4 := by ring
      _ = 64 * Real.rpow X (2 - 2 * ε) * (Real.log X) ^ 4 := by rw [hrpowsq]

/-- Uniform all-center square-sum bound before the final polylogarithmic
absorption. -/
theorem supportBoundary_sq_sum_preabsorption
    {X H h₀ ε : ℝ} (hX : 3 ≤ X) (hε : 0 < ε)
    (hlegal : PrimePairEndpoints.LegalParameters ε X H h₀)
    (hshiftX : 2 * Real.rpow X (1 - ε) < X) :
    (∑ h ∈ PrimePairEndpoints.translatedWindow H h₀,
      |PrimePairEndpoints.primePairSignal X h - dyadicSignal X h| ^ 2) ≤
      192 * H * Real.rpow X (2 - 2 * ε) * (Real.log X) ^ 4 := by
  have hH1 : 1 ≤ H := one_le_H_of_legal (by linarith) hε hlegal
  have hcard := translatedWindow_card_real_le (h₀ := h₀)
    (show 0 ≤ H by linarith)
  have hcard3 : ((PrimePairEndpoints.translatedWindow H h₀).card : ℝ) ≤
      3 * H := hcard.trans (by linarith)
  have hconst0 : 0 ≤
      64 * Real.rpow X (2 - 2 * ε) * (Real.log X) ^ 4 := by
    exact mul_nonneg
      (mul_nonneg (by norm_num) (Real.rpow_nonneg (by linarith) _))
      (by positivity)
  calc
    (∑ h ∈ PrimePairEndpoints.translatedWindow H h₀,
        |PrimePairEndpoints.primePairSignal X h - dyadicSignal X h| ^ 2) ≤
        ∑ _h ∈ PrimePairEndpoints.translatedWindow H h₀,
          64 * Real.rpow X (2 - 2 * ε) * (Real.log X) ^ 4 := by
      exact Finset.sum_le_sum (fun h hh ↦ signal_boundary_sq_le hX hlegal hshiftX hh)
    _ = ((PrimePairEndpoints.translatedWindow H h₀).card : ℝ) *
        (64 * Real.rpow X (2 - 2 * ε) * (Real.log X) ^ 4) := by simp
    _ ≤ (3 * H) *
        (64 * Real.rpow X (2 - 2 * ε) * (Real.log X) ^ 4) :=
      mul_le_mul_of_nonneg_right hcard3 hconst0
    _ = 192 * H * Real.rpow X (2 - 2 * ε) * (Real.log X) ^ 4 := by ring

/-- The complete quantitative support-boundary leaf at exactly the public
`VarianceFamily` envelope and with the same all-center quantifier order. -/
theorem supportBoundary_sq_sum_le_logSaving :
    ∀ A ε : ℝ, 0 < A → 0 < ε →
      ∃ C X₀ : ℝ, 0 < C ∧ 2 ≤ X₀ ∧
        ∀ X H h₀ : ℝ, X₀ ≤ X →
          PrimePairEndpoints.LegalParameters ε X H h₀ →
          (∑ h ∈ PrimePairEndpoints.translatedWindow H h₀,
            |PrimePairEndpoints.primePairSignal X h - dyadicSignal X h| ^ 2) ≤
            C * H * X ^ 2 * Real.rpow (Real.log X) (-A) := by
  intro A ε hA hε
  have hshift := eventually_two_rpow_one_sub_lt hε
  have hpoly := polylog_absorption (A + 4) (2 * ε) (by positivity)
  have hall : ∀ᶠ X : ℝ in Filter.atTop,
      3 ≤ X ∧
      2 * Real.rpow X (1 - ε) < X ∧
      Real.rpow (Real.log X) (A + 4) ≤ Real.rpow X (2 * ε) := by
    filter_upwards [Filter.eventually_ge_atTop (3 : ℝ), hshift, hpoly] with X hX hs hp
    exact ⟨hX, hs, hp⟩
  rcases (Filter.eventually_atTop.1 hall) with ⟨threshold, hthreshold⟩
  refine ⟨192, max 3 threshold, by norm_num, by linarith [le_max_left 3 threshold], ?_⟩
  intro X H h₀ hXlarge hlegal
  have hXt : threshold ≤ X := (le_max_right 3 threshold).trans hXlarge
  rcases hthreshold X hXt with ⟨hX3, hshiftX, hpolyX⟩
  have hpre := supportBoundary_sq_sum_preabsorption hX3 hε hlegal hshiftX
  have htrade := power_log_trade (by linarith) hpolyX
  have hH1 : 1 ≤ H := one_le_H_of_legal (by linarith) hε hlegal
  have hfac0 : 0 ≤ 192 * H := by positivity
  have hmul := mul_le_mul_of_nonneg_left htrade hfac0
  calc
    (∑ h ∈ PrimePairEndpoints.translatedWindow H h₀,
        |PrimePairEndpoints.primePairSignal X h - dyadicSignal X h| ^ 2) ≤
        192 * H * Real.rpow X (2 - 2 * ε) * (Real.log X) ^ 4 := hpre
    _ = (192 * H) *
        (Real.rpow X (2 - 2 * ε) * (Real.log X) ^ 4) := by ring
    _ ≤ (192 * H) *
        (X ^ 2 * Real.rpow (Real.log X) (-A)) := hmul
    _ = 192 * H * X ^ 2 * Real.rpow (Real.log X) (-A) := by ring

end

end SupportBoundaryQuantitative
