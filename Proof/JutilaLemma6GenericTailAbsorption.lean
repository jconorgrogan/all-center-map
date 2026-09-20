import JutilaPseudocharacterHarmonicLower
import JutilaLemma6DirectTail
import JutilaLemma6ParameterLedger
import RamachandraShiftedDirectTailAbsorption
import PostA5RecenteredDetectorAbsorption
import PostA5HighStripSplitReductionFromFourthMoment

/-! Generic source tail absorption for X=D^(1+12δ), R≤D^δ and the literal
floor cutoff X log²D. Valid for every fixed δ≥0, including both collar choices. -/

namespace MAPJutilaLemma6GenericTailAbsorption

open Filter CGLProofDAG
open MAPJutilaLemma6DirectTail
open RamachandraShiftedDirectTailAbsorption
open RamachandraShiftedDirectSeries
open PostA5RecenteredDetectorAbsorption
open PostA5HighStripSplitReductionFromFourthMoment

noncomputable section

variable {δ : ℝ}

def lemmaSixSmoothScale (δ D : ℝ) : ℝ :=
  Real.rpow D (1 + 12 * δ)

def lemmaSixDirectCutoff (δ D : ℝ) : ℕ :=
  Nat.floor (lemmaSixSmoothScale δ D * (Real.log D) ^ 2)

def lemmaSixDirectTailEnvelope (δ D : ℝ) : ℝ :=
  Real.rpow D δ * (lemmaSixDirectCutoff δ D + 1 : ℝ) *
    (Real.exp (-(1 / lemmaSixSmoothScale δ D))) ^
      (lemmaSixDirectCutoff δ D + 1) *
    (Real.exp (-(1 / lemmaSixSmoothScale δ D)) /
        (1 - Real.exp (-(1 / lemmaSixSmoothScale δ D))) ^ 2 +
      (1 - Real.exp (-(1 / lemmaSixSmoothScale δ D)))⁻¹)

theorem lemmaSixSmoothScale_pos {D : ℝ} (hD : 0 < D) :
    0 < lemmaSixSmoothScale δ D := by
  exact Real.rpow_pos_of_pos hD _

theorem lemmaSixSmoothScale_eq_rpow {D : ℝ} :
    lemmaSixSmoothScale δ D = Real.rpow D (1 + 12 * δ) := by
  rfl

/-- The literal floor cutoff supplies the full `exp(-log^2 D)` decay. -/
theorem lemmaSix_geometric_power_le
    {D : ℝ} (hD : 0 < D) :
    (Real.exp (-(1 / lemmaSixSmoothScale δ D))) ^
        (lemmaSixDirectCutoff δ D + 1) ≤
      Real.exp (-(Real.log D) ^ 2) := by
  have hX : 0 < lemmaSixSmoothScale δ D := lemmaSixSmoothScale_pos (δ := δ) hD
  have harg0 : 0 ≤ lemmaSixSmoothScale δ D * (Real.log D) ^ 2 := by positivity
  have hcut : lemmaSixSmoothScale δ D * (Real.log D) ^ 2 <
      (lemmaSixDirectCutoff δ D + 1 : ℝ) := by
    unfold lemmaSixDirectCutoff
    exact Nat.lt_floor_add_one _
  have hratio : (Real.log D) ^ 2 <
      (lemmaSixDirectCutoff δ D + 1 : ℝ) / lemmaSixSmoothScale δ D := by
    exact (lt_div_iff₀ hX).2 (by nlinarith)
  rw [← exp_neg_nat_div_eq_pow
    (X := lemmaSixSmoothScale δ D) (lemmaSixDirectCutoff δ D + 1)]
  apply Real.exp_le_exp.mpr
  norm_num at hratio ⊢
  exact hratio.le

/-- The floor contributes at most `2 X log^2 D` once `D >= e`. -/
theorem lemmaSix_cutoff_succ_le (hδ : 0 ≤ δ)
    {D : ℝ} (hD : Real.exp 1 ≤ D) :
    (lemmaSixDirectCutoff δ D + 1 : ℝ) ≤
      2 * lemmaSixSmoothScale δ D * (Real.log D) ^ 2 := by
  have hDpos : 0 < D := (Real.exp_pos 1).trans_le hD
  have hDone : 1 ≤ D := (Real.one_le_exp (by norm_num)).trans hD
  have hlog : 1 ≤ Real.log D := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hD
  have hXone : 1 ≤ lemmaSixSmoothScale δ D := by
    unfold lemmaSixSmoothScale
    exact Real.one_le_rpow hDone (by linarith)
  have harg0 : 0 ≤ lemmaSixSmoothScale δ D * (Real.log D) ^ 2 := by positivity
  have hfloor : (lemmaSixDirectCutoff δ D : ℝ) ≤
      lemmaSixSmoothScale δ D * (Real.log D) ^ 2 := by
    unfold lemmaSixDirectCutoff
    exact Nat.floor_le harg0
  have hone : 1 ≤ lemmaSixSmoothScale δ D * (Real.log D) ^ 2 := by
    nlinarith [sq_nonneg (Real.log D - 1)]
  norm_num at hfloor ⊢
  nlinarith

theorem lemmaSix_rpow_product_eq {D : ℝ} (hD : 0 < D) :
    Real.rpow D δ *
        lemmaSixSmoothScale δ D ^ 3 =
      Real.rpow D (δ + 3 * (1 + 12 * δ)) := by
  unfold lemmaSixSmoothScale
  have hcube : Real.rpow D (1 + 12 * δ) ^ 3 =
      Real.rpow D ((1 + 12 * δ) * 3) := by
    calc
      Real.rpow D (1 + 12 * δ) ^ 3 =
          Real.rpow (Real.rpow D (1 + 12 * δ)) (3 : ℝ) := by
            exact (Real.rpow_natCast _ 3).symm
      _ = Real.rpow D ((1 + 12 * δ) * 3) := by
            exact (Real.rpow_mul hD.le (1 + 12 * δ) 3).symm
  rw [hcube]
  calc
    Real.rpow D δ *
          Real.rpow D ((1 + 12 * δ) * 3) =
        Real.rpow D (δ + (1 + 12 * δ) * 3) :=
      (Real.rpow_add hD δ ((1 + 12 * δ) * 3)).symm
    _ = Real.rpow D (δ + 3 * (1 + 12 * δ)) := by
      congr 1
      ring

/-- The complete literal tail envelope is eventually strictly smaller than
one.  This includes the floor, `R`, and both inverse-geometric terms. -/
theorem eventually_lemmaSixDirectTailEnvelope_lt_one (hδ : 0 ≤ δ) :
    ∀ᶠ D : ℝ in Filter.atTop,
      lemmaSixDirectTailEnvelope δ D < 1 := by
  have hpoly := eventually_const_mul_polylog_le_rpow
    12 2 1 (by norm_num) (by norm_num)
  filter_upwards [hpoly, eventually_ge_atTop (Real.exp 1),
      eventually_ge_atTop (3 : ℝ),
      eventually_ge_atTop
        (Real.exp (δ + 3 * (1 + 12 * δ) + 2)),
      eventually_gt_atTop (1 : ℝ)] with D hpolyD hDe hD3 hDgap hDone
  have hDpos : 0 < D := lt_trans (by norm_num) hDone
  have hDone' : 1 ≤ D := hDone.le
  have hlog0 : 0 ≤ Real.log D := Real.log_nonneg hDone'
  have hX3 : 3 ≤ lemmaSixSmoothScale δ D := by
    rw [lemmaSixSmoothScale_eq_rpow]
    have hexp : (1 : ℝ) ≤ 1 + 12 * δ := by linarith
    have hpow := Real.rpow_le_rpow_of_exponent_le hDone' hexp
    have hbase : D ≤ Real.rpow D (1 + 12 * δ) := by
      simpa only [Real.rpow_one] using hpow
    exact hD3.trans hbase
  have hcut := lemmaSix_cutoff_succ_le hδ hDe
  have hgeom := lemmaSix_geometric_power_le (δ := δ) hDpos
  have hparent := geometric_tail_parenthesis_le hX3
  have hgauss :
      Real.rpow D (δ + 3 * (1 + 12 * δ)) *
          Real.exp (-(Real.log D) ^ 2) ≤ Real.rpow D (-2) := by
    apply rpow_mul_exp_neg_log_sq_le_rpow_neg hDpos hlog0
    have hlogGap : δ + 3 * (1 + 12 * δ) + 2 ≤
        Real.log D := by
      rw [← Real.log_exp (δ + 3 * (1 + 12 * δ) + 2)]
      exact Real.log_le_log (Real.exp_pos _) hDgap
    exact hlogGap
  have hpowEq := lemmaSix_rpow_product_eq (δ := δ) hDpos
  have hEnv : lemmaSixDirectTailEnvelope δ D ≤
      (12 * Real.rpow (Real.log D) 2) *
        (Real.rpow D (δ + 3 * (1 + 12 * δ)) *
          Real.exp (-(Real.log D) ^ 2)) := by
    unfold lemmaSixDirectTailEnvelope
    have hnonnegCut : 0 ≤ (lemmaSixDirectCutoff δ D + 1 : ℝ) := by positivity
    have hnonnegGeom : 0 ≤
        (Real.exp (-(1 / lemmaSixSmoothScale δ D))) ^
          (lemmaSixDirectCutoff δ D + 1) := by positivity
    have hnonnegParent : 0 ≤
        Real.exp (-(1 / lemmaSixSmoothScale δ D)) /
            (1 - Real.exp (-(1 / lemmaSixSmoothScale δ D))) ^ 2 +
          (1 - Real.exp (-(1 / lemmaSixSmoothScale δ D)))⁻¹ := by
      have hXpos := lemmaSixSmoothScale_pos (δ := δ) hDpos
      have hden : 0 < 1 - Real.exp (-(1 / lemmaSixSmoothScale δ D)) := by
        exact sub_pos.mpr (Real.exp_lt_one_iff.mpr
          (neg_neg_of_pos (one_div_pos.mpr hXpos)))
      positivity
    calc
      Real.rpow D δ *
            (lemmaSixDirectCutoff δ D + 1 : ℝ) *
            (Real.exp (-(1 / lemmaSixSmoothScale δ D))) ^
              (lemmaSixDirectCutoff δ D + 1) *
            (Real.exp (-(1 / lemmaSixSmoothScale δ D)) /
                (1 - Real.exp (-(1 / lemmaSixSmoothScale δ D))) ^ 2 +
              (1 - Real.exp (-(1 / lemmaSixSmoothScale δ D)))⁻¹) ≤
          Real.rpow D δ *
            (2 * lemmaSixSmoothScale δ D * (Real.log D) ^ 2) *
            Real.exp (-(Real.log D) ^ 2) *
            (6 * lemmaSixSmoothScale δ D ^ 2) := by
        have hDrpow0 : 0 ≤ Real.rpow D δ :=
          Real.rpow_nonneg hDpos.le _
        have hcutRight0 : 0 ≤
            2 * lemmaSixSmoothScale δ D * (Real.log D) ^ 2 := by positivity
        have hgeomRight0 : 0 ≤ Real.exp (-(Real.log D) ^ 2) := by positivity
        have hfirst : Real.rpow D δ *
              (lemmaSixDirectCutoff δ D + 1 : ℝ) ≤
            Real.rpow D δ *
              (2 * lemmaSixSmoothScale δ D * (Real.log D) ^ 2) :=
          mul_le_mul_of_nonneg_left hcut hDrpow0
        have hsecond :
            (Real.rpow D δ *
                (lemmaSixDirectCutoff δ D + 1 : ℝ)) *
                (Real.exp (-(1 / lemmaSixSmoothScale δ D))) ^
                  (lemmaSixDirectCutoff δ D + 1) ≤
              (Real.rpow D δ *
                (2 * lemmaSixSmoothScale δ D * (Real.log D) ^ 2)) *
                Real.exp (-(Real.log D) ^ 2) :=
          mul_le_mul hfirst hgeom hnonnegGeom
            (mul_nonneg hDrpow0 hcutRight0)
        exact mul_le_mul hsecond hparent hnonnegParent
          (mul_nonneg (mul_nonneg hDrpow0 hcutRight0) hgeomRight0)
      _ = (12 * Real.rpow (Real.log D) 2) *
            ((Real.rpow D δ *
                lemmaSixSmoothScale δ D ^ 3) *
              Real.exp (-(Real.log D) ^ 2)) := by
        have hlogRpow : Real.rpow (Real.log D) 2 =
            (Real.log D) ^ (2 : ℕ) := by
          exact Real.rpow_natCast _ 2
        rw [hlogRpow]
        ring
      _ = (12 * Real.rpow (Real.log D) 2) *
            (Real.rpow D
                (δ + 3 * (1 + 12 * δ)) *
              Real.exp (-(Real.log D) ^ 2)) := by rw [hpowEq]
  have hmain : lemmaSixDirectTailEnvelope δ D ≤
      Real.rpow D 1 * Real.rpow D (-2) := by
    calc
      lemmaSixDirectTailEnvelope δ D ≤
          (12 * Real.rpow (Real.log D) 2) *
            (Real.rpow D
                (δ + 3 * (1 + 12 * δ)) *
              Real.exp (-(Real.log D) ^ 2)) := hEnv
      _ ≤ Real.rpow D 1 * Real.rpow D (-2) := by
        exact mul_le_mul hpolyD hgauss
          (mul_nonneg (Real.rpow_nonneg hDpos.le _)
            (Real.exp_nonneg _))
          (Real.rpow_nonneg hDpos.le _)
  have hprod : Real.rpow D 1 * Real.rpow D (-2) = Real.rpow D (-1) := by
    calc
      Real.rpow D 1 * Real.rpow D (-2) =
          Real.rpow D (1 + (-2)) := (Real.rpow_add hDpos 1 (-2)).symm
      _ = Real.rpow D (-1) := by norm_num
  rw [hprod] at hmain
  exact hmain.trans_lt (Real.rpow_lt_one_of_one_lt_of_neg hDone (by norm_num))

/-- Apply the absorbed envelope to the literal infinite arithmetic tail. -/
theorem norm_jutilaLemmaSixDirectTail_lt_one_of_envelope
    {D : ℝ} (hD : 0 < D)
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    {z1 z2 : ℝ} (hz1 : 1 < z1) (hz12 : z1 < z2)
    {S : Finset ℕ} {R : ℕ} (hS : S ⊆ Finset.Icc 1 R)
    {rho : ℂ} (hrho : 0 ≤ rho.re)
    (hR : (R : ℝ) ≤ Real.rpow D δ)
    (henv : lemmaSixDirectTailEnvelope δ D < 1) :
    ‖∑' k : ℕ,
        jutilaLemmaSixDirectTerm chi z1 z2 S rho
          (lemmaSixSmoothScale δ D) (k + (lemmaSixDirectCutoff δ D + 1))‖ < 1 := by
  have hX : 0 < lemmaSixSmoothScale δ D := lemmaSixSmoothScale_pos (δ := δ) hD
  have hraw := norm_jutilaLemmaSixDirectTail_le chi hz1 hz12 hS
    (lemmaSixDirectCutoff δ D) hrho hX
  have hden : 0 < 1 - Real.exp (-(1 / lemmaSixSmoothScale δ D)) := by
    exact sub_pos.mpr (Real.exp_lt_one_iff.mpr
      (neg_neg_of_pos (one_div_pos.mpr hX)))
  have hparent0 : 0 ≤
      Real.exp (-(1 / lemmaSixSmoothScale δ D)) /
          (1 - Real.exp (-(1 / lemmaSixSmoothScale δ D))) ^ 2 +
        (1 - Real.exp (-(1 / lemmaSixSmoothScale δ D)))⁻¹ := by
    positivity
  have hscale :
      (R : ℝ) * (lemmaSixDirectCutoff δ D + 1 : ℝ) *
          (Real.exp (-(1 / lemmaSixSmoothScale δ D))) ^
            (lemmaSixDirectCutoff δ D + 1) *
          (Real.exp (-(1 / lemmaSixSmoothScale δ D)) /
              (1 - Real.exp (-(1 / lemmaSixSmoothScale δ D))) ^ 2 +
            (1 - Real.exp (-(1 / lemmaSixSmoothScale δ D)))⁻¹) ≤
        lemmaSixDirectTailEnvelope δ D := by
    unfold lemmaSixDirectTailEnvelope
    gcongr
  exact hraw.trans_lt (hscale.trans_lt henv)

/-- Uniform eventual form used by the source descent: every admissible
character, selected `r`-system, and point on the shifted line has tail `< 1`. -/
theorem eventually_norm_jutilaLemmaSixDirectTail_lt_one (hδ : 0 ≤ δ) :
    ∀ᶠ D : ℝ in Filter.atTop,
      ∀ (q : ℕ) (chi : DirichletCharacter ℂ q)
        (z1 z2 : ℝ) (S : Finset ℕ) (R : ℕ) (rho : ℂ),
        1 < z1 → z1 < z2 → S ⊆ Finset.Icc 1 R → 0 ≤ rho.re →
        (R : ℝ) ≤ Real.rpow D δ →
        ‖∑' k : ℕ,
            jutilaLemmaSixDirectTerm chi z1 z2 S rho
              (lemmaSixSmoothScale δ D)
              (k + (lemmaSixDirectCutoff δ D + 1))‖ < 1 := by
  filter_upwards [eventually_lemmaSixDirectTailEnvelope_lt_one hδ,
      eventually_gt_atTop (0 : ℝ)] with D henv hD
  intro q chi z1 z2 S R rho hz1 hz12 hS hrho hR
  exact norm_jutilaLemmaSixDirectTail_lt_one_of_envelope hD chi
    hz1 hz12 hS hrho hR henv

/-- Canonical floor-selected source system; its range estimate is supplied
by the floor, so no tail-size or range budget remains as a premise. -/
theorem eventually_canonical_directTail_lt_one (hδ : 0 ≤ δ) :
    ∀ᶠ D : ℝ in Filter.atTop,
      ∀ (q : ℕ) (chi : DirichletCharacter ℂ q)
        (z1 z2 : ℝ) (rho : ℂ),
        1 < z1 → z1 < z2 → 0 ≤ rho.re →
        ‖∑' k : ℕ,
          jutilaLemmaSixDirectTerm chi z1 z2
            (MAPJutilaPseudocharacterHarmonicLower.jutilaPrimedRSet q
              (Nat.floor (Real.rpow D δ))) rho (lemmaSixSmoothScale δ D)
            (k + (lemmaSixDirectCutoff δ D + 1))‖ < 1 := by
  filter_upwards [eventually_norm_jutilaLemmaSixDirectTail_lt_one hδ,
    eventually_gt_atTop (0 : ℝ)] with D htail hD
  intro q chi z1 z2 rho hz1 hz12 hrho
  exact htail q chi z1 z2 _ _ rho hz1 hz12
    (MAPJutilaPseudocharacterHarmonicLower.jutilaPrimedRSet_subset_Icc q _)
    hrho (Nat.floor_le (Real.rpow_nonneg hD.le _))

end

end MAPJutilaLemma6GenericTailAbsorption

#print axioms MAPJutilaLemma6GenericTailAbsorption.lemmaSix_geometric_power_le
#print axioms MAPJutilaLemma6GenericTailAbsorption.eventually_lemmaSixDirectTailEnvelope_lt_one
#print axioms MAPJutilaLemma6GenericTailAbsorption.eventually_norm_jutilaLemmaSixDirectTail_lt_one

#print axioms MAPJutilaLemma6GenericTailAbsorption.eventually_canonical_directTail_lt_one
