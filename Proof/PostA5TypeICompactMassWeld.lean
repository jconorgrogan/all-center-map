import APLowRangeGlobal
import APTailReserveAbsorption
import CGLCompactStripSplitDensityConstructor

/-!
# Compact-strip Type-I density to weighted-zero-mass weld

This file contains only the deterministic finite-set reindex needed to feed a
compact-strip density estimate into the weighted zero mass in equation (2.7).
-/

namespace PostA5TypeICompactMassWeld

open scoped BigOperators
open DirichletZeros MAPGuthMaynard MAPLowBetaMeshClosure
open MAPAPWeightedZeroMassIntegration
open MAPAPZeroDensityCert MAPFixedScaleAPZeroRoute

noncomputable section

/-- The literal closed compact strip is covered by the paper's half-open beta
cells.  Analytic multiplicity is unchanged because every cell is cut from the
same `sigma = 0` zero divisor. -/
theorem primitiveCompactRangeMass_le_sum_cells
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {epsilon X T : ℝ} (hepsilon : 0 < epsilon) (hX : 0 ≤ X) :
    primitiveCompactRangeMass chi epsilon X T ≤
      ∑ j ∈ Finset.range
          (meshCellCount (paperDelta0 epsilon) (paperDelta epsilon)),
        primitiveInducerCellMass chi X T
          (meshPoint (paperDelta0 epsilon) (paperDelta epsilon) j)
          (paperDelta epsilon) := by
  classical
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  let psi := chi.primitiveCharacter
  let S := zeroSupport psi 0 T
  let J := Finset.range
    (meshCellCount (paperDelta0 epsilon) (paperDelta epsilon))
  let compact : ℂ → Prop := fun rho =>
    1 / 2 + paperDelta0 epsilon ≤ rho.re ∧ rho.re ≤ 4 / 5
  let cell : ℕ → ℂ → Prop := fun j rho =>
    meshPoint (paperDelta0 epsilon) (paperDelta epsilon) j ≤ rho.re ∧
      rho.re < meshPoint (paperDelta0 epsilon) (paperDelta epsilon) j +
        paperDelta epsilon
  let w : ℂ → ℝ := fun rho =>
    (zeroMultiplicity psi 0 T rho : ℝ) *
      Real.rpow X (2 * (rho.re - 1))
  have hw : ∀ rho, 0 ≤ w rho := by
    intro rho
    exact mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hX _)
  have hcover : ∀ rho, compact rho → ∃ j ∈ J, cell j rho := by
    intro rho hrho
    exact low_or_exists_paper_mesh_cell hepsilon hrho.2 |>.resolve_left
      (not_lt_of_ge hrho.1)
  unfold primitiveCompactRangeMass primitiveInducerCellMass
  change (∑ rho ∈ S.filter compact, w rho) ≤
    ∑ j ∈ J, ∑ rho ∈ S.filter (cell j), w rho
  have hswap :
      (∑ j ∈ J, ∑ rho ∈ S.filter (cell j), w rho) =
        ∑ rho ∈ S, ∑ j ∈ J.filter (fun j => cell j rho), w rho := by
    calc
      (∑ j ∈ J, ∑ rho ∈ S.filter (cell j), w rho) =
          ∑ j ∈ J, ∑ rho ∈ S, if cell j rho then w rho else 0 := by
            simp [Finset.sum_filter]
      _ = ∑ rho ∈ S, ∑ j ∈ J, if cell j rho then w rho else 0 := by
            rw [Finset.sum_comm]
      _ = ∑ rho ∈ S, ∑ j ∈ J.filter (fun j => cell j rho), w rho := by
            apply Finset.sum_congr rfl
            intro rho _hrho
            exact (Finset.sum_filter _ _).symm
  rw [hswap]
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro rho hrho
  by_cases hc : compact rho
  · obtain ⟨j, hjJ, hjcell⟩ := hcover rho hc
    have hsingle : w rho ≤ ∑ j ∈ J.filter (fun j => cell j rho), w rho := by
      exact Finset.single_le_sum (fun _ _ => hw rho)
        (Finset.mem_filter.mpr ⟨hjJ, hjcell⟩)
    have hc' :
        1 / 2 + paperDelta0 epsilon ≤ rho.re ∧ rho.re ≤ 4 / 5 := by
      simpa [compact] using hc
    rw [if_pos hc']
    exact hsingle
  · have hc' :
        ¬ (1 / 2 + paperDelta0 epsilon ≤ rho.re ∧ rho.re ≤ 4 / 5) := by
      simpa [compact] using hc
    rw [if_neg hc']
    exact Finset.sum_nonneg fun _ _ => hw rho

/-- The family cell mass uses exactly the positive-level and ambient-character
indexing of `polylogFamilyZeroCount`. -/
def apPrimitiveInducerCellMass (Q : ℕ) (X T sigma Delta : ℝ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q,
    if hq : q = 0 then 0
    else
      letI : NeZero q := ⟨hq⟩
      ∑ chi : DirichletCharacter ℂ q,
        primitiveInducerCellMass chi X T sigma Delta

/-- Sum the literal compact-strip cover over the same ambient family as
equation (2.7). -/
theorem apCompactRangeMass_le_sum_cells
    {Q : ℕ} {epsilon X T : ℝ}
    (hepsilon : 0 < epsilon) (hX : 0 ≤ X) :
    apCompactRangeMass Q epsilon X T ≤
      ∑ j ∈ Finset.range
          (meshCellCount (paperDelta0 epsilon) (paperDelta epsilon)),
        apPrimitiveInducerCellMass Q X T
          (meshPoint (paperDelta0 epsilon) (paperDelta epsilon) j)
          (paperDelta epsilon) := by
  classical
  let J := Finset.range
    (meshCellCount (paperDelta0 epsilon) (paperDelta epsilon))
  let I := Finset.Icc 1 Q
  unfold apCompactRangeMass apPrimitiveInducerCellMass
  change (∑ q ∈ I,
      if hq : q = 0 then 0
      else
        letI : NeZero q := ⟨hq⟩
        ∑ chi : DirichletCharacter ℂ q,
          primitiveCompactRangeMass chi epsilon X T) ≤
    ∑ j ∈ J, ∑ q ∈ I,
      if hq : q = 0 then 0
      else
        letI : NeZero q := ⟨hq⟩
        ∑ chi : DirichletCharacter ℂ q,
          primitiveInducerCellMass chi X T
            (meshPoint (paperDelta0 epsilon) (paperDelta epsilon) j)
            (paperDelta epsilon)
  rw [show (∑ j ∈ J, ∑ q ∈ I,
      if hq : q = 0 then 0
      else
        letI : NeZero q := ⟨hq⟩
        ∑ chi : DirichletCharacter ℂ q,
          primitiveInducerCellMass chi X T
            (meshPoint (paperDelta0 epsilon) (paperDelta epsilon) j)
            (paperDelta epsilon)) =
      ∑ q ∈ I, ∑ j ∈ J,
      if hq : q = 0 then 0
      else
        letI : NeZero q := ⟨hq⟩
        ∑ chi : DirichletCharacter ℂ q,
          primitiveInducerCellMass chi X T
            (meshPoint (paperDelta0 epsilon) (paperDelta epsilon) j)
            (paperDelta epsilon) by rw [Finset.sum_comm]]
  apply Finset.sum_le_sum
  intro q hqI
  split_ifs with hq0
  · simp
  · letI : NeZero q := ⟨hq0⟩
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro chi _hchi
    exact primitiveCompactRangeMass_le_sum_cells chi hepsilon hX

/-- Each family cell is bounded by the exact primitive-inducer family count at
its left endpoint times the largest zero weight in the cell. -/
theorem apPrimitiveInducerCellMass_le_family_count_weight
    {Q : ℕ} {X T sigma Delta : ℝ} (hX : 1 ≤ X) :
    apPrimitiveInducerCellMass Q X T sigma Delta ≤
      (MAPAPZeroDensityCert.polylogFamilyZeroCount Q sigma T : ℝ) *
        Real.rpow X (2 * (sigma + Delta - 1)) := by
  classical
  let W := Real.rpow X (2 * (sigma + Delta - 1))
  unfold apPrimitiveInducerCellMass
  unfold MAPAPZeroDensityCert.polylogFamilyZeroCount
  calc
    (∑ q ∈ Finset.Icc 1 Q,
      if hq : q = 0 then 0
      else
        letI : NeZero q := ⟨hq⟩
        ∑ chi : DirichletCharacter ℂ q,
          primitiveInducerCellMass chi X T sigma Delta) ≤
      ∑ q ∈ Finset.Icc 1 Q,
        if hq : q = 0 then 0
        else
          letI : NeZero q := ⟨hq⟩
          ∑ chi : DirichletCharacter ℂ q,
            (primitiveDirichletZeroCount chi sigma T : ℝ) * W := by
      apply Finset.sum_le_sum
      intro q hqI
      split_ifs with hq0
      · exact le_rfl
      · letI : NeZero q := ⟨hq0⟩
        apply Finset.sum_le_sum
        intro chi _hchi
        exact primitiveInducerCellMass_le_count_weight chi hX
    _ = (↑(∑ q ∈ Finset.Icc 1 Q,
        MAPAPZeroDensityCert.zeroCountAtLevel q sigma T) : ℝ) * W := by
      rw [Nat.cast_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q _hqI
      unfold MAPAPZeroDensityCert.zeroCountAtLevel
      split_ifs with hq0
      · simp
      · push_cast
        rw [Finset.sum_mul]
    _ = (↑(∑ q ∈ Finset.Icc 1 Q,
        MAPAPZeroDensityCert.zeroCountAtLevel q sigma T) : ℝ) *
          Real.rpow X (2 * (sigma + Delta - 1)) := by rfl

/-- The exact multiplicity-aware compact mass is bounded by the finite sum of
the primitive-inducer family counts at the paper mesh left endpoints. -/
theorem apCompactRangeMass_le_mesh_family_count_weight
    {Q : ℕ} {epsilon X T : ℝ}
    (hepsilon : 0 < epsilon) (hX : 1 ≤ X) :
    apCompactRangeMass Q epsilon X T ≤
      ∑ j ∈ Finset.range
          (meshCellCount (paperDelta0 epsilon) (paperDelta epsilon)),
        (MAPAPZeroDensityCert.polylogFamilyZeroCount Q
            (meshPoint (paperDelta0 epsilon) (paperDelta epsilon) j) T : ℝ) *
          Real.rpow X
            (2 * (meshPoint (paperDelta0 epsilon) (paperDelta epsilon) j +
              paperDelta epsilon - 1)) := by
  calc
    apCompactRangeMass Q epsilon X T ≤
        ∑ j ∈ Finset.range
            (meshCellCount (paperDelta0 epsilon) (paperDelta epsilon)),
          apPrimitiveInducerCellMass Q X T
            (meshPoint (paperDelta0 epsilon) (paperDelta epsilon) j)
            (paperDelta epsilon) :=
      apCompactRangeMass_le_sum_cells hepsilon (zero_le_one.trans hX)
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j _hj
      exact apPrimitiveInducerCellMass_le_family_count_weight hX

/-- Reparameterize the canonical `T`-based polylog conductor range at the MAP
height `T = X^(tau epsilon)`.  Doubling the source log exponent absorbs the
fixed factor `tau epsilon` in `log T`. -/
theorem PolylogConductorDensity.at_apZeroHeight
    (hdensity : PolylogConductorDensity)
    (K delta eta epsilon : ℝ)
    (hK : 0 < K) (hdelta : 0 < delta) (heta : 0 < eta)
    (hepsilon : 0 < epsilon) (hepsilonCap : epsilon ≤ 1 / 10) :
    ∃ C X₀ : ℝ, 0 < C ∧ 2 ≤ X₀ ∧
      ∀ (X : ℝ) (Q : ℕ) (sigma : ℝ), X₀ ≤ X →
        (Q : ℝ) ≤ Real.rpow (Real.log X) K →
        1 / 2 + delta ≤ sigma → sigma ≤ 4 / 5 →
        (polylogFamilyZeroCount Q sigma (apZeroHeight epsilon X) : ℝ) ≤
          C * Real.rpow (apZeroHeight epsilon X)
            (densityCoeff * (1 - sigma) + eta) := by
  obtain ⟨C, Tsource, hC, hTsource, hsource⟩ :=
    hdensity (2 * K) delta eta (by positivity) hdelta heta
  have htau : 0 < tau epsilon := tau_pos hepsilonCap
  have hheightEvent : ∀ᶠ X : ℝ in Filter.atTop,
      Tsource ≤ Real.rpow X (tau epsilon) :=
    (tendsto_rpow_atTop htau).eventually (Filter.eventually_ge_atTop Tsource)
  have hscaleEvent : ∀ᶠ X : ℝ in Filter.atTop,
      Real.exp 4 ≤ X := Filter.eventually_ge_atTop (Real.exp 4)
  have hevent : ∀ᶠ X : ℝ in Filter.atTop,
      Tsource ≤ apZeroHeight epsilon X ∧
      Real.rpow (Real.log X) K ≤
        Real.rpow (Real.log (apZeroHeight epsilon X)) (2 * K) := by
    filter_upwards [hheightEvent, hscaleEvent] with X hheight hX
    have hXpos : 0 < X := (Real.exp_pos 4).trans_le hX
    have hL : 4 ≤ Real.log X := by
      rw [← Real.log_exp 4]
      exact Real.log_le_log (Real.exp_pos 4) hX
    have hL0 : 0 ≤ Real.log X := by linarith
    have htauHalf : (1 / 2 : ℝ) ≤ tau epsilon := by
      exact (by norm_num : (1 / 2 : ℝ) ≤ 49 / 60) |>.trans
        (forty_nine_sixtieths_le_tau hepsilonCap)
    have htauL : Real.log X / 2 ≤ tau epsilon * Real.log X := by
      have := mul_le_mul_of_nonneg_right htauHalf hL0
      nlinarith
    have hbase : Real.log X ≤ (tau epsilon * Real.log X) ^ 2 := by
      nlinarith [sq_nonneg (tau epsilon * Real.log X - Real.log X / 2)]
    have htauL0 : 0 ≤ tau epsilon * Real.log X :=
      mul_nonneg htau.le hL0
    have hrpowBase : Real.rpow (Real.log X) K ≤
        Real.rpow ((tau epsilon * Real.log X) ^ 2) K :=
      Real.rpow_le_rpow hL0 hbase hK.le
    have hnested :
        Real.rpow ((tau epsilon * Real.log X) ^ 2) K =
          Real.rpow (tau epsilon * Real.log X) (2 * K) := by
      rw [← Real.rpow_natCast]
      exact (Real.rpow_mul htauL0 2 K).symm
    have hlogHeight :
        Real.log (apZeroHeight epsilon X) =
          tau epsilon * Real.log X := by
      unfold apZeroHeight tau
      exact Real.log_rpow hXpos (13 / 15 - epsilon / 2)
    constructor
    · simpa [apZeroHeight, tau] using hheight
    · rw [hlogHeight]
      exact hrpowBase.trans_eq hnested
  obtain ⟨Xevent, hXevent⟩ := Filter.eventually_atTop.1 hevent
  let X₀ := max Xevent (Real.exp 4)
  refine ⟨C, X₀, hC, ?_, ?_⟩
  · have : 2 ≤ Real.exp 4 := by
      have := Real.exp_one_gt_two
      exact this.le.trans (Real.exp_le_exp.mpr (by norm_num))
    exact this.trans (le_max_right _ _)
  intro X Q sigma hX hQ hsigmaLow hsigmaHigh
  have hXevent' : Xevent ≤ X := (le_max_left _ _).trans hX
  obtain ⟨hheight, hcondScale⟩ := hXevent X hXevent'
  exact hsource (apZeroHeight epsilon X) Q sigma hheight
    (hQ.trans hcondScale) hsigmaLow hsigmaHigh

/-- The canonical compact-strip density estimate supplies the exact compact
range hypothesis of the equation-(2.7) weighted-mass weld. -/
theorem apCompactRangeMass_logSaving_of_polylogConductorDensity
    (hdensity : PolylogConductorDensity) :
    ∀ K A epsilon : ℝ,
      0 < K → 0 < A → 0 < epsilon → epsilon ≤ 1 / 10 →
      ∃ C X₀ : ℝ, 0 < C ∧ 2 ≤ X₀ ∧
        ∀ X : ℝ, X₀ ≤ X →
          apCompactRangeMass ⌊Real.rpow (Real.log X) K⌋₊ epsilon X
              (apZeroHeight epsilon X) ≤
            C * Real.rpow (Real.log X) (-A) := by
  intro K A epsilon hK hA hepsilon hepsilonCap
  let delta := paperDelta0 epsilon
  let eta := etaZD epsilon
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact paperDelta0_pos hepsilon
  have heta : 0 < eta := by
    dsimp [eta]
    exact etaZD_pos hepsilon hepsilonCap
  obtain ⟨Cd, Xdensity, hCd, hXdensity, hdensityX⟩ :=
    PolylogConductorDensity.at_apZeroHeight hdensity K delta eta epsilon
      hK hdelta heta hepsilon hepsilonCap
  let J := meshCellCount (paperDelta0 epsilon) (paperDelta epsilon)
  let C : ℝ := J * Cd
  have hJpos : 0 < J := by
    dsimp [J, meshCellCount]
    exact Nat.succ_pos _
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have htail := MAPAPTailReserveAbsorption.eventually_tail_power_mul_polylog_le
    A 0 (3 * epsilon / 26) (by positivity)
  have hevent : ∀ᶠ X : ℝ in Filter.atTop,
      Xdensity ≤ X ∧ Real.exp 1 ≤ X ∧
      Real.rpow X (-(3 * epsilon / 52)) ≤
        Real.rpow (Real.log X) (-A) := by
    filter_upwards [Filter.eventually_ge_atTop Xdensity,
      Filter.eventually_ge_atTop (Real.exp 1), htail] with X hXd hX htailX
    refine ⟨hXd, hX, ?_⟩
    simpa [show -(3 * epsilon / 26) / 2 = -(3 * epsilon / 52) by ring]
      using htailX
  obtain ⟨Xevent, hXevent⟩ := Filter.eventually_atTop.1 hevent
  let X₀ := max Xevent Xdensity
  refine ⟨C, X₀, hC, ?_, ?_⟩
  · exact hXdensity.trans (le_max_right _ _)
  intro X hXX₀
  have hXevent' : Xevent ≤ X := (le_max_left _ _).trans hXX₀
  obtain ⟨hXdensityX, hXexp, htailX⟩ := hXevent X hXevent'
  have hXone : 1 ≤ X := by
    have : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr zero_lt_one
    linarith
  have hlog : 1 ≤ Real.log X := by
    have hXpos : 0 < X := (Real.exp_pos 1).trans_le hXexp
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hXexp
  let Q := ⌊Real.rpow (Real.log X) K⌋₊
  have hQ : (Q : ℝ) ≤ Real.rpow (Real.log X) K := by
    dsimp [Q]
    exact Nat.floor_le (Real.rpow_nonneg (zero_le_one.trans hlog) _)
  have hmesh :
      apCompactRangeMass Q epsilon X (apZeroHeight epsilon X) ≤
        ∑ j ∈ Finset.range J,
          (polylogFamilyZeroCount Q
              (meshPoint (paperDelta0 epsilon) (paperDelta epsilon) j)
              (apZeroHeight epsilon X) : ℝ) *
            Real.rpow X
              (2 * (meshPoint (paperDelta0 epsilon) (paperDelta epsilon) j +
                paperDelta epsilon - 1)) := by
    simpa only [J] using
      (apCompactRangeMass_le_mesh_family_count_weight
        (Q := Q) (epsilon := epsilon) (X := X)
        (T := apZeroHeight epsilon X) hepsilon hXone)
  have hcell : ∀ j, j < J →
      (polylogFamilyZeroCount Q
          (meshPoint (paperDelta0 epsilon) (paperDelta epsilon) j)
          (apZeroHeight epsilon X) : ℝ) *
        Real.rpow X
          (2 * (meshPoint (paperDelta0 epsilon) (paperDelta epsilon) j +
            paperDelta epsilon - 1)) ≤
        Cd * Real.rpow X (-(3 * epsilon / 52)) := by
    intro j hj
    let sigma := meshPoint (paperDelta0 epsilon) (paperDelta epsilon) j
    have hsigmaLow : 1 / 2 + delta ≤ sigma := by
      dsimp [delta, sigma, meshPoint]
      exact le_add_of_nonneg_right
        (mul_nonneg (Nat.cast_nonneg j) (paperDelta_pos hepsilon).le)
    have hsigmaHigh : sigma ≤ 4 / 5 := by
      dsimp [sigma, J] at hj ⊢
      exact paper_mesh_left_endpoint_le_four_fifths hepsilon hj
    have hd := hdensityX X Q sigma hXdensityX hQ hsigmaLow hsigmaHigh
    have hd' :
        (polylogFamilyZeroCount Q sigma (Real.rpow X (tau epsilon)) : ℝ) ≤
          Cd * Real.rpow (Real.rpow X (tau epsilon))
            (densityCoeff * (1 - sigma) + etaZD epsilon) := by
      simpa [apZeroHeight, tau, eta, delta,
        ZeroDensityArithmetic.uniformCoeff, densityCoeff] using hd
    simpa only [sigma] using!
      (chosen_densityAtHeight_mul_weight_le hepsilon hepsilonCap hsigmaHigh
        hXone hCd.le hd')
  calc
    apCompactRangeMass Q epsilon X (apZeroHeight epsilon X) ≤
        ∑ j ∈ Finset.range J,
          (polylogFamilyZeroCount Q
              (meshPoint (paperDelta0 epsilon) (paperDelta epsilon) j)
              (apZeroHeight epsilon X) : ℝ) *
            Real.rpow X
              (2 * (meshPoint (paperDelta0 epsilon) (paperDelta epsilon) j +
                paperDelta epsilon - 1)) := hmesh
    _ ≤ J * (Cd * Real.rpow X (-(3 * epsilon / 52))) := by
      apply sum_mesh_cells_le
      intro j hj
      constructor
      · exact mul_nonneg (Nat.cast_nonneg _)
          (Real.rpow_nonneg (zero_le_one.trans hXone) _)
      · exact hcell j hj
    _ = C * Real.rpow X (-(3 * epsilon / 52)) := by
      dsimp [C]
      ring
    _ ≤ C * Real.rpow (Real.log X) (-A) :=
      mul_le_mul_of_nonneg_left htailX hC.le

/-- The narrow equation-(2.7) constructor after the Type-I compact density
leaf: only the already separate regular and exceptional near-one ranges remain. -/
theorem apWeightedZeroMassLogSaving_of_polylogConductorDensity
    (hdensity : PolylogConductorDensity)
    (hRegularNear : ∀ K A epsilon : ℝ,
      0 < K → 0 < A → 0 < epsilon → epsilon ≤ 1 / 10 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧
        ∀ X : ℝ, X0 ≤ X →
          apRegularNearOneRangeMass ⌊Real.rpow (Real.log X) K⌋₊ X
              (apZeroHeight epsilon X) ≤
            C * Real.rpow (Real.log X) (-A))
    (hExceptional : ∀ K A epsilon : ℝ,
      0 < K → 0 < A → 0 < epsilon → epsilon ≤ 1 / 10 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧
        ∀ X : ℝ, X0 ≤ X →
          apExceptionalNearOneRangeMass
              ⌊Real.rpow (Real.log X) K⌋₊ X
              (apZeroHeight epsilon X) ≤
            C * Real.rpow (Real.log X) (-A)) :
    APWeightedZeroMassLogSaving :=
  MAPAPLowRangeGlobal.apWeightedZeroMassLogSaving_of_remaining_ranges
    (apCompactRangeMass_logSaving_of_polylogConductorDensity hdensity)
    hRegularNear hExceptional

/-- Root-facing connector: the source-faithful A.4/A.5 split and
Guth--Maynard supply the compact density, which is then inserted into the
equation-(2.7) weighted-mass weld. -/
theorem apWeightedZeroMassLogSaving_of_guthMaynard_and_split
    (hanalytic :
      CGLCompactStripSplitDensityConstructor.CompactStripSplitAnalyticInput)
    (hGM : CGLProofDAG.GuthMaynardTheorem11)
    (hRegularNear : ∀ K A epsilon : ℝ,
      0 < K → 0 < A → 0 < epsilon → epsilon ≤ 1 / 10 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧
        ∀ X : ℝ, X0 ≤ X →
          apRegularNearOneRangeMass ⌊Real.rpow (Real.log X) K⌋₊ X
              (apZeroHeight epsilon X) ≤
            C * Real.rpow (Real.log X) (-A))
    (hExceptional : ∀ K A epsilon : ℝ,
      0 < K → 0 < A → 0 < epsilon → epsilon ≤ 1 / 10 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧
        ∀ X : ℝ, X0 ≤ X →
          apExceptionalNearOneRangeMass
              ⌊Real.rpow (Real.log X) K⌋₊ X
              (apZeroHeight epsilon X) ≤
            C * Real.rpow (Real.log X) (-A)) :
    APWeightedZeroMassLogSaving :=
  apWeightedZeroMassLogSaving_of_polylogConductorDensity
    (CGLCompactStripSplitDensityConstructor.polylogConductorDensity_of_guthMaynard_and_split
      hanalytic hGM)
    hRegularNear hExceptional

end
end PostA5TypeICompactMassWeld

#print axioms PostA5TypeICompactMassWeld.primitiveCompactRangeMass_le_sum_cells
#print axioms PostA5TypeICompactMassWeld.apCompactRangeMass_le_sum_cells
#print axioms PostA5TypeICompactMassWeld.apPrimitiveInducerCellMass_le_family_count_weight
#print axioms PostA5TypeICompactMassWeld.apCompactRangeMass_le_mesh_family_count_weight
#print axioms PostA5TypeICompactMassWeld.PolylogConductorDensity.at_apZeroHeight
#print axioms PostA5TypeICompactMassWeld.apCompactRangeMass_logSaving_of_polylogConductorDensity
#print axioms PostA5TypeICompactMassWeld.apWeightedZeroMassLogSaving_of_polylogConductorDensity
#print axioms PostA5TypeICompactMassWeld.apWeightedZeroMassLogSaving_of_guthMaynard_and_split
