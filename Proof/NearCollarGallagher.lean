import AllCenterNearFarTransfer
import APZeroDensityCertificate
import SupportBoundaryQuantitative

/-!
# The near-rational Gallagher branch, with the four errors kept separate

This file does not assert the missing harmonic theorem.  It names one exact
analytic leaf, `NearCollarGallagherTransfer`, whose conclusion is the literal
four-term estimate before logarithmic absorption.  Everything after that leaf
-- selection of the AP reserve, conversion of the `lintegral` AP estimate,
scale legality, and absorption of all four terms -- is proved here.

The leaf is deliberately stronger and more informative than the near conjunct
of `CanonicalNearFarEstimates`: its first term contains the actual
`simultaneousAPMax` integral, and the endpoint, bad-prime-power, and continuous
tail errors remain visible.
-/

namespace MAPNearCollarGallagher

open AddCircle MeasureTheory Set Filter
open scoped BigOperators ENNReal ArithmeticFunction

noncomputable section

open APFoundation MAPAPZeroDensityCert PrimePairEndpoints MAPHarmonicEndpoint
open MAPAllCenterApertureTransfer MAPAllCenterNearFarTransfer

/-- The reserve with which Proposition 2.2 must actually be invoked. -/
def apReserve (epsilon : ℝ) : ℝ := apertureReserve epsilon / 2

/-- `R=(log X)^Cc`. -/
def collarR (X : ℝ) (Cc : ℕ) : ℝ := (Real.log X) ^ Cc

/-- `Q=(log X)^B`. -/
def collarQ (X : ℝ) (B : ℕ) : ℝ := (Real.log X) ^ B

/-- `P=(log X)^D`. -/
def collarP (X : ℝ) (D : ℕ) : ℝ := (Real.log X) ^ D

/-- `y=H_*/(32R)`. -/
def gallagherWindow (epsilon X : ℝ) (Cc : ℕ) : ℝ :=
  baseAperture epsilon X / (32 * collarR X Cc)

/-- The actual AP maximal integral consumed by the Gallagher step. -/
def apMaxIntegral (B : ℕ) (epsilonAP X : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in Set.Icc (X / 2) (4 * X),
    simultaneousAPMax (B : ℝ) epsilonAP X x

/-- The four errors on the right side of manuscript (3.2), before absorption.
The AP term is not replaced by its asymptotic upper bound. -/
def nearFourTermRHS
    (B D Cc : ℕ) (epsilon epsilonAP X : ℝ) : ℝ :=
  let Q := collarQ X B
  let P := collarP X D
  let y := gallagherWindow epsilon X Cc
  Q ^ 4 * (apMaxIntegral B epsilonAP X).toReal +
    Q ^ 2 * y * (Real.log X) ^ 2 +
    Q ^ 2 * (Real.log X) ^ 4 / y +
    X * Q ^ 2 / P

/--
The one harmonic-analytic leaf left by this module.

It is the signed-measure Gallagher--Plancherel transfer, including the exact
residue-class decomposition, endpoint sliding energy, bad-prime-power sliding
energy, circle/real-line transfer, union-to-sum step, and continuous-main-term
tail.  Those ingredients are not present in mathlib.  Unlike the desired near
conjunct, this statement exposes the actual AP integral and all four error
sources.
-/
def NearCollarGallagherTransfer : Prop :=
  ∃ Cg Xg : ℝ, 0 < Cg ∧ 2 ≤ Xg ∧
    ∀ (epsilon epsilonAP X : ℝ) (B D Cc : ℕ),
      0 < epsilon → 0 < epsilonAP → Xg ≤ X →
      2 ≤ Real.log X →
      Real.rpow X (2 / 15 + epsilonAP) ≤
        gallagherWindow epsilon X Cc →
      1 ≤ gallagherWindow epsilon X Cc →
      gallagherWindow epsilon X Cc ≤ X / 2 →
      collarP X D / X ≤
        1 / (8 * gallagherWindow epsilon X Cc) →
      (∫ alpha in outerRationalCollars epsilon X B Cc ∩
            minorArcs X B D,
          ‖primeExponentialSum X alpha‖ ^ 2
            ∂AddCircle.haarAddCircle) ≤
        Cg * nearFourTermRHS B D Cc epsilon epsilonAP X

/-- Exact first conjunct of `CanonicalNearFarEstimates`, kept as a standalone
proposition so it can later be synchronized with the far branch. -/
def CanonicalNearCollarEstimate : Prop :=
  ∀ A epsilon : ℝ, 0 < A → 0 < epsilon →
    ∃ B D Cc : ℕ, ∃ C X₀ : ℝ,
      0 < C ∧ 2 ≤ X₀ ∧
      ∀ X : ℝ, X₀ ≤ X →
        1 ≤ Real.log X ∧
        (∫ alpha in outerRationalCollars epsilon X B Cc ∩
              minorArcs X B D,
            ‖primeExponentialSum X alpha‖ ^ 2
              ∂AddCircle.haarAddCircle) ≤
          C * X * Real.rpow (Real.log X) (-A)

theorem apReserve_pos {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    0 < apReserve epsilon := by
  exact div_pos (apertureReserve_pos hepsilon) (by norm_num)

theorem apReserve_le_cap (epsilon : ℝ) : apReserve epsilon ≤ 13 / 30 := by
  unfold apReserve apertureReserve
  have h : min (epsilon / 4) (1 / 1200) ≤ (1 / 1200 : ℝ) := min_le_right _ _
  linarith

/-- Natural logarithmic powers are real powers on a nonnegative base. -/
theorem log_pow_eq_rpow {X : ℝ} (n : ℕ) :
    (Real.log X) ^ n = Real.rpow (Real.log X) (n : ℝ) := by
  symm
  exact Real.rpow_natCast (Real.log X) n

/-- Direct exponent subtraction used for the first and fourth errors. -/
theorem log_pow_mul_negative_rpow_le
    {X A : ℝ} {m n : ℕ}
    (hlog : 1 ≤ Real.log X) (hexp : A + m ≤ n) :
    (Real.log X) ^ m * Real.rpow (Real.log X) (-(n : ℝ)) ≤
      Real.rpow (Real.log X) (-A) := by
  have hlogpos : 0 < Real.log X := zero_lt_one.trans_le hlog
  rw [log_pow_eq_rpow]
  calc
    Real.rpow (Real.log X) (m : ℝ) *
        Real.rpow (Real.log X) (-(n : ℝ)) =
      Real.rpow (Real.log X) ((m : ℝ) + -(n : ℝ)) :=
        (Real.rpow_add hlogpos _ _).symm
    _ ≤ Real.rpow (Real.log X) (-A) := by
      apply Real.rpow_le_rpow_of_exponent_le hlog
      linarith

/-- Eventual trade of an arbitrary real polylog power for `X^eta`. -/
theorem eventually_log_pow_le_rpow_mul_negative
    (A : ℝ) (n : ℕ) {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ X : ℝ in atTop,
      (Real.log X) ^ n ≤
        Real.rpow X eta * Real.rpow (Real.log X) (-A) := by
  have hpoly := SupportBoundaryQuantitative.polylog_absorption
    (A + n) eta heta
  filter_upwards [hpoly, eventually_ge_atTop (Real.exp 1)] with X hpoly hX
  have hXpos : 0 < X := (Real.exp_pos 1).trans_le hX
  have hlog : 1 ≤ Real.log X :=
    (Real.le_log_iff_exp_le hXpos).2 hX
  have hlogpos : 0 < Real.log X := zero_lt_one.trans_le hlog
  have hneg : 0 ≤ Real.rpow (Real.log X) (-A) :=
    Real.rpow_nonneg hlogpos.le _
  have hmul := mul_le_mul_of_nonneg_right hpoly hneg
  calc
    (Real.log X) ^ n = Real.rpow (Real.log X) (n : ℝ) :=
      log_pow_eq_rpow n
    _ = Real.rpow (Real.log X) ((A + n) + (-A)) := by
      congr 1
      ring
    _ = Real.rpow (Real.log X) (A + n) *
          Real.rpow (Real.log X) (-A) :=
      Real.rpow_add hlogpos _ _
    _ ≤ Real.rpow X eta * Real.rpow (Real.log X) (-A) := hmul

/-- The manuscript's omitted scale check: with `epsilon_AP=rho/2`, its
`y=H_*/(32R)` is eventually a legal Proposition 2.2 aperture. -/
theorem eventually_aperture_legal (epsilon : ℝ) (Cc : ℕ)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ X : ℝ in atTop,
      Real.rpow X (2 / 15 + apReserve epsilon) ≤
        gallagherWindow epsilon X Cc := by
  let rho := apertureReserve epsilon
  have hrho : 0 < rho := apertureReserve_pos hepsilon
  have hpoly := SupportBoundaryQuantitative.polylog_absorption
    (Cc + 6 : ℝ) (rho / 2) (div_pos hrho (by norm_num))
  filter_upwards [hpoly, eventually_ge_atTop (Real.exp 2)] with X hpoly hX
  have hXpos : 0 < X := (Real.exp_pos 2).trans_le hX
  have hlog2 : 2 ≤ Real.log X :=
    (Real.le_log_iff_exp_le hXpos).2 hX
  have hlogpos : 0 < Real.log X := by linarith
  have h64 : (64 : ℝ) ≤ (Real.log X) ^ 6 := by
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hlog2 6]
  have hRnonneg : 0 ≤ collarR X Cc := by
    unfold collarR
    positivity
  have h64R : 64 * collarR X Cc ≤
      Real.rpow (Real.log X) (Cc + 6 : ℝ) := by
    calc
      64 * collarR X Cc ≤ (Real.log X) ^ 6 * (Real.log X) ^ Cc := by
        unfold collarR
        gcongr
      _ = (Real.log X) ^ (Cc + 6) := by
        rw [← pow_add]
        congr 1
        omega
      _ = Real.rpow (Real.log X) (Cc + 6 : ℝ) := by
        rw [show (Cc : ℝ) + 6 = ((Cc + 6 : ℕ) : ℝ) by norm_num]
        exact (Real.rpow_natCast (Real.log X) (Cc + 6)).symm
  have hden : 0 < 32 * collarR X Cc := by
    unfold collarR
    positivity
  have hscale : 64 * collarR X Cc ≤ Real.rpow X (rho / 2) :=
    h64R.trans hpoly
  unfold gallagherWindow baseAperture apReserve
  change Real.rpow X (2 / 15 + rho / 2) ≤
    ((1 / 2) * Real.rpow X (2 / 15 + rho)) /
      (32 * collarR X Cc)
  apply (le_div_iff₀ hden).2
  have hpowpos : 0 < Real.rpow X (2 / 15 + rho / 2) :=
    Real.rpow_pos_of_pos hXpos _
  have hmul := mul_le_mul_of_nonneg_left hscale hpowpos.le
  calc
    Real.rpow X (2 / 15 + rho / 2) * (32 * collarR X Cc) ≤
        Real.rpow X (2 / 15 + rho / 2) *
          ((1 / 2) * Real.rpow X (rho / 2)) := by
      nlinarith
    _ = (1 / 2) * Real.rpow X (2 / 15 + rho) := by
      calc
        Real.rpow X (2 / 15 + rho / 2) *
            ((1 / 2) * Real.rpow X (rho / 2)) =
          (1 / 2) *
            (Real.rpow X (2 / 15 + rho / 2) *
              Real.rpow X (rho / 2)) := by ring
        _ = (1 / 2) *
            Real.rpow X ((2 / 15 + rho / 2) + rho / 2) := by
          congr 1
          exact (Real.rpow_add hXpos _ _).symm
        _ = (1 / 2) * Real.rpow X (2 / 15 + rho) := by
          congr 2
          ring

theorem apertureReserve_le_small (epsilon : ℝ) :
    apertureReserve epsilon ≤ 1 / 1200 := by
  exact min_le_right _ _

/-- The Gallagher window is positive at every positive arithmetic scale. -/
theorem gallagherWindow_pos
    {epsilon X : ℝ} (Cc : ℕ) (hX : 0 < X)
    (hlog : 0 < Real.log X) :
    0 < gallagherWindow epsilon X Cc := by
  unfold gallagherWindow collarR
  have hbase := baseAperture_pos (ε := epsilon) hX
  have hpow : 0 < (Real.log X) ^ Cc := pow_pos hlog Cc
  exact div_pos hbase (mul_pos (by norm_num) hpow)

/-- Exact normalization behind the collar choice:
`4R/H_* = 1/(8y)`.  This rules out a hidden factor-of-two ambiguity in the
real-line Gallagher radius. -/
theorem outerRadius_eq_inv_eight_window
    {epsilon X : ℝ} (Cc : ℕ) (hX : 0 < X)
    (hlog : 0 < Real.log X) :
    4 * collarR X Cc / baseAperture epsilon X =
      1 / (8 * gallagherWindow epsilon X Cc) := by
  have hbase : 0 < baseAperture epsilon X := baseAperture_pos hX
  have hR : 0 < collarR X Cc := by
    unfold collarR
    exact pow_pos hlog Cc
  unfold gallagherWindow
  field_simp
  ring

/-- A rough but sufficient upper bound used in both middle-term absorption and
the continuous-tail scale check. -/
theorem gallagherWindow_le_sqrt
    {epsilon X : ℝ} (Cc : ℕ) (hX : 1 ≤ X)
    (hlog : 1 ≤ Real.log X) :
    gallagherWindow epsilon X Cc ≤ Real.rpow X (1 / 2) := by
  have hXpos : 0 < X := zero_lt_one.trans_le hX
  have hR : 1 ≤ collarR X Cc := by
    unfold collarR
    exact one_le_pow₀ hlog
  have hden : 32 ≤ 32 * collarR X Cc := by nlinarith
  have hexp : 2 / 15 + apertureReserve epsilon ≤ 1 / 2 := by
    have hrho := apertureReserve_le_small epsilon
    linarith
  have hrpow :
      Real.rpow X (2 / 15 + apertureReserve epsilon) ≤
        Real.rpow X (1 / 2) :=
    Real.rpow_le_rpow_of_exponent_le hX hexp
  have hsqnonneg : 0 ≤ Real.rpow X (1 / 2) := Real.rpow_nonneg hXpos.le _
  unfold gallagherWindow baseAperture
  calc
    (1 / 2) * Real.rpow X (2 / 15 + apertureReserve epsilon) /
        (32 * collarR X Cc) ≤
      (1 / 2) * Real.rpow X (2 / 15 + apertureReserve epsilon) := by
        apply div_le_self
        · exact mul_nonneg (by norm_num) (Real.rpow_nonneg hXpos.le _)
        · linarith
    _ ≤ (1 / 2) * Real.rpow X (1 / 2) := by gcongr
    _ ≤ Real.rpow X (1 / 2) := by nlinarith

/-- The main-term tail starts inside the Gallagher collar for the manuscript's
polylogarithmic `P`, eventually and uniformly for fixed cutoffs. -/
theorem eventually_tail_scale
    (epsilon : ℝ) (D Cc : ℕ) :
    ∀ᶠ X : ℝ in atTop,
      collarP X D / X ≤ 1 / (8 * gallagherWindow epsilon X Cc) := by
  have hpoly := SupportBoundaryQuantitative.polylog_absorption
    (D + 3 : ℝ) (1 / 2) (by norm_num)
  filter_upwards [hpoly, eventually_ge_atTop (Real.exp 2)] with X hpoly hX
  have hXpos : 0 < X := (Real.exp_pos 2).trans_le hX
  have hXone : 1 ≤ X := by
    have he : Real.exp 0 ≤ Real.exp 2 := Real.exp_le_exp.mpr (by norm_num)
    simpa using he.trans hX
  have hlog2 : 2 ≤ Real.log X :=
    (Real.le_log_iff_exp_le hXpos).2 hX
  have hlog1 : 1 ≤ Real.log X := one_le_two.trans hlog2
  have hypos : 0 < gallagherWindow epsilon X Cc :=
    gallagherWindow_pos Cc hXpos (zero_lt_one.trans_le hlog1)
  have hy : gallagherWindow epsilon X Cc ≤ Real.rpow X (1 / 2) :=
    gallagherWindow_le_sqrt Cc hXone hlog1
  have h8 : (8 : ℝ) ≤ (Real.log X) ^ 3 := by
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hlog2 3]
  have hPnonneg : 0 ≤ collarP X D := by unfold collarP; positivity
  have h8P : 8 * collarP X D ≤
      Real.rpow (Real.log X) (D + 3 : ℝ) := by
    calc
      8 * collarP X D ≤ (Real.log X) ^ 3 * (Real.log X) ^ D := by
        unfold collarP
        gcongr
      _ = (Real.log X) ^ (D + 3) := by
        rw [← pow_add]
        congr 1
        omega
      _ = Real.rpow (Real.log X) (D + 3 : ℝ) := by
        rw [show (D : ℝ) + 3 = ((D + 3 : ℕ) : ℝ) by norm_num]
        exact (Real.rpow_natCast (Real.log X) (D + 3)).symm
  have h8Ppow : 8 * collarP X D ≤ Real.rpow X (1 / 2) :=
    h8P.trans hpoly
  have hsquare : Real.rpow X (1 / 2) * Real.rpow X (1 / 2) = X := by
    calc
      Real.rpow X (1 / 2) * Real.rpow X (1 / 2) =
          Real.rpow X ((1 / 2 : ℝ) + 1 / 2) :=
        (Real.rpow_add hXpos _ _).symm
      _ = X := by norm_num
  have hsqrtnonneg : 0 ≤ Real.rpow X (1 / 2) :=
    Real.rpow_nonneg hXpos.le _
  apply (div_le_div_iff₀ hXpos (mul_pos (by norm_num) hypos)).2
  calc
    collarP X D * (8 * gallagherWindow epsilon X Cc) =
        (8 * collarP X D) * gallagherWindow epsilon X Cc := by ring
    _ ≤ Real.rpow X (1 / 2) * Real.rpow X (1 / 2) := by
      exact mul_le_mul h8Ppow hy (by positivity) hsqrtnonneg
    _ = X := hsquare
    _ = 1 * X := by ring

/-- A legal AP window is automatically between `1` and `X/2` after enlarging
the base point. -/
theorem eventually_window_range (epsilon : ℝ) (Cc : ℕ)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ X : ℝ in atTop,
      1 ≤ gallagherWindow epsilon X Cc ∧
      gallagherWindow epsilon X Cc ≤ X / 2 := by
  have hlegal := eventually_aperture_legal epsilon Cc hepsilon
  filter_upwards [hlegal, eventually_ge_atTop (Real.exp 2),
      eventually_ge_atTop (4 : ℝ)] with X hlegal hX hX4
  have hXpos : 0 < X := (Real.exp_pos 2).trans_le hX
  have hXone : 1 ≤ X := by linarith
  have hlog2 : 2 ≤ Real.log X :=
    (Real.le_log_iff_exp_le hXpos).2 hX
  have hlowexp : 0 ≤ 2 / 15 + apReserve epsilon := by
    have := apReserve_pos hepsilon
    linarith
  have hone : 1 ≤ Real.rpow X (2 / 15 + apReserve epsilon) :=
    Real.one_le_rpow hXone hlowexp
  have hyhalf := gallagherWindow_le_sqrt (epsilon := epsilon) Cc hXone
    (one_le_two.trans hlog2)
  have hsqrtX : Real.rpow X (1 / 2) ≤ X / 2 := by
    have hsquare : Real.rpow X (1 / 2) ^ 2 = X := by
      calc
        Real.rpow X (1 / 2) ^ 2 =
            Real.rpow X (1 / 2) * Real.rpow X (1 / 2) := by ring
        _ = Real.rpow X ((1 / 2 : ℝ) + 1 / 2) :=
          (Real.rpow_add hXpos _ _).symm
        _ = X := by norm_num
    have hsqrtnonneg : 0 ≤ Real.rpow X (1 / 2) := Real.rpow_nonneg hXpos.le _
    nlinarith
  exact ⟨hone.trans hlegal, hyhalf.trans hsqrtX⟩

/-- Cutoff-selectable form of the near branch.  This is the form needed to use
exactly the same `B,D,Cc` later in the far branch. -/
def SelectableCanonicalNearCollarEstimate : Prop :=
  ∀ (A epsilon : ℝ) (B D Cc : ℕ),
    0 < A → 0 < epsilon → 1 ≤ B → A + 2 * B ≤ D →
    ∃ C X₀ : ℝ, 0 < C ∧ 2 ≤ X₀ ∧
      ∀ X : ℝ, X₀ ≤ X →
        1 ≤ Real.log X ∧
        (∫ alpha in outerRationalCollars epsilon X B Cc ∩
              minorArcs X B D,
            ‖primeExponentialSum X alpha‖ ^ 2
              ∂AddCircle.haarAddCircle) ≤
          C * X * Real.rpow (Real.log X) (-A)

/-- Everything from Proposition 2.2 through logarithmic absorption, conditional
only on the one named Gallagher transfer leaf. -/
theorem selectableCanonicalNearCollarEstimate_of_gallagher_ap
    (hGallagher : NearCollarGallagherTransfer)
    (hAP : APFoundation.SimultaneousShortIntervalAP) :
    SelectableCanonicalNearCollarEstimate := by
  intro A epsilon B D Cc hA hepsilon hB hD
  let DAP : ℕ := ⌈A⌉₊ + 4 * B + 10
  have hBpos : 0 < (B : ℝ) := by exact_mod_cast hB
  have hDAPpos : 0 < (DAP : ℝ) := by
    dsimp [DAP]
    positivity
  have hepsAP : 0 < apReserve epsilon := apReserve_pos hepsilon
  obtain ⟨Cap, Xap, hCap, hXap, hap⟩ :=
    hAP (B : ℝ) (DAP : ℝ) (apReserve epsilon)
      hBpos hDAPpos hepsAP (apReserve_le_cap epsilon)
  obtain ⟨Cg, Xg, hCg, hXg, hg⟩ := hGallagher
  have hlegal := eventually_aperture_legal epsilon Cc hepsilon
  have hrange := eventually_window_range epsilon Cc hepsilon
  have htail := eventually_tail_scale epsilon D Cc
  have hterm2 := eventually_log_pow_le_rpow_mul_negative
    A (2 * B + 2) (eta := 1 / 2) (by norm_num)
  have hterm3 := eventually_log_pow_le_rpow_mul_negative
    A (2 * B + 4) (eta := 1) (by norm_num)
  have hall : ∀ᶠ X : ℝ in atTop,
      2 ≤ Real.log X ∧
      Real.rpow X (2 / 15 + apReserve epsilon) ≤
        gallagherWindow epsilon X Cc ∧
      (1 ≤ gallagherWindow epsilon X Cc ∧
        gallagherWindow epsilon X Cc ≤ X / 2) ∧
      collarP X D / X ≤ 1 / (8 * gallagherWindow epsilon X Cc) ∧
      (Real.log X) ^ (2 * B + 2) ≤
        Real.rpow X (1 / 2) * Real.rpow (Real.log X) (-A) ∧
      (Real.log X) ^ (2 * B + 4) ≤
        Real.rpow X 1 * Real.rpow (Real.log X) (-A) := by
    filter_upwards [eventually_ge_atTop (Real.exp 2), hlegal, hrange,
        htail, hterm2, hterm3] with X hX hlegalX hrangeX htailX ht2 ht3
    have hXpos : 0 < X := (Real.exp_pos 2).trans_le hX
    have hlog2 : 2 ≤ Real.log X :=
      (Real.le_log_iff_exp_le hXpos).2 hX
    exact ⟨hlog2, hlegalX, hrangeX, htailX, ht2, ht3⟩
  obtain ⟨Xs, hXs⟩ := eventually_atTop.mp hall
  let C : ℝ := Cg * (Cap + 3)
  let X₀ : ℝ := max (max (max Xap Xg) Xs) 2
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hX₀ : 2 ≤ X₀ := le_max_right _ _
  refine ⟨C, X₀, hC, hX₀, ?_⟩
  intro X hXX₀
  have hXXap : Xap ≤ X :=
    (le_max_left Xap Xg).trans
      ((le_max_left (max Xap Xg) Xs).trans
        ((le_max_left (max (max Xap Xg) Xs) 2).trans hXX₀))
  have hXXg : Xg ≤ X :=
    (le_max_right Xap Xg).trans
      ((le_max_left (max Xap Xg) Xs).trans
        ((le_max_left (max (max Xap Xg) Xs) 2).trans hXX₀))
  have hXXs : Xs ≤ X :=
    (le_max_right (max Xap Xg) Xs).trans
      ((le_max_left (max (max Xap Xg) Xs) 2).trans hXX₀)
  obtain ⟨hlog2, hlegalX, ⟨hyone, hyhalfX⟩, htailX, ht2, ht3⟩ :=
    hXs X hXXs
  have hlog1 : 1 ≤ Real.log X := one_le_two.trans hlog2
  have hlogpos : 0 < Real.log X := zero_lt_one.trans_le hlog1
  have hXtwo : 2 ≤ X := hX₀.trans hXX₀
  have hXpos : 0 < X := by
    linarith
  have hAPenn : apMaxIntegral B (apReserve epsilon) X ≤
      ENNReal.ofReal
        (Cap * X * Real.rpow (Real.log X) (-(DAP : ℝ))) := by
    simpa [apMaxIntegral] using hap X hXXap
  have hAPreal : (apMaxIntegral B (apReserve epsilon) X).toReal ≤
      Cap * X * Real.rpow (Real.log X) (-(DAP : ℝ)) := by
    have hmono := ENNReal.toReal_mono ENNReal.ofReal_ne_top hAPenn
    rw [ENNReal.toReal_ofReal] at hmono
    · exact hmono
    · exact mul_nonneg (mul_nonneg hCap.le hXpos.le)
        (Real.rpow_nonneg hlogpos.le _)
  have hDAPexp : A + (4 * B : ℕ) ≤ (DAP : ℝ) := by
    dsimp [DAP]
    have hceil : A ≤ (⌈A⌉₊ : ℝ) := Nat.le_ceil A
    norm_num at hceil ⊢
    linarith
  have hfirstLog := log_pow_mul_negative_rpow_le
    (X := X) (A := A) (m := 4 * B) (n := DAP) hlog1 hDAPexp
  have hD' : A + (2 * B : ℕ) ≤ (D : ℝ) := by
    convert hD using 1 <;> norm_num
  have hfourthLog := log_pow_mul_negative_rpow_le
    (X := X) (A := A) (m := 2 * B) (n := D) hlog1 hD'
  have hQnonneg : 0 ≤ collarQ X B := by unfold collarQ; positivity
  have hPpos : 0 < collarP X D := by unfold collarP; positivity
  have hypos : 0 < gallagherWindow epsilon X Cc :=
    gallagherWindow_pos Cc hXpos hlogpos
  have hsqrtnonneg : 0 ≤ Real.rpow X (1 / 2) :=
    Real.rpow_nonneg hXpos.le _
  have hysqrt : gallagherWindow epsilon X Cc ≤ Real.rpow X (1 / 2) :=
    gallagherWindow_le_sqrt (epsilon := epsilon) Cc
      (by linarith) hlog1
  have hsquare : Real.rpow X (1 / 2) * Real.rpow X (1 / 2) = X := by
    calc
      Real.rpow X (1 / 2) * Real.rpow X (1 / 2) =
          Real.rpow X ((1 / 2 : ℝ) + 1 / 2) :=
        (Real.rpow_add hXpos _ _).symm
      _ = X := by norm_num
  let target := X * Real.rpow (Real.log X) (-A)
  have htarget : 0 ≤ target := by dsimp [target]; positivity
  have hterm1 :
      collarQ X B ^ 4 * (apMaxIntegral B (apReserve epsilon) X).toReal ≤
        Cap * target := by
    calc
      collarQ X B ^ 4 * (apMaxIntegral B (apReserve epsilon) X).toReal ≤
          collarQ X B ^ 4 *
            (Cap * X * Real.rpow (Real.log X) (-(DAP : ℝ))) := by
        gcongr
      _ = (Cap * X) *
          ((Real.log X) ^ (4 * B) *
            Real.rpow (Real.log X) (-(DAP : ℝ))) := by
        unfold collarQ
        rw [← pow_mul]
        ring
      _ ≤ (Cap * X) * Real.rpow (Real.log X) (-A) := by
        gcongr
      _ = Cap * target := by simp [target]; ring
  have hterm2bound :
      collarQ X B ^ 2 * gallagherWindow epsilon X Cc *
          (Real.log X) ^ 2 ≤ target := by
    calc
      collarQ X B ^ 2 * gallagherWindow epsilon X Cc *
          (Real.log X) ^ 2 =
        gallagherWindow epsilon X Cc * (Real.log X) ^ (2 * B + 2) := by
          unfold collarQ
          calc
            ((Real.log X) ^ B) ^ 2 * gallagherWindow epsilon X Cc *
                (Real.log X) ^ 2 =
              gallagherWindow epsilon X Cc *
                ((Real.log X) ^ (B * 2) * (Real.log X) ^ 2) := by
                  rw [pow_mul]
                  ring
            _ = gallagherWindow epsilon X Cc *
                (Real.log X) ^ (B * 2 + 2) := by
                  rw [pow_add]
            _ = gallagherWindow epsilon X Cc *
                (Real.log X) ^ (2 * B + 2) := by
                  congr 2
                  omega
      _ ≤ Real.rpow X (1 / 2) *
          (Real.rpow X (1 / 2) * Real.rpow (Real.log X) (-A)) := by
        exact mul_le_mul hysqrt ht2 (by positivity) hsqrtnonneg
      _ = target := by rw [← mul_assoc, hsquare]
  have hterm3bound :
      collarQ X B ^ 2 * (Real.log X) ^ 4 /
          gallagherWindow epsilon X Cc ≤ target := by
    have hnum : 0 ≤ collarQ X B ^ 2 * (Real.log X) ^ 4 := by positivity
    calc
      collarQ X B ^ 2 * (Real.log X) ^ 4 /
          gallagherWindow epsilon X Cc ≤
        collarQ X B ^ 2 * (Real.log X) ^ 4 :=
          div_le_self hnum hyone
      _ = (Real.log X) ^ (2 * B + 4) := by
        unfold collarQ
        calc
          ((Real.log X) ^ B) ^ 2 * (Real.log X) ^ 4 =
              (Real.log X) ^ (B * 2) * (Real.log X) ^ 4 := by
                rw [pow_mul]
          _ = (Real.log X) ^ (B * 2 + 4) := by rw [pow_add]
          _ = (Real.log X) ^ (2 * B + 4) := by congr 1 <;> omega
      _ ≤ Real.rpow X 1 * Real.rpow (Real.log X) (-A) := ht3
      _ = target := by simp [target]
  have hterm4bound : X * collarQ X B ^ 2 / collarP X D ≤ target := by
    have hlogBound :
        (Real.log X) ^ (2 * B) / (Real.log X) ^ D ≤
          Real.rpow (Real.log X) (-A) := by
      rw [div_eq_mul_inv]
      have hinv : ((Real.log X) ^ D)⁻¹ =
          Real.rpow (Real.log X) (-(D : ℝ)) := by
        calc
          ((Real.log X) ^ D)⁻¹ =
              (Real.rpow (Real.log X) (D : ℝ))⁻¹ := by
                exact congrArg Inv.inv
                  (Real.rpow_natCast (Real.log X) D).symm
          _ = Real.rpow (Real.log X) (-(D : ℝ)) :=
            (Real.rpow_neg hlogpos.le _).symm
      rw [hinv]
      exact hfourthLog
    calc
      X * collarQ X B ^ 2 / collarP X D =
          X * ((Real.log X) ^ (2 * B) / (Real.log X) ^ D) := by
        unfold collarQ collarP
        rw [← pow_mul]
        ring
      _ ≤ X * Real.rpow (Real.log X) (-A) := by gcongr
      _ = target := rfl
  have hfour :
      nearFourTermRHS B D Cc epsilon (apReserve epsilon) X ≤
        (Cap + 3) * target := by
    unfold nearFourTermRHS
    dsimp only
    nlinarith
  refine ⟨hlog1, ?_⟩
  calc
    (∫ alpha in outerRationalCollars epsilon X B Cc ∩ minorArcs X B D,
        ‖primeExponentialSum X alpha‖ ^ 2
          ∂AddCircle.haarAddCircle) ≤
      Cg * nearFourTermRHS B D Cc epsilon (apReserve epsilon) X :=
        hg epsilon (apReserve epsilon) X B D Cc hepsilon hepsAP hXXg
          hlog2 hlegalX hyone hyhalfX htailX
    _ ≤ Cg * ((Cap + 3) * target) := by gcongr
    _ = C * X * Real.rpow (Real.log X) (-A) := by
      simp only [C, target]
      ring

/-- Existential cutoff form matching the standalone near proposition. -/
theorem canonicalNearCollarEstimate_of_gallagher_ap
    (hGallagher : NearCollarGallagherTransfer)
    (hAP : APFoundation.SimultaneousShortIntervalAP) :
    CanonicalNearCollarEstimate := by
  have hselect := selectableCanonicalNearCollarEstimate_of_gallagher_ap
    hGallagher hAP
  intro A epsilon hA hepsilon
  let B : ℕ := ⌈A⌉₊ + 1
  let D : ℕ := ⌈A⌉₊ + 2 * B + 10
  let Cc : ℕ := ⌈A⌉₊ + 2 * B + 30
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hD : A + 2 * B ≤ (D : ℝ) := by
    have hceil : A ≤ (⌈A⌉₊ : ℝ) := Nat.le_ceil A
    dsimp [D]
    norm_num at hceil ⊢
    linarith
  obtain ⟨C, X₀, hC, hX₀, hbound⟩ :=
    hselect A epsilon B D Cc hA hepsilon hB hD
  exact ⟨B, D, Cc, C, X₀, hC, hX₀, hbound⟩

end
end MAPNearCollarGallagher

#print axioms MAPNearCollarGallagher.selectableCanonicalNearCollarEstimate_of_gallagher_ap
#print axioms MAPNearCollarGallagher.canonicalNearCollarEstimate_of_gallagher_ap
