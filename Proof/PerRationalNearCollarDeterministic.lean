import NearCollarGallagherFiniteUnion
import SignedGallagherCore
import APMaximalExplicitFormulaBridge
import MajorArcPublicLiftBridge
import PointwiseAbelWeld
import SiegelWalfiszToPointwise
import BadEulerFactorMass

/-!
# Deterministic per-rational near-collar reductions

This staging module proves the literal residue-class and dyadic-support
identities needed between the signed Gallagher inequality and the AP maximal
integral.  It introduces no source proposition.
-/

namespace MAPNearCollarGallagher

open AddCircle MeasureTheory Metric Set
open scoped BigOperators ENNReal ArithmeticFunction
noncomputable section

open APFoundation PrimePairEndpoints MAPHarmonicEndpoint
open MAPAllCenterApertureTransfer MAPAllCenterNearFarTransfer
open MAPMajorArcWeld MAPPointwiseMajorArc
open MAPSiegelWalfiszToPointwise
open MAPAPZeroDensityCert

/-- The additive-character interval discrepancy before dyadic truncation. -/
def rationalIntervalError (q a : ℕ) (x y : ℝ) : ℂ :=
  rationalContinuousPrefixError q a (x + y) -
    rationalContinuousPrefixError q a x

/-- The non-coprime residue contribution in one interval. -/
def badResidueWindowMass (q : ℕ) (x y : ℝ) : ℝ :=
  ∑ r ∈ (Finset.range q).filter (fun r => ¬ r.Coprime q),
    |progressionPsi (x + y) q r - progressionPsi x q r|

theorem badResidueWindowMass_nonneg (q : ℕ) (x y : ℝ) :
    0 ≤ badResidueWindowMass q x y := by
  unfold badResidueWindowMass
  positivity

/-- Exact interval residue decomposition. -/
theorem norm_rationalIntervalError_le_of_progression
    {q a : ℕ} {x y W : ℝ}
    (hq : 1 ≤ q) (ha : a.Coprime q) (hW : 0 ≤ W)
    (hprogression : ∀ r : ℕ, r < q → r.Coprime q →
      |(progressionPsi (x + y) q r - progressionPsi x q r) -
          y / (q.totient : ℝ)| ≤ W) :
    ‖rationalIntervalError q a x y‖ ≤
      (q : ℝ) * W + badResidueWindowMass q x y := by
  classical
  let good := (Finset.range q).filter (fun r => r.Coprime q)
  let bad := (Finset.range q).filter (fun r => ¬ r.Coprime q)
  let phase : ℕ → ℂ := fun r => fourier (r : ℤ) (rationalCenter q a)
  let psiWin : ℕ → ℂ := fun r =>
    ((progressionPsi (x + y) q r - progressionPsi x q r : ℝ) : ℂ)
  let mainC : ℂ := ((y / (q.totient : ℝ) : ℝ) : ℂ)
  have hphase : (∑ r ∈ good, phase r) =
      ((ArithmeticFunction.moebius q : ℤ) : ℂ) := by
    simpa only [good, phase] using
      sum_coprime_rational_phase_eq_moebius hq ha
  have hmain : (∑ r ∈ good, phase r * mainC) =
      primeMajorCoefficient q * (y : ℂ) := by
    calc
      (∑ r ∈ good, phase r * mainC) =
          (∑ r ∈ good, phase r) * mainC := by rw [Finset.sum_mul]
      _ = ((ArithmeticFunction.moebius q : ℤ) : ℂ) * mainC := by rw [hphase]
      _ = primeMajorCoefficient q * (y : ℂ) := by
        unfold primeMajorCoefficient mainC
        push_cast
        ring
  have hgoodExact :
      (∑ r ∈ good, phase r * psiWin r) -
          primeMajorCoefficient q * (y : ℂ) =
        ∑ r ∈ good, phase r * (psiWin r - mainC) := by
    rw [← hmain, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    ring
  have hgoodNorm :
      ‖(∑ r ∈ good, phase r * psiWin r) -
          primeMajorCoefficient q * (y : ℂ)‖ ≤ (q : ℝ) * W := by
    rw [hgoodExact]
    calc
      ‖∑ r ∈ good, phase r * (psiWin r - mainC)‖ ≤
          ∑ r ∈ good, ‖phase r * (psiWin r - mainC)‖ := norm_sum_le _ _
      _ ≤ ∑ _r ∈ good, W := by
        apply Finset.sum_le_sum
        intro r hr
        have hr' := Finset.mem_filter.mp hr
        rw [norm_mul]
        have hphaseNorm : ‖phase r‖ = 1 := by
          simp only [phase, fourier_apply, Circle.norm_coe]
        rw [hphaseNorm, one_mul]
        have hcast : psiWin r - mainC =
            (((progressionPsi (x + y) q r - progressionPsi x q r) -
              y / (q.totient : ℝ) : ℝ) : ℂ) := by
          simp only [psiWin, mainC, Complex.ofReal_sub]
        rw [hcast, Complex.norm_real, Real.norm_eq_abs]
        exact hprogression r (Finset.mem_range.mp hr'.1) hr'.2
      _ = (good.card : ℝ) * W := by simp
      _ ≤ (q : ℝ) * W := by
        apply mul_le_mul_of_nonneg_right _ hW
        exact_mod_cast (show good.card ≤ q by
          calc
            good.card ≤ (Finset.range q).card := by
              dsimp [good]
              exact Finset.card_filter_le _ _
            _ = q := Finset.card_range q)
  have hbadNorm : ‖∑ r ∈ bad, phase r * psiWin r‖ ≤
      badResidueWindowMass q x y := by
    calc
      ‖∑ r ∈ bad, phase r * psiWin r‖ ≤
          ∑ r ∈ bad, ‖phase r * psiWin r‖ := norm_sum_le _ _
      _ = ∑ r ∈ bad,
          |progressionPsi (x + y) q r - progressionPsi x q r| := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [norm_mul]
        simp only [phase, fourier_apply, Circle.norm_coe, one_mul,
          psiWin, Complex.norm_real, Real.norm_eq_abs]
      _ = badResidueWindowMass q x y := by rfl
  have hraw (t : ℝ) :
      (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, rationalRawCoefficient q a n) =
        ∑ r ∈ Finset.range q,
          phase r * (progressionPsi t q r : ℂ) := by
    simpa only [phase] using
      sum_rationalRawCoefficient_eq_sum_progressionPsi hq a t
  have hsplit :
      (∑ r ∈ Finset.range q, phase r * psiWin r) =
        (∑ r ∈ good, phase r * psiWin r) +
          ∑ r ∈ bad, phase r * psiWin r := by
    dsimp [good, bad]
    exact (Finset.sum_filter_add_sum_filter_not
      (Finset.range q) (fun r => r.Coprime q)
      (fun r => phase r * psiWin r)).symm
  unfold rationalIntervalError rationalContinuousPrefixError
  rw [hraw (x + y), hraw x]
  have hsumdiff :
      (∑ r ∈ Finset.range q, phase r * (progressionPsi (x + y) q r : ℂ)) -
          ∑ r ∈ Finset.range q, phase r * (progressionPsi x q r : ℂ) =
        ∑ r ∈ Finset.range q, phase r * psiWin r := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    dsimp [psiWin]
    push_cast
    ring
  have herr :
      (∑ r ∈ Finset.range q,
          phase r * (progressionPsi (x + y) q r : ℂ)) -
          primeMajorCoefficient q * ((x + y : ℝ) : ℂ) -
        ((∑ r ∈ Finset.range q,
            phase r * (progressionPsi x q r : ℂ)) -
          primeMajorCoefficient q * (x : ℂ)) =
      (∑ r ∈ Finset.range q, phase r * psiWin r) -
          primeMajorCoefficient q * (y : ℂ) := by
    calc
      _ = ((∑ r ∈ Finset.range q,
            phase r * (progressionPsi (x + y) q r : ℂ)) -
          ∑ r ∈ Finset.range q,
            phase r * (progressionPsi x q r : ℂ)) -
          primeMajorCoefficient q * (y : ℂ) := by
            push_cast
            ring
      _ = _ := by rw [hsumdiff]
  rw [herr, hsplit]
  have hreassoc2 :
      (∑ r ∈ good, phase r * psiWin r) +
          (∑ r ∈ bad, phase r * psiWin r) -
            primeMajorCoefficient q * (y : ℂ) =
        ((∑ r ∈ good, phase r * psiWin r) -
            primeMajorCoefficient q * (y : ℂ)) +
          ∑ r ∈ bad, phase r * psiWin r := by ring
  rw [hreassoc2]
  exact (norm_add_le _ _).trans (add_le_add hgoodNorm hbadNorm)

theorem progression_interval_error_eq_mul_normalizedAPError
    {x y : ℝ} {q r : ℕ} (hy : 0 < y) :
    (progressionPsi (x + y) q r - progressionPsi x q r) -
        y / (q.totient : ℝ) =
      y * normalizedAPError x y q r := by
  unfold normalizedAPError
  field_simp

theorem norm_rationalIntervalError_le_of_normalizedAP
    {q a : ℕ} {x y G : ℝ}
    (hq : 1 ≤ q) (ha : a.Coprime q) (hy : 0 < y) (hG : 0 ≤ G)
    (hAP : ∀ r : ℕ, r < q → r.Coprime q →
      |normalizedAPError x y q r| ≤ G) :
    ‖rationalIntervalError q a x y‖ ≤
      (q : ℝ) * (y * G) + badResidueWindowMass q x y := by
  apply norm_rationalIntervalError_le_of_progression hq ha
    (mul_nonneg hy.le hG)
  intro r hr hcop
  rw [progression_interval_error_eq_mul_normalizedAPError hy, abs_mul,
    abs_of_pos hy]
  exact mul_le_mul_of_nonneg_left (hAP r hr hcop) hy.le

/-- On an interior interval the dyadic support truncation is inactive. -/
theorem twistedPrimeSlidingWindow_eq_raw_interval
    {X x y : ℝ} {q a : ℕ}
    (hX : 0 < X) (hx : X ≤ x) (hy : 0 ≤ y)
    (hxy : x + y ≤ 2 * X) :
    twistedPrimeSlidingWindow X q a x y =
      ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊,
        rationalRawCoefficient q a n := by
  classical
  have hx0 : 0 ≤ x := hX.le.trans hx
  have hxy0 : 0 ≤ x + y := by linarith
  have h2X0 : 0 ≤ 2 * X := by linarith
  have hfloorXx : ⌊X⌋₊ ≤ ⌊x⌋₊ := Nat.floor_mono hx
  have hfloorxy2X : ⌊x + y⌋₊ ≤ ⌊2 * X⌋₊ := Nat.floor_mono hxy
  have hset :
      ((Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊).filter
          (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ x + y) : Finset ℕ) =
        Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊ := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · intro hn
      constructor
      · exact (Nat.floor_lt hx0).mpr hn.2.1
      · exact Nat.le_floor hn.2.2
    · intro hn
      have hxn : x < (n : ℝ) := (Nat.floor_lt hx0).mp hn.1
      have hnxy : (n : ℝ) ≤ x + y :=
        (show (n : ℝ) ≤ (⌊x + y⌋₊ : ℝ) by exact_mod_cast hn.2).trans
          (Nat.floor_le hxy0)
      exact ⟨⟨hfloorXx.trans_lt hn.1,
        hn.2.trans hfloorxy2X⟩, hxn, hnxy⟩
  unfold twistedPrimeSlidingWindow
  rw [← Finset.sum_filter]
  change (∑ n ∈ (Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊).filter
      (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ x + y),
        (ArithmeticFunction.vonMangoldt n : ℂ) *
          fourier (n : ℤ) (rationalCenter q a)) = _
  rw [hset]
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := by
    have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le ⌊x⌋₊)
      (Finset.mem_Ioc.mp hn).1
    omega
  rw [rationalRawCoefficient, if_neg hn0]

theorem dyadicContinuousWindowLength_eq_window
    {X x y : ℝ} (hx : X ≤ x) (hy : 0 ≤ y)
    (hxy : x + y ≤ 2 * X) :
    dyadicContinuousWindowLength X x y = y := by
  unfold dyadicContinuousWindowLength
  rw [min_eq_right hxy, max_eq_right hx]
  simp [hy]

/-- Exact interior identity between the AP and signed Gallagher objects. -/
theorem signedSlidingDiscrepancy_eq_rationalIntervalError
    {X x y : ℝ} {q a : ℕ}
    (hX : 0 < X) (hx : X ≤ x) (hy : 0 ≤ y)
    (hxy : x + y ≤ 2 * X) :
    signedSlidingDiscrepancy X q a x y =
      rationalIntervalError q a x y := by
  rw [signedSlidingDiscrepancy,
    twistedPrimeSlidingWindow_eq_raw_interval hX hx hy hxy,
    dyadicContinuousWindowLength_eq_window hx hy hxy]
  unfold rationalIntervalError rationalContinuousPrefixError
  have hfloor : ⌊x⌋₊ ≤ ⌊x + y⌋₊ := Nat.floor_mono (by linarith)
  have hsets :
      Finset.Icc 0 ⌊x + y⌋₊ \ Finset.Icc 0 ⌊x⌋₊ =
        Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊ := by
    ext n
    simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hsubset : Finset.Icc 0 ⌊x⌋₊ ⊆ Finset.Icc 0 ⌊x + y⌋₊ := by
    intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    exact ⟨hn.1, hn.2.trans hfloor⟩
  have hsum :
      (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊,
          rationalRawCoefficient q a n) =
        (∑ n ∈ Finset.Icc 0 ⌊x + y⌋₊,
          rationalRawCoefficient q a n) -
        ∑ n ∈ Finset.Icc 0 ⌊x⌋₊,
          rationalRawCoefficient q a n := by
    rw [← hsets]
    exact Finset.sum_sdiff_eq_sub hsubset
  rw [hsum]
  push_cast
  ring

/-! ## The non-coprime residues are already charged to the AP maximum -/

/-- Summing all residue classes modulo `q` gives the modulus-one prefix. -/
theorem sum_progressionPsi_all_residues_eq_mod_one
    {q : ℕ} (hq : 1 ≤ q) (t : ℝ) :
    (∑ r ∈ Finset.range q, progressionPsi t q r) =
      progressionPsi t 1 0 := by
  classical
  have hqpos : 0 < q := Nat.zero_lt_of_lt hq
  unfold progressionPsi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  have hrange : n % q ∈ Finset.range q :=
    Finset.mem_range.mpr (Nat.mod_lt n hqpos)
  rw [Finset.sum_eq_single (n % q)]
  · simp [Nat.mod_eq_of_lt (Nat.mod_lt n hqpos), Nat.mod_one]
  · intro r hr hne
    have hrmod : r % q = r := Nat.mod_eq_of_lt (Finset.mem_range.mp hr)
    have hneq : n % q ≠ r % q := by simpa [hrmod] using hne.symm
    simp [hneq]
  · intro hnot
    exact (hnot hrange).elim

theorem progressionPsi_interval_nonneg
    {x y : ℝ} (hy : 0 ≤ y) (q r : ℕ) :
    0 ≤ progressionPsi (x + y) q r - progressionPsi x q r := by
  unfold progressionPsi
  have hfloor : ⌊x⌋₊ ≤ ⌊x + y⌋₊ := Nat.floor_mono (by linarith)
  apply sub_nonneg.mpr
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    exact ⟨hn.1, hn.2.trans hfloor⟩
  · intro n hn hnot
    split_ifs
    · exact ArithmeticFunction.vonMangoldt_nonneg
    · exact le_rfl

/-- The bad-prime-power residue mass is controlled by the same AP maximum,
using the exact identity `bad = error(mod 1) - sum_good error(mod q)`.
This avoids any `B`-dependent use of `log q`. -/
theorem badResidueWindowMass_le_of_normalizedAP
    {q : ℕ} {x y G : ℝ}
    (hq : 1 ≤ q) (hy : 0 < y) (hG : 0 ≤ G)
    (hAPq : ∀ r : ℕ, r < q → r.Coprime q →
      |normalizedAPError x y q r| ≤ G)
    (hAPone : |normalizedAPError x y 1 0| ≤ G) :
    badResidueWindowMass q x y ≤ (q : ℝ) * (2 * y * G) := by
  classical
  let good := (Finset.range q).filter (fun r => r.Coprime q)
  let bad := (Finset.range q).filter (fun r => ¬ r.Coprime q)
  let win : ℕ → ℝ := fun r =>
    progressionPsi (x + y) q r - progressionPsi x q r
  let err : ℕ → ℝ := fun r => win r - y / (q.totient : ℝ)
  have hwin0 : ∀ r, 0 ≤ win r := fun r =>
    progressionPsi_interval_nonneg hy.le q r
  have hbadEq : badResidueWindowMass q x y = ∑ r ∈ bad, win r := by
    unfold badResidueWindowMass bad win
    apply Finset.sum_congr rfl
    intro r hr
    rw [abs_of_nonneg (progressionPsi_interval_nonneg hy.le q r)]
  have hall : (∑ r ∈ Finset.range q, win r) =
      progressionPsi (x + y) 1 0 - progressionPsi x 1 0 := by
    dsimp [win]
    rw [Finset.sum_sub_distrib,
      sum_progressionPsi_all_residues_eq_mod_one hq,
      sum_progressionPsi_all_residues_eq_mod_one hq]
  have hsplit : (∑ r ∈ Finset.range q, win r) =
      (∑ r ∈ good, win r) + ∑ r ∈ bad, win r := by
    dsimp [good, bad]
    exact (Finset.sum_filter_add_sum_filter_not
      (Finset.range q) (fun r => r.Coprime q) win).symm
  have hcard : good.card = q.totient := by
    dsimp [good]
    rw [Nat.totient]
    congr 1
    ext r
    simp [Nat.coprime_comm]
  have hphi : (q.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.zero_lt_of_lt hq)).ne'
  have hgoodErr : (∑ r ∈ good, err r) = (∑ r ∈ good, win r) - y := by
    dsimp [err]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul, hcard]
    field_simp
  have honeErr :
      progressionPsi (x + y) 1 0 - progressionPsi x 1 0 - y =
        y * normalizedAPError x y 1 0 := by
    simpa using (progression_interval_error_eq_mul_normalizedAPError
      (q := 1) (r := 0) hy)
  have hbadIdentity :
      (∑ r ∈ bad, win r) =
        y * normalizedAPError x y 1 0 - ∑ r ∈ good, err r := by
    rw [← honeErr, hgoodErr]
    linarith [hall, hsplit]
  rw [hbadEq, hbadIdentity]
  calc
    y * normalizedAPError x y 1 0 - ∑ r ∈ good, err r ≤
        |y * normalizedAPError x y 1 0| +
          ∑ r ∈ good, |err r| := by
      have hs := Finset.abs_sum_le_sum_abs err good
      calc
        y * normalizedAPError x y 1 0 - ∑ r ∈ good, err r ≤
            |y * normalizedAPError x y 1 0| +
              |∑ r ∈ good, err r| := by
          linarith [le_abs_self (y * normalizedAPError x y 1 0),
            neg_le_abs (∑ r ∈ good, err r)]
        _ ≤ |y * normalizedAPError x y 1 0| +
              ∑ r ∈ good, |err r| := add_le_add le_rfl hs
    _ ≤ y * G + ∑ _r ∈ good, y * G := by
      apply add_le_add
      · rw [abs_mul, abs_of_pos hy]
        exact mul_le_mul_of_nonneg_left hAPone hy.le
      · apply Finset.sum_le_sum
        intro r hr
        have hr' := Finset.mem_filter.mp hr
        have herr : err r = y * normalizedAPError x y q r := by
          exact progression_interval_error_eq_mul_normalizedAPError hy
        rw [herr, abs_mul, abs_of_pos hy]
        exact mul_le_mul_of_nonneg_left
          (hAPq r (Finset.mem_range.mp hr'.1) hr'.2) hy.le
    _ = (1 + good.card : ℝ) * (y * G) := by simp; ring
    _ ≤ (q : ℝ) * (2 * y * G) := by
      have hgoodCard : (good.card : ℝ) ≤ q := by
        exact_mod_cast (show good.card ≤ q by
          calc
            good.card ≤ (Finset.range q).card := by
              dsimp [good]
              exact Finset.card_filter_le _ _
            _ = q := Finset.card_range q)
      have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
      have hyG : 0 ≤ y * G := mul_nonneg hy.le hG
      nlinarith

/-- Exact per-rational interior bound, with every non-coprime prime-power
contribution charged to `q^2` times the AP control. -/
theorem norm_rationalIntervalError_le_three_q_mul
    {q a : ℕ} {x y G : ℝ}
    (hq : 1 ≤ q) (ha : a.Coprime q) (hy : 0 < y) (hG : 0 ≤ G)
    (hAPq : ∀ r : ℕ, r < q → r.Coprime q →
      |normalizedAPError x y q r| ≤ G)
    (hAPone : |normalizedAPError x y 1 0| ≤ G) :
    ‖rationalIntervalError q a x y‖ ≤ 3 * (q : ℝ) * y * G := by
  have hbase := norm_rationalIntervalError_le_of_normalizedAP
    hq ha hy hG hAPq
  have hbad := badResidueWindowMass_le_of_normalizedAP
    hq hy hG hAPq hAPone
  calc
    ‖rationalIntervalError q a x y‖ ≤
        (q : ℝ) * (y * G) + badResidueWindowMass q x y := hbase
    _ ≤ (q : ℝ) * (y * G) + (q : ℝ) * (2 * y * G) :=
      add_le_add le_rfl hbad
    _ = 3 * (q : ℝ) * y * G := by ring

/-- Pointwise interior energy is at most `9 q² y²` times the literal
simultaneous AP maximum.  This includes the non-coprime prime powers through
the modulus-one identity above. -/
theorem ofReal_norm_rationalIntervalError_sq_le_APMax
    {B q a : ℕ} {epsilonAP X x y : ℝ}
    (hlog : 1 ≤ Real.log X)
    (hq : 1 ≤ q) (hqcap : (q : ℝ) ≤ collarQ X B)
    (ha : a.Coprime q)
    (hy : 0 < y)
    (hYlow : Real.rpow X (2 / 15 + epsilonAP) ≤ y)
    (hYhigh : y ≤ X) :
    ENNReal.ofReal (‖rationalIntervalError q a x y‖ ^ 2) ≤
      ENNReal.ofReal (9 * (q : ℝ) ^ 2 * y ^ 2) *
        simultaneousAPMax (B : ℝ) epsilonAP X x := by
  let S := simultaneousAPMax (B : ℝ) epsilonAP X x
  by_cases htop : S = ∞
  · have hcoefpos : 0 < 9 * (q : ℝ) ^ 2 * y ^ 2 := by positivity
    rw [show simultaneousAPMax (B : ℝ) epsilonAP X x = ∞ by
      simpa [S] using htop]
    rw [ENNReal.mul_top (by
      exact (ENNReal.ofReal_pos.mpr hcoefpos).ne')]
    exact le_top
  have hS : S ≠ ∞ := htop
  let G : ℝ := Real.sqrt S.toReal
  have hG : 0 ≤ G := Real.sqrt_nonneg _
  have hqcap' : (q : ℝ) ≤ Real.rpow (Real.log X) (B : ℝ) := by
    simpa [collarQ, Real.rpow_natCast] using hqcap
  have honecap : (1 : ℝ) ≤ Real.rpow (Real.log X) (B : ℝ) :=
    Real.one_le_rpow hlog (Nat.cast_nonneg B)
  have hsquare
      {m r : ℕ} (hm : 1 ≤ m)
      (hmcap : (m : ℝ) ≤ Real.rpow (Real.log X) (B : ℝ))
      (hrm : r < m) (hrcop : r.Coprime m) :
      |normalizedAPError x y m r| ^ 2 ≤ S.toReal := by
    have hp := individualAPError_le_simultaneousAPMax
      (K := (B : ℝ)) (ε := epsilonAP) (X := X) (x := x)
      (Y := y) hm hmcap hrm hrcop hYlow hYhigh
    change ENNReal.ofReal |normalizedAPError x y m r| ^ 2 ≤ S at hp
    have hp' := ENNReal.toReal_mono hS hp
    simpa only [ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (abs_nonneg _)] using hp'
  have habs
      {m r : ℕ} (hm : 1 ≤ m)
      (hmcap : (m : ℝ) ≤ Real.rpow (Real.log X) (B : ℝ))
      (hrm : r < m) (hrcop : r.Coprime m) :
      |normalizedAPError x y m r| ≤ G := by
    have hs := hsquare hm hmcap hrm hrcop
    have hroot : G ^ 2 = S.toReal := by
      dsimp [G]
      exact Real.sq_sqrt ENNReal.toReal_nonneg
    nlinarith [abs_nonneg (normalizedAPError x y m r)]
  have hAPq : ∀ r : ℕ, r < q → r.Coprime q →
      |normalizedAPError x y q r| ≤ G := by
    intro r hr hrcop
    exact habs hq hqcap' hr hrcop
  have hAPone : |normalizedAPError x y 1 0| ≤ G := by
    have honecap' : ((1 : ℕ) : ℝ) ≤ Real.rpow (Real.log X) (B : ℝ) := by
      simpa only [Nat.cast_one] using honecap
    exact habs (m := 1) (r := 0) (by norm_num) honecap'
      (by norm_num) (by norm_num)
  have hnorm := norm_rationalIntervalError_le_three_q_mul
    hq ha hy hG hAPq hAPone
  have hsq : ‖rationalIntervalError q a x y‖ ^ 2 ≤
      9 * (q : ℝ) ^ 2 * y ^ 2 * S.toReal := by
    have hpow := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    calc
      ‖rationalIntervalError q a x y‖ ^ 2 ≤
          (3 * (q : ℝ) * y * G) ^ 2 := hpow
      _ = 9 * (q : ℝ) ^ 2 * y ^ 2 * (G ^ 2) := by ring
      _ = 9 * (q : ℝ) ^ 2 * y ^ 2 * S.toReal := by
        rw [show G ^ 2 = S.toReal by
          dsimp [G]
          exact Real.sq_sqrt ENNReal.toReal_nonneg]
  have hcoef : 0 ≤ 9 * (q : ℝ) ^ 2 * y ^ 2 := by positivity
  have hprodtop : ENNReal.ofReal (9 * (q : ℝ) ^ 2 * y ^ 2) * S ≠ ∞ := by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hS
  apply (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hprodtop).mp
  rw [ENNReal.toReal_ofReal (sq_nonneg _), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hcoef]
  exact hsq

/-! ## Uniform short-window and endpoint bounds -/

/-- The finite set of dyadically supported atoms active in `(x,x+y]`. -/
def activeTwistedIndices (X x y : ℝ) : Finset ℕ :=
  (Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊).filter fun n =>
    x < (n : ℝ) ∧ (n : ℝ) ≤ x + y

theorem activeTwistedIndices_card_real_le
    {X x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ((activeTwistedIndices X x y).card : ℝ) ≤ y + 1 := by
  have hxy : 0 ≤ x + y := add_nonneg hx hy
  have hsub : activeTwistedIndices X x y ⊆
      Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊ := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨_hnDyadic, hxn, hnxy⟩
    exact Finset.mem_Ioc.mpr ⟨(Nat.floor_lt hx).mpr hxn, Nat.le_floor hnxy⟩
  have hcard := Finset.card_le_card hsub
  have hfloor : ⌊x⌋₊ ≤ ⌊x + y⌋₊ := Nat.floor_mono (le_add_of_nonneg_right hy)
  have hcardEq : (Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊).card =
      ⌊x + y⌋₊ - ⌊x⌋₊ := by simp
  rw [hcardEq] at hcard
  have hcast : ((⌊x + y⌋₊ - ⌊x⌋₊ : ℕ) : ℝ) =
      (⌊x + y⌋₊ : ℝ) - (⌊x⌋₊ : ℝ) := by
    rw [Nat.cast_sub hfloor]
  have hupper : (⌊x + y⌋₊ : ℝ) ≤ x + y := Nat.floor_le hxy
  have hlower : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
  have hcardR : ((activeTwistedIndices X x y).card : ℝ) ≤
      ((⌊x + y⌋₊ - ⌊x⌋₊ : ℕ) : ℝ) := by exact_mod_cast hcard
  rw [hcast] at hcardR
  linarith

theorem norm_twistedPrimeSlidingWindow_le_short
    {X x y : ℝ} {q a : ℕ}
    (hX : 2 ≤ X) (hx : 0 ≤ x) (hy : 1 ≤ y) :
    ‖twistedPrimeSlidingWindow X q a x y‖ ≤
      4 * y * Real.log X := by
  classical
  have h2Xpos : 0 < 2 * X := by positivity
  have hlogX0 : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hlog2le : Real.log 2 ≤ Real.log X :=
    Real.log_le_log (by norm_num) hX
  have hlog2X : Real.log (2 * X) ≤ 2 * Real.log X := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt (by linarith : 0 < X))]
    linarith
  have hweight : ∀ n ∈ activeTwistedIndices X x y,
      ‖(ArithmeticFunction.vonMangoldt n : ℂ) *
          fourier (n : ℤ) (rationalCenter q a)‖ ≤ 2 * Real.log X := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnDyadic, _hxn, _hnxy⟩
    have hnIoc := Finset.mem_Ioc.mp hnDyadic
    have hX0 : 0 ≤ X := by linarith
    have hnpos : 0 < n := by
      have : X < (n : ℝ) := (Nat.floor_lt hX0).mp hnIoc.1
      have hnposR : (0 : ℝ) < (n : ℝ) :=
        (by linarith : 0 < X).trans this
      exact_mod_cast hnposR
    have hn2X : (n : ℝ) ≤ 2 * X :=
      (show (n : ℝ) ≤ (⌊2 * X⌋₊ : ℝ) by exact_mod_cast hnIoc.2).trans
        (Nat.floor_le h2Xpos.le)
    have hvm : ArithmeticFunction.vonMangoldt n ≤ Real.log (2 * X) :=
      ArithmeticFunction.vonMangoldt_le_log.trans
        (Real.log_le_log (Nat.cast_pos.mpr hnpos) hn2X)
    rw [norm_mul, fourier_apply, Circle.norm_coe, mul_one,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact hvm.trans hlog2X
  have hcard := activeTwistedIndices_card_real_le (X := X) hx
    (zero_le_one.trans hy)
  have hcard2 : ((activeTwistedIndices X x y).card : ℝ) ≤ 2 * y := by
    linarith
  unfold twistedPrimeSlidingWindow
  rw [← Finset.sum_filter]
  change ‖∑ n ∈ activeTwistedIndices X x y,
      (ArithmeticFunction.vonMangoldt n : ℂ) *
        fourier (n : ℤ) (rationalCenter q a)‖ ≤ _
  calc
    _ ≤ ∑ n ∈ activeTwistedIndices X x y,
        ‖(ArithmeticFunction.vonMangoldt n : ℂ) *
          fourier (n : ℤ) (rationalCenter q a)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ activeTwistedIndices X x y, 2 * Real.log X :=
      Finset.sum_le_sum hweight
    _ = ((activeTwistedIndices X x y).card : ℝ) *
        (2 * Real.log X) := by simp
    _ ≤ (2 * y) * (2 * Real.log X) := by
      exact mul_le_mul_of_nonneg_right hcard2 (by positivity)
    _ = 4 * y * Real.log X := by ring

/-- Every active endpoint window has a `5 y log X` signed-field bound. -/
theorem norm_signedSlidingDiscrepancy_le_short
    {X x y : ℝ} {q a : ℕ}
    (hX : 2 ≤ X) (hlog : 1 ≤ Real.log X)
    (hx : 0 ≤ x) (hy : 1 ≤ y) (hq : 1 ≤ q) :
    ‖signedSlidingDiscrepancy X q a x y‖ ≤
      5 * y * Real.log X := by
  have hatom := norm_twistedPrimeSlidingWindow_le_short
    (q := q) (a := a) hX hx hy
  have hcoeff := MAPMajorArcIntegratedError.norm_primeMajorCoefficient_le_one hq
  have hover := dyadicContinuousWindowLength_le_window (X := X) (x := x)
    (zero_le_one.trans hy)
  have hover0 := dyadicContinuousWindowLength_nonneg X x y
  unfold signedSlidingDiscrepancy
  calc
    _ ≤ ‖twistedPrimeSlidingWindow X q a x y‖ +
        ‖primeMajorCoefficient q * dyadicContinuousWindowLength X x y‖ :=
      norm_sub_le _ _
    _ ≤ 4 * y * Real.log X + y := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hover0]
      exact add_le_add hatom
        ((mul_le_mul hcoeff hover (by positivity) (by positivity)).trans_eq
          (one_mul y))
    _ ≤ 5 * y * Real.log X := by nlinarith

theorem signedSlidingDiscrepancy_eq_zero_of_left
    {X x y : ℝ} {q a : ℕ} (hX : 0 ≤ X) (hxy : x + y ≤ X) :
    signedSlidingDiscrepancy X q a x y = 0 := by
  have hatom : twistedPrimeSlidingWindow X q a x y = 0 := by
    unfold twistedPrimeSlidingWindow
    apply Finset.sum_eq_zero
    intro n hn
    have hnlo : X < (n : ℝ) :=
      (Nat.floor_lt hX).mp (Finset.mem_Ioc.mp hn).1
    split_ifs with hactive
    · exact False.elim (not_lt_of_ge (hactive.2.trans hxy) hnlo)
    · rfl
  have hover : dyadicContinuousWindowLength X x y = 0 := by
    unfold dyadicContinuousWindowLength
    rw [max_eq_left]
    have hmin : min (2 * X) (x + y) ≤ x + y := min_le_right _ _
    have hmax : X ≤ max X x := le_max_left _ _
    linarith
  simp [signedSlidingDiscrepancy, hatom, hover]

theorem signedSlidingDiscrepancy_eq_zero_of_right
    {X x y : ℝ} {q a : ℕ} (hX : 0 ≤ X) (hx : 2 * X ≤ x) :
    signedSlidingDiscrepancy X q a x y = 0 := by
  have hatom : twistedPrimeSlidingWindow X q a x y = 0 := by
    unfold twistedPrimeSlidingWindow
    apply Finset.sum_eq_zero
    intro n hn
    have hnhi : (n : ℝ) ≤ 2 * X :=
      (show (n : ℝ) ≤ (⌊2 * X⌋₊ : ℝ) by
        exact_mod_cast (Finset.mem_Ioc.mp hn).2).trans
        (Nat.floor_le (by positivity))
    split_ifs with hactive
    · exact False.elim (not_lt_of_ge (hnhi.trans hx) hactive.1)
    · rfl
  have hover : dyadicContinuousWindowLength X x y = 0 := by
    unfold dyadicContinuousWindowLength
    rw [max_eq_left]
    have hmin : min (2 * X) (x + y) ≤ 2 * X := min_le_left _ _
    have hmax : x ≤ max X x := le_max_right _ _
    linarith
  simp [signedSlidingDiscrepancy, hatom, hover]

/-- The two endpoint collars together cost at most `50 y^3 log(X)^2`. -/
theorem endpointCollarsEnergy_le
    {X y : ℝ} {q a : ℕ}
    (hX : 2 ≤ X) (hlog : 1 ≤ Real.log X)
    (hy : 1 ≤ y) (hyhalf : y ≤ X / 2) (hq : 1 ≤ q) :
    (∫ x in Set.Icc (X - y) X,
        ‖signedSlidingDiscrepancy X q a x y‖ ^ 2) +
      (∫ x in Set.Icc (2 * X - y) (2 * X),
        ‖signedSlidingDiscrepancy X q a x y‖ ^ 2) ≤
      50 * y ^ 3 * (Real.log X) ^ 2 := by
  let f : ℝ → ℝ := fun x => ‖signedSlidingDiscrepancy X q a x y‖ ^ 2
  let C : ℝ := (5 * y * Real.log X) ^ 2
  have hf : Integrable f := by
    have hm := memLp_two_signedSlidingDiscrepancy (X := X) q a
      (zero_le_one.trans hy)
    have hbase := integrable_signedSlidingDiscrepancy (X := X) q a
      (zero_le_one.trans hy)
    exact (memLp_two_iff_integrable_sq_norm hbase.aestronglyMeasurable).mp hm
  have hC : IntegrableOn (fun _x : ℝ => C) (Set.Icc (X - y) X) :=
    integrableOn_const (by simp)
  have hC' : IntegrableOn (fun _x : ℝ => C)
      (Set.Icc (2 * X - y) (2 * X)) := integrableOn_const (by simp)
  have hleft : (∫ x in Set.Icc (X - y) X, f x) ≤ y * C := by
    calc
      (∫ x in Set.Icc (X - y) X, f x) ≤
          ∫ _x in Set.Icc (X - y) X, C := by
        apply MeasureTheory.setIntegral_mono_on hf.integrableOn hC
          measurableSet_Icc
        intro x hxmem
        dsimp [f, C]
        have hx0 : 0 ≤ x := by
          have : X / 2 ≤ X - y := by linarith
          have hX0 : 0 ≤ X / 2 := by positivity
          linarith [hxmem.1]
        have hn := norm_signedSlidingDiscrepancy_le_short
          (X := X) (x := x) (y := y) (q := q) (a := a)
          hX hlog hx0 hy hq
        exact (sq_le_sq₀
          (norm_nonneg (signedSlidingDiscrepancy X q a x y))
          (by positivity)).mpr hn
      _ = y * C := by
        rw [MeasureTheory.setIntegral_const]
        have hvol : (volume : Measure ℝ).real (Set.Icc (X - y) X) = y := by
          rw [Measure.real, Real.volume_Icc,
            ENNReal.toReal_ofReal (by linarith : 0 ≤ X - (X - y))]
          ring
        rw [hvol]
        simp [smul_eq_mul]
  have hright : (∫ x in Set.Icc (2 * X - y) (2 * X), f x) ≤ y * C := by
    calc
      (∫ x in Set.Icc (2 * X - y) (2 * X), f x) ≤
          ∫ _x in Set.Icc (2 * X - y) (2 * X), C := by
        apply MeasureTheory.setIntegral_mono_on hf.integrableOn hC'
          measurableSet_Icc
        intro x hxmem
        dsimp [f, C]
        have hx0 : 0 ≤ x := by
          have hbound : 0 ≤ 2 * X - y := by linarith
          exact hbound.trans hxmem.1
        have hn := norm_signedSlidingDiscrepancy_le_short
          (X := X) (x := x) (y := y) (q := q) (a := a)
          hX hlog hx0 hy hq
        exact (sq_le_sq₀
          (norm_nonneg (signedSlidingDiscrepancy X q a x y))
          (by positivity)).mpr hn
      _ = y * C := by
        rw [MeasureTheory.setIntegral_const]
        have hvol : (volume : Measure ℝ).real
            (Set.Icc (2 * X - y) (2 * X)) = y := by
          rw [Measure.real, Real.volume_Icc,
            ENNReal.toReal_ofReal (by linarith : 0 ≤ 2 * X - (2 * X - y))]
          ring
        rw [hvol]
        simp [smul_eq_mul]
  change (∫ x in Set.Icc (X - y) X, f x) +
      (∫ x in Set.Icc (2 * X - y) (2 * X), f x) ≤ _
  calc
    _ ≤ y * C + y * C := add_le_add hleft hright
    _ = 50 * y ^ 3 * (Real.log X) ^ 2 := by
      dsimp [C]
      ring

/-! ## Elementary finiteness of the AP maximal integral -/

theorem progressionPsi_nonneg (t : ℝ) (q r : ℕ) :
    0 ≤ progressionPsi t q r := by
  unfold progressionPsi
  apply Finset.sum_nonneg
  intro n hn
  split_ifs
  · exact ArithmeticFunction.vonMangoldt_nonneg
  · exact le_rfl

theorem progressionPsi_le_chebyshevPsi
    {t : ℝ} (q r : ℕ) :
    progressionPsi t q r ≤ Chebyshev.psi t := by
  unfold progressionPsi Chebyshev.psi
  apply Finset.sum_le_sum
  intro n hn
  split_ifs
  · exact le_rfl
  · exact ArithmeticFunction.vonMangoldt_nonneg

/-- A deliberately crude uniform bound.  Its sole role is to certify that the
literal AP maximal integral is finite, so taking `.toReal` loses no mass. -/
theorem abs_normalizedAPError_le_crude
    {epsilonAP X x Y : ℝ} {q r : ℕ}
    (hXone : 1 ≤ X) (hepsilonAP : 0 < epsilonAP)
    (hxlow : X / 2 ≤ x) (hxhigh : x ≤ 4 * X)
    (hq : 1 ≤ q)
    (hYlow : Real.rpow X (2 / 15 + epsilonAP) ≤ Y)
    (hYhigh : Y ≤ X) :
    |normalizedAPError x Y q r| ≤
      10 * (Real.log 4 + 4) * X := by
  let c : ℝ := Real.log 4 + 4
  have hexp0 : 0 ≤ 2 / 15 + epsilonAP := by linarith
  have hpowone : 1 ≤ Real.rpow X (2 / 15 + epsilonAP) :=
    Real.one_le_rpow hXone hexp0
  have hYone : 1 ≤ Y := hpowone.trans hYlow
  have hx0 : 0 ≤ x := by linarith
  have hxy0 : 0 ≤ x + Y := by positivity
  have hcpos : 0 < c := by
    dsimp [c]
    have := Real.log_pos (by norm_num : (1 : ℝ) < 4)
    linarith
  have hA0 := progressionPsi_nonneg (x + Y) q r
  have hB0 := progressionPsi_nonneg x q r
  have hA : progressionPsi (x + Y) q r ≤ c * (x + Y) :=
    (progressionPsi_le_chebyshevPsi q r).trans
      (Chebyshev.psi_le_const_mul_self hxy0)
  have hB : progressionPsi x q r ≤ c * x :=
    (progressionPsi_le_chebyshevPsi q r).trans
      (Chebyshev.psi_le_const_mul_self hx0)
  have hphiNat : 1 ≤ q.totient := Nat.totient_pos.mpr (by omega)
  have hphi : (1 : ℝ) ≤ (q.totient : ℝ) := by exact_mod_cast hphiNat
  have hphiPos : (0 : ℝ) < (q.totient : ℝ) := zero_lt_one.trans_le hphi
  have hmain0 : 0 ≤ Y / (q.totient : ℝ) :=
    div_nonneg (zero_le_one.trans hYone) hphiPos.le
  have hmain : Y / (q.totient : ℝ) ≤ Y := by
    apply (div_le_iff₀ hphiPos).mpr
    nlinarith
  have hc1 : 1 ≤ c := by
    dsimp [c]
    have := Real.log_pos (by norm_num : (1 : ℝ) < 4)
    linarith
  have hnum :
      |(progressionPsi (x + Y) q r - progressionPsi x q r) -
          Y / (q.totient : ℝ)| ≤ 10 * c * X := by
    calc
      _ ≤ |progressionPsi (x + Y) q r - progressionPsi x q r| +
          |Y / (q.totient : ℝ)| := abs_sub _ _
      _ ≤ (progressionPsi (x + Y) q r + progressionPsi x q r) +
          Y / (q.totient : ℝ) := by
        rw [abs_of_nonneg hmain0]
        gcongr
        have hab := abs_sub_le (progressionPsi (x + Y) q r) 0
          (progressionPsi x q r)
        simpa [abs_of_nonneg hA0, abs_of_nonneg hB0] using hab
      _ ≤ c * (x + Y) + c * x + Y := by linarith
      _ ≤ 10 * c * X := by nlinarith
  unfold normalizedAPError
  rw [abs_div, abs_of_pos (zero_lt_one.trans_le hYone)]
  exact (div_le_iff₀ (zero_lt_one.trans_le hYone)).mpr (by
    nlinarith [mul_nonneg (by positivity : 0 ≤ 10 * c * X)
      (sub_nonneg.mpr hYone)])

theorem simultaneousAPMax_le_crude
    {B : ℕ} {epsilonAP X x : ℝ}
    (hXone : 1 ≤ X) (hepsilonAP : 0 < epsilonAP)
    (hxlow : X / 2 ≤ x) (hxhigh : x ≤ 4 * X) :
    simultaneousAPMax (B : ℝ) epsilonAP X x ≤
      ENNReal.ofReal (10 * (Real.log 4 + 4) * X) ^ 2 := by
  unfold simultaneousAPMax
  apply iSup_le
  intro q
  apply iSup_le
  intro hq
  apply iSup_le
  intro hqcap
  apply iSup_le
  intro a
  apply iSup_le
  intro haq
  apply iSup_le
  intro hacop
  apply iSup_le
  intro Y
  apply iSup_le
  intro hYlow
  apply iSup_le
  intro hYhigh
  have habs := abs_normalizedAPError_le_crude hXone hepsilonAP
    hxlow hxhigh hq hYlow hYhigh (r := a)
  exact pow_le_pow_left' (ENNReal.ofReal_le_ofReal habs) 2

theorem apMaxIntegral_ne_top
    {B : ℕ} {epsilonAP X : ℝ}
    (hXone : 1 ≤ X) (hepsilonAP : 0 < epsilonAP) :
    apMaxIntegral B epsilonAP X ≠ ∞ := by
  let M : ℝ≥0∞ := ENNReal.ofReal (10 * (Real.log 4 + 4) * X) ^ 2
  have hbound : apMaxIntegral B epsilonAP X ≤
      M * ENNReal.ofReal (4 * X - X / 2) := by
    unfold apMaxIntegral
    calc
      (∫⁻ x in Set.Icc (X / 2) (4 * X),
          simultaneousAPMax (B : ℝ) epsilonAP X x) ≤
          ∫⁻ _x in Set.Icc (X / 2) (4 * X), M := by
        apply setLIntegral_mono' measurableSet_Icc
        intro x hx
        exact simultaneousAPMax_le_crude hXone hepsilonAP hx.1 hx.2
      _ = M * ENNReal.ofReal (4 * X - X / 2) := by
        rw [setLIntegral_const, Real.volume_Icc]
  have hM : M ≠ ∞ := by
    dsimp [M]
    exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  exact ne_top_of_le_ne_top
    (ENNReal.mul_ne_top hM ENNReal.ofReal_ne_top) hbound

/-- The interior portion of the whole-line signed energy is exactly charged
to `9 q² y²` times the AP maximal integral. -/
theorem interiorSignedSlidingEnergy_le_APMax
    {B q a : ℕ} {epsilonAP X y : ℝ}
    (hXone : 1 ≤ X) (hlog : 1 ≤ Real.log X)
    (hepsilonAP : 0 < epsilonAP)
    (hq : 1 ≤ q) (hqcap : (q : ℝ) ≤ collarQ X B)
    (ha : a.Coprime q)
    (hy : 0 < y)
    (hYlow : Real.rpow X (2 / 15 + epsilonAP) ≤ y)
    (hYhigh : y ≤ X) :
    (∫ x in Set.Icc X (2 * X - y),
        ‖signedSlidingDiscrepancy X q a x y‖ ^ 2) ≤
      9 * (q : ℝ) ^ 2 * y ^ 2 *
        (apMaxIntegral B epsilonAP X).toReal := by
  let c : ℝ≥0∞ := ENNReal.ofReal (9 * (q : ℝ) ^ 2 * y ^ 2)
  let f : ℝ → ℝ := fun x => ‖signedSlidingDiscrepancy X q a x y‖ ^ 2
  have hXpos : 0 < X := zero_lt_one.trans_le hXone
  have hf : Integrable f := by
    have hm := memLp_two_signedSlidingDiscrepancy (X := X) q a hy.le
    have hbase := integrable_signedSlidingDiscrepancy (X := X) q a hy.le
    exact (memLp_two_iff_integrable_sq_norm hbase.aestronglyMeasurable).mp hm
  have hsubset : Set.Icc X (2 * X - y) ⊆ Set.Icc (X / 2) (4 * X) := by
    intro x hx
    constructor
    · exact (by linarith : X / 2 ≤ X).trans hx.1
    · have : 2 * X - y ≤ 4 * X := by linarith
      exact hx.2.trans this
  have hcTop : c ≠ ∞ := by
    dsimp [c]
    exact ENNReal.ofReal_ne_top
  have hlin : ENNReal.ofReal
      (∫ x in Set.Icc X (2 * X - y), f x) ≤
      c * apMaxIntegral B epsilonAP X := by
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      hf.integrableOn (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
    calc
      (∫⁻ x in Set.Icc X (2 * X - y), ENNReal.ofReal (f x)) ≤
          ∫⁻ x in Set.Icc X (2 * X - y),
            c * simultaneousAPMax (B : ℝ) epsilonAP X x := by
        apply setLIntegral_mono' measurableSet_Icc
        intro x hx
        have hid : signedSlidingDiscrepancy X q a x y =
            rationalIntervalError q a x y :=
          signedSlidingDiscrepancy_eq_rationalIntervalError
            (q := q) (a := a) hXpos hx.1 hy.le (by linarith [hx.2])
        have hp := ofReal_norm_rationalIntervalError_sq_le_APMax
          hlog hq hqcap ha hy hYlow hYhigh (x := x)
        simpa only [f, c, hid] using hp
      _ = c * (∫⁻ x in Set.Icc X (2 * X - y),
          simultaneousAPMax (B : ℝ) epsilonAP X x) := by
        exact lintegral_const_mul' c _ hcTop
      _ ≤ c * apMaxIntegral B epsilonAP X := by
        exact mul_le_mul_left' (lintegral_mono_set hsubset) c
  have hapTop := apMaxIntegral_ne_top (B := B) (epsilonAP := epsilonAP)
    hXone hepsilonAP
  have hrhsTop : c * apMaxIntegral B epsilonAP X ≠ ∞ :=
    ENNReal.mul_ne_top hcTop hapTop
  have hreal := ENNReal.toReal_mono hrhsTop hlin
  have hintegral0 : 0 ≤ ∫ x in Set.Icc X (2 * X - y), f x :=
    integral_nonneg fun _ => sq_nonneg _
  rw [ENNReal.toReal_ofReal hintegral0, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 9 * (q : ℝ) ^ 2 * y ^ 2)] at hreal
  simpa [f, c] using hreal

/-- The complete real-line signed energy, with the AP interior and both
endpoint collars separated and no bad-factor remainder. -/
theorem wholeLineSignedSlidingEnergy_le
    {B q a : ℕ} {epsilonAP X y : ℝ}
    (hX : 2 ≤ X) (hlog : 1 ≤ Real.log X)
    (hepsilonAP : 0 < epsilonAP)
    (hq : 1 ≤ q) (hqcap : (q : ℝ) ≤ collarQ X B)
    (ha : a.Coprime q)
    (hy : 1 ≤ y) (hyhalf : y ≤ X / 2)
    (hYlow : Real.rpow X (2 / 15 + epsilonAP) ≤ y) :
    (∫ x : ℝ, ‖signedSlidingDiscrepancy X q a x y‖ ^ 2) ≤
      9 * (q : ℝ) ^ 2 * y ^ 2 *
          (apMaxIntegral B epsilonAP X).toReal +
        50 * y ^ 3 * (Real.log X) ^ 2 := by
  let f : ℝ → ℝ := fun x => ‖signedSlidingDiscrepancy X q a x y‖ ^ 2
  have hXpos : 0 < X := by linarith
  have hypos : 0 < y := zero_lt_one.trans_le hy
  have hyX : y ≤ X := hyhalf.trans (by linarith)
  have hf : Integrable f := by
    have hm := memLp_two_signedSlidingDiscrepancy (X := X) q a hypos.le
    have hbase := integrable_signedSlidingDiscrepancy (X := X) q a hypos.le
    exact (memLp_two_iff_integrable_sq_norm hbase.aestronglyMeasurable).mp hm
  have hzero : ∀ x ∉ Set.Ioc (X - y) (2 * X), f x = 0 := by
    intro x hx
    have hor : x ≤ X - y ∨ 2 * X < x := by
      simpa only [Set.mem_Ioc, not_and_or, not_lt, not_le] using hx
    rcases hor with hleft | hright
    · have hz := signedSlidingDiscrepancy_eq_zero_of_left
        (X := X) (x := x) (y := y) (q := q) (a := a)
        hXpos.le (by linarith)
      simp [f, hz]
    · have hz := signedSlidingDiscrepancy_eq_zero_of_right
        (X := X) (x := x) (y := y) (q := q) (a := a)
        hXpos.le hright.le
      simp [f, hz]
  have horders : X - y ≤ X ∧ X ≤ 2 * X - y ∧ 2 * X - y ≤ 2 * X := by
    exact ⟨by linarith, by constructor <;> linarith⟩
  have hsplit : (∫ x : ℝ, f x) =
      (∫ x in Set.Ioc (X - y) X, f x) +
      (∫ x in Set.Ioc X (2 * X - y), f x) +
      (∫ x in Set.Ioc (2 * X - y) (2 * X), f x) := by
    rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
    rw [← intervalIntegral.integral_of_le
      (horders.1.trans (horders.2.1.trans horders.2.2))]
    rw [← intervalIntegral.integral_of_le horders.1,
      ← intervalIntegral.integral_of_le horders.2.1,
      ← intervalIntegral.integral_of_le horders.2.2]
    have hi1 : IntervalIntegrable f volume (X - y) X := hf.intervalIntegrable
    have hi2 : IntervalIntegrable f volume X (2 * X - y) := hf.intervalIntegrable
    have hi12 : IntervalIntegrable f volume (X - y) (2 * X - y) :=
      hf.intervalIntegrable
    have hi3 : IntervalIntegrable f volume (2 * X - y) (2 * X) :=
      hf.intervalIntegrable
    have hadd1 := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
    have hadd2 := intervalIntegral.integral_add_adjacent_intervals hi12 hi3
    linarith
  have hleftMono : (∫ x in Set.Ioc (X - y) X, f x) ≤
      ∫ x in Set.Icc (X - y) X, f x := by
    apply MeasureTheory.setIntegral_mono_set hf.integrableOn
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)
    exact Filter.Eventually.of_forall fun _ hx => ⟨hx.1.le, hx.2⟩
  have hinteriorMono : (∫ x in Set.Ioc X (2 * X - y), f x) ≤
      ∫ x in Set.Icc X (2 * X - y), f x := by
    apply MeasureTheory.setIntegral_mono_set hf.integrableOn
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)
    exact Filter.Eventually.of_forall fun _ hx => ⟨hx.1.le, hx.2⟩
  have hrightMono : (∫ x in Set.Ioc (2 * X - y) (2 * X), f x) ≤
      ∫ x in Set.Icc (2 * X - y) (2 * X), f x := by
    apply MeasureTheory.setIntegral_mono_set hf.integrableOn
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)
    exact Filter.Eventually.of_forall fun _ hx => ⟨hx.1.le, hx.2⟩
  have hinterior := interiorSignedSlidingEnergy_le_APMax
    (B := B) (q := q) (a := a) (epsilonAP := epsilonAP)
    (X := X) (y := y) (by linarith) hlog hepsilonAP hq hqcap ha
    hypos hYlow hyX
  have hend := endpointCollarsEnergy_le hX hlog hy hyhalf hq
    (q := q) (a := a)
  change (∫ x : ℝ, f x) ≤ _
  rw [hsplit]
  dsimp [f] at hleftMono hinteriorMono hrightMono hinterior hend ⊢
  linarith

/-! ## Circle-to-line lift and continuous minor tail -/

theorem setIntegral_closedBall_eq_intervalIntegral_lift_real
    {t R : ℝ} (hR0 : 0 ≤ R) (hRhalf : R < (1 : ℝ) / 2)
    (f : UnitAddCircle → ℝ) :
    (∫ α in Metric.closedBall (t : UnitAddCircle) R, f α
        ∂AddCircle.haarAddCircle) =
      ∫ β in -R..R, f ((t : UnitAddCircle) + (β : UnitAddCircle)) := by
  have h := MAPMajorArcPublicLiftBridge.setIntegral_closedBall_eq_intervalIntegral_lift
    (t := t) (R := R) hR0 hRhalf (fun α => (f α : ℂ))
  have h' : ((∫ α in Metric.closedBall (t : UnitAddCircle) R, f α
      ∂AddCircle.haarAddCircle : ℝ) : ℂ) =
      ((∫ β in Set.Ioc (-R) R,
        f ((t : UnitAddCircle) + (β : UnitAddCircle)) : ℝ) : ℂ) := by
    simpa only [intervalIntegral.integral_of_le (by linarith : -R ≤ R),
      integral_complex_ofReal] using h
  apply Complex.ofReal_injective
  simpa only [intervalIntegral.integral_of_le (by linarith : -R ≤ R)] using h'

theorem minorContinuousModelEnergy_le
    {X R r : ℝ} {B D q a : ℕ}
    (hX : 0 ≤ X) (hR : 0 < R) (hr : 0 ≤ r) (hrhalf : r < 1 / 2)
    (hq : 1 ≤ q) (hqcap : (q : ℝ) ≤ (Real.log X) ^ B)
    (haq : a < q) (ha : a.Coprime q)
    (hReq : R = (Real.log X) ^ D / X) :
    (∫ β in Set.Icc (-r) r ∩
          {β : ℝ | rationalCenter q a + (β : UnitAddCircle) ∈
            minorArcs X B D},
        ‖primeMajorCoefficient q * dyadicContinuousAmplitude X β‖ ^ 2) ≤
      2 / (Real.pi ^ 2 * R) := by
  let s : Set ℝ := Set.Icc (-r) r ∩
    {β : ℝ | rationalCenter q a + (β : UnitAddCircle) ∈ minorArcs X B D}
  let tail : Set ℝ := Set.Iic (-R) ∪ Set.Ioi R
  let g : ℝ → ℝ := fun β => ‖dyadicContinuousAmplitude X β‖ ^ 2
  let m : ℝ → ℝ := fun β =>
    ‖primeMajorCoefficient q * dyadicContinuousAmplitude X β‖ ^ 2
  have hsMeas : MeasurableSet s := by
    apply measurableSet_Icc.inter
    exact (MAPHarmonicEndpoint.measurableSet_minorArcs X B D).preimage
      ((continuous_const.add (AddCircle.continuous_mk' (p := (1 : ℝ)))).measurable)
  have htailMeas : MeasurableSet tail := measurableSet_Iic.union measurableSet_Ioi
  have hsubset : s ⊆ tail := by
    intro β hβ
    rcases hβ with ⟨hβband, hβminor⟩
    have hminorDist :=
      (RationalArcPartition.mem_minorArcs_iff_strictly_outside.mp hβminor)
        q a hq hqcap haq ha
    have hβabs : |β| ≤ r := (abs_le).2 hβband
    have hdist : dist (rationalCenter q a + (β : UnitAddCircle))
        (rationalCenter q a) = |β| := by
      rw [dist_eq_norm, add_sub_cancel_left]
      exact (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) one_ne_zero).2
        (by simpa using hβabs.trans hrhalf.le)
    rw [← hReq] at hminorDist
    change R < dist (rationalCenter q a + (β : UnitAddCircle))
      (rationalCenter q a) at hminorDist
    have : R < |β| := by simpa only [hdist] using hminorDist
    rw [Set.mem_union, Set.mem_Iic, Set.mem_Ioi]
    rcases (lt_or_ge β 0) with hneg | hnonneg
    · left
      rw [abs_of_neg hneg] at this
      linarith
    · right
      rw [abs_of_nonneg hnonneg] at this
      exact this
  have hg : Integrable g := by
    simpa only [g, dyadicContinuousAmplitude] using
      MAPContinuousOverlap.integrable_sq_norm_dyadicAmplitude hX
  have hmOn : IntegrableOn m s := by
    have hmcont : Continuous m := by
      dsimp [m]
      exact (continuous_const.mul
        (by simpa only [dyadicContinuousAmplitude] using
          MAPContinuousOverlap.continuous_dyadicAmplitude X)).norm.pow 2
    exact hmcont.integrableOn_Icc.mono_set Set.inter_subset_left
  have hgOn : IntegrableOn g s := hg.integrableOn
  have hcoeff := MAPMajorArcIntegratedError.norm_primeMajorCoefficient_le_one hq
  have hmg : (∫ β in s, m β) ≤ ∫ β in s, g β := by
    apply MeasureTheory.setIntegral_mono_on hmOn hgOn hsMeas
    intro β hβ
    dsimp [m, g]
    rw [norm_mul]
    have hamp0 := norm_nonneg (dyadicContinuousAmplitude X β)
    have hmul := mul_le_mul_of_nonneg_right hcoeff hamp0
    simpa only [one_mul] using pow_le_pow_left₀ (by positivity) hmul 2
  have hgtail : (∫ β in s, g β) ≤ ∫ β in tail, g β := by
    apply MeasureTheory.setIntegral_mono_set hg.integrableOn
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)
    exact Filter.Eventually.of_forall fun _ hmem => hsubset hmem
  have htailEq : (∫ β in tail, g β) =
      MAPContinuousOverlap.symmetricAmplitudeTail X R := by
    dsimp [tail, g]
    rw [MeasureTheory.setIntegral_union
      (Set.disjoint_left.2 fun x hxneg hxpos => by
        rw [Set.mem_Iic] at hxneg
        rw [Set.mem_Ioi] at hxpos
        linarith)
      measurableSet_Ioi hg.integrableOn hg.integrableOn]
    rw [← integral_comp_neg_Ioi]
    unfold MAPContinuousOverlap.symmetricAmplitudeTail
    change (∫ β in Set.Ioi R,
        ‖MAPContinuousOverlap.dyadicAmplitude X (-β)‖ ^ 2) +
      (∫ β in Set.Ioi R,
        ‖MAPContinuousOverlap.dyadicAmplitude X β‖ ^ 2) = _
    ac_rfl
  change (∫ β in s, m β) ≤ _
  calc
    _ ≤ ∫ β in s, g β := hmg
    _ ≤ ∫ β in tail, g β := hgtail
    _ = MAPContinuousOverlap.symmetricAmplitudeTail X R := htailEq
    _ ≤ 2 / (Real.pi ^ 2 * R) :=
      MAPContinuousOverlap.symmetricAmplitudeTail_le hR

theorem setIntegral_inter_eq_indicator
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s t : Set α} (hs : MeasurableSet s) (f : α → ℝ) :
    (∫ x in t ∩ s, f x ∂μ) = ∫ x in t, s.indicator f x ∂μ := by
  rw [MeasureTheory.integral_indicator hs]
  rw [Measure.restrict_restrict hs]
  rw [Set.inter_comm]

theorem perRationalNearCollar_raw_bound
    {epsilon epsilonAP X : ℝ} {B D Cc q a : ℕ}
    (hepsilonAP : 0 < epsilonAP)
    (hX : 2 ≤ X) (hlog : 2 ≤ Real.log X)
    (hlegal : Real.rpow X (2 / 15 + epsilonAP) ≤
      gallagherWindow epsilon X Cc)
    (hyone : 1 ≤ gallagherWindow epsilon X Cc)
    (hyhalf : gallagherWindow epsilon X Cc ≤ X / 2)
    (htail : collarP X D / X ≤
      1 / (8 * gallagherWindow epsilon X Cc))
    (hq : 1 ≤ q) (hqcap : (q : ℝ) ≤ collarQ X B)
    (haq : a < q) (ha : a.Coprime q) :
    (∫ alpha in rationalCollar epsilon X Cc (q, a) ∩ minorArcs X B D,
        ‖primeExponentialSum X alpha‖ ^ 2
          ∂AddCircle.haarAddCircle) ≤
      72 * (q : ℝ) ^ 2 * (apMaxIntegral B epsilonAP X).toReal +
        400 * gallagherWindow epsilon X Cc * (Real.log X) ^ 2 +
        4 * X / collarP X D := by
  let y := gallagherWindow epsilon X Cc
  let r : ℝ := 1 / (8 * y)
  let R : ℝ := collarP X D / X
  let center : UnitAddCircle := rationalCenter q a
  let pred : Set ℝ := {β : ℝ | center + (β : UnitAddCircle) ∈ minorArcs X B D}
  let s : Set ℝ := Set.Icc (-r) r ∩ pred
  let d : ℝ → ℝ := fun β => ‖signedFourierDiscrepancy X q a β‖ ^ 2
  let m : ℝ → ℝ := fun β =>
    ‖primeMajorCoefficient q * dyadicContinuousAmplitude X β‖ ^ 2
  let p : ℝ → ℝ := fun β =>
    ‖primeExponentialSum X (center + (β : UnitAddCircle))‖ ^ 2
  have hXpos : 0 < X := by linarith
  have hypos : 0 < y := zero_lt_one.trans_le hyone
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hrhalf : r < (1 : ℝ) / 2 := by
    dsimp [r]
    have : 8 * y ≥ 8 := by nlinarith
    have hinv : 1 / (8 * y) ≤ 1 / 8 := by
      exact one_div_le_one_div_of_le (by norm_num) this
    linarith
  have hPpos : 0 < collarP X D := by
    unfold collarP
    positivity
  have hRpos : 0 < R := by dsimp [R]; positivity
  have hpredMeas : MeasurableSet pred := by
    dsimp [pred, center]
    exact (MAPHarmonicEndpoint.measurableSet_minorArcs X B D).preimage
      ((continuous_const.add (AddCircle.continuous_mk' (p := (1 : ℝ)))).measurable)
  have hsMeas : MeasurableSet s := measurableSet_Icc.inter hpredMeas
  have hsourceLift :
      (∫ alpha in rationalCollar epsilon X Cc (q, a) ∩ minorArcs X B D,
          ‖primeExponentialSum X alpha‖ ^ 2
            ∂AddCircle.haarAddCircle) =
        ∫ β in s, p β := by
    rw [rationalCollar_eq_gallagherBall Cc (q, a) hXpos (by linarith)]
    change (∫ alpha in Metric.closedBall center r ∩ minorArcs X B D,
        ‖primeExponentialSum X alpha‖ ^ 2
          ∂AddCircle.haarAddCircle) = _
    rw [setIntegral_inter_eq_indicator
      (MAPHarmonicEndpoint.measurableSet_minorArcs X B D)]
    have hlift := setIntegral_closedBall_eq_intervalIntegral_lift_real
      (t := (a : ℝ) / (q : ℝ)) (R := r) hrpos.le hrhalf
      ((minorArcs X B D).indicator
        (fun alpha => ‖primeExponentialSum X alpha‖ ^ 2))
    have hlift' :
        (∫ alpha in Metric.closedBall center r,
            (minorArcs X B D).indicator
              (fun alpha => ‖primeExponentialSum X alpha‖ ^ 2) alpha
              ∂AddCircle.haarAddCircle) =
          ∫ β in -r..r,
            (minorArcs X B D).indicator
              (fun alpha => ‖primeExponentialSum X alpha‖ ^ 2)
              (center + (β : UnitAddCircle)) := by
      simpa [center, rationalCenter] using hlift
    rw [hlift']
    rw [intervalIntegral.integral_of_le (by linarith : -r ≤ r)]
    have hind : (fun β : ℝ =>
        (minorArcs X B D).indicator
          (fun alpha => ‖primeExponentialSum X alpha‖ ^ 2)
          (center + (β : UnitAddCircle))) = pred.indicator p := by
      funext β
      by_cases hβ : β ∈ pred
      · simp only [Set.indicator_of_mem hβ]
        have hcirc : center + (β : UnitAddCircle) ∈ minorArcs X B D := hβ
        simp only [Set.indicator_of_mem hcirc]
        rfl
      · simp only [Set.indicator_of_notMem hβ]
        have hcirc : center + (β : UnitAddCircle) ∉ minorArcs X B D := hβ
        simp only [Set.indicator_of_notMem hcirc]
    rw [hind]
    rw [← MeasureTheory.integral_Icc_eq_integral_Ioc]
    rw [← setIntegral_inter_eq_indicator hpredMeas]
  have hpOn : IntegrableOn p s := by
    have hpcont : Continuous p := by
      dsimp [p, center]
      exact ((MAPHarmonicEndpoint.primeExponentialSum_continuous X).comp
        (continuous_const.add (AddCircle.continuous_mk' (p := (1 : ℝ))))).norm.pow 2
    exact hpcont.integrableOn_Icc.mono_set Set.inter_subset_left
  have hdOn : IntegrableOn d s :=
    ((continuous_signedFourierDiscrepancy_lift X q a).norm.pow 2).integrableOn_Icc
      |>.mono_set Set.inter_subset_left
  have hmOn : IntegrableOn m s := by
    have hmcont : Continuous m := by
      dsimp [m]
      exact (continuous_const.mul
        (by simpa only [dyadicContinuousAmplitude] using
          MAPContinuousOverlap.continuous_dyadicAmplitude X)).norm.pow 2
    exact hmcont.integrableOn_Icc.mono_set Set.inter_subset_left
  have hsplitPoint : ∀ β ∈ s, p β ≤ 2 * d β + 2 * m β := by
    intro β hβ
    have hid : primeExponentialSum X (center + (β : UnitAddCircle)) =
        signedFourierDiscrepancy X q a β +
          primeMajorCoefficient q * dyadicContinuousAmplitude X β := by
      dsimp [center]
      unfold signedFourierDiscrepancy
      ring
    dsimp [p, d, m]
    rw [hid]
    have hn := norm_add_le
      (signedFourierDiscrepancy X q a β)
      (primeMajorCoefficient q * dyadicContinuousAmplitude X β)
    have hnsq := pow_le_pow_left₀
      (norm_nonneg (signedFourierDiscrepancy X q a β +
        primeMajorCoefficient q * dyadicContinuousAmplitude X β)) hn 2
    nlinarith [hnsq, sq_nonneg
      (‖signedFourierDiscrepancy X q a β‖ -
        ‖primeMajorCoefficient q * dyadicContinuousAmplitude X β‖)]
  have hsplitInt : (∫ β in s, p β) ≤
      2 * (∫ β in s, d β) + 2 * (∫ β in s, m β) := by
    calc
      (∫ β in s, p β) ≤ ∫ β in s, (2 * d β + 2 * m β) :=
        MeasureTheory.setIntegral_mono_on hpOn
          ((hdOn.const_mul 2).add (hmOn.const_mul 2)) hsMeas hsplitPoint
      _ = 2 * (∫ β in s, d β) + 2 * (∫ β in s, m β) := by
        rw [MeasureTheory.integral_add (hdOn.const_mul 2) (hmOn.const_mul 2),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  have hdFull : (∫ β in s, d β) ≤
      ∫ β in Set.Icc (-r) r, d β := by
    apply MeasureTheory.setIntegral_mono_set
      (((continuous_signedFourierDiscrepancy_lift X q a).norm.pow 2).integrableOn_Icc)
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)
    exact Filter.Eventually.of_forall fun _ hβ => hβ.1
  have hGallagher : (∫ β in Set.Icc (-r) r, d β) ≤
      4 / y ^ 2 * ∫ x : ℝ,
        ‖signedSlidingDiscrepancy X q a x y‖ ^ 2 := by
    dsimp [d, r]
    exact signedMeasureGallagherInequality_constant_four X y q a hXpos.le hypos
  have hwhole := wholeLineSignedSlidingEnergy_le
    (B := B) (q := q) (a := a) (epsilonAP := epsilonAP)
    (X := X) (y := y) hX (by linarith) hepsilonAP hq hqcap ha
    hyone hyhalf hlegal
  have hdBound : 2 * (∫ β in s, d β) ≤
      72 * (q : ℝ) ^ 2 * (apMaxIntegral B epsilonAP X).toReal +
        400 * y * (Real.log X) ^ 2 := by
    have hchain := hdFull.trans hGallagher
    have hmul := mul_le_mul_of_nonneg_left hchain (by norm_num : (0 : ℝ) ≤ 2)
    calc
      2 * (∫ β in s, d β) ≤
          2 * (4 / y ^ 2 * ∫ x : ℝ,
            ‖signedSlidingDiscrepancy X q a x y‖ ^ 2) := hmul
      _ ≤ 2 * (4 / y ^ 2 *
          (9 * (q : ℝ) ^ 2 * y ^ 2 *
              (apMaxIntegral B epsilonAP X).toReal +
            50 * y ^ 3 * (Real.log X) ^ 2)) := by
        gcongr
      _ = 72 * (q : ℝ) ^ 2 * (apMaxIntegral B epsilonAP X).toReal +
          400 * y * (Real.log X) ^ 2 := by field_simp; ring
  have hmBound : (∫ β in s, m β) ≤ 2 / (Real.pi ^ 2 * R) := by
    dsimp [s, pred, center, m]
    exact minorContinuousModelEnergy_le hXpos.le hRpos hrpos.le hrhalf
      hq hqcap haq ha rfl
  rw [hsourceLift]
  calc
    (∫ β in s, p β) ≤ 2 * (∫ β in s, d β) + 2 * (∫ β in s, m β) := hsplitInt
    _ ≤ (72 * (q : ℝ) ^ 2 * (apMaxIntegral B epsilonAP X).toReal +
          400 * y * (Real.log X) ^ 2) +
        2 * (2 / (Real.pi ^ 2 * R)) := by gcongr
    _ ≤ 72 * (q : ℝ) ^ 2 * (apMaxIntegral B epsilonAP X).toReal +
        400 * y * (Real.log X) ^ 2 + 4 * X / collarP X D := by
      have hpi : 1 ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
      dsimp [R]
      have hden : 0 < Real.pi ^ 2 * (collarP X D / X) := by positivity
      have htailCrude : 2 * (2 / (Real.pi ^ 2 * (collarP X D / X))) ≤
          4 * X / collarP X D := by
        calc
          2 * (2 / (Real.pi ^ 2 * (collarP X D / X))) =
              4 * X / (Real.pi ^ 2 * collarP X D) := by
                field_simp
                ring
          _ ≤ 4 * X / collarP X D := by
            gcongr
            nlinarith [mul_nonneg (sub_nonneg.mpr hpi) hPpos.le]
      linarith
    _ = 72 * (q : ℝ) ^ 2 * (apMaxIntegral B epsilonAP X).toReal +
        400 * gallagherWindow epsilon X Cc * (Real.log X) ^ 2 +
        4 * X / collarP X D := by rfl

/-- The exact remaining analytic proposition is inhabited with universal
constant `400` and threshold `2`.  The third four-term reserve is unused and
stays available for downstream bookkeeping. -/
theorem perRationalNearCollarTransfer_proved :
    PerRationalNearCollarTransfer := by
  refine ⟨400, 2, by norm_num, by norm_num, ?_⟩
  intro epsilon epsilonAP X B D Cc q a hepsilon hepsilonAP hX hlog
    hlegal hyone hyhalf htail hq hqcap haq ha
  have hraw := perRationalNearCollar_raw_bound
    hepsilonAP hX hlog hlegal hyone hyhalf htail hq hqcap haq ha
  have hAP : 0 ≤ (q : ℝ) ^ 2 *
      (apMaxIntegral B epsilonAP X).toReal := by positivity
  have hylog : 0 ≤ gallagherWindow epsilon X Cc * (Real.log X) ^ 2 := by
    positivity
  have hthird : 0 ≤ (Real.log X) ^ 4 /
      gallagherWindow epsilon X Cc := by positivity
  have hPpos : 0 < collarP X D := by
    unfold collarP
    positivity
  have hfourth : 0 ≤ X / collarP X D := by positivity
  unfold perRationalFourTermRHS
  calc
    (∫ alpha in rationalCollar epsilon X Cc (q, a) ∩ minorArcs X B D,
        ‖primeExponentialSum X alpha‖ ^ 2
          ∂AddCircle.haarAddCircle) ≤
      72 * (q : ℝ) ^ 2 * (apMaxIntegral B epsilonAP X).toReal +
        400 * gallagherWindow epsilon X Cc * (Real.log X) ^ 2 +
        4 * X / collarP X D := hraw
    _ ≤ 400 *
        ((q : ℝ) ^ 2 * (apMaxIntegral B epsilonAP X).toReal +
          gallagherWindow epsilon X Cc * (Real.log X) ^ 2 +
          (Real.log X) ^ 4 / gallagherWindow epsilon X Cc +
          X / collarP X D) := by
      ring_nf at hAP hylog hthird hfourth ⊢
      nlinarith

end
end MAPNearCollarGallagher

#print axioms MAPNearCollarGallagher.norm_rationalIntervalError_le_of_normalizedAP
#print axioms MAPNearCollarGallagher.signedSlidingDiscrepancy_eq_rationalIntervalError
#print axioms MAPNearCollarGallagher.apMaxIntegral_ne_top
#print axioms MAPNearCollarGallagher.wholeLineSignedSlidingEnergy_le
#print axioms MAPNearCollarGallagher.minorContinuousModelEnergy_le
#print axioms MAPNearCollarGallagher.perRationalNearCollar_raw_bound
#print axioms MAPNearCollarGallagher.perRationalNearCollarTransfer_proved
