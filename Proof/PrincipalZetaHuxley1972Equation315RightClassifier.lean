import PrincipalZetaHuxley1972Equation35Identity
import PrincipalZetaHuxley1972Equation315ClassifierArithmetic

/-!
# Huxley 1972 (3.5)--(3.15): the literal right-hand classifier

This module connects the already certified source identity and error bounds to
the numerical `(3.15)` lemma.  It treats only failure of the class-I blocks
`(3.12)`.  The class-II / critical-line upper bound `(3.13)` is deliberately
absent.

The factor-100 repair of the later terminal threshold remains untouched:
this local classifier argument has no `(6.10)` threshold parameter.
-/

namespace MAPPrincipalZetaHuxley1972Equation315RightClassifier

open scoped ArithmeticFunction LSeries.notation BigOperators
open MAPMollifierCoefficientIdentity MAPAppendixA4GammaEndpoint
open MAPPrincipalZetaDetectorPoleRemoval MAPPrincipalZetaPoleContour
open MAPPrincipalZetaHuxley1972Equation35Identity
open MAPPrincipalZetaHuxley1972Equation315ClassifierArithmetic

noncomputable section

local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩
local notation "chiOne" => (1 : DirichletCharacter ℂ 1)
local notation "principalF" => MAPPrincipalZetaFixedStrip.principalRegularized

/-- Literal dyadic label for an arithmetic index: the integer `j` for which
`n/Y` lies in the half-open dyadic shell selected by
`floor (log (n/Y) / log 2)`. -/
def huxleyDyadicIndex (Y : ℝ) (n : ℕ) : ℤ :=
  Int.floor (Real.log ((n : ℝ) / Y) / Real.log 2)

/-- The dyadic shells which actually meet the finite detector range
`U<n≤N`.  Empty shells are omitted, exactly as in Huxley's count of at most
`2 ell` intervals. -/
def huxleyOccupiedDyadicBlocks (U N : ℕ) (Y : ℝ) : Finset ℤ :=
  (Finset.Ico (U + 1) (N + 1)).image (huxleyDyadicIndex Y)

/-- The literal `(3.12)` sum on one occupied dyadic shell. -/
def huxleyDyadicBlockTerm
    (U N : ℕ) (rho : ℂ) (Y : ℝ) (j : ℤ) : ℂ :=
  ∑ n ∈ Finset.Ico (U + 1) (N + 1) with huxleyDyadicIndex Y n = j,
    huxleyArithmeticTerm U rho Y n

/-- Literal class-I alternative `(3.12)` on one of the occupied arithmetic
dyadic shells. -/
def HuxleyClassI
    (U N : ℕ) (rho : ℂ) (Y ell : ℝ) : Prop :=
  ∃ j ∈ huxleyOccupiedDyadicBlocks U N Y,
    (6 * ell)⁻¹ < ‖huxleyDyadicBlockTerm U N rho Y j‖

/-- The occupied dyadic fibers partition the finite range `U<n≤N`
exactly.  This is the structural equality formerly exposed as
`hblockPartition`; it uses no analytic estimate. -/
theorem huxleyFiniteBlock_eq_sum_occupiedDyadicBlocks
    (U N : ℕ) (rho : ℂ) (Y : ℝ) :
    (∑ n ∈ Finset.Ico (U + 1) (N + 1),
        huxleyArithmeticTerm U rho Y n) =
      ∑ j ∈ huxleyOccupiedDyadicBlocks U N Y,
        huxleyDyadicBlockTerm U N rho Y j := by
  unfold huxleyOccupiedDyadicBlocks huxleyDyadicBlockTerm
  exact (Finset.sum_fiberwise_of_maps_to
    (fun n hn => Finset.mem_image_of_mem (huxleyDyadicIndex Y) hn)
    (fun n => huxleyArithmeticTerm U rho Y n)).symm

/-- The infinite arithmetic tail `n>U` in (3.5) is exactly the finite block
`U<n≤N` plus the shifted far tail `n≥N+1`. -/
theorem huxleyArithmeticTail_eq_finiteBlock_add_farTail
    {U N : ℕ} (hU : 1 ≤ U) (hUN : U ≤ N)
    {rho : ℂ} (hbeta : 1 / 2 < rho.re)
    {Y : ℝ} (hY : 0 < Y) :
    (∑' n : {n // n ∉ Finset.range (U + 1)},
        huxleyArithmeticTerm U rho Y n) =
      (∑ n ∈ Finset.Ico (U + 1) (N + 1),
          huxleyArithmeticTerm U rho Y n) +
        ∑' k : ℕ, huxleyArithmeticTerm U rho Y (k + (N + 1)) := by
  let f : ℕ → ℂ := fun n => huxleyArithmeticTerm U rho Y n
  have hsumA : Summable (fun n : ℕ =>
      arithmeticDetectorTerm chiOne U rho Y n) :=
    summable_arithmeticDetectorTerm chiOne U hbeta hY
  have hsum : Summable f := by
    apply hsumA.congr
    intro n
    exact arithmeticDetectorTerm_eq_huxleyArithmeticTerm U rho Y n
  have hmain :
      ∑ n ∈ Finset.range (U + 1), f n =
        (Real.exp (-(1 / Y)) : ℂ) := by
    dsimp [f]
    simpa only [arithmeticDetectorTerm_eq_huxleyArithmeticTerm]
      using arithmeticDetectorTerm_sum_range_eq_main
        chiOne hU rho hY
  have htotalTail :
      (∑' n : ℕ, f n) =
        (Real.exp (-(1 / Y)) : ℂ) +
          ∑' n : {n // n ∉ Finset.range (U + 1)}, f n := by
    calc
      (∑' n : ℕ, f n) =
          (∑ n ∈ Finset.range (U + 1), f n) +
            ∑' n : {n // n ∉ Finset.range (U + 1)}, f n :=
        (hsum.sum_add_tsum_subtype_compl (Finset.range (U + 1))).symm
      _ = (Real.exp (-(1 / Y)) : ℂ) +
            ∑' n : {n // n ∉ Finset.range (U + 1)}, f n := by
        rw [hmain]
  have hUN' : U + 1 ≤ N + 1 := by omega
  have hfinite := Finset.sum_range_add_sum_Ico f hUN'
  have hsplit := hsum.sum_add_tsum_nat_add (N + 1)
  have htotalBlock :
      (∑' n : ℕ, f n) =
        (Real.exp (-(1 / Y)) : ℂ) +
          (∑ n ∈ Finset.Ico (U + 1) (N + 1), f n) +
            ∑' k : ℕ, f (k + (N + 1)) := by
    calc
      (∑' n : ℕ, f n) =
          (∑ n ∈ Finset.range (N + 1), f n) +
            ∑' k : ℕ, f (k + (N + 1)) := hsplit.symm
      _ = ((∑ n ∈ Finset.range (U + 1), f n) +
            ∑ n ∈ Finset.Ico (U + 1) (N + 1), f n) +
            ∑' k : ℕ, f (k + (N + 1)) := by rw [hfinite]
      _ = (Real.exp (-(1 / Y)) : ℂ) +
            (∑ n ∈ Finset.Ico (U + 1) (N + 1), f n) +
              ∑' k : ℕ, f (k + (N + 1)) := by rw [hmain]
  apply add_left_cancel (a := (Real.exp (-(1 / Y)) : ℂ))
  calc
    (Real.exp (-(1 / Y)) : ℂ) +
        (∑' n : {n // n ∉ Finset.range (U + 1)},
          huxleyArithmeticTerm U rho Y n) =
      ∑' n : ℕ, f n := by
        simpa [f] using htotalTail.symm
    _ = (Real.exp (-(1 / Y)) : ℂ) +
          (∑ n ∈ Finset.Ico (U + 1) (N + 1), f n) +
            ∑' k : ℕ, f (k + (N + 1)) := htotalBlock
    _ = (Real.exp (-(1 / Y)) : ℂ) +
          ((∑ n ∈ Finset.Ico (U + 1) (N + 1),
              huxleyArithmeticTerm U rho Y n) +
            ∑' k : ℕ,
              huxleyArithmeticTerm U rho Y (k + (N + 1))) := by
      simp only [f]
      ring

/-- Failure of every literal `(3.12)` block, the exact `(3.5)` identity,
the certified residue `(3.8)`, and far tail `(3.10)` force the right-hand
critical-line expression strictly above `1/3` in real part.

`hblockPartition` is only the finite dyadic partition equality: it contains
no estimate.  `hfailure312` is exactly the failure of the strict class-I
witness on every occupied block. -/
theorem huxleyEquation315_right_real_gt_oneThird_of_failure312
    {T Y ell : ℝ} {U N : ℕ} {rho : ℂ}
    (hT : 480 ≤ T) (hY : 15 / 2 < Y)
    (hU : 1 ≤ U) (hUN : U ≤ N)
    (hUY : (U + 1 : ℝ) ≤ 2 * Y) (hYT : Y ≤ T ^ 2)
    (hrho : principalF rho = 0)
    (hbetaLow : 7 / 10 ≤ rho.re) (hbetaHigh : rho.re ≤ 1)
    (hgamma : 100 * Real.log T ≤ |rho.im|)
    (hcut : 100 * Y * Real.log T ≤ (N + 1 : ℕ))
    {iota : Type*} [DecidableEq iota]
    (blocks : Finset iota) (blockTerm : iota → ℂ)
    (hell : 0 < ell) (hcard : (blocks.card : ℝ) ≤ 2 * ell)
    (hblockPartition :
      (∑ n ∈ Finset.Ico (U + 1) (N + 1),
          huxleyArithmeticTerm U rho Y n) =
        ∑ i ∈ blocks, blockTerm i)
    (hfailure312 : ∀ i ∈ blocks, ‖blockTerm i‖ ≤ (6 * ell)⁻¹) :
    1 / 3 <
      ((((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, principalRawDetector rho U Y
          (((1 / 2 - rho.re : ℝ) : ℂ) + t * Complex.I))).re := by
  have hYone : 1 ≤ Y := by linarith
  have hYpos : 0 < Y := by linarith
  have hbeta : 1 / 2 < rho.re := by linarith
  have hid := huxleyEquation35_full_identity hU hrho
    hbetaLow hbetaHigh hYone
  have hsplit := huxleyArithmeticTail_eq_finiteBlock_add_farTail
    hU hUN hbeta hYpos
  have hresidue := huxleyEquation38_residue_le_oneTenth
    hT hYone hUY hYT hrho hbetaLow hbetaHigh hgamma
  have htail := huxleyEquation310_farTail_le_oneTenth
    hT hYone hUY hYT (by linarith : 0 ≤ rho.re) hcut
  let mainTerm : ℂ := (Real.exp (-(1 / Y)) : ℂ)
  let residueTerm : ℂ := -principalDetectorResidue rho U Y
  let tailTerm : ℂ :=
    ∑' k : ℕ, huxleyArithmeticTerm U rho Y (k + (N + 1))
  let right : ℂ :=
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ t : ℝ, principalRawDetector rho U Y
        (((1 / 2 - rho.re : ℝ) : ℂ) + t * Complex.I))
  have hmain : 1 - 1 / Y ≤ mainTerm.re := by
    dsimp [mainTerm]
    simpa [sub_eq_add_neg, add_comm] using
      Real.add_one_le_exp (-(1 / Y))
  have hresidue' : ‖residueTerm‖ ≤ 1 / 10 := by
    simpa [residueTerm] using hresidue
  have htail' : ‖tailTerm‖ ≤ 1 / 10 := by
    simpa [tailTerm] using htail
  have hright : right = mainTerm + residueTerm + tailTerm +
      ∑ i ∈ blocks, blockTerm i := by
    dsimp [right, mainTerm, residueTerm, tailTerm]
    rw [hsplit, hblockPartition] at hid
    linear_combination hid.symm
  exact equation315_right_real_gt_oneThird_of_source_bounds
    blocks blockTerm hY hell hcard hfailure312 hmain hresidue' htail' hright

/-- Source-facing right classifier using the literal dyadic blocks.  The
partition equality is now internal.  Apart from source scale and cardinality
conditions, the sole classifier-branch hypothesis is failure of every strict
`(3.12)` inequality. -/
theorem huxleyEquation315_right_real_gt_oneThird_of_literal_failure312
    {T Y ell : ℝ} {U N : ℕ} {rho : ℂ}
    (hT : 480 ≤ T) (hY : 15 / 2 < Y)
    (hU : 1 ≤ U) (hUN : U ≤ N)
    (hUY : (U + 1 : ℝ) ≤ 2 * Y) (hYT : Y ≤ T ^ 2)
    (hrho : principalF rho = 0)
    (hbetaLow : 7 / 10 ≤ rho.re) (hbetaHigh : rho.re ≤ 1)
    (hgamma : 100 * Real.log T ≤ |rho.im|)
    (hcut : 100 * Y * Real.log T ≤ (N + 1 : ℕ))
    (hell : 0 < ell)
    (hcard : (huxleyOccupiedDyadicBlocks U N Y).card ≤
      ⌊2 * ell⌋₊)
    (hfailure312 : ∀ j ∈ huxleyOccupiedDyadicBlocks U N Y,
      ‖huxleyDyadicBlockTerm U N rho Y j‖ ≤ (6 * ell)⁻¹) :
    1 / 3 <
      ((((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, principalRawDetector rho U Y
          (((1 / 2 - rho.re : ℝ) : ℂ) + t * Complex.I))).re := by
  have hcardReal :
      ((huxleyOccupiedDyadicBlocks U N Y).card : ℝ) ≤ 2 * ell := by
    calc
      ((huxleyOccupiedDyadicBlocks U N Y).card : ℝ) ≤
          (⌊2 * ell⌋₊ : ℝ) := by exact_mod_cast hcard
      _ ≤ 2 * ell := Nat.floor_le (by positivity)
  exact huxleyEquation315_right_real_gt_oneThird_of_failure312
    hT hY hU hUN hUY hYT hrho hbetaLow hbetaHigh hgamma hcut
    (huxleyOccupiedDyadicBlocks U N Y)
    (huxleyDyadicBlockTerm U N rho Y) hell hcardReal
    (huxleyFiniteBlock_eq_sum_occupiedDyadicBlocks U N rho Y)
    hfailure312

/-- Final right-half classifier: after the literal dyadic partition has been
certified internally, the only classifier-branch hypothesis is
`not HuxleyClassI`, i.e. failure of every strict `(3.12)` witness. -/
theorem huxleyEquation315_right_real_gt_oneThird_of_not_classI
    {T Y ell : ℝ} {U N : ℕ} {rho : ℂ}
    (hT : 480 ≤ T) (hY : 15 / 2 < Y)
    (hU : 1 ≤ U) (hUN : U ≤ N)
    (hUY : (U + 1 : ℝ) ≤ 2 * Y) (hYT : Y ≤ T ^ 2)
    (hrho : principalF rho = 0)
    (hbetaLow : 7 / 10 ≤ rho.re) (hbetaHigh : rho.re ≤ 1)
    (hgamma : 100 * Real.log T ≤ |rho.im|)
    (hcut : 100 * Y * Real.log T ≤ (N + 1 : ℕ))
    (hell : 0 < ell)
    (hcard : (huxleyOccupiedDyadicBlocks U N Y).card ≤
      ⌊2 * ell⌋₊)
    (hnotClassI : ¬ HuxleyClassI U N rho Y ell) :
    1 / 3 <
      ((((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, principalRawDetector rho U Y
          (((1 / 2 - rho.re : ℝ) : ℂ) + t * Complex.I))).re := by
  apply huxleyEquation315_right_real_gt_oneThird_of_literal_failure312
    hT hY hU hUN hUY hYT hrho hbetaLow hbetaHigh hgamma hcut hell hcard
  intro j hj
  by_contra hbound
  apply hnotClassI
  exact ⟨j, hj, lt_of_not_ge hbound⟩

end

end MAPPrincipalZetaHuxley1972Equation315RightClassifier

#print axioms MAPPrincipalZetaHuxley1972Equation315RightClassifier.huxleyArithmeticTail_eq_finiteBlock_add_farTail
#print axioms MAPPrincipalZetaHuxley1972Equation315RightClassifier.huxleyEquation315_right_real_gt_oneThird_of_failure312
#print axioms MAPPrincipalZetaHuxley1972Equation315RightClassifier.huxleyFiniteBlock_eq_sum_occupiedDyadicBlocks
#print axioms MAPPrincipalZetaHuxley1972Equation315RightClassifier.huxleyEquation315_right_real_gt_oneThird_of_literal_failure312
#print axioms MAPPrincipalZetaHuxley1972Equation315RightClassifier.huxleyEquation315_right_real_gt_oneThird_of_not_classI
