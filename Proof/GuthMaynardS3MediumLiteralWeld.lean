import GuthMaynardJIterationMediumRegionTailInsertion
import GuthMaynardJIterationMediumLocalizedPairs
import GuthMaynardS3ZeroEllSupport
import GuthMaynardS3LiteralLemma92NonzeroMedium

open scoped BigOperators Real FourierTransform ContDiff
open MeasureTheory

noncomputable section
namespace GuthMaynardS3MediumLiteralWeld

open GuthMaynardJIteration
open GuthMaynardS3ZeroEllSupport
open GuthMaynardS3LiteralLemma92NonzeroMedium

/-! A deterministic medium weld for the literal localized pair sum.

The two functions `z` and `n` are intended to be the exact `ell = 0` and
`ell ≠ 0` sums from the source pair mask.  The theorem takes their integral
bounds explicitly, so the zero-ell narrow band and the nonzero divisor/Sigma-II
producer remain separate obligations.  No `hwindowBelowMedium` or centered
collar inclusion is used.
-/

theorem integral_norm_sq_le_two_add
    (S : Set ℝ) (r z n : ℝ → ℂ)
    (hS : MeasurableSet S)
    (hr : IntegrableOn (fun xi => ‖r xi‖ ^ 2) S)
    (hz : IntegrableOn (fun xi => ‖z xi‖ ^ 2) S)
    (hn : IntegrableOn (fun xi => ‖n xi‖ ^ 2) S)
    (hsplit : ∀ xi ∈ S, r xi = z xi + n xi) :
    (∫ xi in S, ‖r xi‖ ^ 2) ≤
      2 * (∫ xi in S, ‖z xi‖ ^ 2) +
      2 * (∫ xi in S, ‖n xi‖ ^ 2) := by
  have hmajor : IntegrableOn
      (fun xi => 2 * ‖z xi‖ ^ 2 + 2 * ‖n xi‖ ^ 2) S := by
    exact (hz.const_mul 2).add (hn.const_mul 2)
  have hpoint : ∀ xi ∈ S,
      ‖r xi‖ ^ 2 ≤ 2 * ‖z xi‖ ^ 2 + 2 * ‖n xi‖ ^ 2 := by
    intro xi hxi
    rw [hsplit xi hxi]
    have hnorm : ‖z xi + n xi‖ ≤ ‖z xi‖ + ‖n xi‖ :=
      norm_add_le _ _
    have hnormsq : ‖z xi + n xi‖ ^ 2 ≤
        (‖z xi‖ + ‖n xi‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    exact hnormsq.trans (by
      nlinarith [sq_nonneg (‖z xi‖ - ‖n xi‖)])
  calc
    (∫ xi in S, ‖r xi‖ ^ 2) ≤
        ∫ xi in S, (2 * ‖z xi‖ ^ 2 + 2 * ‖n xi‖ ^ 2) :=
      setIntegral_mono_on hr hmajor hS hpoint
    _ = 2 * (∫ xi in S, ‖z xi‖ ^ 2) +
        2 * (∫ xi in S, ‖n xi‖ ^ 2) := by
      rw [integral_add (hz.const_mul 2) (hn.const_mul 2)]
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]

theorem medium_integral_le_split_bounds
    (S : Set ℝ) (g r z n : ℝ → ℂ) (tail Z N : ℝ)
    (hS : MeasurableSet S)
    (hfull : IntegrableOn (fun xi => ‖g xi‖ ^ 2) S)
    (hr : IntegrableOn (fun xi => ‖r xi‖ ^ 2) S)
    (hz : IntegrableOn (fun xi => ‖z xi‖ ^ 2) S)
    (hn : IntegrableOn (fun xi => ‖n xi‖ ^ 2) S)
    (hsplit : ∀ xi ∈ S, r xi = z xi + n xi)
    (happrox : (∫ xi in S, ‖g xi‖ ^ 2) ≤
      2 * (∫ xi in S, ‖r xi‖ ^ 2) + tail)
    (hZ : (∫ xi in S, ‖z xi‖ ^ 2) ≤ Z)
    (hN : (∫ xi in S, ‖n xi‖ ^ 2) ≤ N)
    (hZ0 : 0 ≤ Z) (hN0 : 0 ≤ N) :
    (∫ xi in S, ‖g xi‖ ^ 2) ≤ 4 * Z + 4 * N + tail := by
  have hsplitBound := integral_norm_sq_le_two_add S r z n hS hr hz hn hsplit
  have hR0 : 0 ≤ (∫ xi in S, ‖r xi‖ ^ 2) :=
    setIntegral_nonneg hS (fun _ _ => sq_nonneg _)
  have hRbound : (∫ xi in S, ‖r xi‖ ^ 2) ≤ 2 * Z + 2 * N := by
    calc
      (∫ xi in S, ‖r xi‖ ^ 2) ≤
          2 * (∫ xi in S, ‖z xi‖ ^ 2) +
          2 * (∫ xi in S, ‖n xi‖ ^ 2) := hsplitBound
      _ ≤ 2 * Z + 2 * N := by gcongr
  calc
    (∫ xi in S, ‖g xi‖ ^ 2) ≤
        2 * (∫ xi in S, ‖r xi‖ ^ 2) + tail := happrox
    _ ≤ 2 * (2 * Z + 2 * N) + tail := by gcongr
    _ = 4 * Z + 4 * N + tail := by ring

/-! Sigma-II form of the same weld.  The nonzero-ell Cauchy estimate is an
explicit premise, ready for `setIntegral_norm_sourceFirstPoissonLocalizedPairSum_sq_le_sigmaII`
with `nonzeroEllRange ellRange`; the zero-ell integral is a separate scalar.
-/
theorem medium_integral_le_nonzeroSigmaII_add_zero
    (S : Set ℝ) (g r z n : ℝ → ℂ) (tail Z : ℝ)
    (P N1 M1 M3 Kpsi Sigma : ℝ)
    (hS : MeasurableSet S)
    (hfull : IntegrableOn (fun xi => ‖g xi‖ ^ 2) S)
    (hr : IntegrableOn (fun xi => ‖r xi‖ ^ 2) S)
    (hz : IntegrableOn (fun xi => ‖z xi‖ ^ 2) S)
    (hn : IntegrableOn (fun xi => ‖n xi‖ ^ 2) S)
    (hsplit : ∀ xi ∈ S, r xi = z xi + n xi)
    (happrox : (∫ xi in S, ‖g xi‖ ^ 2) ≤
      2 * (∫ xi in S, ‖r xi‖ ^ 2) + tail)
    (hZ : (∫ xi in S, ‖z xi‖ ^ 2) ≤ Z)
    (hN : (∫ xi in S, ‖n xi‖ ^ 2) ≤
      P * (N1 * (M3 * Kpsi ^ 2 / M1)) * Sigma)
    (hZ0 : 0 ≤ Z) (hP : 0 ≤ P) (hN10 : 0 ≤ N1)
    (hM10 : 0 < M1) (hM30 : 0 < M3) (hKpsi0 : 0 ≤ Kpsi)
    (hSigma0 : 0 ≤ Sigma) :
    (∫ xi in S, ‖g xi‖ ^ 2) ≤
      4 * (P * (N1 * (M3 * Kpsi ^ 2 / M1)) * Sigma) +
      4 * Z + tail := by
  have hraw := medium_integral_le_split_bounds S g r z n tail Z
    (P * (N1 * (M3 * Kpsi ^ 2 / M1)) * Sigma)
    hS hfull hr hz hn hsplit happrox hZ hN hZ0
    (by positivity)
  simpa [add_assoc, add_comm, add_left_comm] using hraw

/-! Actual-mask downstream interface.  `hnonzeroSigma` is the Cauchy-to-
Sigma-II estimate on `nonzeroEllRange ellRange`; `hzero` is the separate
narrow-band producer. -/
theorem medium_integral_le_actual_nonzeroSigmaII_add_zero
    (S : Set ℝ) (g r : ℝ → ℂ)
    (m1Range ellRange m2Range : Finset ℤ) (F fhat : ℝ → ℂ)
    (tail Z P N1 M1 M3 B Kpsi Sigma : ℝ)
    (hS : MeasurableSet S)
    (hfull : IntegrableOn (fun xi => ‖g xi‖ ^ 2) S)
    (hr : IntegrableOn (fun xi => ‖r xi‖ ^ 2) S)
    (hzeroInt : IntegrableOn (fun xi =>
      ‖sourceMediumZeroEllSum m1Range ellRange m2Range F fhat M3 B xi‖ ^ 2) S)
    (hnonzeroInt : IntegrableOn (fun xi =>
      ‖sourceMediumNonzeroEllSum m1Range ellRange m2Range F fhat M3 B xi‖ ^ 2) S)
    (happrox : (∫ xi in S, ‖g xi‖ ^ 2) ≤
      2 * (∫ xi in S, ‖r xi‖ ^ 2) + tail)
    (hzero : (∫ xi in S,
      ‖sourceMediumZeroEllSum m1Range ellRange m2Range F fhat M3 B xi‖ ^ 2) ≤ Z)
    (hnonzeroSigma : (∫ xi in S,
      ‖sourceMediumNonzeroEllSum m1Range ellRange m2Range F fhat M3 B xi‖ ^ 2) ≤
      P * (N1 * (M3 * Kpsi ^ 2 / M1)) * Sigma)
    (hZ0 : 0 ≤ Z) (hP : 0 ≤ P) (hN10 : 0 ≤ N1)
    (hM10 : 0 < M1) (hM30 : 0 < M3) (hKpsi0 : 0 ≤ Kpsi)
    (hSigma0 : 0 ≤ Sigma)
    (hsplit : ∀ xi ∈ S,
      r xi = sourceMediumZeroEllSum m1Range ellRange m2Range F fhat M3 B xi +
        sourceMediumNonzeroEllSum m1Range ellRange m2Range F fhat M3 B xi) :
    (∫ xi in S, ‖g xi‖ ^ 2) ≤
      4 * (P * (N1 * (M3 * Kpsi ^ 2 / M1)) * Sigma) +
      4 * Z + tail := by
  exact medium_integral_le_nonzeroSigmaII_add_zero S g r
    (sourceMediumZeroEllSum m1Range ellRange m2Range F fhat M3 B)
    (sourceMediumNonzeroEllSum m1Range ellRange m2Range F fhat M3 B)
    tail Z P N1 M1 M3 Kpsi Sigma hS hfull hr hzeroInt hnonzeroInt
    hsplit happrox hzero hnonzeroSigma hZ0 hP hN10 hM10 hM30 hKpsi0 hSigma0

/-! The exact defeq bridge needed before applying the baseline Sigma-II
consumer: filtering the full pair mask by `p.2 ≠ 0` is the same as filtering
the ell range first. -/
theorem sourceMediumNonzeroEllSum_eq_nonzeroEllRange_localizedPairSum
    (m1Range ellRange m2Range : Finset ℤ) (F fhat : ℝ → ℂ)
    (M3 B xi : ℝ) :
    sourceMediumZeroEllSum m1Range ellRange m2Range F fhat M3 B xi +
      sourceMediumNonzeroEllSum m1Range ellRange m2Range F fhat M3 B xi =
      sourceFirstPoissonLocalizedPairSum m1Range ellRange m2Range F fhat M3 B xi := by
  exact (sourceFirstPoissonLocalizedPairSum_eq_zeroEll_add_nonzeroEll
    m1Range ellRange m2Range F fhat M3 B xi).symm

theorem sourceMediumNonzeroEllSum_eq_nonzeroRange_sum
    (m1Range ellRange m2Range : Finset ℤ) (F fhat : ℝ → ℂ)
    (M3 B xi : ℝ) :
    sourceMediumNonzeroEllSum m1Range ellRange m2Range F fhat M3 B xi =
    sourceFirstPoissonLocalizedPairSum m1Range
        (nonzeroEllRange ellRange) m2Range F fhat M3 B xi := by
  have hmask :
      (sourceMediumLocalizedPairs m1Range ellRange M3 B xi).filter
          (fun p => p.2 ≠ 0) =
        sourceMediumLocalizedPairs m1Range (nonzeroEllRange ellRange)
          M3 B xi := by
    ext p
    simp [sourceMediumLocalizedPairs, nonzeroEllRange, and_assoc,
      and_left_comm, and_comm]
  unfold sourceMediumNonzeroEllSum sourceFirstPoissonLocalizedPairSum
  rw [hmask]

/-! Literal Cauchy-to-Sigma-II estimate on the nonzero-ell slice. -/
theorem sourceMediumNonzeroEllSum_integral_le_sigmaII
    (S : Set ℝ) (m1Range ellRange m2Range : Finset ℤ)
    (F fhat : ℝ → ℂ) (psi2 : ℝ → ℝ) (M2 T : ℝ)
    {M1 M3 B Kpsi P N1 : ℝ}
    (hfhat : Continuous fhat) (hS : MeasurableSet S)
    (hM1 : 0 < M1) (hM3 : 0 < M3) (hB : 0 ≤ B)
    (hKpsi : 0 ≤ Kpsi) (hP : 0 ≤ P) (hN1 : 0 ≤ N1)
    (hF : ∀ z, ‖F z‖ ≤ Kpsi)
    (hm1 : ∀ m1 ∈ m1Range, m1 ≠ 0)
    (hm1lo : ∀ m1 ∈ m1Range, M1 ≤ |(m1 : ℝ)|)
    (hm2pos : ∀ m2 ∈ m2Range, 0 < m2)
    (hcard1 : (m1Range.card : ℝ) ≤ N1)
    (hpairCard : ∀ xi ∈ S,
      ((sourceMediumLocalizedPairs m1Range (nonzeroEllRange ellRange)
        M3 B xi).card : ℝ) ≤ P)
    (hpsi2 : ∀ ell ∈ nonzeroEllRange ellRange,
      1 ≤ psi2 (M2 * (ell : ℝ) / T))
    (hleft : IntegrableOn (fun xi =>
      ‖sourceFirstPoissonLocalizedPairSum m1Range
        (nonzeroEllRange ellRange) m2Range F fhat M3 B xi‖ ^ 2) S) :
    (∫ xi in S,
      ‖sourceMediumNonzeroEllSum m1Range ellRange m2Range F fhat M3 B xi‖ ^ 2) ≤
      P * (N1 * (M3 * Kpsi ^ 2 / M1)) *
        sigmaIIFinite (nonzeroEllRange ellRange) m2Range psi2 fhat M2 T M3 B := by
  have hfun :
      (fun xi : ℝ =>
        sourceMediumNonzeroEllSum m1Range ellRange m2Range F fhat M3 B xi) =
      (fun xi : ℝ =>
        sourceFirstPoissonLocalizedPairSum m1Range
          (nonzeroEllRange ellRange) m2Range F fhat M3 B xi) := by
    funext xi
    exact sourceMediumNonzeroEllSum_eq_nonzeroRange_sum
      m1Range ellRange m2Range F fhat M3 B xi
  have hintegrand :
      (fun xi : ℝ =>
        ‖sourceMediumNonzeroEllSum m1Range ellRange m2Range F fhat M3 B xi‖ ^ 2) =
      (fun xi : ℝ =>
        ‖sourceFirstPoissonLocalizedPairSum m1Range
          (nonzeroEllRange ellRange) m2Range F fhat M3 B xi‖ ^ 2) := by
    funext xi
    rw [sourceMediumNonzeroEllSum_eq_nonzeroRange_sum]
  rw [hintegrand]
  exact setIntegral_norm_sourceFirstPoissonLocalizedPairSum_sq_le_sigmaII
    m1Range (nonzeroEllRange ellRange) m2Range F fhat hfhat S hS psi2 M2 T
    hM1 hM3 hB hKpsi hP hN1 hF hm1 hm1lo hm2pos hcard1 hpairCard hpsi2 hleft

end GuthMaynardS3MediumLiteralWeld
