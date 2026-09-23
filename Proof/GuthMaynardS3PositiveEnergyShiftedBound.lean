import GuthMaynardS3FixedEnergyRecurrence
import GuthMaynardS3EnergyNormalization
import GuthMaynardS3ScaledWideOrbit
import GuthMaynardFiniteSqrtBootstrap
import GuthMaynardS3FiniteEndcap
import GuthMaynardS3PositiveFourierBridge

open scoped BigOperators Real FourierTransform ContDiff
open MeasureTheory

noncomputable section
set_option maxHeartbeats 2000000
namespace GuthMaynardS3PositiveEnergyShiftedBound

open GuthMaynardJIteration
open GuthMaynardS3FixedEnergyRecurrence
open GuthMaynardS3EnergyNormalization
open GuthMaynardS3ScaledWideOrbit
open GuthMaynardS3ScaledWideProfile
open GuthMaynardS3LiteralProfileFourier
open GuthMaynardS3PositiveFourierBridge

/-- Finite positive-coordinate energy closure along the literal scaled wide
orbit, with the explicit inverse-power remainder retained in the denominator. -/
theorem scaledWideOrbit_positive_energy_shifted_bound
    {eta delta : ℝ} (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hdelta : 0 < delta) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (T B : ℝ) (W : Finset ℝ) (M N r : ℕ),
        7 ≤ T → 4 ≤ B → B ≤ T →
        4 * (W.card : ℝ) ^ 2 ≤ T ^ (4 : ℝ) →
        16 * (M : ℝ) ≤ T → Real.rpow T delta ≤ T →
        (N : ℝ) * (2 * Real.rpow T delta / T) ≤ 1 / 4 →
        1 ≤ M →
        r ≤ N →
        (hRpos : 0 < Real.rpow T delta) →
        sourceFiniteAffineEnergy (sourcePositiveDyadicRange M)
            (sourcePositiveDyadicRange M) (sourceCenteredRange (16 * M))
            (scaledWideOrbit B T delta hRpos W r) ≤
          (M : ℝ) ^ 4 *
            (max 1 (max
              (2 * (C * (16 : ℝ) ^ 6 * T ^ (3 * eta) + C))
              (4 * (C * T ^ (4 * eta + delta) * (16 : ℝ) ^ 2) ^ 2)) *
            iterSqrt (N - r) (max 1 (
              (34848 * T ^ 2) /
                max 1 (max
                  (2 * (C * (16 : ℝ) ^ 6 * T ^ (3 * eta) + C))
                  (4 * (C * T ^ (4 * eta + delta) * (16 : ℝ) ^ 2) ^ 2)))) *
            ((M : ℝ) ^ 2 *
                (∫ u : ℝ, scaledWideOrbit B T delta hRpos W 0 u) ^ 2 +
              (∫ u : ℝ, scaledWideOrbit B T delta hRpos W 0 u ^ 2) +
              1 / T ^ 100)) := by
  let Cdec : ℕ → ℝ :=
    fun q => (4 : ℝ) ^ q * lemma84SmoothingFourierConstant q
  have hCdec : ∀ q, 0 ≤ Cdec q := by
    intro q
    dsimp [Cdec]
    exact mul_nonneg (pow_nonneg (by norm_num) _)
      (lemma84SmoothingFourierConstant_nonneg q)
  obtain ⟨C, hC, hstep⟩ :=
    signed_energy_step_uniform Cdec hCdec heta heta1 hdelta
  refine ⟨C, hC, ?_⟩
  intro T B W M N r hT7 hB4 hBT hSgrowth hMT hdT hNiter hM hrN hRpos
  have hT1 : 1 ≤ T := by linarith
  have hTpos : 0 < T := by linarith
  have hMpos : 0 < M := by omega
  have hMreal : 0 < (M : ℝ) := by exact_mod_cast hMpos
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hM16 : (M : ℝ) ≤ 16 * (M : ℝ) := by nlinarith
  let f : ℕ → ℝ → ℝ :=
    fun n => scaledWideOrbit B T delta hRpos W (r + n)
  let L0 : ℝ := ∫ u : ℝ, scaledWideOrbit B T delta hRpos W 0 u
  let Q0 : ℝ := ∫ u : ℝ, scaledWideOrbit B T delta hRpos W 0 u ^ 2
  let D0 : ℝ := (M : ℝ) ^ 2 * L0 ^ 2 + Q0 + 1 / T ^ 100
  let A : ℝ := C * (16 : ℝ) ^ 6 * T ^ (3 * eta) + C
  let Bcoef : ℝ := C * T ^ (4 * eta + delta) * (16 : ℝ) ^ 2
  let Dscale : ℝ := max 1 (max (2 * A) (4 * Bcoef ^ 2))
  have hf0 := scaledWideOrbit_admissible hT1 hB4 hBT hdelta.le W 0
  have hL0 : 0 ≤ L0 := by
    dsimp [L0]
    exact integral_nonneg (fun u =>
      (scaledWideOrbit_admissible hT1 hB4 hBT hdelta.le W 0).nonneg u)
  have hQ0 : 0 ≤ Q0 := by
    dsimp [Q0]
    exact integral_nonneg (fun u => sq_nonneg _)
  have hrem : 0 < 1 / T ^ 100 := by positivity
  have hD0 : 0 < D0 := by
    dsimp [D0]
    exact add_pos_of_nonneg_of_pos
      (add_nonneg (by positivity) hQ0) hrem
  have hden : 0 < (M : ℝ) ^ 4 * D0 := by positivity
  have hL0D : (M : ℝ) ^ 2 * L0 ^ 2 ≤ D0 := by
    dsimp [D0]
    have hp : 0 ≤ (M : ℝ) ^ 2 * L0 ^ 2 := by positivity
    linarith [hQ0, hrem.le]
  have hQ0D : Q0 ≤ D0 := by
    dsimp [D0]
    have hp : 0 ≤ (M : ℝ) ^ 2 * L0 ^ 2 := by positivity
    linarith [hp, hrem.le]
  have hremD : 1 / T ^ 100 ≤ D0 := by
    dsimp [D0]
    have hp : 0 ≤ (M : ℝ) ^ 2 * L0 ^ 2 := by positivity
    linarith [hp, hQ0]
  have hMpow : 1 ≤ (M : ℝ) ^ 4 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hM1 4
    simpa using this
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hB : 0 ≤ Bcoef := by
    dsimp [Bcoef]
    positivity
  have hDscale : 1 ≤ Dscale := by
    dsimp [Dscale]
    exact le_max_left _ _
  have hX : ∀ n, 0 ≤
      sourceFiniteAffineEnergy (sourcePositiveDyadicRange M)
        (sourcePositiveDyadicRange M) (sourceCenteredRange (16 * M)) (f n) /
        ((M : ℝ) ^ 4 * D0) := by
    intro n
    apply div_nonneg
    · exact integral_nonneg (fun u => sq_nonneg _)
    · exact hden.le
  have hrec : ∀ n, n < N - r →
      sourceFiniteAffineEnergy (sourcePositiveDyadicRange M)
        (sourcePositiveDyadicRange M) (sourceCenteredRange (16 * M)) (f n) /
        ((M : ℝ) ^ 4 * D0) ≤
      A + Bcoef * Real.sqrt (
        sourceFiniteAffineEnergy (sourcePositiveDyadicRange M)
          (sourcePositiveDyadicRange M) (sourceCenteredRange (16 * M)) (f (n + 1)) /
          ((M : ℝ) ^ 4 * D0)) := by
    intro n hn
    have hnN : (r + n : ℕ) ≤ N := by omega
    have hF2 : (7 : ℝ) / 4 + (r + n : ℝ) *
        (2 * Real.rpow T delta / T) ≤ 2 := by
      have hfactor : 0 ≤ 2 * Real.rpow T delta / T := by positivity
      have hprod := mul_le_mul_of_nonneg_right hNiter hfactor
      have hidx : (r + n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnN
      nlinarith
    have hfn : SourceAdmissibleProfile T (4 * (W.card : ℝ)^2)
        (7 / 4 + (r + n : ℝ) * (2 * Real.rpow T delta / T)) (f n) := by
      simpa [f] using (scaledWideOrbit_admissible hT1 hB4 hBT hdelta.le W (r+n))
    have hcontract := scaledWideOrbit_L1_L2_contractions
      hT1 hB4 hBT hdelta.le W (r+n)
    have hLn0 : 0 ≤ ∫ u : ℝ, f n u := by
      dsimp [f]
      exact integral_nonneg (fun u =>
        (scaledWideOrbit_admissible hT1 hB4 hBT hdelta.le W (r+n)).nonneg u)
    have hLn : ∫ u : ℝ, f n u ≤ L0 := by
      dsimp [f, L0]
      exact hcontract.1
    have hQn : ∫ u : ℝ, f n u ^ 2 ≤ Q0 := by
      dsimp [f, Q0]
      exact hcontract.2
    have hQn0 : 0 ≤ ∫ u : ℝ, f n u ^ 2 :=
      integral_nonneg (fun u => sq_nonneg _)
    have hLn_sq : (∫ u : ℝ, f n u) ^ 2 ≤ L0 ^ 2 := by
      exact (sq_le_sq₀ hLn0 hL0).2 hLn
    have hLD : (M : ℝ) ^ 2 * (∫ u : ℝ, f n u) ^ 2 ≤ D0 := by
      calc
        (M : ℝ) ^ 2 * (∫ u : ℝ, f n u) ^ 2 ≤
            (M : ℝ) ^ 2 * L0 ^ 2 :=
          mul_le_mul_of_nonneg_left hLn_sq (by positivity)
        _ ≤ D0 := hL0D
    have hQD : (∫ u : ℝ, f n u ^ 2) ≤ D0 :=
      hQn.trans hQ0D
    have hdec : ∀ q : ℕ, ∀ z : ℝ, z ≠ 0 →
        ‖FourierTransform.fourier (fun u : ℝ => (f n u : ℂ)) z‖ ≤
          Cdec q * T ^ eta * (T / |z|) ^ q *
            (4 * (W.card : ℝ) ^ 2) := by
      intro q z hz
      dsimp [f, Cdec]
      exact scaledWideOrbit_fourier_bound hT1 hB4 hBT hdelta.le W (r+n) q heta hz
    have hraw := hstep T (4 * (W.card : ℝ) ^ 2)
      (7 / 4 + (r+n : ℝ) * (2 * Real.rpow T delta / T)) (f n) M M
      hT7 (by positivity) hF2 (by positivity) hSgrowth
      hM hM (by omega) hMT hdT hfn hdec
    have hpos := positive_energy_le_signed hfn hMpos hMpos (M3 := 16 * M)
    have hstep0 := hpos.trans hraw
    have hnorm :
        (∫ u : ℝ, ‖(f n u : ℂ)‖) = ∫ u : ℝ, f n u := by
      apply integral_congr_ae
      filter_upwards [] with u
      have hu : 0 ≤ f n u := by
        dsimp [f]
        exact (scaledWideOrbit_admissible hT1 hB4 hBT hdelta.le W (r+n)).nonneg u
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu]
    rw [hnorm] at hstep0
    have hE' : 0 ≤ sourceFiniteAffineEnergy (sourcePositiveDyadicRange M)
        (sourcePositiveDyadicRange M) (sourceCenteredRange (16 * M)) (f (n + 1)) := by
      exact integral_nonneg (fun u => sq_nonneg _)
    have hnext :
        sourceFiniteAffineEnergy (sourcePositiveDyadicRange M)
          (sourcePositiveDyadicRange M) (sourceCenteredRange (16 * M)) (f n) ≤
        (C * (16 : ℝ) ^ 6 * T ^ (3 * eta)) * (M : ℝ) ^ 6 *
            (∫ u : ℝ, f n u) ^ 2 +
          Bcoef * (M : ℝ) ^ 2 * Real.sqrt
            ((∫ u : ℝ, f n u ^ 2) *
              sourceFiniteAffineEnergy (sourcePositiveDyadicRange M)
                (sourcePositiveDyadicRange M) (sourceCenteredRange (16 * M))
                (affineSmoothing T (sourceBumpNormalized (Real.rpow T delta) hRpos) (f n))) +
          C / T ^ 100 := by
      dsimp [Bcoef]
      convert hstep0 using 1 <;> ring_nf
    have hnext' : sourceFiniteAffineEnergy (sourcePositiveDyadicRange M)
        (sourcePositiveDyadicRange M) (sourceCenteredRange (16 * M))
        (f (n + 1)) =
        sourceFiniteAffineEnergy (sourcePositiveDyadicRange M)
          (sourcePositiveDyadicRange M) (sourceCenteredRange (16 * M))
          (affineSmoothing T (sourceBumpNormalized (Real.rpow T delta) hRpos) (f n)) := by
      rfl
    rw [← hnext'] at hnext
    apply normalized_energy_step
      (m := (M : ℝ)) (D := D0) (L := ∫ u : ℝ, f n u)
      (Q := ∫ u : ℝ, f n u ^ 2)
      (E := sourceFiniteAffineEnergy (sourcePositiveDyadicRange M)
        (sourcePositiveDyadicRange M) (sourceCenteredRange (16 * M)) (f n))
      (E' := sourceFiniteAffineEnergy (sourcePositiveDyadicRange M)
        (sourcePositiveDyadicRange M) (sourceCenteredRange (16 * M)) (f (n + 1)))
      (a := C * (16 : ℝ) ^ 6 * T ^ (3 * eta))
      (b := Bcoef) (c := C) (r := C / T ^ 100)
      hMreal hD0 hQn0 hE' (by positivity) hB hLD hQD
    · have hCD : C * (1 / T ^ 100) ≤ C * D0 :=
        mul_le_mul_of_nonneg_left hremD hC.le
      have hscale : C * D0 ≤ C * ((M : ℝ) ^ 4 * D0) := by
        have hMD : D0 ≤ (M : ℝ) ^ 4 * D0 := by
          nlinarith [hMpow, hD0.le]
        exact mul_le_mul_of_nonneg_left hMD hC.le
      calc
        C / T ^ 100 = C * (1 / T ^ 100) := by ring
        _ ≤ C * D0 := hCD
        _ ≤ C * ((M : ℝ) ^ 4 * D0) := hscale
    · exact hnext
  have hterm : sourceFiniteAffineEnergy (sourcePositiveDyadicRange M)
      (sourcePositiveDyadicRange M) (sourceCenteredRange (16 * M)) (f (N-r)) ≤
      34848 * (M : ℝ) ^ 6 * Q0 := by
    have hend := sourcePositiveCentered_endcap_energy_le
      (scaledWideOrbit_admissible hT1 hB4 hBT hdelta.le W N) hM
    have hcontract := scaledWideOrbit_L1_L2_contractions
      hT1 hB4 hBT hdelta.le W N
    have hcap := hend.trans (mul_le_mul_of_nonneg_left hcontract.2
      (by positivity))
    have hidx : r + (N - r) = N := by omega
    dsimp [f]
    rw [hidx]
    simpa [Q0, Nat.mul_comm] using! hcap
  have hMleT : (M : ℝ) ≤ T := by nlinarith [hMT]
  have hM2leT2 : (M : ℝ) ^ 2 ≤ T ^ 2 :=
    pow_le_pow_left₀ hMreal.le hMleT 2
  have hXN : sourceFiniteAffineEnergy (sourcePositiveDyadicRange M)
      (sourcePositiveDyadicRange M) (sourceCenteredRange (16 * M)) (f (N-r)) /
        ((M : ℝ) ^ 4 * D0) ≤ 34848 * T ^ 2 := by
    apply (div_le_iff₀ hden).2
    have hmul := mul_le_mul_of_nonneg_right hM2leT2
      (by positivity : 0 ≤ (M : ℝ)^4 * D0)
    have hEbound := hterm.trans
      (mul_le_mul_of_nonneg_left hQ0D (by positivity))
    have hgoal :
        34848 * (M : ℝ) ^ 6 * D0 ≤
          34848 * T ^ 2 * ((M : ℝ) ^ 4 * D0) := by
      calc
        34848 * (M : ℝ) ^ 6 * D0 =
            34848 * (M : ℝ) ^ 2 * ((M : ℝ) ^ 4 * D0) := by ring
        _ ≤ 34848 * T ^ 2 * ((M : ℝ) ^ 4 * D0) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hM2leT2 (by norm_num))
            (by positivity)
    exact hEbound.trans hgoal
  have hfinite := finite_sqrt_recurrence_bound
    (A := A) (B := Bcoef) (H := 34848 * T ^ 2) (N := N-r)
    (K := fun n =>
      sourceFiniteAffineEnergy (sourcePositiveDyadicRange M)
        (sourcePositiveDyadicRange M) (sourceCenteredRange (16 * M)) (f n) /
        ((M : ℝ) ^ 4 * D0))
    hA hB (by positivity) hX hrec hXN
  have hE0 := hfinite
  dsimp [f, D0, L0, Q0, A, Bcoef, Dscale] at hE0 ⊢
  calc
    sourceFiniteAffineEnergy (sourcePositiveDyadicRange M)
        (sourcePositiveDyadicRange M) (sourceCenteredRange (16 * M))
        (scaledWideOrbit B T delta hRpos W r) ≤
      (M : ℝ) ^ 4 * D0 *
        (max 1 (max (2 * A) (4 * Bcoef ^ 2))) *
        iterSqrt (N-r) (max 1 ((34848 * T ^ 2) /
          max 1 (max (2 * A) (4 * Bcoef ^ 2)))) := by
      have hh := (div_le_iff₀ hden).mp hE0
      convert hh using 1 <;> ring
    _ = _ := by ring

end GuthMaynardS3PositiveEnergyShiftedBound

#print axioms GuthMaynardS3PositiveEnergyShiftedBound.scaledWideOrbit_positive_energy_shifted_bound
