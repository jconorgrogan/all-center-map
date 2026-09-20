import GuthMaynardLemma295DeepLeftExteriorEnvelope
import GuthMaynardLemma295ExactMScale
import GuthMaynardLemma295TailScaleLedger
import GuthMaynardLemma295TailExponentLedger

/-! Exact-source-scale power saving for the discarded deep-left tail. -/

namespace GuthMaynardLemma295ExactMDeepLeft

open Complex MeasureTheory
open GuthMaynardJutilaReflection2941
open GuthMaynardLemma295DualTail
open GuthMaynardLemma295FloorTruncation
open GuthMaynardLemma295ExactMScale
open GuthMaynardLemma295TailScaleLedger
open GuthMaynardLemma295TailExponentLedger
open GuthMaynardLemma295DeepLeftExteriorEnvelope
open GuthMaynardLemma295MellinPolynomialDecay

noncomputable section

theorem floorDualTail_mul_N_le_sourceRpow
    {T epsilon N sigma : ℝ}
    (hT : 0 < T) (hN : 0 < N)
    (hNcap : N ≤ sourceReflectionNumerator29_40 T epsilon)
    (hsigma : sigma < 0) :
    (((⌊reflectedLength29_40 T epsilon N⌋₊ + 1 : ℕ) : ℝ)^(sigma-1) +
      ((⌊reflectedLength29_40 T epsilon N⌋₊ + 1 : ℕ) : ℝ)^sigma/(-sigma)) *
      Real.rpow N sigma ≤
    (1+1/(-sigma))*
      Real.rpow (sourceReflectionNumerator29_40 T epsilon) sigma := by
  let M := reflectedLength29_40 T epsilon N
  have hMpos : 0 < M := reflectedLength29_40_pos hT hN
  have hM : 1 ≤ M := one_le_reflectedLength29_40 hT hN hNcap
  have hfloor1 : Real.rpow (((⌊M⌋₊ : ℕ):ℝ)+1) (sigma-1) ≤
      Real.rpow M (sigma-1) := floor_tail_rpow_le hMpos (by linarith)
  have hfloor2 : Real.rpow (((⌊M⌋₊ : ℕ):ℝ)+1) sigma ≤
      Real.rpow M sigma := floor_tail_rpow_le hMpos hsigma.le
  have hden : 0 < -sigma := by linarith
  have htail :
      (Real.rpow (((⌊M⌋₊ : ℕ):ℝ)+1) (sigma-1) +
        Real.rpow (((⌊M⌋₊ : ℕ):ℝ)+1) sigma/(-sigma)) * Real.rpow N sigma ≤
      (Real.rpow M (sigma-1)+Real.rpow M sigma/(-sigma))*Real.rpow N sigma := by
    have hNpow : 0 ≤ Real.rpow N sigma := Real.rpow_nonneg hN.le _
    gcongr
  have hMN : sourceReflectionNumerator29_40 T epsilon ≤ M*N := by
    dsimp [M]
    exact (reflectedLength29_40_mul_N hN.ne').ge
  have hscale := dualTail_scale_le hM hN
    (sourceReflectionNumerator29_40_pos hT) hMN hsigma
  simpa [M, Nat.cast_add, Nat.cast_one] using htail.trans hscale

/-- The decay constant depends only on `epsilon` and `A`; it is uniform in
all source parameters, including every positive length `N`. -/
theorem deepLeftTail_exactM_power_saving
    {epsilon A : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧
    ∀ {T N U g : ℝ},
    2 ≤ T → 0 < N →
    N ≤ sourceReflectionNumerator29_40 T epsilon →
    1 ≤ U → U ≤ T → |g| ≤ U →
      ‖∫ t : ℝ, lemma295DeepLeftTailIntegrand N g
        ⌊reflectedLength29_40 T epsilon N⌋₊
        (lemma295TailDepthStrong epsilon A) t‖ ≤
      C * Real.rpow T (-A) := by
  let n := lemma295TailDepthStrong epsilon A
  let sigma := deepLeftSigma n
  let d := deepLeftDegree n
  obtain ⟨C₀,hC₀,hrawAll⟩ := exists_norm_integral_deepLeftTail_le n
  let C : ℝ := 1 +
    (4*C₀*sourceMellinDecayConstantAt sigma 0 +
      1152*(1+|sigma|+2*n)^(2*n) * 2^d *
        sourceMellinDecayConstantAt sigma (d+4) *
        ((2:ℝ)^(d+1)*Real.pi)) *
      (1+1/(-sigma))
  refine ⟨C, ?_, ?_⟩
  · have hsigma : sigma < 0 := by
      dsimp [sigma, deepLeftSigma]
      have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hcoef0 : 0 ≤ 4*C₀*sourceMellinDecayConstantAt sigma 0 +
      1152*(1+|sigma|+2*n)^(2*n) * 2^d *
        sourceMellinDecayConstantAt sigma (d+4) *
        ((2:ℝ)^(d+1)*Real.pi) := by
          have hm0 := sourceMellinDecayConstantAt_nonneg sigma 0
          have hmd := sourceMellinDecayConstantAt_nonneg sigma (d+4)
          positivity
    have hsigfac : 0 ≤ 1+1/(-sigma) := by
      have : 0 < 1/(-sigma) := one_div_pos.mpr (by linarith)
      linarith
    dsimp [C]
    positivity
  · intro T N U g hT hN hNcap hU hUT hg
    have hraw := hrawAll (N := N) (by linarith) g
      ⌊reflectedLength29_40 T epsilon N⌋₊
    have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hT
    have hNpos : 0 < N := hN
    have hsigma : sigma < 0 := by
      dsimp [sigma, deepLeftSigma]
      have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hscale := floorDualTail_mul_N_le_sourceRpow
      hTpos hNpos hNcap hsigma
    have hgp : (1+|g|)^d ≤ (2*U)^d := by
      gcongr
      linarith [abs_nonneg g]
    have hcoef :
      4*C₀*sourceMellinDecayConstantAt sigma 0 +
        1152*(1+|sigma|+2*n)^(2*n)*(1+|g|)^d *
          sourceMellinDecayConstantAt sigma (d+4)*((2:ℝ)^(d+1)*Real.pi) ≤
      (4*C₀*sourceMellinDecayConstantAt sigma 0 +
        1152*(1+|sigma|+2*n)^(2*n)*2^d *
          sourceMellinDecayConstantAt sigma (d+4)*((2:ℝ)^(d+1)*Real.pi)) * U^d := by
      have hUd : 1 ≤ U^d := one_le_pow₀ hU
      have hgp' : (1+|g|)^d ≤ 2^d*U^d := by
        calc
          (1+|g|)^d ≤ (2*U)^d := hgp
          _ = 2^d*U^d := mul_pow _ _ _
      have hc0 : 0 ≤ 4*C₀*sourceMellinDecayConstantAt sigma 0 := by
        have := sourceMellinDecayConstantAt_nonneg sigma 0
        positivity
      have hc1 : 0 ≤ 1152*(1+|sigma|+2*n)^(2*n)*
          sourceMellinDecayConstantAt sigma (d+4)*((2:ℝ)^(d+1)*Real.pi) := by
        have := sourceMellinDecayConstantAt_nonneg sigma (d+4)
        positivity
      nlinarith
    have hQ : U * Real.rpow T epsilon ≤
        sourceReflectionNumerator29_40 T epsilon := by
      unfold sourceReflectionNumerator29_40
      calc
        U * Real.rpow T epsilon ≤ T * Real.rpow T epsilon :=
          mul_le_mul_of_nonneg_right hUT (Real.rpow_nonneg hTpos.le _)
        _ = Real.rpow T 1 * Real.rpow T epsilon := by
          simpa using congrArg (fun x : ℝ => x * Real.rpow T epsilon)
            (Real.rpow_one T).symm
        _ = Real.rpow T (1+epsilon) := (Real.rpow_add hTpos 1 epsilon).symm
    have hQpow : Real.rpow (sourceReflectionNumerator29_40 T epsilon) sigma ≤
        Real.rpow (U*Real.rpow T epsilon) sigma :=
      Real.rpow_le_rpow_of_nonpos (mul_pos (lt_of_lt_of_le zero_lt_one hU)
        (Real.rpow_pos_of_pos hTpos _)) hQ hsigma.le
    have hledger := thetaPolynomial_mul_sourceScale_le
      (by linarith : 1 ≤ T) hU hUT hepsilon (A:=A)
    have hUdRpow : Real.rpow U (d:ℝ) = U^d := by
      exact Real.rpow_natCast U d
    have hledger' : U^d * Real.rpow (U*Real.rpow T epsilon) sigma ≤
        Real.rpow T (-A) := by
      rw [← hUdRpow]
      simpa [n,sigma,d,deepLeftDegree] using hledger
    have htail0 : 0 ≤
        (((⌊reflectedLength29_40 T epsilon N⌋₊ + 1 : ℕ) : ℝ)^(sigma-1)+
          ((⌊reflectedLength29_40 T epsilon N⌋₊ + 1 : ℕ) : ℝ)^sigma/(-sigma)) := by
      have hb : 0 < (((⌊reflectedLength29_40 T epsilon N⌋₊ + 1 : ℕ) : ℝ)) := by positivity
      have hden : 0 < -sigma := by linarith
      positivity
    have htailN0 : 0 ≤
        ((((⌊reflectedLength29_40 T epsilon N⌋₊ + 1 : ℕ) : ℝ)^(sigma-1)+
          ((⌊reflectedLength29_40 T epsilon N⌋₊ + 1 : ℕ) : ℝ)^sigma/(-sigma)) *
          Real.rpow N sigma) := mul_nonneg htail0 (Real.rpow_nonneg hNpos.le _)
    have hcoefBig0 : 0 ≤
        (4*C₀*sourceMellinDecayConstantAt sigma 0 +
          1152*(1+|sigma|+2*n)^(2*n)*2^d *
            sourceMellinDecayConstantAt sigma (d+4)*((2:ℝ)^(d+1)*Real.pi))*U^d := by
      have hm0 := sourceMellinDecayConstantAt_nonneg sigma 0
      have hmd := sourceMellinDecayConstantAt_nonneg sigma (d+4)
      positivity
    have hbase0 : 0 ≤
        (4*C₀*sourceMellinDecayConstantAt sigma 0 +
          1152*(1+|sigma|+2*n)^(2*n)*2^d *
            sourceMellinDecayConstantAt sigma (d+4)*((2:ℝ)^(d+1)*Real.pi)) := by
      have hm0 := sourceMellinDecayConstantAt_nonneg sigma 0
      have hmd := sourceMellinDecayConstantAt_nonneg sigma (d+4)
      positivity
    have hsig0 : 0 ≤ 1+1/(-sigma) := by
      have : 0 < 1/(-sigma) := one_div_pos.mpr (by linarith)
      linarith
    calc
      ‖∫ t : ℝ, lemma295DeepLeftTailIntegrand N g
          ⌊reflectedLength29_40 T epsilon N⌋₊ n t‖ ≤
        (4*C₀*sourceMellinDecayConstantAt sigma 0 +
          1152*(1+|sigma|+2*n)^(2*n)*(1+|g|)^d *
            sourceMellinDecayConstantAt sigma (d+4)*((2:ℝ)^(d+1)*Real.pi)) *
        (((⌊reflectedLength29_40 T epsilon N⌋₊ + 1 : ℕ) : ℝ)^(sigma-1)+
          ((⌊reflectedLength29_40 T epsilon N⌋₊ + 1 : ℕ) : ℝ)^sigma/(-sigma)) *
          Real.rpow N sigma := by simpa [n,sigma,d] using hraw
      _ ≤ ((4*C₀*sourceMellinDecayConstantAt sigma 0 +
          1152*(1+|sigma|+2*n)^(2*n)*2^d *
            sourceMellinDecayConstantAt sigma (d+4)*((2:ℝ)^(d+1)*Real.pi))*U^d) *
          ((1+1/(-sigma))*Real.rpow (sourceReflectionNumerator29_40 T epsilon) sigma) := by
        rw [mul_assoc]
        exact mul_le_mul hcoef hscale htailN0 hcoefBig0
      _ ≤ C * Real.rpow T (-A) := by
        have hnon : 0 ≤ (4*C₀*sourceMellinDecayConstantAt sigma 0 +
          1152*(1+|sigma|+2*n)^(2*n)*2^d *
            sourceMellinDecayConstantAt sigma (d+4)*((2:ℝ)^(d+1)*Real.pi)) *
            (1+1/(-sigma)) := mul_nonneg hbase0 hsig0
        calc
          ((4*C₀*sourceMellinDecayConstantAt sigma 0 +
            1152*(1+|sigma|+2*n)^(2*n)*2^d *
              sourceMellinDecayConstantAt sigma (d+4)*((2:ℝ)^(d+1)*Real.pi))*U^d) *
            ((1+1/(-sigma))*Real.rpow (sourceReflectionNumerator29_40 T epsilon) sigma) =
            ((4*C₀*sourceMellinDecayConstantAt sigma 0 +
            1152*(1+|sigma|+2*n)^(2*n)*2^d *
              sourceMellinDecayConstantAt sigma (d+4)*((2:ℝ)^(d+1)*Real.pi)) *
              (1+1/(-sigma))) *
              (U^d*Real.rpow (sourceReflectionNumerator29_40 T epsilon) sigma) := by ring
          _ ≤ ((4*C₀*sourceMellinDecayConstantAt sigma 0 +
            1152*(1+|sigma|+2*n)^(2*n)*2^d *
              sourceMellinDecayConstantAt sigma (d+4)*((2:ℝ)^(d+1)*Real.pi)) *
              (1+1/(-sigma))) *
              (U^d*Real.rpow (U*Real.rpow T epsilon) sigma) := by
                apply mul_le_mul_of_nonneg_left _ hnon
                exact mul_le_mul_of_nonneg_left hQpow (pow_nonneg (by linarith) d)
          _ ≤ ((4*C₀*sourceMellinDecayConstantAt sigma 0 +
            1152*(1+|sigma|+2*n)^(2*n)*2^d *
              sourceMellinDecayConstantAt sigma (d+4)*((2:ℝ)^(d+1)*Real.pi)) *
              (1+1/(-sigma))) * Real.rpow T (-A) := by
                exact mul_le_mul_of_nonneg_left hledger' hnon
          _ ≤ C * Real.rpow T (-A) := by
            dsimp [C]
            have hpow0 : 0 ≤ Real.rpow T (-A) := Real.rpow_nonneg hTpos.le _
            apply mul_le_mul_of_nonneg_right _ hpow0
            linarith

end
end GuthMaynardLemma295ExactMDeepLeft

#print axioms GuthMaynardLemma295ExactMDeepLeft.floorDualTail_mul_N_le_sourceRpow
#print axioms GuthMaynardLemma295ExactMDeepLeft.deepLeftTail_exactM_power_saving
