import PostA5CrowdingDeterministic
import FixedCharacterFourthMomentFromAFE

/-!
# Source-faithful Type-II fourth-moment adapter

The Appendix A.4 Type-II branch does not produce a common Dirichlet
polynomial.  After selecting one critical-line shift for each zero, the source
thins the original ordinates at distance `3 * B`; shifts of size at most `B`
are then one-separated.  Montgomery's discrete fourth moment is applied
directly to the resulting `L(1/2+it, chi)` values.

This file certifies the finite selection, spacing, moment-to-cardinality, and
exact exponent algebra.  The only analytic surface named below is the literal
fixed-character consequence of Montgomery, Theorem 10.3; it is data, not an
asserted theorem.
-/

namespace PostA5TypeIIFourthMoment

open scoped BigOperators
open CGLProofDAG MAPAppendixA4DetectorDichotomy
open MAPAppendixA4PostA5SetAdapter

noncomputable section

variable {q : ℕ} [NeZero q]

/-- The elementary telescoping inequality behind the sharp critical-line
mollifier bound. -/
private theorem inv_sqrt_succ_le_two_mul_sqrt_sub
    (n : ℕ) :
    1 / Real.sqrt (n + 1 : ℝ) ≤
      2 * (Real.sqrt (n + 1 : ℝ) - Real.sqrt (n : ℝ)) := by
  have hnpos : 0 < Real.sqrt (n + 1 : ℝ) := by positivity
  have hn0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hsqrtle : Real.sqrt (n : ℝ) ≤ Real.sqrt (n + 1 : ℝ) := by
    exact Real.sqrt_le_sqrt (by norm_num)
  have hdenpos : 0 < Real.sqrt (n + 1 : ℝ) + Real.sqrt (n : ℝ) := by
    positivity
  have hdenle :
      Real.sqrt (n + 1 : ℝ) + Real.sqrt (n : ℝ) ≤
        2 * Real.sqrt (n + 1 : ℝ) := by linarith
  have hinv :
      1 / (2 * Real.sqrt (n + 1 : ℝ)) ≤
        1 / (Real.sqrt (n + 1 : ℝ) + Real.sqrt (n : ℝ)) := by
    exact one_div_le_one_div_of_le hdenpos hdenle
  have hdiff :
      Real.sqrt (n + 1 : ℝ) - Real.sqrt (n : ℝ) =
        1 / (Real.sqrt (n + 1 : ℝ) + Real.sqrt (n : ℝ)) := by
    apply (eq_div_iff hdenpos.ne').2
    have hsq1 := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n + 1)
    have hsq0 := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n)
    nlinarith
  rw [hdiff]
  calc
    1 / Real.sqrt (n + 1 : ℝ) =
        2 * (1 / (2 * Real.sqrt (n + 1 : ℝ))) := by field_simp
    _ ≤ 2 * (1 /
        (Real.sqrt (n + 1 : ℝ) + Real.sqrt (n : ℝ))) := by gcongr

/-- The source-critical pointwise mollifier estimate.  On `Re s=1/2`, the
finite mollifier costs `2*sqrt U`, rather than the cruder cardinal bound
`U+1`; this is exactly what gives `2*kappa` after taking fourth powers. -/
theorem norm_mollifier_criticalLine_le_two_sqrt
    (chi : DirichletCharacter ℂ q) (U : ℕ) {s : ℂ}
    (hs : s.re = 1 / 2) :
    ‖MAPMollifierCoefficientIdentity.mollifier chi U s‖ ≤
      2 * Real.sqrt U := by
  rw [MAPAppendixA4Detector.mollifier_eq_sum_range]
  calc
    ‖∑ n ∈ Finset.range (U + 1),
        LSeries.term (((chi ·) : ℕ → ℂ) *
          MAPMollifierCoefficientIdentity.truncatedMoebius U) s n‖ ≤
        ∑ n ∈ Finset.range (U + 1),
          ‖LSeries.term (((chi ·) : ℕ → ℂ) *
            MAPMollifierCoefficientIdentity.truncatedMoebius U) s n‖ :=
      norm_sum_le _ _
    _ = ∑ n ∈ Finset.range U,
          ‖LSeries.term (((chi ·) : ℕ → ℂ) *
            MAPMollifierCoefficientIdentity.truncatedMoebius U) s (n + 1)‖ := by
      rw [Finset.sum_range_succ']
      simp [LSeries.term]
    _ ≤ ∑ n ∈ Finset.range U,
          2 * (Real.sqrt (n + 1 : ℝ) - Real.sqrt (n : ℝ)) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [LSeries.norm_term_eq, if_neg (Nat.succ_ne_zero n)]
      have hchi : ‖chi ((n + 1 : ℕ) : ZMod q)‖ ≤ 1 := chi.norm_le_one _
      have hmu :
          ‖MAPMollifierCoefficientIdentity.truncatedMoebius U (n + 1)‖ ≤ 1 :=
        MAPMollifierCoefficientIdentity.norm_truncatedMoebius_le_one U (n + 1)
      have hnum :
          ‖chi ((n + 1 : ℕ) : ZMod q) *
            MAPMollifierCoefficientIdentity.truncatedMoebius U (n + 1)‖ ≤ 1 := by
        rw [norm_mul]
        nlinarith [norm_nonneg (chi ((n + 1 : ℕ) : ZMod q)),
          norm_nonneg
            (MAPMollifierCoefficientIdentity.truncatedMoebius U (n + 1))]
      have hsqrt : 0 < Real.sqrt (n + 1 : ℝ) := by positivity
      have hterm :
          ‖chi ((n + 1 : ℕ) : ZMod q) *
              MAPMollifierCoefficientIdentity.truncatedMoebius U (n + 1)‖ /
              Real.sqrt (n + 1 : ℝ) ≤
            1 / Real.sqrt (n + 1 : ℝ) :=
        (div_le_div_iff_of_pos_right hsqrt).2 hnum
      simp only [Pi.mul_apply]
      rw [hs, ← Real.sqrt_eq_rpow]
      norm_num [Nat.cast_add, Nat.cast_one]
      rw [← norm_mul]
      simpa only [Nat.cast_add, Nat.cast_one] using
        hterm.trans (inv_sqrt_succ_le_two_mul_sqrt_sub n)
    _ = 2 * Real.sqrt U := by
      rw [← Finset.mul_sum]
      congr 1
      simpa [Nat.cast_add, Nat.cast_one] using
        (Finset.sum_range_sub (fun n : ℕ => Real.sqrt (n : ℝ)) U)

/-- Divide a product lower bound by a positive pointwise factor bound. -/
theorem norm_lower_of_product
    {L M : ℂ} {V W : ℝ} (hW : 0 < W)
    (hproduct : V ≤ ‖L * M‖) (hM : ‖M‖ ≤ W) :
    V / W ≤ ‖L‖ := by
  apply (div_le_iff₀ hW).2
  calc
    V ≤ ‖L * M‖ := hproduct
    _ = ‖L‖ * ‖M‖ := norm_mul _ _
    _ ≤ ‖L‖ * W :=
      mul_le_mul_of_nonneg_left hM (norm_nonneg _)

/-- Strong source-normalized pointwise detector alternative.  Unlike the
shared-threshold wrapper used by the Type-I polynomial route, this retains the
factor `Y^(beta-1/2)/sqrt U` required by the Type-II fourth-moment exponent. -/
theorem post_A5_detector_to_typeI_or_sourceTypeII
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {U : ℕ} (hU : 1 ≤ U) {rho : ℂ}
    (hrho : DirichletCharacter.LFunction chi rho = 0)
    (hbetaLow : 7 / 10 ≤ rho.re) (hbetaHigh : rho.re ≤ 1)
    {Y R V : ℝ} (hY : 1 ≤ Y) (hV : 0 < V)
    (hUN : U ≤ detectorArithmeticCutoff Y R)
    (hB : 1 ≤ detectorVerticalCutoff R)
    (hbudget :
      MAPAppendixA4DetectorDichotomy.detectorTruncationErrorEnvelope
          q U rho Y R + V + V ≤ Real.exp (-(1 / Y))) :
    V ≤ ‖MAPAppendixA4DetectorDichotomy.arithmeticDetectorBlock chi U
        (detectorArithmeticCutoff Y R) rho Y‖ ∨
      ∃ t ∈ Set.Icc (-(detectorVerticalCutoff R))
          (detectorVerticalCutoff R),
        V /
            (29 * Real.rpow Y (1 / 2 - rho.re) *
              (2 * Real.sqrt U)) ≤
          ‖DirichletCharacter.LFunction chi
            (((1 / 2 : ℝ) : ℂ) + (rho.im + t) * Complex.I)‖ := by
  rcases
      MAPAppendixA4DetectorDichotomy.post_A5_quantitative_detector_dichotomy_with_criticalLine_large_value
        chi hchi hU hrho (by linarith) hbetaHigh hY hUN hB
          (a := V) (b := V) hbudget with hI | hII
  · exact Or.inl hI
  · right
    obtain ⟨t, ht, htlarge⟩ := hII
    let s : ℂ := (((1 / 2 : ℝ) : ℂ) + (rho.im + t) * Complex.I)
    let D : ℝ := (1 / (2 * Real.pi)) *
      MAPAppendixA4DetectorDichotomy.truncatedGammaLeftKernelMass rho Y
        (detectorVerticalCutoff R)
    let W : ℝ := 2 * Real.sqrt U
    let E : ℝ := 29 * Real.rpow Y (1 / 2 - rho.re) * W
    have hYpos : 0 < Y := zero_lt_one.trans_le hY
    have hBpos : 0 < detectorVerticalCutoff R := zero_lt_one.trans_le hB
    have hmasspos : 0 <
        MAPAppendixA4DetectorDichotomy.truncatedGammaLeftKernelMass rho Y
          (detectorVerticalCutoff R) :=
      MAPAppendixA4DetectorDichotomy.truncatedGammaLeftKernelMass_pos
        (by linarith) hbetaHigh hYpos hBpos
    have hDpos : 0 < D := by dsimp [D]; positivity
    have hWpos : 0 < W := by
      dsimp [W]
      have hUpos : (0 : ℝ) < U := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hU)
      positivity
    have hEpos : 0 < E := by dsimp [E]; positivity
    have hDle : D ≤ 29 * Real.rpow Y (1 / 2 - rho.re) := by
      have h :=
        MAPAppendixA4DetectorDichotomy.normalized_truncatedGammaLeftKernelMass_le_uniform
          hbetaLow hbetaHigh 0 hY (zero_le_one.trans hB)
      simpa [D] using h
    have hDE : D * W ≤ E := by
      dsimp [E]
      exact mul_le_mul_of_nonneg_right hDle hWpos.le
    have hsre : s.re = 1 / 2 := by dsimp [s]; simp
    have hM := norm_mollifier_criticalLine_le_two_sqrt chi U hsre
    have hproduct : V / D ≤
        ‖DirichletCharacter.LFunction chi s *
          MAPMollifierCoefficientIdentity.mollifier chi U s‖ := by
      simpa [D, s] using htlarge
    have hLraw := norm_lower_of_product hWpos hproduct hM
    have hL : V / (D * W) ≤ ‖DirichletCharacter.LFunction chi s‖ := by
      simpa [div_div] using hLraw
    refine ⟨t, ht, ?_⟩
    have hquot : V / E ≤ V / (D * W) :=
      (div_le_div_iff_of_pos_left hV hEpos (mul_pos hDpos hWpos)).2 hDE
    exact hquot.trans (by simpa [E, W, s] using hL)

/-- A finite subset of the certified Type-II fiber admits one simultaneous
choice of shift at every point. -/
theorem exists_typeII_shift_assignment
    (chi : DirichletCharacter ℂ q) {R V : ℝ} {Z S : Finset ℂ}
    (hS : S ⊆ postA5TypeIISet chi R V Z) :
    ∃ u : ℂ → ℝ, ∀ rho ∈ S,
      u rho ∈ Set.Icc (-(detectorVerticalCutoff R))
          (detectorVerticalCutoff R) ∧
        V ≤ ‖DirichletCharacter.LFunction chi
          (((1 / 2 : ℝ) : ℂ) + (rho.im + u rho) * Complex.I)‖ := by
  classical
  have hwitness : ∀ rho ∈ S,
      ∃ t ∈ Set.Icc (-(detectorVerticalCutoff R))
          (detectorVerticalCutoff R),
        V ≤ ‖DirichletCharacter.LFunction chi
          (((1 / 2 : ℝ) : ℂ) + (rho.im + t) * Complex.I)‖ := by
    intro rho hrho
    exact (mem_postA5TypeIISet_iff chi R V Z rho).mp (hS hrho) |>.2
  let u : ℂ → ℝ := fun rho =>
    if hrho : rho ∈ S then Classical.choose (hwitness rho hrho) else 0
  refine ⟨u, ?_⟩
  intro rho hrho
  dsimp [u]
  rw [dif_pos hrho]
  exact Classical.choose_spec (hwitness rho hrho)

/-- Moving each ordinate by at most `B` preserves one-spacing once the
original ordinates were thinned at distance `3B`.  The image cardinality is
also preserved, so the fourth-moment sum counts the selected zeros exactly. -/
theorem shifted_image_oneSeparated_and_card
    {ι : Type*} (S : Finset ι) (gamma shift : ι → ℝ) {B : ℝ}
    (hB : 1 ≤ B)
    (hshift : ∀ x ∈ S, |shift x| ≤ B)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y →
      3 * B ≤ |gamma x - gamma y|) :
    OneSeparated (S.image fun x => gamma x + shift x) ∧
      (S.image fun x => gamma x + shift x).card = S.card := by
  classical
  have hgap : ∀ x ∈ S, ∀ y ∈ S, x ≠ y →
      B ≤ |(gamma x + shift x) - (gamma y + shift y)| := by
    intro x hx y hy hxy
    have htri : |gamma x - gamma y| ≤
        |(gamma x + shift x) - (gamma y + shift y)| +
          |shift x| + |shift y| := by
      calc
        |gamma x - gamma y| =
            |((gamma x + shift x) - (gamma y + shift y)) -
              shift x + shift y| := by congr 1 <;> ring
        _ ≤ |((gamma x + shift x) - (gamma y + shift y)) - shift x| +
              |shift y| := abs_add_le _ _
        _ ≤ (|(gamma x + shift x) - (gamma y + shift y)| +
              |shift x|) + |shift y| := by
          gcongr
          exact abs_sub _ _
    have hsource := hsep x hx y hy hxy
    have hxshift := hshift x hx
    have hyshift := hshift y hy
    linarith
  constructor
  · intro t ht v hv htv
    rw [Finset.mem_image] at ht hv
    obtain ⟨x, hx, rfl⟩ := ht
    obtain ⟨y, hy, rfl⟩ := hv
    have hxy : x ≠ y := by
      intro h
      apply htv
      rw [h]
    exact hB.trans (hgap x hx y hy hxy)
  · apply Finset.card_image_iff.mpr
    intro x hx y hy heq
    by_contra hxy
    have hpositive := hB.trans (hgap x hx y hy hxy)
    have hzero : gamma x + shift x - (gamma y + shift y) = 0 :=
      sub_eq_zero.mpr heq
    rw [hzero, abs_zero] at hpositive
    linarith

/-- Complete deterministic Type-II set weld after the pointwise detector has
chosen shifts.  The beta-dependent pointwise lower bound is uniformized at
`beta = sigma`, the shifted image is one-separated with unchanged cardinality,
and the supplied fourth moment gives the literal cardinal bound. -/
theorem typeII_card_le_of_shifted_fourthMoment
    (chi : DirichletCharacter ℂ q) (S : Finset ℂ) (shift : ℂ → ℝ)
    {B sigma Y V M : ℝ} {U : ℕ}
    (hB : 1 ≤ B) (hU : 1 ≤ U) (hY : 1 ≤ Y) (hV : 0 < V)
    (hshift : ∀ rho ∈ S, |shift rho| ≤ B)
    (hsep : ∀ rho ∈ S, ∀ rho' ∈ S, rho ≠ rho' →
      3 * B ≤ |rho.im - rho'.im|)
    (hbeta : ∀ rho ∈ S, sigma ≤ rho.re)
    (hlower : ∀ rho ∈ S,
      V / (29 * Real.rpow Y (1 / 2 - rho.re) *
          (2 * Real.sqrt U)) ≤
        ‖DirichletCharacter.LFunction chi
          (((1 / 2 : ℝ) : ℂ) +
            (rho.im + shift rho) * Complex.I)‖)
    (hmoment :
      (∑ t ∈ S.image (fun rho => rho.im + shift rho),
        ‖DirichletCharacter.LFunction chi
          (((1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ ^ 4) ≤ M) :
    (S.card : ℝ) ≤
      M / (V / (29 * Real.rpow Y (1 / 2 - sigma) *
        (2 * Real.sqrt U))) ^ 4 := by
  classical
  let W : Finset ℝ := S.image (fun rho => rho.im + shift rho)
  have hspacing := shifted_image_oneSeparated_and_card S Complex.im shift
    hB hshift hsep
  have hWcard : W.card = S.card := by simpa [W] using hspacing.2
  have hUp : (0 : ℝ) < U := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hU)
  have hcommonPos :
      0 < 29 * Real.rpow Y (1 / 2 - sigma) *
        (2 * Real.sqrt U) := by
    exact mul_pos
      (mul_pos (by norm_num) (Real.rpow_pos_of_pos (zero_lt_one.trans_le hY) _))
      (mul_pos (by norm_num) (Real.sqrt_pos.2 hUp))
  have hlowerW : ∀ t ∈ W,
      V / (29 * Real.rpow Y (1 / 2 - sigma) *
          (2 * Real.sqrt U)) ≤
        ‖DirichletCharacter.LFunction chi
          (((1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ := by
    intro t ht
    change t ∈ S.image (fun rho => rho.im + shift rho) at ht
    rw [Finset.mem_image] at ht
    obtain ⟨rho, hrho, rfl⟩ := ht
    have hrpow :
        Real.rpow Y (1 / 2 - rho.re) ≤
          Real.rpow Y (1 / 2 - sigma) :=
      Real.rpow_le_rpow_of_exponent_le hY (by linarith [hbeta rho hrho])
    have hrhoDenPos :
        0 < 29 * Real.rpow Y (1 / 2 - rho.re) *
          (2 * Real.sqrt U) := by
      exact mul_pos
        (mul_pos (by norm_num) (Real.rpow_pos_of_pos (zero_lt_one.trans_le hY) _))
        (mul_pos (by norm_num) (Real.sqrt_pos.2 hUp))
    have hden :
        29 * Real.rpow Y (1 / 2 - rho.re) *
            (2 * Real.sqrt U) ≤
          29 * Real.rpow Y (1 / 2 - sigma) *
            (2 * Real.sqrt U) := by
      gcongr
    have hquot :
        V / (29 * Real.rpow Y (1 / 2 - sigma) *
            (2 * Real.sqrt U)) ≤
          V / (29 * Real.rpow Y (1 / 2 - rho.re) *
            (2 * Real.sqrt U)) :=
      (div_le_div_iff_of_pos_left hV hcommonPos hrhoDenPos).2 hden
    exact hquot.trans (by simpa using hlower rho hrho)
  let L : ℝ → ℂ := fun t => DirichletCharacter.LFunction chi
    (((1 / 2 : ℝ) : ℂ) + t * Complex.I)
  let threshold : ℝ :=
    V / (29 * Real.rpow Y (1 / 2 - sigma) * (2 * Real.sqrt U))
  have hthreshold : 0 < threshold := by
    dsimp [threshold]
    exact div_pos hV hcommonPos
  apply (le_div_iff₀ (pow_pos hthreshold 4)).2
  rw [← hWcard]
  calc
    (W.card : ℝ) * threshold ^ 4 = ∑ _t ∈ W, threshold ^ 4 := by simp
    _ ≤ ∑ t ∈ W, ‖L t‖ ^ 4 := by
      apply Finset.sum_le_sum
      intro t ht
      exact pow_le_pow_left₀ hthreshold.le (by
        simpa [threshold, L] using hlowerW t ht) 4
    _ ≤ M := by simpa [W, L] using hmoment

/-- A uniform lower bound converts a discrete fourth moment into the literal
cardinality inequality. -/
theorem card_mul_fourth_le_moment
    {ι : Type*} (S : Finset ι) (L : ι → ℂ) {V M : ℝ}
    (hV : 0 ≤ V)
    (hlower : ∀ v ∈ S, V ≤ ‖L v‖)
    (hmoment : (∑ v ∈ S, ‖L v‖ ^ 4) ≤ M) :
    (S.card : ℝ) * V ^ 4 ≤ M := by
  calc
    (S.card : ℝ) * V ^ 4 = ∑ _v ∈ S, V ^ 4 := by simp
    _ ≤ ∑ v ∈ S, ‖L v‖ ^ 4 := by
      apply Finset.sum_le_sum
      intro v hv
      exact pow_le_pow_left₀ hV (hlower v hv) 4
    _ ≤ M := hmoment

/-- Division form of `card_mul_fourth_le_moment`. -/
theorem card_le_moment_div_fourth
    {ι : Type*} (S : Finset ι) (L : ι → ℂ) {V M : ℝ}
    (hV : 0 < V)
    (hlower : ∀ v ∈ S, V ≤ ‖L v‖)
    (hmoment : (∑ v ∈ S, ‖L v‖ ^ 4) ≤ M) :
    (S.card : ℝ) ≤ M / V ^ 4 := by
  apply (le_div_iff₀ (pow_pos hV 4)).2
  simpa [mul_comm] using
    card_mul_fourth_le_moment S L hV.le hlower hmoment

/-- A detector lower bound for `L*M`, a pointwise mollifier upper bound, and
the discrete fourth moment imply the selected-ordinate count. -/
theorem criticalLine_selected_count
    {ι : Type*} (S : Finset ι) (L Mfun : ι → ℂ) {V W M : ℝ}
    (hV : 0 < V) (hW : 0 < W)
    (hdetector : ∀ v ∈ S, V ≤ ‖L v * Mfun v‖)
    (hmollifier : ∀ v ∈ S, ‖Mfun v‖ ≤ W)
    (hmoment : (∑ v ∈ S, ‖L v‖ ^ 4) ≤ M) :
    (S.card : ℝ) ≤ M / (V / W) ^ 4 := by
  have hVW : 0 < V / W := div_pos hV hW
  apply card_le_moment_div_fourth S L hVW
  · intro v hv
    apply (div_le_iff₀ hW).2
    calc
      V ≤ ‖L v * Mfun v‖ := hdetector v hv
      _ = ‖L v‖ * ‖Mfun v‖ := norm_mul _ _
      _ ≤ ‖L v‖ * W :=
        mul_le_mul_of_nonneg_left (hmollifier v hv) (norm_nonneg _)
  · exact hmoment

/-- Exact exponent in Appendix (A.6). -/
theorem criticalLine_exponent_identity (sigma kappa loss : ℝ) :
    (1 + loss) + 2 * kappa - (2 * sigma - 1) =
      2 * (1 - sigma) + 2 * kappa + loss := by
  ring

/-- The literal real-power normalization in (A.6), with
`Y=R^(1/2)`, `U=R^kappa`, and moment cost `R^(1+loss)`. -/
theorem criticalLine_rpow_quotient_identity
    {R sigma kappa loss : ℝ} (hR : 0 < R) :
    R ^ (1 + loss) /
        ((R ^ (1 / 2 : ℝ)) ^ (sigma - 1 / 2) /
          Real.sqrt (R ^ kappa)) ^ 4 =
      R ^ (2 * (1 - sigma) + 2 * kappa + loss) := by
  have hv :
      (R ^ (1 / 2 : ℝ)) ^ (sigma - 1 / 2) /
          Real.sqrt (R ^ kappa) =
        R ^ ((1 / 2 : ℝ) * (sigma - 1 / 2) - kappa / 2) := by
    rw [← Real.rpow_mul hR.le (1 / 2 : ℝ) (sigma - 1 / 2)]
    rw [Real.sqrt_eq_rpow,
      ← Real.rpow_mul hR.le kappa (1 / 2 : ℝ)]
    rw [← Real.rpow_sub hR]
    congr 1
    ring
  rw [hv]
  let y : ℝ := (1 / 2 : ℝ) * (sigma - 1 / 2) - kappa / 2
  have hpownat : (R ^ y) ^ (4 : ℕ) = (R ^ y) ^ (4 : ℝ) :=
    (Real.rpow_natCast (R ^ y) 4).symm
  have hpowreal : (R ^ y) ^ (4 : ℝ) = R ^ (y * 4) :=
    (Real.rpow_mul hR.le y 4).symm
  change R ^ (1 + loss) / (R ^ y) ^ (4 : ℕ) = _
  rw [hpownat, hpowreal]
  rw [← Real.rpow_sub hR]
  congr 1
  ring

/-- Local source name for the canonical nonprincipal fixed-character fourth
moment.  It is the fixed-character consequence used from Montgomery,
Theorem 10.3.  The imported AFE module proves it from the still narrower
`NonprincipalSquaredDyadicAFE` contract, so no duplicate fourth-moment
proposition is introduced here. -/
abbrev MontgomeryFixedCharacterDiscreteFourthMoment : Prop :=
  FixedCharacterFourthMomentFromAFE.NonprincipalFixedCharacterDiscreteFourthMoment

end

end PostA5TypeIIFourthMoment

#print axioms PostA5TypeIIFourthMoment.exists_typeII_shift_assignment
#print axioms PostA5TypeIIFourthMoment.norm_mollifier_criticalLine_le_two_sqrt
#print axioms PostA5TypeIIFourthMoment.post_A5_detector_to_typeI_or_sourceTypeII
#print axioms PostA5TypeIIFourthMoment.shifted_image_oneSeparated_and_card
#print axioms PostA5TypeIIFourthMoment.typeII_card_le_of_shifted_fourthMoment
#print axioms PostA5TypeIIFourthMoment.card_le_moment_div_fourth
#print axioms PostA5TypeIIFourthMoment.criticalLine_selected_count
#print axioms PostA5TypeIIFourthMoment.criticalLine_rpow_quotient_identity
