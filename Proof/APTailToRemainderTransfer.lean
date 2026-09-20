import APLiteralTailContract
import APFloorMaximalBridge

/-!
# Literal tail family to the maximal AP remainder transfer

This staging module contains only deterministic measure-theoretic and finite
character-family bookkeeping.  Its eventual source premise is exactly
`MAPAPLiteralTailContract.APExplicitFormulaTailFamilySquare`.
-/

namespace MAPAPTailToRemainderTransfer

open MeasureTheory Set
open scoped BigOperators ENNReal
open APFoundation APMaximalExplicitFormulaBridge OneSidedMaximalL2
open APExplicitFormulaMajorantAdapter
open MAPFixedScaleAPZeroRoute MAPAPLiteralTailContract

noncomputable section

variable {q : ℕ} [NeZero q]

private theorem continuousOn_norm_primitiveActualZeroField
    (chi : DirichletCharacter ℂ q) {T x Y : ℝ} (hx : 0 < x) (hY : 0 ≤ Y) :
    ContinuousOn (fun t : ℝ => ‖primitiveActualZeroField chi T t‖)
      (Set.Icc x (x + Y)) := by
  apply ContinuousOn.norm
  unfold primitiveActualZeroField actualZeroField finiteZeroField
  apply continuousOn_finsetSum
  intro rho hrho
  intro t ht
  have htpos : 0 < t := hx.trans_le ht.1
  exact (continuousAt_const.mul
    (Complex.continuousAt_ofReal_cpow_const t (rho - 1)
      (Or.inr htpos.ne'))).continuousWithinAt

/-- Exact conversion of the real interval average appearing in the endpoint
formula to the indicator-valued ENNReal right average used by the maximal
theorem. -/
theorem ofReal_primitiveFieldAverage_eq_rightAverage
    (chi : DirichletCharacter ℂ q) {X T x Y : ℝ}
    (hX : 0 < X) (hx : x ∈ Set.Icc (X / 2) (4 * X))
    (hY : 0 < Y) (hYX : Y ≤ X) :
    ENNReal.ofReal
        (Y⁻¹ * (∫ t : ℝ in x..x + Y,
          ‖primitiveActualZeroField chi T t‖)) =
      rightAverage (primitiveZeroNormField chi X T) Y x := by
  let f : ℝ → ℝ := fun t => ‖primitiveActualZeroField chi T t‖
  have hcont : ContinuousOn f (Set.Icc x (x + Y)) :=
    continuousOn_norm_primitiveActualZeroField chi
      ((half_pos hX).trans_le hx.1)
      hY.le
  have hintIcc : IntegrableOn f (Set.Icc x (x + Y)) :=
    hcont.integrableOn_Icc
  have hintIoc : IntegrableOn f (Set.Ioc x (x + Y)) :=
    hintIcc.mono_set Set.Ioc_subset_Icc_self
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc x (x + Y))] f :=
    Filter.Eventually.of_forall (fun t => norm_nonneg _)
  have hint :
      ENNReal.ofReal (∫ t : ℝ in x..x + Y, f t) =
        ∫⁻ t : ℝ in Set.Ioc x (x + Y), ENNReal.ofReal (f t) := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    exact ofReal_integral_eq_lintegral_ofReal hintIoc hnonneg
  have hsupport : ∀ t ∈ Set.Ioc x (x + Y),
      t ∈ Set.Icc (X / 4) (6 * X) := by
    intro t ht
    constructor
    · have hquarterhalf : X / 4 ≤ X / 2 := by linarith
      exact hquarterhalf.trans (hx.1.trans ht.1.le)
    · have hX0 : 0 ≤ X := hX.le
      linarith [ht.2, hx.2, hYX]
  rw [ENNReal.ofReal_mul (inv_nonneg.mpr hY.le),
    ENNReal.ofReal_inv_of_pos hY, hint, rightAverage_eq_interval]
  congr 1
  apply setLIntegral_congr_fun measurableSet_Ioc
  intro t ht
  simp [primitiveZeroNormField, hsupport t ht, f]

/-- The exact per-modulus pointwise majorant after character Cauchy and the
two legal nonlinear suprema.  The factor two is the elementary
`(u+v)^2 ≤ 2(u^2+v^2)` loss. -/
def fixedModulusZeroTailMajorant
    (q : ℕ) [NeZero q] (sigma : DirichletCharacter ℂ q → ℝ)
    (T epsilon X x : ℝ) : ℝ≥0∞ :=
  2 * ((q.totient : ℝ≥0∞)⁻¹ *
      ∑ chi : DirichletCharacter ℂ q,
        rightMaxSqBetween (primitiveZeroNormField chi X T)
          (Real.rpow X (2 / 15 + epsilon)) X x +
    (q.totient : ℝ≥0∞)⁻¹ *
      ∑ chi : DirichletCharacter ℂ q,
        literalRemainderMaxSq chi (sigma chi) T epsilon X x)

/-- Deterministic character-Cauchy/supremum weld at one positive modulus. -/
theorem fixedModulusAPMax_le_zeroTailMajorant
    {q : ℕ} [NeZero q] {T epsilon X x : ℝ}
    (sigma : DirichletCharacter ℂ q → ℝ)
    (hlegal : ∀ chi : DirichletCharacter ℂ q,
      primitiveContourLegal chi (sigma chi) T)
    (hX : 0 < X) (hx : x ∈ Set.Icc (X / 2) (4 * X)) :
    fixedModulusAPMax q epsilon X x ≤
      fixedModulusZeroTailMajorant q sigma T epsilon X x := by
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hphiNat : 0 < q.totient := Nat.totient_pos.mpr hqpos
  have hphi : 0 < (q.totient : ℝ) := by exact_mod_cast hphiNat
  unfold fixedModulusAPMax
  apply iSup_le
  intro a
  apply iSup_le
  intro haq
  apply iSup_le
  intro ha
  apply iSup_le
  intro Y
  apply iSup_le
  intro hYlow
  apply iSup_le
  intro hYhigh
  have hY : 0 < Y := (Real.rpow_pos_of_pos hX _).trans_le hYlow
  let z : DirichletCharacter ℂ q → ℝ := fun chi =>
    Y⁻¹ * (∫ t : ℝ in x..x + Y,
      ‖primitiveActualZeroField chi T t‖)
  let r : DirichletCharacter ℂ q → ℝ := fun chi =>
    ‖(literalEndpointRemainder chi (sigma chi) T (x + Y) -
        literalEndpointRemainder chi (sigma chi) T x) / Y‖
  have hznonneg : ∀ chi, 0 ≤ z chi := by
    intro chi
    dsimp only [z]
    exact mul_nonneg (inv_nonneg.mpr hY.le)
      (intervalIntegral.integral_nonneg_of_ae (by linarith)
        (Filter.Eventually.of_forall (fun t => norm_nonneg _)))
  have hrnonneg : ∀ chi, 0 ≤ r chi := fun chi => norm_nonneg _
  have hcauchy : |normalizedAPError x Y q a| ^ 2 ≤
      (q.totient : ℝ)⁻¹ *
        ∑ chi : DirichletCharacter ℂ q, (z chi + r chi) ^ 2 := by
    apply normalizedAPError_sq_le_mean_characterMajorants hY ha (fun chi => z chi + r chi)
    intro chi
    exact norm_ambientCharacterWindowError_div_le_primitiveField_add_literalTail
      chi (hlegal chi) ((half_pos hX).trans_le hx.1) hY
  have hreal : |normalizedAPError x Y q a| ^ 2 ≤
      2 * ((q.totient : ℝ)⁻¹ * ∑ chi : DirichletCharacter ℂ q, (z chi) ^ 2 +
        (q.totient : ℝ)⁻¹ * ∑ chi : DirichletCharacter ℂ q, (r chi) ^ 2) := by
    refine hcauchy.trans ?_
    calc
      (q.totient : ℝ)⁻¹ *
          ∑ chi : DirichletCharacter ℂ q, (z chi + r chi) ^ 2 ≤
        (q.totient : ℝ)⁻¹ *
          ∑ chi : DirichletCharacter ℂ q,
            2 * ((z chi) ^ 2 + (r chi) ^ 2) := by
              gcongr with chi
              exact (add_sq_le : (z chi + r chi) ^ 2 ≤
                2 * ((z chi) ^ 2 + (r chi) ^ 2))
      _ = 2 * ((q.totient : ℝ)⁻¹ *
            ∑ chi : DirichletCharacter ℂ q, (z chi) ^ 2 +
          (q.totient : ℝ)⁻¹ *
            ∑ chi : DirichletCharacter ℂ q, (r chi) ^ 2) := by
              simp_rw [mul_add]
              rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
              ring
  rw [← ENNReal.ofReal_pow (abs_nonneg _) 2]
  refine (ENNReal.ofReal_le_ofReal hreal).trans ?_
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ENNReal.ofReal_ofNat, ENNReal.ofReal_add]
  · simp only [fixedModulusZeroTailMajorant]
    gcongr
    · rw [ENNReal.ofReal_mul (inv_nonneg.mpr hphi.le),
        ENNReal.ofReal_inv_of_pos hphi, ENNReal.ofReal_natCast,
        ENNReal.ofReal_sum_of_nonneg]
      · gcongr with chi
        rw [ENNReal.ofReal_pow (hznonneg chi) 2,
          ofReal_primitiveFieldAverage_eq_rightAverage chi hX hx hY hYhigh]
        exact le_iSup_of_le Y <| le_iSup_of_le hYlow <| le_iSup_of_le hYhigh le_rfl
      · intro chi hchi
        exact sq_nonneg _
    · rw [ENNReal.ofReal_mul (inv_nonneg.mpr hphi.le),
        ENNReal.ofReal_inv_of_pos hphi, ENNReal.ofReal_natCast,
        ENNReal.ofReal_sum_of_nonneg]
      · gcongr with chi
        rw [ENNReal.ofReal_pow (hrnonneg chi) 2]
        exact le_iSup_of_le Y <| le_iSup_of_le hYlow <| le_iSup_of_le hYhigh le_rfl
      · intro chi hchi
        exact sq_nonneg _
  · positivity
  · positivity

/-- Measurable finite-dyadic zero majorant for the full floor-capped family. -/
def familyDyadicZeroMajorant (Q N : ℕ) (T H X x : ℝ) : ℝ≥0∞ :=
  ∑ q ∈ Finset.Icc 1 Q,
    if hq : q = 0 then 0 else
      letI : NeZero q := ⟨hq⟩
      (q.totient : ℝ≥0∞)⁻¹ *
        ∑ chi : DirichletCharacter ℂ q,
          4 * finiteRightMaxSq (primitiveZeroNormField chi X T)
            (dyadicRightScales H N) x

/-- Literal (possibly not separately measurable) tail majorant for the full
floor-capped family.  Its whole-family outer integral is the source contract. -/
def familyLiteralTailMajorant
    (Q : ℕ) (sigma : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ)
    (T epsilon X x : ℝ) : ℝ≥0∞ :=
  ∑ q ∈ Finset.Icc 1 Q,
    if hq : q = 0 then 0 else
      letI : NeZero q := ⟨hq⟩
      (q.totient : ℝ≥0∞)⁻¹ *
        ∑ chi : DirichletCharacter ℂ q,
          literalRemainderMaxSq chi (sigma q chi) T epsilon X x

theorem measurable_familyDyadicZeroMajorant
    (Q N : ℕ) (T H X : ℝ) :
    Measurable (familyDyadicZeroMajorant Q N T H X) := by
  unfold familyDyadicZeroMajorant
  apply Finset.measurable_sum
  intro q hq
  split_ifs with hq0
  · exact measurable_const
  · letI : NeZero q := ⟨hq0⟩
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro chi hchi
    exact measurable_const.mul
      (measurable_finiteRightMaxSq
        (primitiveZeroNormField chi X T)
        (measurable_primitiveZeroNormField chi X T)
        (dyadicRightScales H N))

/-- Floor-tight simultaneous maximum dominated by a measurable dyadic zero
family plus the literal total tail family. -/
theorem simultaneousAPMax_le_dyadicZero_add_literalTail
    {K epsilon X x T H : ℝ} {Q N : ℕ}
    (hQ : Q = ⌊Real.rpow (Real.log X) K⌋₊)
    (hH : H = Real.rpow X (2 / 15 + epsilon))
    (hX : 0 < X) (hx : x ∈ Set.Icc (X / 2) (4 * X))
    (hreach : X / H < (2 : ℝ) ^ (N + 1))
    (sigma : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ)
    (hlegal : ∀ (q : ℕ) (hq : q ∈ Finset.Icc 1 Q)
        (chi : DirichletCharacter ℂ q),
      @primitiveContourLegal q
        ⟨Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩ chi
        (sigma q chi) T) :
    simultaneousAPMax K epsilon X x ≤
      2 * (familyDyadicZeroMajorant Q N T H X x +
        familyLiteralTailMajorant Q sigma T epsilon X x) := by
  subst Q
  refine (MAPAPFloorMaximalBridge.simultaneousAPMax_le_sum_floor_fixedModulusMajorants
    (fun q =>
      if hq : q = 0 then 0 else
        letI : NeZero q := ⟨hq⟩
        fixedModulusZeroTailMajorant q (sigma q) T epsilon X x) ?_).trans ?_
  · intro q hqpos hqcap
    letI : NeZero q := ⟨Nat.ne_of_gt hqpos⟩
    simp only [dif_neg (Nat.ne_of_gt hqpos)]
    apply fixedModulusAPMax_le_zeroTailMajorant (sigma q)
    · intro chi
      exact hlegal q
        (Finset.mem_Icc.mpr ⟨hqpos, Nat.le_floor hqcap⟩) chi
    · exact hX
    · exact hx
  · simp only [fixedModulusZeroTailMajorant, familyDyadicZeroMajorant,
      familyLiteralTailMajorant]
    let S := Finset.Icc 1 ⌊Real.rpow (Real.log X) K⌋₊
    let Zold : ℕ → ℝ≥0∞ := fun q =>
      if hq : q = 0 then 0 else
        letI : NeZero q := ⟨hq⟩
        (q.totient : ℝ≥0∞)⁻¹ *
          ∑ chi : DirichletCharacter ℂ q,
            rightMaxSqBetween (primitiveZeroNormField chi X T)
              (Real.rpow X (2 / 15 + epsilon)) X x
    let Znew : ℕ → ℝ≥0∞ := fun q =>
      if hq : q = 0 then 0 else
        letI : NeZero q := ⟨hq⟩
        (q.totient : ℝ≥0∞)⁻¹ *
          ∑ chi : DirichletCharacter ℂ q,
            4 * finiteRightMaxSq (primitiveZeroNormField chi X T)
              (dyadicRightScales H N) x
    let R : ℕ → ℝ≥0∞ := fun q =>
      if hq : q = 0 then 0 else
        letI : NeZero q := ⟨hq⟩
        (q.totient : ℝ≥0∞)⁻¹ *
          ∑ chi : DirichletCharacter ℂ q,
            literalRemainderMaxSq chi (sigma q chi) T epsilon X x
    have hcalc : (∑ q ∈ S, 2 * (Zold q + R q)) ≤
        2 * ((∑ q ∈ S, Znew q) + ∑ q ∈ S, R q) := by
      calc
      (∑ q ∈ S, 2 * (Zold q + R q)) ≤
          ∑ q ∈ S, 2 * (Znew q + R q) := by
        apply Finset.sum_le_sum
        intro q hq
        gcongr
        dsimp only [Zold, Znew]
        have hqpos := (Finset.mem_Icc.mp hq).1
        have hq0 : q ≠ 0 := Nat.ne_of_gt hqpos
        simp only [dif_neg hq0]
        letI : NeZero q := ⟨hq0⟩
        gcongr with chi
        rw [hH]
        exact rightMaxSqBetween_le_dyadic
          (primitiveZeroNormField chi X T)
          (Real.rpow_pos_of_pos hX _) (by simpa [hH] using hreach)
      _ = 2 * ((∑ q ∈ S, Znew q) + ∑ q ∈ S, R q) := by
        rw [mul_add, Finset.mul_sum, Finset.mul_sum,
          ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro q hq
        rw [mul_add]
    convert hcalc using 1
    · apply Finset.sum_congr rfl
      intro q hq
      have hq0 : q ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hq).1
      simp [Zold, R, hq0, mul_add]

/-- Integrated finite-dyadic zero family costs exactly the number of dyadic
scales, with the character normalization retained until the final harmless
`1/phi(q) ≤ 1` step. -/
theorem lintegral_familyDyadicZeroMajorant_le
    (Q N : ℕ) {T H X : ℝ} (hH : 0 < H) :
    (∫⁻ x in Set.Icc (X / 2) (4 * X),
        familyDyadicZeroMajorant Q N T H X x) ≤
      4 * (N + 1 : ℝ≥0∞) * apZeroFieldEnergy Q X T := by
  unfold familyDyadicZeroMajorant
  rw [lintegral_finsetSum (Finset.Icc 1 Q)]
  · unfold apZeroFieldEnergy
    calc
      (∑ q ∈ Finset.Icc 1 Q,
          ∫⁻ x in Set.Icc (X / 2) (4 * X),
            (if hq : q = 0 then 0 else
              letI : NeZero q := ⟨hq⟩
              (q.totient : ℝ≥0∞)⁻¹ *
                ∑ chi : DirichletCharacter ℂ q,
                  4 * finiteRightMaxSq (primitiveZeroNormField chi X T)
                    (dyadicRightScales H N) x)) ≤
          ∑ q ∈ Finset.Icc 1 Q,
            4 * (N + 1 : ℝ≥0∞) * zeroFieldEnergyAtLevel q X T := by
        apply Finset.sum_le_sum
        intro q hq
        have hqpos := (Finset.mem_Icc.mp hq).1
        have hq0 : q ≠ 0 := Nat.ne_of_gt hqpos
        letI : NeZero q := ⟨hq0⟩
        simp only [dif_neg hq0, zeroFieldEnergyAtLevel, dite_false]
        have hphiNat : 0 < q.totient := Nat.totient_pos.mpr hqpos
        have hphiOne : (1 : ℝ≥0∞) ≤ (q.totient : ℝ≥0∞) := by
          exact_mod_cast hphiNat
        calc
          (∫⁻ x in Set.Icc (X / 2) (4 * X),
              (q.totient : ℝ≥0∞)⁻¹ *
                ∑ chi : DirichletCharacter ℂ q,
                  4 * finiteRightMaxSq (primitiveZeroNormField chi X T)
                    (dyadicRightScales H N) x) ≤
            ∫⁻ x : ℝ,
              (q.totient : ℝ≥0∞)⁻¹ *
                ∑ chi : DirichletCharacter ℂ q,
                  4 * finiteRightMaxSq (primitiveZeroNormField chi X T)
                    (dyadicRightScales H N) x :=
              setLIntegral_le_lintegral _ _
          _ = (q.totient : ℝ≥0∞)⁻¹ *
              ∑ chi : DirichletCharacter ℂ q,
                ∫⁻ x : ℝ,
                  4 * finiteRightMaxSq (primitiveZeroNormField chi X T)
                    (dyadicRightScales H N) x := by
            rw [lintegral_const_mul]
            · congr 1
              exact lintegral_finsetSum Finset.univ (fun chi hchi =>
                measurable_const.mul
                  (measurable_finiteRightMaxSq
                    (primitiveZeroNormField chi X T)
                    (measurable_primitiveZeroNormField chi X T)
                    (dyadicRightScales H N)))
            · apply Finset.measurable_sum
              intro chi hchi
              exact measurable_const.mul
                (measurable_finiteRightMaxSq
                  (primitiveZeroNormField chi X T)
                  (measurable_primitiveZeroNormField chi X T)
                  (dyadicRightScales H N))
          _ ≤ (q.totient : ℝ≥0∞)⁻¹ *
              ∑ chi : DirichletCharacter ℂ q,
                4 * ((N + 1 : ℝ≥0∞) *
                  ∫⁻ x : ℝ, (primitiveZeroNormField chi X T x) ^ 2) := by
            gcongr with chi
            rw [lintegral_const_mul 4
              (measurable_finiteRightMaxSq
                (primitiveZeroNormField chi X T)
                (measurable_primitiveZeroNormField chi X T)
                (dyadicRightScales H N))]
            gcongr
            simpa [Nat.cast_add, Nat.cast_one] using
              (lintegral_finiteRightMaxSq_le
                (primitiveZeroNormField chi X T)
                (measurable_primitiveZeroNormField chi X T)
                (dyadicRightScales H N)
                (fun j => mul_pos (pow_pos (by norm_num) _) hH))
          _ ≤ ∑ chi : DirichletCharacter ℂ q,
                4 * ((N + 1 : ℝ≥0∞) *
                  ∫⁻ x : ℝ, (primitiveZeroNormField chi X T x) ^ 2) := by
            have hinv : (q.totient : ℝ≥0∞)⁻¹ ≤ 1 :=
              ENNReal.inv_le_one.mpr hphiOne
            exact (mul_le_mul_right' hinv _).trans_eq (one_mul _)
          _ = 4 * (N + 1 : ℝ≥0∞) *
              ∑ chi : DirichletCharacter ℂ q,
                ∫⁻ x : ℝ, (primitiveZeroNormField chi X T x) ^ 2 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro chi hchi
            ring
      _ = 4 * (N + 1 : ℝ≥0∞) *
          ∑ q ∈ Finset.Icc 1 Q, zeroFieldEnergyAtLevel q X T := by
        rw [Finset.mul_sum]
  · intro q hq
    split_ifs with hq0
    · exact measurable_const
    · letI : NeZero q := ⟨hq0⟩
      apply Measurable.const_mul
      apply Finset.measurable_sum
      intro chi hchi
      exact measurable_const.mul
        (measurable_finiteRightMaxSq
          (primitiveZeroNormField chi X T)
          (measurable_primitiveZeroNormField chi X T)
          (dyadicRightScales H N))

/-- Generous logarithmic absorption of the canonical dyadic scale count. -/
theorem eight_dyadicScaleCount_add_one_le_log_sq
    {X : ℝ} (hX : Real.exp 1 ≤ X) :
    8 * (dyadicScaleCount X + 1 : ℝ≥0∞) ≤
      ENNReal.ofReal (32 * (Real.log X) ^ 2) := by
  have hXpos : 0 < X := (Real.exp_pos 1).trans_le hX
  have hlog : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hXpos]
    exact hX
  have hlog2 : 1 / 2 < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hlogb : Real.logb 2 X ≤ 2 * Real.log X := by
    unfold Real.logb
    apply (div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).2
    nlinarith
  have hN := dyadicScaleCount_cast_lt_logb_add_one (X := X)
    (show 1 ≤ X by
      exact (Real.one_lt_exp_iff.mpr zero_lt_one).le.trans hX)
  have hreal :
      8 * ((dyadicScaleCount X : ℝ) + 1) ≤
        32 * (Real.log X) ^ 2 := by
    have hNlog : (dyadicScaleCount X : ℝ) + 1 ≤ 4 * Real.log X := by
      linarith
    have hlogsq : Real.log X ≤ (Real.log X) ^ 2 := by
      nlinarith
    nlinarith
  have hof := ENNReal.ofReal_le_ofReal hreal
  calc
    8 * (dyadicScaleCount X + 1 : ℝ≥0∞) =
        ENNReal.ofReal
          (8 * (((dyadicScaleCount X + 1 : ℕ) : ℝ))) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8)]
      push_cast
      rw [ENNReal.ofReal_add (Nat.cast_nonneg _) (by norm_num),
        ENNReal.ofReal_natCast]
      norm_num
    _ = ENNReal.ofReal
          (8 * ((dyadicScaleCount X : ℝ) + 1)) := by
      norm_num
    _ ≤ ENNReal.ofReal (32 * (Real.log X) ^ 2) := hof

/-- The corrected total-family literal tail estimate supplies exactly the
remaining explicit-formula transfer contract.  No zero-density input is used
here. -/
theorem maximalExplicitFormulaRemainderTransfer_of_tailFamilySquare
    (htail : APExplicitFormulaTailFamilySquare) :
    MAPAPConditionalShortIntervalConnector.APMaximalExplicitFormulaRemainderTransfer := by
  intro K A epsilon hK hA hepsilon hepsilonCap
  rcases htail K A epsilon hK hA hepsilon hepsilonCap with
    ⟨Ct, Xt, hCt, hXt, htailX⟩
  let C : ℝ := 32 + 2 * Ct
  let X0 : ℝ := max (Real.exp 1) Xt
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hX0 : 2 ≤ X0 := by
    have hexp : 2 < Real.exp 1 := by
      nlinarith [Real.exp_one_gt_d9]
    exact hexp.le.trans (le_max_left _ _)
  refine ⟨C, X0, hC, hX0, ?_⟩
  intro X hXX0
  have hXexp : Real.exp 1 ≤ X :=
    (le_max_left _ _).trans hXX0
  have hXXt : Xt ≤ X :=
    (le_max_right _ _).trans hXX0
  have hXpos : 0 < X := (Real.exp_pos 1).trans_le hXexp
  have hXone : 1 ≤ X :=
    (Real.one_lt_exp_iff.mpr zero_lt_one).le.trans hXexp
  have hlog : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hXpos]
    exact hXexp
  let reserve : ℝ := min epsilon (1 / 10)
  let T : ℝ := apZeroHeight reserve X
  let Q : ℕ := ⌊Real.rpow (Real.log X) K⌋₊
  let H : ℝ := Real.rpow X (2 / 15 + epsilon)
  let N : ℕ := dyadicScaleCount X
  have hHpos : 0 < H := Real.rpow_pos_of_pos hXpos _
  have hHone : 1 ≤ H := by
    apply Real.one_le_rpow hXone
    dsimp [H]
    linarith
  have hreach : X / H < (2 : ℝ) ^ (N + 1) := by
    have hdiv : X / H ≤ X := by
      exact (div_le_iff₀ hHpos).2 (by nlinarith)
    exact hdiv.trans_lt (lt_two_pow_dyadicScaleCount_add_one hXone)
  have htailAtX := htailX X hXXt
  dsimp only at htailAtX
  rcases htailAtX with ⟨sigma, hlegal, htailBound⟩
  have hzero :
      (∫⁻ x in Set.Icc (X / 2) (4 * X),
          familyDyadicZeroMajorant Q N T H X x) ≤
        4 * (N + 1 : ℝ≥0∞) * apZeroFieldEnergy Q X T :=
    lintegral_familyDyadicZeroMajorant_le Q N hHpos
  have hpoint : ∀ x ∈ Set.Icc (X / 2) (4 * X),
      simultaneousAPMax K epsilon X x ≤
        2 * (familyDyadicZeroMajorant Q N T H X x +
          familyLiteralTailMajorant Q sigma T epsilon X x) := by
    intro x hx
    exact simultaneousAPMax_le_dyadicZero_add_literalTail
      rfl rfl hXpos hx hreach sigma hlegal
  have hscale : 8 * (N + 1 : ℝ≥0∞) ≤
      ENNReal.ofReal (C * (Real.log X) ^ 2) := by
    refine (eight_dyadicScaleCount_add_one_le_log_sq hXexp).trans ?_
    apply ENNReal.ofReal_le_ofReal
    have hlogSq : 0 ≤ (Real.log X) ^ 2 := sq_nonneg _
    dsimp [C]
    nlinarith [hCt]
  have htailCoeff :
      2 * ENNReal.ofReal
          (Ct * X * Real.rpow (Real.log X) (-A)) ≤
        ENNReal.ofReal
          (C * X * Real.rpow (Real.log X) (-A)) := by
    have hrpow : 0 ≤ Real.rpow (Real.log X) (-A) :=
      Real.rpow_nonneg (zero_le_one.trans hlog) _
    have htNonneg : 0 ≤ Ct * X * Real.rpow (Real.log X) (-A) := by
      positivity
    rw [← ENNReal.ofReal_ofNat 2,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    apply ENNReal.ofReal_le_ofReal
    have hCge : 2 * Ct ≤ C := by
      dsimp [C]
      linarith
    calc
      2 * (Ct * X * Real.rpow (Real.log X) (-A)) =
          (2 * Ct) * (X * Real.rpow (Real.log X) (-A)) := by ring
      _ ≤ C * (X * Real.rpow (Real.log X) (-A)) :=
        mul_le_mul_of_nonneg_right hCge (mul_nonneg hXpos.le hrpow)
      _ = C * X * Real.rpow (Real.log X) (-A) := by ring
  change (∫⁻ x in Set.Icc (X / 2) (4 * X),
      simultaneousAPMax K epsilon X x) ≤ _
  calc
    (∫⁻ x in Set.Icc (X / 2) (4 * X),
        simultaneousAPMax K epsilon X x) ≤
      ∫⁻ x in Set.Icc (X / 2) (4 * X),
        2 * (familyDyadicZeroMajorant Q N T H X x +
          familyLiteralTailMajorant Q sigma T epsilon X x) := by
      exact setLIntegral_mono' measurableSet_Icc hpoint
    _ = 2 * ((∫⁻ x in Set.Icc (X / 2) (4 * X),
            familyDyadicZeroMajorant Q N T H X x) +
          ∫⁻ x in Set.Icc (X / 2) (4 * X),
            familyLiteralTailMajorant Q sigma T epsilon X x) := by
      rw [lintegral_const_mul' 2 _ (by norm_num)]
      rw [lintegral_add_left'
        (measurable_familyDyadicZeroMajorant Q N T H X).aemeasurable]
    _ ≤ 2 * (4 * (N + 1 : ℝ≥0∞) * apZeroFieldEnergy Q X T +
          ENNReal.ofReal
            (Ct * X * Real.rpow (Real.log X) (-A))) := by
      apply mul_le_mul_left'
      apply add_le_add hzero
      simpa [familyLiteralTailMajorant, reserve, T, Q] using htailBound
    _ = (8 * (N + 1 : ℝ≥0∞)) * apZeroFieldEnergy Q X T +
          2 * ENNReal.ofReal
            (Ct * X * Real.rpow (Real.log X) (-A)) := by
      ring
    _ ≤ ENNReal.ofReal (C * (Real.log X) ^ 2) *
          apZeroFieldEnergy Q X T +
        ENNReal.ofReal
          (C * X * Real.rpow (Real.log X) (-A)) := by
      exact add_le_add (mul_le_mul_right' hscale _) htailCoeff
    _ = ENNReal.ofReal (C * (Real.log X) ^ 2) *
          apZeroFieldEnergy
            ⌊Real.rpow (Real.log X) K⌋₊ X
            (apZeroHeight (min epsilon (1 / 10)) X) +
        ENNReal.ofReal
          (C * X * Real.rpow (Real.log X) (-A)) := by
      rfl

/-- End-to-end AP export.  After all deterministic calculus, character
Cauchy, maximal and family-integration steps have been discharged, the only
analytic premises are weighted zero-mass saving (2.7) and the corrected
literal total-family contour-tail estimate. -/
theorem simultaneousShortIntervalAP_of_weightedZeroMass_of_tailFamilySquare
    (h27 : APWeightedZeroMassLogSaving)
    (htail : APExplicitFormulaTailFamilySquare) :
    APFoundation.SimultaneousShortIntervalAP :=
  MAPAPConditionalShortIntervalConnector.simultaneousShortIntervalAP_of_weightedZeroMass_of_remainderTransfer
    h27 (maximalExplicitFormulaRemainderTransfer_of_tailFamilySquare htail)

end
end MAPAPTailToRemainderTransfer

#print axioms MAPAPTailToRemainderTransfer.ofReal_primitiveFieldAverage_eq_rightAverage
#print axioms MAPAPTailToRemainderTransfer.fixedModulusAPMax_le_zeroTailMajorant
#print axioms MAPAPTailToRemainderTransfer.measurable_familyDyadicZeroMajorant
#print axioms MAPAPTailToRemainderTransfer.simultaneousAPMax_le_dyadicZero_add_literalTail
#print axioms MAPAPTailToRemainderTransfer.lintegral_familyDyadicZeroMajorant_le
#print axioms MAPAPTailToRemainderTransfer.eight_dyadicScaleCount_add_one_le_log_sq
#print axioms MAPAPTailToRemainderTransfer.maximalExplicitFormulaRemainderTransfer_of_tailFamilySquare
#print axioms MAPAPTailToRemainderTransfer.simultaneousShortIntervalAP_of_weightedZeroMass_of_tailFamilySquare
