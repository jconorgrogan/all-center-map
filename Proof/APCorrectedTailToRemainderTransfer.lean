import APCorrectedPaperEdgeTail
import APTailToRemainderTransfer

/-!
# Deterministic transfer from the corrected common-height paper-edge tail

This module reuses the certified dyadic maximal and family integration stack.
The only changes are the paper-edge endpoint remainder and the existential
common contour height.  Exact `1/phi(q)` weights are retained.
-/

namespace MAPAPCorrectedTailToRemainderTransfer

open MeasureTheory Set
open scoped BigOperators ENNReal
open APFoundation APMaximalExplicitFormulaBridge OneSidedMaximalL2
open APExplicitFormulaMajorantAdapter
open MAPFixedScaleAPZeroRoute
open MAPAPCorrectedCommonHeightContract MAPAPCorrectedPaperEdgeTail
open MAPAPTailToRemainderTransfer

noncomputable section

variable {q : ℕ} [NeZero q]

/-- Per-modulus zero plus corrected paper-edge tail majorant. -/
def fixedModulusPaperEdgeZeroTailMajorant
    (q : ℕ) [NeZero q] (sigma : DirichletCharacter ℂ q → ℝ)
    (T epsilon X x : ℝ) : ℝ≥0∞ :=
  2 * ((q.totient : ℝ≥0∞)⁻¹ *
      ∑ chi : DirichletCharacter ℂ q,
        rightMaxSqBetween (primitiveZeroNormField chi X T)
          (Real.rpow X (2 / 15 + epsilon)) X x +
    (q.totient : ℝ≥0∞)⁻¹ *
      ∑ chi : DirichletCharacter ℂ q,
        paperEdgeRemainderMaxSq chi (sigma chi) T epsilon X x)

/-- Character Cauchy and the legal aperture suprema at the paper edge. -/
theorem fixedModulusAPMax_le_paperEdgeZeroTailMajorant
    {q : ℕ} [NeZero q] {T epsilon X x : ℝ}
    (sigma : DirichletCharacter ℂ q → ℝ)
    (hlegal : ∀ chi : DirichletCharacter ℂ q,
      paperEdgeContourLegal chi (sigma chi) T)
    (hXtwo : 2 ≤ X) (hx : x ∈ Set.Icc (X / 2) (4 * X)) :
    fixedModulusAPMax q epsilon X x ≤
      fixedModulusPaperEdgeZeroTailMajorant q sigma T epsilon X x := by
  have hX : 0 < X := lt_of_lt_of_le (by norm_num) hXtwo
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
  have hxone : 1 ≤ x := by linarith [hx.1]
  have hxYone : 1 ≤ x + Y := by linarith
  have hNx : 1 ≤ ⌊x⌋₊ :=
    Nat.le_floor (show ((1 : ℕ) : ℝ) ≤ x by simpa using hxone)
  have hNxY : 1 ≤ ⌊x + Y⌋₊ :=
    Nat.le_floor (show ((1 : ℕ) : ℝ) ≤ x + Y by simpa using hxYone)
  let z : DirichletCharacter ℂ q → ℝ := fun chi =>
    Y⁻¹ * (∫ t : ℝ in x..x + Y,
      ‖primitiveActualZeroField chi T t‖)
  let r : DirichletCharacter ℂ q → ℝ := fun chi =>
    ‖(PaperEdgePrimitiveComponents.endpointRemainder
          chi (sigma chi) T (x + Y) -
        PaperEdgePrimitiveComponents.endpointRemainder
          chi (sigma chi) T x) / Y‖
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
    apply normalizedAPError_sq_le_mean_characterMajorants hY ha
      (fun chi => z chi + r chi)
    intro chi
    exact norm_ambientCharacterWindowError_div_le_primitiveField_add_paperEdgeTail
      chi (hlegal chi) ((half_pos hX).trans_le hx.1) hY hNx hNxY
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
  · simp only [fixedModulusPaperEdgeZeroTailMajorant]
    gcongr
    · rw [ENNReal.ofReal_mul (inv_nonneg.mpr hphi.le),
        ENNReal.ofReal_inv_of_pos hphi, ENNReal.ofReal_natCast,
        ENNReal.ofReal_sum_of_nonneg]
      · gcongr with chi
        rw [ENNReal.ofReal_pow (hznonneg chi) 2,
          ofReal_primitiveFieldAverage_eq_rightAverage chi hX hx hY hYhigh]
        exact le_iSup_of_le Y <| le_iSup_of_le hYlow <|
          le_iSup_of_le hYhigh le_rfl
      · intro chi hchi
        exact sq_nonneg _
    · rw [ENNReal.ofReal_mul (inv_nonneg.mpr hphi.le),
        ENNReal.ofReal_inv_of_pos hphi, ENNReal.ofReal_natCast,
        ENNReal.ofReal_sum_of_nonneg]
      · gcongr with chi
        rw [ENNReal.ofReal_pow (hrnonneg chi) 2]
        exact le_iSup_of_le Y <| le_iSup_of_le hYlow <|
          le_iSup_of_le hYhigh le_rfl
      · intro chi hchi
        exact sq_nonneg _
  · positivity
  · positivity

/-- Floor-tight simultaneous maximum at an arbitrary legal common height. -/
theorem simultaneousAPMax_le_dyadicZero_add_paperEdgeTail
    {K epsilon X x T H : ℝ} {Q N : ℕ}
    (hQ : Q = ⌊Real.rpow (Real.log X) K⌋₊)
    (hH : H = Real.rpow X (2 / 15 + epsilon))
    (hXtwo : 2 ≤ X) (hx : x ∈ Set.Icc (X / 2) (4 * X))
    (hreach : X / H < (2 : ℝ) ^ (N + 1))
    (sigma : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ)
    (hlegal : ∀ (q : ℕ) (hq : q ∈ Finset.Icc 1 Q)
        (chi : DirichletCharacter ℂ q),
      @paperEdgeContourLegal q
        ⟨Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩ chi
        (sigma q chi) T) :
    simultaneousAPMax K epsilon X x ≤
      2 * (familyDyadicZeroMajorant Q N T H X x +
        familyPaperEdgeTailMajorant Q sigma T epsilon X x) := by
  subst Q
  refine (MAPAPFloorMaximalBridge.simultaneousAPMax_le_sum_floor_fixedModulusMajorants
    (fun q =>
      if hq : q = 0 then 0 else
        letI : NeZero q := ⟨hq⟩
        fixedModulusPaperEdgeZeroTailMajorant q (sigma q) T epsilon X x) ?_).trans ?_
  · intro q hqpos hqcap
    letI : NeZero q := ⟨Nat.ne_of_gt hqpos⟩
    simp only [dif_neg (Nat.ne_of_gt hqpos)]
    apply fixedModulusAPMax_le_paperEdgeZeroTailMajorant (sigma q)
    · intro chi
      exact hlegal q
        (Finset.mem_Icc.mpr ⟨hqpos, Nat.le_floor hqcap⟩) chi
    · exact hXtwo
    · exact hx
  · simp only [fixedModulusPaperEdgeZeroTailMajorant,
      MAPAPTailToRemainderTransfer.familyDyadicZeroMajorant,
      familyPaperEdgeTailMajorant]
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
            paperEdgeRemainderMaxSq chi (sigma q chi) T epsilon X x
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
          have hX : 0 < X := lt_of_lt_of_le (by norm_num) hXtwo
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

/-- Corrected transfer target: the one common selected height is kept in the
conclusion instead of being silently replaced by the prescribed base height. -/
def CommonHeightAPMaximalExplicitFormulaRemainderTransfer : Prop :=
  ∀ K A epsilon : ℝ,
    0 < K → 0 < A → 0 < epsilon → epsilon ≤ 13 / 30 →
    ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧
      ∀ X : ℝ, X0 ≤ X →
        let reserve := min epsilon (1 / 10)
        let H0 := apZeroHeight reserve X
        let Q := ⌊Real.rpow (Real.log X) K⌋₊
        ∃ T ∈ Set.Ioo H0 (H0 + 1),
          (∫⁻ x in Set.Icc (X / 2) (4 * X),
              simultaneousAPMax K epsilon X x) ≤
            ENNReal.ofReal (C * (Real.log X) ^ 2) *
                apZeroFieldEnergy Q X T +
              ENNReal.ofReal (C * X * Real.rpow (Real.log X) (-A))

/-- The corrected one-integral tail contract deterministically gives the
common-height maximal transfer. -/
theorem commonHeightRemainderTransfer_of_correctedTailFamilySquare
    (htail : CorrectedAPExplicitFormulaTailFamilySquare) :
    CommonHeightAPMaximalExplicitFormulaRemainderTransfer := by
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
  have hXexp : Real.exp 1 ≤ X := (le_max_left _ _).trans hXX0
  have hXXt : Xt ≤ X := (le_max_right _ _).trans hXX0
  have hXtwo : 2 ≤ X := hX0.trans hXX0
  have hXpos : 0 < X := (Real.exp_pos 1).trans_le hXexp
  have hXone : 1 ≤ X :=
    (Real.one_lt_exp_iff.mpr zero_lt_one).le.trans hXexp
  let reserve : ℝ := min epsilon (1 / 10)
  let H0 : ℝ := apZeroHeight reserve X
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
  rcases htailAtX with ⟨T, hT, sigma, hlegal, htailBound⟩
  refine ⟨T, hT, ?_⟩
  have hzero := lintegral_familyDyadicZeroMajorant_le Q N (T := T)
    (X := X) hHpos
  have hpoint : ∀ x ∈ Set.Icc (X / 2) (4 * X),
      simultaneousAPMax K epsilon X x ≤
        2 * (familyDyadicZeroMajorant Q N T H X x +
          familyPaperEdgeTailMajorant Q sigma T epsilon X x) := by
    intro x hx
    exact simultaneousAPMax_le_dyadicZero_add_paperEdgeTail
      rfl rfl hXtwo hx hreach sigma hlegal
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
    have hlog : 1 ≤ Real.log X := by
      rw [Real.le_log_iff_exp_le hXpos]
      exact hXexp
    have hrpow : 0 ≤ Real.rpow (Real.log X) (-A) :=
      Real.rpow_nonneg (zero_le_one.trans hlog) _
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
        mul_le_mul_of_nonneg_right hCge
          (mul_nonneg hXpos.le hrpow)
      _ = C * X * Real.rpow (Real.log X) (-A) := by ring
  change (∫⁻ x in Set.Icc (X / 2) (4 * X),
      simultaneousAPMax K epsilon X x) ≤ _
  calc
    (∫⁻ x in Set.Icc (X / 2) (4 * X),
        simultaneousAPMax K epsilon X x) ≤
      ∫⁻ x in Set.Icc (X / 2) (4 * X),
        2 * (familyDyadicZeroMajorant Q N T H X x +
          familyPaperEdgeTailMajorant Q sigma T epsilon X x) := by
      exact setLIntegral_mono' measurableSet_Icc hpoint
    _ = 2 * ((∫⁻ x in Set.Icc (X / 2) (4 * X),
            familyDyadicZeroMajorant Q N T H X x) +
          ∫⁻ x in Set.Icc (X / 2) (4 * X),
            familyPaperEdgeTailMajorant Q sigma T epsilon X x) := by
      rw [lintegral_const_mul' 2 _ (by norm_num)]
      rw [lintegral_add_left'
        (measurable_familyDyadicZeroMajorant Q N T H X).aemeasurable]
    _ ≤ 2 * (4 * (N + 1 : ℝ≥0∞) * apZeroFieldEnergy Q X T +
          ENNReal.ofReal
            (Ct * X * Real.rpow (Real.log X) (-A))) := by
      apply mul_le_mul_left'
      apply add_le_add hzero
      simpa [familyPaperEdgeTailMajorant, reserve, H0, Q] using htailBound
    _ = (8 * (N + 1 : ℝ≥0∞)) * apZeroFieldEnergy Q X T +
          2 * ENNReal.ofReal
            (Ct * X * Real.rpow (Real.log X) (-A)) := by ring
    _ ≤ ENNReal.ofReal (C * (Real.log X) ^ 2) *
          apZeroFieldEnergy Q X T +
        ENNReal.ofReal
          (C * X * Real.rpow (Real.log X) (-A)) := by
      exact add_le_add (mul_le_mul_right' hscale _) htailCoeff

end
end MAPAPCorrectedTailToRemainderTransfer

#print axioms MAPAPCorrectedTailToRemainderTransfer.fixedModulusAPMax_le_paperEdgeZeroTailMajorant
#print axioms MAPAPCorrectedTailToRemainderTransfer.simultaneousAPMax_le_dyadicZero_add_paperEdgeTail
#print axioms MAPAPCorrectedTailToRemainderTransfer.commonHeightRemainderTransfer_of_correctedTailFamilySquare
