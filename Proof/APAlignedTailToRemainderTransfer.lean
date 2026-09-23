import APAlignedMaximalAdapter
import APCorrectedCommonHeightContract
import APFloorMaximalBridge

/-!
# Release-path AP transfer with half-integer Perron endpoints

The arithmetic prefix and Perron endpoints are aligned at half integers.  The
zero term is therefore exactly the sigma-truncated Perron field, averaged at
scale `Y+1` and base `x-1/2`.  The only source proposition left by this file is
the one-integral family square estimate for the aligned endpoint remainder.
-/

namespace MAPAPAlignedTailToRemainderTransfer

open MeasureTheory Set
open scoped BigOperators ENNReal
open APFoundation APMaximalExplicitFormulaBridge OneSidedMaximalL2
open APExplicitFormulaMajorantAdapter
open MAPFixedScaleAPZeroRoute MAPAPHalfIntegerAlignedTail
open MAPAPSelectedTruncatedZeroFieldEnergy28
open MAPAPAlignedMaximalAdapter MAPAPCorrectedCommonHeightContract

noncomputable section

variable {q : ℕ} [NeZero q]

/-- Legal-aperture maximal square of the half-integer-aligned remainder. -/
def alignedRemainderMaxSq
    (chi : DirichletCharacter ℂ q)
    (sigma T epsilon X x : ℝ) : ℝ≥0∞ :=
  ⨆ (Y : ℝ) (_hYlow : Real.rpow X (2 / 15 + epsilon) ≤ Y)
      (_hYhigh : Y ≤ X),
    ENNReal.ofReal
      ‖(alignedEndpointRemainder chi sigma T (x + Y) -
          alignedEndpointRemainder chi sigma T x) / Y‖ ^ 2

/-- One-outer-integral aligned tail family with exact character weights. -/
def familyAlignedTailMajorant
    (Q : ℕ) (sigma : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ)
    (T epsilon X x : ℝ) : ℝ≥0∞ :=
  ∑ q ∈ Finset.Icc 1 Q,
    if hq : q = 0 then 0 else
      letI : NeZero q := ⟨hq⟩
      (q.totient : ℝ≥0∞)⁻¹ *
        ∑ chi : DirichletCharacter ℂ q,
          alignedRemainderMaxSq chi (sigma q chi) T epsilon X x

/-- The sole analytic source left on the aligned release path.  One common
height and character-dependent positive left edges are selected for the whole
finite family.  The possibly nonmeasurable real-`Y` supremum remains inside a
single outer integral. -/
def AlignedAPExplicitFormulaTailFamilySquare : Prop :=
  ∀ K A epsilon : ℝ,
    0 < K → 0 < A → 0 < epsilon → epsilon ≤ 13 / 30 →
    ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧
      ∀ X : ℝ, X0 ≤ X →
        let reserve := min epsilon (1 / 10)
        let H0 := apZeroHeight reserve X
        let Q := ⌊Real.rpow (Real.log X) K⌋₊
        ∃ T ∈ Set.Ioo H0 (H0 + 1),
          ∃ sigma : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ,
            (∀ (q : ℕ) (hq : q ∈ Finset.Icc 1 Q)
                (chi : DirichletCharacter ℂ q),
              @paperEdgeContourLegal q
                ⟨Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩
                chi (sigma q chi) T) ∧
            (∫⁻ x in Set.Icc (X / 2) (4 * X),
                familyAlignedTailMajorant Q sigma T epsilon X x) ≤
              ENNReal.ofReal (C * X * Real.rpow (Real.log X) (-A))

/-- Per-modulus aligned zero plus endpoint-tail majorant.  The factor four
inside the zero term is the square of the endpoint-enlargement factor two;
the outer factor two is `(u+v)^2 ≤ 2(u^2+v^2)`. -/
def fixedModulusAlignedZeroTailMajorant
    (q : ℕ) [NeZero q] (sigma : DirichletCharacter ℂ q → ℝ)
    (T epsilon X x : ℝ) : ℝ≥0∞ :=
  2 * ((q.totient : ℝ≥0∞)⁻¹ *
      ∑ chi : DirichletCharacter ℂ q,
        4 * rightMaxSqBetween
          (truncatedZeroNormField chi (sigma chi) X T)
          (Real.rpow X (2 / 15 + epsilon) + 1) (X + 1) (x - 1 / 2) +
    (q.totient : ℝ≥0∞)⁻¹ *
      ∑ chi : DirichletCharacter ℂ q,
        alignedRemainderMaxSq chi (sigma chi) T epsilon X x)

/-- Character Cauchy followed by the aligned endpoint identity. -/
theorem fixedModulusAPMax_le_alignedZeroTailMajorant
    {q : ℕ} [NeZero q] {T epsilon X x : ℝ}
    (sigma : DirichletCharacter ℂ q → ℝ)
    (hlegal : ∀ chi : DirichletCharacter ℂ q,
      paperEdgeContourLegal chi (sigma chi) T)
    (hepsilon : 0 < epsilon)
    (hXtwo : 2 ≤ X) (hx : x ∈ Set.Icc (X / 2) (4 * X)) :
    fixedModulusAPMax q epsilon X x ≤
      fixedModulusAlignedZeroTailMajorant q sigma T epsilon X x := by
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
  have hHone : 1 ≤ Real.rpow X (2 / 15 + epsilon) := by
    apply Real.one_le_rpow (by linarith)
    linarith
  have hYone : 1 ≤ Y := hHone.trans hYlow
  have hY : 0 < Y := zero_lt_one.trans_le hYone
  have hxone : 1 ≤ x := by linarith [hx.1]
  have hxYone : 1 ≤ x + Y := by linarith
  have hNx : 1 ≤ ⌊x⌋₊ :=
    Nat.le_floor (show ((1 : ℕ) : ℝ) ≤ x by simpa using hxone)
  have hNxY : 1 ≤ ⌊x + Y⌋₊ :=
    Nat.le_floor (show ((1 : ℕ) : ℝ) ≤ x + Y by simpa using hxYone)
  let z : DirichletCharacter ℂ q → ℝ := fun chi =>
    2 * ((Y + 1)⁻¹ *
      ∫ t : ℝ in x - 1 / 2..x + Y + 1 / 2,
        ‖perronZeroField chi (sigma chi) T t‖)
  let r : DirichletCharacter ℂ q → ℝ := fun chi =>
    ‖(alignedEndpointRemainder chi (sigma chi) T (x + Y) -
        alignedEndpointRemainder chi (sigma chi) T x) / Y‖
  have hznonneg : ∀ chi, 0 ≤ z chi := by
    intro chi
    dsimp only [z]
    apply mul_nonneg (by norm_num)
    apply mul_nonneg (inv_nonneg.mpr (by linarith : 0 ≤ Y + 1))
    apply intervalIntegral.integral_nonneg (by linarith)
    intro t ht
    exact norm_nonneg _
  have hrnonneg : ∀ chi, 0 ≤ r chi := fun chi => norm_nonneg _
  have hcauchy : |normalizedAPError x Y q a| ^ 2 ≤
      (q.totient : ℝ)⁻¹ *
        ∑ chi : DirichletCharacter ℂ q, (z chi + r chi) ^ 2 := by
    apply normalizedAPError_sq_le_mean_characterMajorants hY ha
      (fun chi => z chi + r chi)
    intro chi
    dsimp only [z, r]
    letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
    exact norm_ambientCharacterWindowError_div_le_alignedAverage_add_tail
      chi (hlegal chi) hxone hYone hNx hNxY
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
  · simp only [fixedModulusAlignedZeroTailMajorant]
    gcongr
    · rw [ENNReal.ofReal_mul (inv_nonneg.mpr hphi.le),
        ENNReal.ofReal_inv_of_pos hphi, ENNReal.ofReal_natCast,
        ENNReal.ofReal_sum_of_nonneg]
      · gcongr with chi
        rw [ENNReal.ofReal_pow (hznonneg chi) 2]
        dsimp only [z]
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num only [ENNReal.ofReal_ofNat, mul_pow]
        apply mul_le_mul_right
        letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
        exact ofReal_alignedZeroAverage_sq_le_rightMax
          chi hXtwo hx hYone hYhigh hYlow
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

/-- The sigma-truncated indicator field is measurable. -/
theorem measurable_truncatedZeroNormField
    (chi : DirichletCharacter ℂ q) (sigma X T : ℝ) :
    Measurable (truncatedZeroNormField chi sigma X T) := by
  unfold truncatedZeroNormField perronZeroField finiteZeroField
  apply Measurable.indicator _ measurableSet_Icc
  fun_prop

/-- Measurable finite-dyadic zero family after the aligned shift.  The
coefficient sixteen combines the squared endpoint enlargement with dyadic
covering. -/
def familyAlignedDyadicZeroMajorant
    (Q N : ℕ) (sigma : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ)
    (T H X x : ℝ) : ℝ≥0∞ :=
  ∑ q ∈ Finset.Icc 1 Q,
    if hq : q = 0 then 0 else
      letI : NeZero q := ⟨hq⟩
      (q.totient : ℝ≥0∞)⁻¹ *
        ∑ chi : DirichletCharacter ℂ q,
          16 * finiteRightMaxSq
            (truncatedZeroNormField chi (sigma q chi) X T)
            (dyadicRightScales (H + 1) N) (x - 1 / 2)

theorem measurable_familyAlignedDyadicZeroMajorant
    (Q N : ℕ) (sigma : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ)
    (T H X : ℝ) :
    Measurable (familyAlignedDyadicZeroMajorant Q N sigma T H X) := by
  unfold familyAlignedDyadicZeroMajorant
  apply Finset.measurable_sum
  intro q hq
  split_ifs with hq0
  · exact measurable_const
  · letI : NeZero q := ⟨hq0⟩
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro chi hchi
    exact measurable_const.mul
      ((measurable_finiteRightMaxSq
        (truncatedZeroNormField chi (sigma q chi) X T)
        (measurable_truncatedZeroNormField chi (sigma q chi) X T)
        (dyadicRightScales (H + 1) N)).comp
          (measurable_id.sub measurable_const))

/-- Floor-tight simultaneous maximum dominated by the aligned measurable
dyadic zero family plus the one-integral aligned endpoint tail. -/
theorem simultaneousAPMax_le_alignedDyadicZero_add_tail
    {K epsilon X x T H : ℝ} {Q N : ℕ}
    (hQ : Q = ⌊Real.rpow (Real.log X) K⌋₊)
    (hH : H = Real.rpow X (2 / 15 + epsilon))
    (hepsilon : 0 < epsilon)
    (hXtwo : 2 ≤ X) (hx : x ∈ Set.Icc (X / 2) (4 * X))
    (hreach : (X + 1) / (H + 1) < (2 : ℝ) ^ (N + 1))
    (sigma : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ)
    (hlegal : ∀ (q : ℕ) (hq : q ∈ Finset.Icc 1 Q)
        (chi : DirichletCharacter ℂ q),
      @paperEdgeContourLegal q
        ⟨Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩ chi
        (sigma q chi) T) :
    simultaneousAPMax K epsilon X x ≤
      2 * (familyAlignedDyadicZeroMajorant Q N sigma T H X x +
        familyAlignedTailMajorant Q sigma T epsilon X x) := by
  subst Q
  refine (MAPAPFloorMaximalBridge.simultaneousAPMax_le_sum_floor_fixedModulusMajorants
    (fun q =>
      if hq : q = 0 then 0 else
        letI : NeZero q := ⟨hq⟩
        fixedModulusAlignedZeroTailMajorant q (sigma q) T epsilon X x) ?_).trans ?_
  · intro q hqpos hqcap
    letI : NeZero q := ⟨Nat.ne_of_gt hqpos⟩
    simp only [dif_neg (Nat.ne_of_gt hqpos)]
    apply fixedModulusAPMax_le_alignedZeroTailMajorant (sigma q)
    · intro chi
      exact hlegal q
        (Finset.mem_Icc.mpr ⟨hqpos, Nat.le_floor hqcap⟩) chi
    · exact hepsilon
    · exact hXtwo
    · exact hx
  · simp only [fixedModulusAlignedZeroTailMajorant,
      familyAlignedDyadicZeroMajorant, familyAlignedTailMajorant]
    let S := Finset.Icc 1 ⌊Real.rpow (Real.log X) K⌋₊
    let Zold : ℕ → ℝ≥0∞ := fun q =>
      if hq : q = 0 then 0 else
        letI : NeZero q := ⟨hq⟩
        (q.totient : ℝ≥0∞)⁻¹ *
          ∑ chi : DirichletCharacter ℂ q,
            4 * rightMaxSqBetween
              (truncatedZeroNormField chi (sigma q chi) X T)
              (Real.rpow X (2 / 15 + epsilon) + 1) (X + 1) (x - 1 / 2)
    let Znew : ℕ → ℝ≥0∞ := fun q =>
      if hq : q = 0 then 0 else
        letI : NeZero q := ⟨hq⟩
        (q.totient : ℝ≥0∞)⁻¹ *
          ∑ chi : DirichletCharacter ℂ q,
            16 * finiteRightMaxSq
              (truncatedZeroNormField chi (sigma q chi) X T)
              (dyadicRightScales (H + 1) N) (x - 1 / 2)
    let R : ℕ → ℝ≥0∞ := fun q =>
      if hq : q = 0 then 0 else
        letI : NeZero q := ⟨hq⟩
        (q.totient : ℝ≥0∞)⁻¹ *
          ∑ chi : DirichletCharacter ℂ q,
            alignedRemainderMaxSq chi (sigma q chi) T epsilon X x
    have hHpos : 0 < H + 1 := by
      rw [hH]
      have hXpos : 0 < X := lt_of_lt_of_le (by norm_num) hXtwo
      have hrpow : 0 ≤ Real.rpow X (2 / 15 + epsilon) :=
        Real.rpow_nonneg hXpos.le _
      linarith
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
          apply mul_le_mul_right
          apply Finset.sum_le_sum
          intro chi hchi
          have hmax := rightMaxSqBetween_le_dyadic
            (truncatedZeroNormField chi (sigma q chi) X T)
            (x := x - 1 / 2) hHpos hreach
          calc
            4 * rightMaxSqBetween
                (truncatedZeroNormField chi (sigma q chi) X T)
                (Real.rpow X (2 / 15 + epsilon) + 1) (X + 1)
                (x - 1 / 2) ≤
              4 * (4 * finiteRightMaxSq
                (truncatedZeroNormField chi (sigma q chi) X T)
                (dyadicRightScales (H + 1) N) (x - 1 / 2)) := by
                  apply mul_le_mul_right
                  simpa [hH] using hmax
            _ = 16 * finiteRightMaxSq
                (truncatedZeroNormField chi (sigma q chi) X T)
                (dyadicRightScales (H + 1) N) (x - 1 / 2) := by ring
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

/-- Integrated aligned finite-dyadic family.  Translation by `-1/2` leaves
the global `L²` integral unchanged. -/
theorem lintegral_familyAlignedDyadicZeroMajorant_le
    (Q N : ℕ) (sigma : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ)
    {T H X : ℝ} (hH : 0 < H + 1) :
    (∫⁻ x in Set.Icc (X / 2) (4 * X),
        familyAlignedDyadicZeroMajorant Q N sigma T H X x) ≤
      16 * (N + 1 : ℝ≥0∞) *
        truncatedAPZeroFieldEnergy Q sigma X T := by
  unfold familyAlignedDyadicZeroMajorant
  rw [lintegral_finsetSum (Finset.Icc 1 Q)]
  · unfold truncatedAPZeroFieldEnergy
    calc
      (∑ q ∈ Finset.Icc 1 Q,
          ∫⁻ x in Set.Icc (X / 2) (4 * X),
            (if hq : q = 0 then 0 else
              letI : NeZero q := ⟨hq⟩
              (q.totient : ℝ≥0∞)⁻¹ *
                ∑ chi : DirichletCharacter ℂ q,
                  16 * finiteRightMaxSq
                    (truncatedZeroNormField chi (sigma q chi) X T)
                    (dyadicRightScales (H + 1) N) (x - 1 / 2))) ≤
          ∑ q ∈ Finset.Icc 1 Q,
            16 * (N + 1 : ℝ≥0∞) *
              truncatedZeroFieldEnergyAtLevel q (sigma q) X T := by
        apply Finset.sum_le_sum
        intro q hq
        have hqpos := (Finset.mem_Icc.mp hq).1
        have hq0 : q ≠ 0 := Nat.ne_of_gt hqpos
        letI : NeZero q := ⟨hq0⟩
        simp only [dif_neg hq0, truncatedZeroFieldEnergyAtLevel, dite_false]
        have hphiNat : 0 < q.totient := Nat.totient_pos.mpr hqpos
        have hphiOne : (1 : ℝ≥0∞) ≤ (q.totient : ℝ≥0∞) := by
          exact_mod_cast hphiNat
        calc
          (∫⁻ x in Set.Icc (X / 2) (4 * X),
              (q.totient : ℝ≥0∞)⁻¹ *
                ∑ chi : DirichletCharacter ℂ q,
                  16 * finiteRightMaxSq
                    (truncatedZeroNormField chi (sigma q chi) X T)
                    (dyadicRightScales (H + 1) N) (x - 1 / 2)) ≤
            ∫⁻ x : ℝ,
              (q.totient : ℝ≥0∞)⁻¹ *
                ∑ chi : DirichletCharacter ℂ q,
                  16 * finiteRightMaxSq
                    (truncatedZeroNormField chi (sigma q chi) X T)
                    (dyadicRightScales (H + 1) N) (x - 1 / 2) :=
              setLIntegral_le_lintegral _ _
          _ = (q.totient : ℝ≥0∞)⁻¹ *
              ∑ chi : DirichletCharacter ℂ q,
                ∫⁻ x : ℝ,
                  16 * finiteRightMaxSq
                    (truncatedZeroNormField chi (sigma q chi) X T)
                    (dyadicRightScales (H + 1) N) (x - 1 / 2) := by
            rw [lintegral_const_mul]
            · congr 1
              exact lintegral_finsetSum Finset.univ (fun chi hchi =>
                measurable_const.mul
                  ((measurable_finiteRightMaxSq
                    (truncatedZeroNormField chi (sigma q chi) X T)
                    (measurable_truncatedZeroNormField chi (sigma q chi) X T)
                    (dyadicRightScales (H + 1) N)).comp
                      (measurable_id.sub measurable_const)))
            · apply Finset.measurable_sum
              intro chi hchi
              exact measurable_const.mul
                ((measurable_finiteRightMaxSq
                  (truncatedZeroNormField chi (sigma q chi) X T)
                  (measurable_truncatedZeroNormField chi (sigma q chi) X T)
                  (dyadicRightScales (H + 1) N)).comp
                    (measurable_id.sub measurable_const))
          _ ≤ (q.totient : ℝ≥0∞)⁻¹ *
              ∑ chi : DirichletCharacter ℂ q,
                16 * ((N + 1 : ℝ≥0∞) *
                  ∫⁻ x : ℝ,
                    (truncatedZeroNormField chi (sigma q chi) X T x) ^ 2) := by
            gcongr with chi
            rw [lintegral_const_mul' 16
              (fun x : ℝ => finiteRightMaxSq
                (truncatedZeroNormField chi (sigma q chi) X T)
                (dyadicRightScales (H + 1) N) (x - 1 / 2)) (by norm_num)]
            have hshift :
                (∫⁻ x : ℝ, finiteRightMaxSq
                    (truncatedZeroNormField chi (sigma q chi) X T)
                    (dyadicRightScales (H + 1) N) (x - 1 / 2)) =
                  ∫⁻ x : ℝ, finiteRightMaxSq
                    (truncatedZeroNormField chi (sigma q chi) X T)
                    (dyadicRightScales (H + 1) N) x := by
              simpa [sub_eq_add_neg] using
                (lintegral_add_right_eq_self (μ := volume)
                  (finiteRightMaxSq
                    (truncatedZeroNormField chi (sigma q chi) X T)
                    (dyadicRightScales (H + 1) N)) (-(1 / 2) : ℝ))
            rw [hshift]
            gcongr
            simpa [Nat.cast_add, Nat.cast_one] using
              (lintegral_finiteRightMaxSq_le
                (truncatedZeroNormField chi (sigma q chi) X T)
                (measurable_truncatedZeroNormField chi (sigma q chi) X T)
                (dyadicRightScales (H + 1) N)
                (fun j => mul_pos (pow_pos (by norm_num) _) hH))
          _ ≤ ∑ chi : DirichletCharacter ℂ q,
                16 * ((N + 1 : ℝ≥0∞) *
                  ∫⁻ x : ℝ,
                    (truncatedZeroNormField chi (sigma q chi) X T x) ^ 2) := by
            have hinv : (q.totient : ℝ≥0∞)⁻¹ ≤ 1 :=
              ENNReal.inv_le_one.mpr hphiOne
            exact (mul_le_mul_left hinv _).trans_eq (one_mul _)
          _ = 16 * (N + 1 : ℝ≥0∞) *
              ∑ chi : DirichletCharacter ℂ q,
                ∫⁻ x : ℝ,
                  (truncatedZeroNormField chi (sigma q chi) X T x) ^ 2 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro chi hchi
            ring
      _ = 16 * (N + 1 : ℝ≥0∞) *
          ∑ q ∈ Finset.Icc 1 Q,
            truncatedZeroFieldEnergyAtLevel q (sigma q) X T := by
        rw [Finset.mul_sum]
  · intro q hq
    split_ifs with hq0
    · exact measurable_const
    · letI : NeZero q := ⟨hq0⟩
      apply Measurable.const_mul
      apply Finset.measurable_sum
      intro chi hchi
      exact measurable_const.mul
        ((measurable_finiteRightMaxSq
          (truncatedZeroNormField chi (sigma q chi) X T)
          (measurable_truncatedZeroNormField chi (sigma q chi) X T)
          (dyadicRightScales (H + 1) N)).comp
            (measurable_id.sub measurable_const))

/-- The aligned scale count at endpoint `X+1` is absorbed by two logarithms
of `X`.  The constant is deliberately generous and source-independent. -/
theorem thirtytwo_alignedScaleCount_le_log_sq
    {X : ℝ} (hX : Real.exp 1 ≤ X) :
    32 * (dyadicScaleCount (X + 1) + 1 : ℝ≥0∞) ≤
      ENNReal.ofReal (256 * (Real.log X) ^ 2) := by
  have hXpos : 0 < X := (Real.exp_pos 1).trans_le hX
  have hXone : 1 ≤ X :=
    (Real.one_lt_exp_iff.mpr zero_lt_one).le.trans hX
  have hXtwo : 2 ≤ X := by
    have hexp : 2 < Real.exp 1 := by
      nlinarith [Real.exp_one_gt_d9]
    exact hexp.le.trans hX
  have hlog : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hXpos]
    exact hX
  have hXp1 : 1 ≤ X + 1 := by linarith
  have hlog2 : 1 / 2 < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hsumle : X + 1 ≤ X ^ 2 := by
    nlinarith
  have hlogsum : Real.log (X + 1) ≤ 2 * Real.log X := by
    have hXp1pos : 0 < X + 1 := by linarith
    have hlogmono := Real.strictMonoOn_log.monotoneOn
      (show X + 1 ∈ Set.Ioi (0 : ℝ) by exact hXp1pos)
      (show X ^ 2 ∈ Set.Ioi (0 : ℝ) by
        change 0 < X ^ 2
        positivity) hsumle
    simpa [Real.log_pow] using hlogmono
  have hlogb : Real.logb 2 (X + 1) ≤ 4 * Real.log X := by
    unfold Real.logb
    apply (div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).2
    nlinarith
  have hN := dyadicScaleCount_cast_lt_logb_add_one (X := X + 1) hXp1
  have hreal :
      32 * ((dyadicScaleCount (X + 1) : ℝ) + 1) ≤
        256 * (Real.log X) ^ 2 := by
    have hNlog : (dyadicScaleCount (X + 1) : ℝ) + 1 ≤
        6 * Real.log X := by
      linarith
    have hlogsq : Real.log X ≤ (Real.log X) ^ 2 := by
      nlinarith
    nlinarith
  have hof := ENNReal.ofReal_le_ofReal hreal
  calc
    32 * (dyadicScaleCount (X + 1) + 1 : ℝ≥0∞) =
        ENNReal.ofReal
          (32 * (((dyadicScaleCount (X + 1) + 1 : ℕ) : ℝ))) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 32),
        ENNReal.ofReal_ofNat, ENNReal.ofReal_natCast]
      norm_num
    _ = ENNReal.ofReal
        (32 * ((dyadicScaleCount (X + 1) : ℝ) + 1)) := by
      congr 2
      norm_num
    _ ≤ ENNReal.ofReal (256 * (Real.log X) ^ 2) := hof

/-- Corrected release-path transfer target.  The selected common height and
the left-edge family remain visible so the certified sigma-truncated equation
(2.8) can be inserted without energy monotonicity. -/
def AlignedCommonHeightAPMaximalExplicitFormulaRemainderTransfer : Prop :=
  ∀ K A epsilon : ℝ,
    0 < K → 0 < A → 0 < epsilon → epsilon ≤ 13 / 30 →
    ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧
      ∀ X : ℝ, X0 ≤ X →
        let reserve := min epsilon (1 / 10)
        let H0 := apZeroHeight reserve X
        let Q := ⌊Real.rpow (Real.log X) K⌋₊
        ∃ T ∈ Set.Ioo H0 (H0 + 1),
          ∃ sigma : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ,
            (∀ (q : ℕ) (hq : q ∈ Finset.Icc 1 Q)
                (chi : DirichletCharacter ℂ q),
              @paperEdgeContourLegal q
                ⟨Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩
                chi (sigma q chi) T) ∧
            (∫⁻ x in Set.Icc (X / 2) (4 * X),
                simultaneousAPMax K epsilon X x) ≤
              ENNReal.ofReal (C * (Real.log X) ^ 2) *
                  truncatedAPZeroFieldEnergy Q sigma X T +
                ENNReal.ofReal
                  (C * X * Real.rpow (Real.log X) (-A))

/-- The aligned one-integral endpoint-tail source gives the full deterministic
common-height transfer. -/
theorem alignedCommonHeightRemainderTransfer_of_tailFamilySquare
    (htail : AlignedAPExplicitFormulaTailFamilySquare) :
    AlignedCommonHeightAPMaximalExplicitFormulaRemainderTransfer := by
  intro K A epsilon hK hA hepsilon hepsilonCap
  rcases htail K A epsilon hK hA hepsilon hepsilonCap with
    ⟨Ct, Xt, hCt, hXt, htailX⟩
  let C : ℝ := 256 + 2 * Ct
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
  let N : ℕ := dyadicScaleCount (X + 1)
  have hHnonneg : 0 ≤ H := by
    dsimp [H]
    exact Real.rpow_nonneg hXpos.le _
  have hHpos : 0 < H + 1 := by linarith
  have hreach : (X + 1) / (H + 1) < (2 : ℝ) ^ (N + 1) := by
    have hdiv : (X + 1) / (H + 1) ≤ X + 1 := by
      exact (div_le_iff₀ hHpos).2 (by nlinarith)
    exact hdiv.trans_lt
      (lt_two_pow_dyadicScaleCount_add_one
        (X := X + 1) (by linarith : 1 ≤ X + 1))
  have htailAtX := htailX X hXXt
  dsimp only at htailAtX
  rcases htailAtX with ⟨T, hT, sigma, hlegal, htailBound⟩
  refine ⟨T, hT, sigma, hlegal, ?_⟩
  have hzero := lintegral_familyAlignedDyadicZeroMajorant_le
    Q N sigma (T := T) (H := H) (X := X) hHpos
  have hpoint : ∀ x ∈ Set.Icc (X / 2) (4 * X),
      simultaneousAPMax K epsilon X x ≤
        2 * (familyAlignedDyadicZeroMajorant Q N sigma T H X x +
          familyAlignedTailMajorant Q sigma T epsilon X x) := by
    intro x hx
    exact simultaneousAPMax_le_alignedDyadicZero_add_tail
      rfl rfl hepsilon hXtwo hx hreach sigma hlegal
  have hscale : 32 * (N + 1 : ℝ≥0∞) ≤
      ENNReal.ofReal (C * (Real.log X) ^ 2) := by
    refine (thirtytwo_alignedScaleCount_le_log_sq hXexp).trans ?_
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
        mul_le_mul_of_nonneg_right hCge (mul_nonneg hXpos.le hrpow)
      _ = C * X * Real.rpow (Real.log X) (-A) := by ring
  change (∫⁻ x in Set.Icc (X / 2) (4 * X),
      simultaneousAPMax K epsilon X x) ≤ _
  calc
    (∫⁻ x in Set.Icc (X / 2) (4 * X),
        simultaneousAPMax K epsilon X x) ≤
      ∫⁻ x in Set.Icc (X / 2) (4 * X),
        2 * (familyAlignedDyadicZeroMajorant Q N sigma T H X x +
          familyAlignedTailMajorant Q sigma T epsilon X x) := by
      exact setLIntegral_mono' measurableSet_Icc hpoint
    _ = 2 * ((∫⁻ x in Set.Icc (X / 2) (4 * X),
            familyAlignedDyadicZeroMajorant Q N sigma T H X x) +
          ∫⁻ x in Set.Icc (X / 2) (4 * X),
            familyAlignedTailMajorant Q sigma T epsilon X x) := by
      rw [lintegral_const_mul' 2 _ (by norm_num)]
      rw [lintegral_add_left'
        (measurable_familyAlignedDyadicZeroMajorant
          Q N sigma T H X).aemeasurable]
    _ ≤ 2 * (16 * (N + 1 : ℝ≥0∞) *
            truncatedAPZeroFieldEnergy Q sigma X T +
          ENNReal.ofReal
            (Ct * X * Real.rpow (Real.log X) (-A))) := by
      apply mul_le_mul_right
      exact add_le_add hzero htailBound
    _ = (32 * (N + 1 : ℝ≥0∞)) *
          truncatedAPZeroFieldEnergy Q sigma X T +
          2 * ENNReal.ofReal
            (Ct * X * Real.rpow (Real.log X) (-A)) := by ring
    _ ≤ ENNReal.ofReal (C * (Real.log X) ^ 2) *
          truncatedAPZeroFieldEnergy Q sigma X T +
        ENNReal.ofReal
          (C * X * Real.rpow (Real.log X) (-A)) := by
      exact add_le_add (mul_le_mul_left hscale _) htailCoeff

end
end MAPAPAlignedTailToRemainderTransfer

#print axioms MAPAPAlignedTailToRemainderTransfer.fixedModulusAPMax_le_alignedZeroTailMajorant
#print axioms MAPAPAlignedTailToRemainderTransfer.simultaneousAPMax_le_alignedDyadicZero_add_tail
#print axioms MAPAPAlignedTailToRemainderTransfer.lintegral_familyAlignedDyadicZeroMajorant_le
#print axioms MAPAPAlignedTailToRemainderTransfer.thirtytwo_alignedScaleCount_le_log_sq
#print axioms MAPAPAlignedTailToRemainderTransfer.alignedCommonHeightRemainderTransfer_of_tailFamilySquare
