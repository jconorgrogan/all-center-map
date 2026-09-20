import APHeightMonotonicity
import CertifiedAPZeroFieldEnergy28

/-!
# Equation (2.8) at the selected common contour height

The proof is rerun at the selected height `T ∈ (H,H+1)`.  Only the positive
weighted zero mass is then enlarged to `H+1`; no monotonicity of the complex
zero-field energy is used or asserted.
-/

namespace MAPAPSelectedHeightZeroFieldEnergy28

open MeasureTheory Set
open scoped ENNReal BigOperators
open APExplicitFormulaMajorantAdapter MAPFixedScaleAPZeroRoute
open DirichletZeros MAPLocalZeroWindow
open MAPAPHeightMonotonicity

noncomputable section

private theorem harmonic_nonneg_real (n : ℕ) :
    (0 : ℝ) ≤ (harmonic n : ℝ) := by
  norm_cast
  unfold harmonic
  positivity

private theorem conductor_le_level {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) : chi.conductor ≤ q :=
  Nat.le_of_dvd (NeZero.pos q) chi.conductor_dvd_level

private theorem zeroMass_nonneg {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {X T : ℝ} (hX : 0 ≤ X) :
    0 ≤ primitiveWeightedZeroMass chi X T := by
  unfold primitiveWeightedZeroMass
  apply Finset.sum_nonneg
  intro rho hrho
  exact mul_nonneg (Nat.cast_nonneg _)
    (Real.rpow_nonneg hX _)

/-- Public arithmetic collapse for any common height selected in `(H,H+1)`.
It is reused by the sigma-truncated half-integer route. -/
theorem selectedHeight_rowFactor_le
    (Cp K : ℝ) (hCp : 0 < Cp) (hK : 0 < K)
    {q Q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {reserve X H T : ℝ}
    (hqQ : q ≤ Q)
    (hQ : Q ≤ ⌊Real.rpow (Real.log X) K⌋₊)
    (hreserve : 0 < reserve)
    (hH : H = apZeroHeight reserve X)
    (hT : T ∈ Set.Ioo H (H + 1))
    (hX : Real.exp 4 ≤ X) :
    2 * (1 + (Cp + 306) *
        Real.log ((chi.conductor : ℝ) * (T + 4))) *
        (harmonic (⌊2 * T⌋₊ + 1) : ℝ) ≤
      (6 * (1 + (Cp + 306) * (K + 3))) * (Real.log X) ^ 2 := by
  let L := Real.log X
  have hXpos : 0 < X := (Real.exp_pos 4).trans_le hX
  have hXone : 1 ≤ X := by
    have : 1 < Real.exp 4 := Real.one_lt_exp_iff.mpr (by norm_num)
    linarith
  have hX0 : 0 ≤ X := zero_le_one.trans hXone
  have hL : 4 ≤ L := by
    dsimp [L]
    rw [← Real.log_exp 4]
    exact Real.log_le_log (Real.exp_pos 4) hX
  have hL0 : 0 ≤ L := by linarith
  have hLX : L ≤ X := by
    have h := Real.log_le_sub_one_of_pos hXpos
    dsimp [L]
    linarith
  have hH0 : 0 ≤ H := by
    rw [hH]
    exact Real.rpow_nonneg hX0 _
  have hHleX : H ≤ X := by
    rw [hH]
    calc
      Real.rpow X (13 / 15 - reserve / 2) ≤ Real.rpow X 1 := by
        apply Real.rpow_le_rpow_of_exponent_le hXone
        linarith
      _ = X := Real.rpow_one X
  have hT0 : 0 ≤ T := hH0.trans hT.1.le
  have hTX1 : T ≤ X + 1 := hT.2.le.trans (by linarith)
  have hQreal : (Q : ℝ) ≤ Real.rpow L K := by
    have hQcast : (Q : ℝ) ≤ (⌊Real.rpow L K⌋₊ : ℕ) := by
      exact_mod_cast hQ
    exact hQcast.trans (Nat.floor_le (Real.rpow_nonneg hL0 _))
  have hqcast : (q : ℝ) ≤ Q := by exact_mod_cast hqQ
  have hqreal : (q : ℝ) ≤ Real.rpow L K := hqcast.trans hQreal
  have hcq : chi.conductor ≤ q := conductor_le_level chi
  have hcreal : (chi.conductor : ℝ) ≤ Real.rpow L K :=
    (by exact_mod_cast hcq : (chi.conductor : ℝ) ≤ q) |>.trans hqreal
  have hLKXK : Real.rpow L K ≤ Real.rpow X K :=
    Real.rpow_le_rpow hL0 hLX hK.le
  have hcXK : (chi.conductor : ℝ) ≤ Real.rpow X K :=
    hcreal.trans hLKXK
  have hT4 : T + 4 ≤ 6 * X := by nlinarith
  have hscalePos : 0 < (chi.conductor : ℝ) * (T + 4) := by
    exact mul_pos
      (by exact_mod_cast Nat.pos_of_ne_zero chi.conductor_ne_zero)
      (by linarith)
  have hscaleUpper : (chi.conductor : ℝ) * (T + 4) ≤
      6 * Real.rpow X (K + 1) := by
    calc
      (chi.conductor : ℝ) * (T + 4) ≤ Real.rpow X K * (6 * X) :=
        mul_le_mul hcXK hT4 (by linarith) (Real.rpow_nonneg hX0 _)
      _ = 6 * Real.rpow X (K + 1) := by
        change (X ^ K) * (6 * X) = 6 * (X ^ (K + 1))
        rw [Real.rpow_add hXpos K 1, Real.rpow_one]
        ring
  have hlog6 : Real.log 6 ≤ 2 * L := by
    have h6 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 6)
    dsimp [L]
    linarith
  have hlogscale : Real.log ((chi.conductor : ℝ) * (T + 4)) ≤
      (K + 3) * L := by
    have hpowPos : 0 < (X ^ (K + 1) : ℝ) :=
      Real.rpow_pos_of_pos hXpos _
    calc
      Real.log ((chi.conductor : ℝ) * (T + 4)) ≤
          Real.log (6 * (X ^ (K + 1) : ℝ)) :=
        Real.log_le_log hscalePos hscaleUpper
      _ = Real.log 6 + (K + 1) * Real.log X := by
        rw [Real.log_mul (by norm_num : (6 : ℝ) ≠ 0) hpowPos.ne',
          Real.log_rpow hXpos]
      _ ≤ (K + 3) * L := by
        dsimp [L] at hlog6 ⊢
        linarith
  have hnCast : ((⌊2 * T⌋₊ + 1 : ℕ) : ℝ) ≤ 5 * X := by
    have hfloor : (⌊2 * T⌋₊ : ℝ) ≤ 2 * T :=
      Nat.floor_le (by positivity)
    norm_num at hfloor ⊢
    nlinarith
  have hnPos : (0 : ℝ) < (⌊2 * T⌋₊ + 1 : ℕ) := by positivity
  have hlog5 : Real.log 5 ≤ L := by
    have h5 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5)
    dsimp [L]
    linarith
  have hlogn : Real.log ((⌊2 * T⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * L := by
    have hlog := Real.log_le_log hnPos hnCast
    rw [Real.log_mul (by norm_num : (5 : ℝ) ≠ 0) hXpos.ne'] at hlog
    dsimp [L] at hlog5 ⊢
    linarith
  have hharm0 := harmonic_nonneg_real (⌊2 * T⌋₊ + 1)
  have hharm : (harmonic (⌊2 * T⌋₊ + 1) : ℝ) ≤ 3 * L := by
    have hh := harmonic_le_one_add_log (⌊2 * T⌋₊ + 1)
    linarith
  have hscale1 : 1 ≤ (chi.conductor : ℝ) * (T + 4) := by
    have hc1 : (1 : ℝ) ≤ chi.conductor := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr chi.conductor_ne_zero
    nlinarith
  have hlog0 := Real.log_nonneg hscale1
  have hcoef : 1 + (Cp + 306) *
      Real.log ((chi.conductor : ℝ) * (T + 4)) ≤
      (1 + (Cp + 306) * (K + 3)) * L := by
    have hCK : 0 ≤ Cp + 306 := by linarith
    calc
      1 + (Cp + 306) * Real.log ((chi.conductor : ℝ) * (T + 4)) ≤
          1 + (Cp + 306) * ((K + 3) * L) := by gcongr
      _ ≤ (1 + (Cp + 306) * (K + 3)) * L := by
        nlinarith
  have hcoef0 : 0 ≤ 1 + (Cp + 306) *
      Real.log ((chi.conductor : ℝ) * (T + 4)) := by nlinarith
  have hbig0 : 0 ≤ 1 + (Cp + 306) * (K + 3) := by nlinarith
  calc
    2 * (1 + (Cp + 306) *
        Real.log ((chi.conductor : ℝ) * (T + 4))) *
        (harmonic (⌊2 * T⌋₊ + 1) : ℝ) ≤
      2 * ((1 + (Cp + 306) * (K + 3)) * L) *
        (harmonic (⌊2 * T⌋₊ + 1) : ℝ) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hcoef (by norm_num)) hharm0
    _ ≤ 2 * ((1 + (Cp + 306) * (K + 3)) * L) * (3 * L) := by
          exact mul_le_mul_of_nonneg_left hharm
            (mul_nonneg (by norm_num) (mul_nonneg hbig0 hL0))
    _ = (6 * (1 + (Cp + 306) * (K + 3))) * L ^ 2 := by ring

private theorem primitive_energy_selected_le
    (Cp K : ℝ) (hCp : 0 < Cp) (hK : 0 < K)
    (hcount : ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q),
      chi.IsPrimitive → chi = 1 → ∀ t : ℝ,
        (closedUnitWindowCount chi 0 t : ℝ) ≤
          Cp * Real.log (arithmeticScale q t))
    {q Q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {reserve X H T : ℝ}
    (hqQ : q ≤ Q)
    (hQ : Q ≤ ⌊Real.rpow (Real.log X) K⌋₊)
    (hreserve : 0 < reserve)
    (hH : H = apZeroHeight reserve X)
    (hT : T ∈ Set.Ioo H (H + 1))
    (hX : Real.exp 4 ≤ X) :
    (∫⁻ t : ℝ, (primitiveZeroNormField chi X T t) ^ 2) ≤
      ENNReal.ofReal
        ((1152 * (1 + (Cp + 306) * (K + 3))) * X *
          (Real.log X) ^ 2 *
          primitiveWeightedZeroMass chi X (H + 1)) := by
  have hXpos : 0 < X := (Real.exp_pos 4).trans_le hX
  have hT0 : 0 ≤ T := by
    have hH0 : 0 ≤ H := by
      rw [hH]
      exact Real.rpow_nonneg hXpos.le _
    exact hH0.trans hT.1.le
  have hraw := MAPCertifiedAPZeroFieldEnergy28.primitive_energy_le_raw
    Cp hCp hcount chi hXpos hT0
  have hrow := selectedHeight_rowFactor_le Cp K hCp hK chi
    hqQ hQ hreserve hH hT hX
  have hmassT := zeroMass_nonneg chi (X := X) (T := T) hXpos.le
  have hmassMono : primitiveWeightedZeroMass chi X T ≤
      primitiveWeightedZeroMass chi X (H + 1) :=
    primitiveWeightedZeroMass_mono_height chi hXpos.le hT.2.le
  have hmassTop := zeroMass_nonneg chi (X := X) (T := H + 1) hXpos.le
  refine hraw.trans ?_
  apply ENNReal.ofReal_le_ofReal
  calc
    192 * X *
        (2 * (1 + (Cp + 306) *
          Real.log ((chi.conductor : ℝ) * (T + 4))) *
          (harmonic (⌊2 * T⌋₊ + 1) : ℝ)) *
        primitiveWeightedZeroMass chi X T ≤
      192 * X *
        ((6 * (1 + (Cp + 306) * (K + 3))) * (Real.log X) ^ 2) *
        primitiveWeightedZeroMass chi X T := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hrow
              (mul_nonneg (by norm_num) hXpos.le)) hmassT
    _ ≤ 192 * X *
        ((6 * (1 + (Cp + 306) * (K + 3))) * (Real.log X) ^ 2) *
        primitiveWeightedZeroMass chi X (H + 1) := by
          gcongr
    _ = (1152 * (1 + (Cp + 306) * (K + 3))) * X *
          (Real.log X) ^ 2 *
          primitiveWeightedZeroMass chi X (H + 1) := by ring

private theorem energyAtLevel_selected_le
    (Cp K : ℝ) (hCp : 0 < Cp) (hK : 0 < K)
    (hcount : ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q),
      chi.IsPrimitive → chi = 1 → ∀ t : ℝ,
        (closedUnitWindowCount chi 0 t : ℝ) ≤
          Cp * Real.log (arithmeticScale q t))
    {q Q : ℕ} (hqQ : q ≤ Q)
    {reserve X H T : ℝ}
    (hQ : Q ≤ ⌊Real.rpow (Real.log X) K⌋₊)
    (hreserve : 0 < reserve)
    (hH : H = apZeroHeight reserve X)
    (hT : T ∈ Set.Ioo H (H + 1))
    (hX : Real.exp 4 ≤ X) :
    zeroFieldEnergyAtLevel q X T ≤
      ENNReal.ofReal
        ((1152 * (1 + (Cp + 306) * (K + 3))) * X *
          (Real.log X) ^ 2 * weightedZeroMassAtLevel q X (H + 1)) := by
  by_cases hq0 : q = 0
  · simp [zeroFieldEnergyAtLevel, weightedZeroMassAtLevel, hq0]
  · letI : NeZero q := ⟨hq0⟩
    let C : ℝ := 1152 * (1 + (Cp + 306) * (K + 3))
    have hXpos : 0 < X := (Real.exp_pos 4).trans_le hX
    have hC0 : 0 ≤ C := by
      dsimp [C]
      have : 0 ≤ 1 + (Cp + 306) * (K + 3) := by nlinarith
      positivity
    have hcoef0 : 0 ≤ C * X * (Real.log X) ^ 2 := by positivity
    simp only [zeroFieldEnergyAtLevel, weightedZeroMassAtLevel, hq0,
      dite_false]
    calc
      (∑ chi : DirichletCharacter ℂ q,
          ∫⁻ t : ℝ, (primitiveZeroNormField chi X T t) ^ 2) ≤
        ∑ chi : DirichletCharacter ℂ q,
          ENNReal.ofReal
            (C * X * (Real.log X) ^ 2 *
              primitiveWeightedZeroMass chi X (H + 1)) := by
          apply Finset.sum_le_sum
          intro chi hchi
          exact primitive_energy_selected_le Cp K hCp hK hcount chi
            hqQ hQ hreserve hH hT hX
      _ = ENNReal.ofReal
          (∑ chi : DirichletCharacter ℂ q,
            C * X * (Real.log X) ^ 2 *
              primitiveWeightedZeroMass chi X (H + 1)) := by
          symm
          apply ENNReal.ofReal_sum_of_nonneg
          intro chi hchi
          exact mul_nonneg hcoef0
            (zeroMass_nonneg chi hXpos.le)
      _ = ENNReal.ofReal
          (C * X * (Real.log X) ^ 2 *
            ∑ chi : DirichletCharacter ℂ q,
              primitiveWeightedZeroMass chi X (H + 1)) := by
          congr 1
          rw [Finset.mul_sum]

/-- Correct selected-height equation-(2.8) family. -/
def SelectedHeightAPZeroFieldEnergy28 : Prop :=
  ∀ K : ℝ, 0 < K →
    ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧
      ∀ (Q : ℕ) (reserve X H T : ℝ),
        Q ≤ ⌊Real.rpow (Real.log X) K⌋₊ →
        0 < reserve → reserve ≤ 1 / 10 →
        H = apZeroHeight reserve X →
        T ∈ Set.Ioo H (H + 1) → X0 ≤ X →
        apZeroFieldEnergy Q X T ≤
          ENNReal.ofReal
            (C * X * (Real.log X) ^ 2 *
              apWeightedZeroMass Q X (H + 1))

/-- Premise-free selected-height equation (2.8), proved at `T` itself. -/
theorem certifiedSelectedHeightAPZeroFieldEnergy28 :
    SelectedHeightAPZeroFieldEnergy28 := by
  rcases MAPPrincipalZetaFullStrip.certifiedPrincipalFullStripA5 with
    ⟨Cp, hCp, hcount⟩
  intro K hK
  let C : ℝ := 1152 * (1 + (Cp + 306) * (K + 3))
  refine ⟨C, Real.exp 4, ?_, ?_, ?_⟩
  · dsimp [C]
    have : 0 < 1 + (Cp + 306) * (K + 3) := by nlinarith
    positivity
  · have : 2 < Real.exp 4 := by
      have he2 : 2 < Real.exp 1 := by
        nlinarith [Real.exp_one_gt_d9]
      exact he2.trans_le (Real.exp_le_exp.mpr (by norm_num))
    exact this.le
  · intro Q reserve X H T hQ hreserve hreserveCap hH hT hX
    let coef : ℝ := C * X * (Real.log X) ^ 2
    have hXpos : 0 < X := (Real.exp_pos 4).trans_le hX
    have hC0 : 0 ≤ C := by
      dsimp [C]
      have : 0 ≤ 1 + (Cp + 306) * (K + 3) := by nlinarith
      positivity
    have hcoef0 : 0 ≤ coef := by
      dsimp [coef]
      positivity
    unfold apZeroFieldEnergy apWeightedZeroMass
    calc
      (∑ q ∈ Finset.Icc 1 Q, zeroFieldEnergyAtLevel q X T) ≤
        ∑ q ∈ Finset.Icc 1 Q,
          ENNReal.ofReal
            (coef * weightedZeroMassAtLevel q X (H + 1)) := by
          apply Finset.sum_le_sum
          intro q hq
          simpa [coef, C] using
            energyAtLevel_selected_le Cp K hCp hK hcount
              (Finset.mem_Icc.mp hq).2 hQ hreserve hH hT hX
      _ = ENNReal.ofReal
          (∑ q ∈ Finset.Icc 1 Q,
            coef * weightedZeroMassAtLevel q X (H + 1)) := by
          symm
          apply ENNReal.ofReal_sum_of_nonneg
          intro q hq
          exact mul_nonneg hcoef0
            (MAPAPConditionalShortIntervalConnector.weightedZeroMassAtLevel_nonneg
              q hXpos.le (H + 1))
      _ = ENNReal.ofReal
          (C * X * (Real.log X) ^ 2 *
            ∑ q ∈ Finset.Icc 1 Q,
              weightedZeroMassAtLevel q X (H + 1)) := by
          congr 1
          dsimp [coef]
          rw [Finset.mul_sum]

end
end MAPAPSelectedHeightZeroFieldEnergy28

#print axioms MAPAPSelectedHeightZeroFieldEnergy28.certifiedSelectedHeightAPZeroFieldEnergy28
