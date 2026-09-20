import PrincipalZetaFullStrip
import FixedScaleAPZeroRoute

namespace MAPCertifiedAPZeroFieldEnergy28

open MeasureTheory Set
open scoped ENNReal BigOperators
open APExplicitFormulaMajorantAdapter
open MAPFixedScaleAPZeroRoute
open DirichletZeros MAPLocalZeroWindow

noncomputable section

private theorem harmonic_nonneg_real (n : ℕ) :
    (0 : ℝ) ≤ (harmonic n : ℝ) := by
  norm_cast
  unfold harmonic
  positivity

private theorem conductor_le_level {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) : χ.conductor ≤ q :=
  Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level

private theorem zeroMass_nonneg {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {X T : ℝ} (hX : 0 ≤ X) :
    0 ≤ primitiveWeightedZeroMass χ X T := by
  unfold primitiveWeightedZeroMass
  apply Finset.sum_nonneg
  intro ρ hρ
  exact mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hX _)

/-- Exported raw-height form of equation (2.8).  Downstream common-height
contour selection must apply this theorem at the selected height itself;
complex zero-field energy is not monotone in the height.  `Cp` is the
certified principal-zeta A.5 constant. -/
theorem primitive_energy_le_raw
    (Cp : ℝ) (hCp : 0 < Cp)
    (hcount : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ = 1 → ∀ t : ℝ,
        (closedUnitWindowCount χ 0 t : ℝ) ≤
          Cp * Real.log (arithmeticScale q t))
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {X T : ℝ} (hX : 0 < X) (hT : 0 ≤ T) :
    (∫⁻ t : ℝ, (primitiveZeroNormField χ X T t) ^ 2) ≤
      ENNReal.ofReal
        (192 * X *
          (2 * (1 + (Cp + 306) *
            Real.log ((χ.conductor : ℝ) * (T + 4))) *
            (harmonic (⌊2 * T⌋₊ + 1) : ℝ)) *
          primitiveWeightedZeroMass χ X T) := by
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  let ψ := χ.primitiveCharacter
  have hprim : ψ.IsPrimitive := χ.primitiveCharacter_isPrimitive
  have hscale1 : 1 ≤ (χ.conductor : ℝ) * (T + 4) := by
    have hr : (1 : ℝ) ≤ χ.conductor := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr χ.conductor_ne_zero
    nlinarith
  have hlog : 0 ≤ Real.log ((χ.conductor : ℝ) * (T + 4)) :=
    Real.log_nonneg hscale1
  have hharm : 0 ≤ (harmonic (⌊2 * T⌋₊ + 1) : ℝ) := by
    exact harmonic_nonneg_real _
  by_cases hψ : ψ = 1
  · have hrow : ∀ ρ ∈ zeroSupport ψ 0 T,
        (∑ ρ' ∈ zeroSupport ψ 0 T,
          (zeroMultiplicity ψ 0 T ρ' : ℝ) /
            (1 + |ρ'.im - ρ.im|)) ≤
          2 * (Cp * Real.log ((χ.conductor : ℝ) * (T + 4))) *
            (harmonic (⌊2 * T⌋₊ + 1) : ℝ) := by
      intro ρ hρ
      classical
      apply MAPHarmonicRowGrouping.finite_reciprocal_row_le_harmonic
        (zeroSupport ψ 0 T)
        (fun z => (zeroMultiplicity ψ 0 T z : ℝ))
        (fun z => z.im) hT
      · exact mul_nonneg hCp.le hlog
      · intro z hz; positivity
      · intro z hz
        have hrect := PrimitiveExplicitFormulaSpine.mem_zeroRectangle_of_mem_zeroSupport
          ψ 0 T hz
        exact abs_le.mpr (Complex.mem_reProdIm.mp hrect).2
      · intro a
        exact MAPPrincipalFullStripA5Source.principal_globalUnitWindowMass_le_uniform
          Cp hCp hcount ψ hprim hψ hT a
      · exact hρ
    have hbase := MAPAPZeroFieldEnergy28Grouping.lintegral_zeroNormField_sq_le_of_row
      ψ hX hrow
    have hmass : 0 ≤
        (∑ ρ ∈ zeroSupport ψ 0 T,
          (zeroMultiplicity ψ 0 T ρ : ℝ) *
            Real.rpow X (2 * (ρ.re - 1))) := by
      apply Finset.sum_nonneg
      intro ρ hρ
      exact mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hX.le _)
    have hmono :
        192 * X *
            (2 * (Cp * Real.log ((χ.conductor : ℝ) * (T + 4))) *
              (harmonic (⌊2 * T⌋₊ + 1) : ℝ)) *
            (∑ ρ ∈ zeroSupport ψ 0 T,
              (zeroMultiplicity ψ 0 T ρ : ℝ) *
                Real.rpow X (2 * (ρ.re - 1))) ≤
          192 * X *
            (2 * (1 + (Cp + 306) *
              Real.log ((χ.conductor : ℝ) * (T + 4))) *
              (harmonic (⌊2 * T⌋₊ + 1) : ℝ)) *
            (∑ ρ ∈ zeroSupport ψ 0 T,
              (zeroMultiplicity ψ 0 T ρ : ℝ) *
                Real.rpow X (2 * (ρ.re - 1))) := by
      gcongr
      nlinarith
    refine hbase.trans ?_
    apply ENNReal.ofReal_le_ofReal
    simpa [primitiveZeroNormField, primitiveActualZeroField,
      primitiveWeightedZeroMass, ψ] using hmono
  · have hbase := MAPAPZeroFieldEnergy28Grouping.lintegral_zeroNormField_sq_le_nonprincipal
      ψ hprim hψ hX hT
    have hmass : 0 ≤
        (∑ ρ ∈ zeroSupport ψ 0 T,
          (zeroMultiplicity ψ 0 T ρ : ℝ) *
            Real.rpow X (2 * (ρ.re - 1))) := by
      apply Finset.sum_nonneg
      intro ρ hρ
      exact mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hX.le _)
    have hmono :
        192 * X *
            (2 * (1 + 306 * Real.log ((χ.conductor : ℝ) * (T + 4))) *
              (harmonic (⌊2 * T⌋₊ + 1) : ℝ)) *
            (∑ ρ ∈ zeroSupport ψ 0 T,
              (zeroMultiplicity ψ 0 T ρ : ℝ) *
                Real.rpow X (2 * (ρ.re - 1))) ≤
          192 * X *
            (2 * (1 + (Cp + 306) *
              Real.log ((χ.conductor : ℝ) * (T + 4))) *
              (harmonic (⌊2 * T⌋₊ + 1) : ℝ)) *
            (∑ ρ ∈ zeroSupport ψ 0 T,
              (zeroMultiplicity ψ 0 T ρ : ℝ) *
                Real.rpow X (2 * (ρ.re - 1))) := by
      gcongr
      nlinarith
    refine hbase.trans ?_
    apply ENNReal.ofReal_le_ofReal
    simpa [primitiveZeroNormField, primitiveActualZeroField,
      primitiveWeightedZeroMass, ψ] using hmono

#print axioms primitive_energy_le_raw

private theorem zeroHeight_nonneg (epsilon X : ℝ) (hX : 0 ≤ X) :
    0 ≤ apZeroHeight epsilon X :=
  Real.rpow_nonneg hX _

private theorem zeroHeight_le_X
    {epsilon X : ℝ} (hepsilon : 0 ≤ epsilon) (hX : 1 ≤ X) :
    apZeroHeight epsilon X ≤ X := by
  unfold apZeroHeight
  calc
    Real.rpow X (13 / 15 - epsilon / 2) ≤ Real.rpow X 1 := by
      apply Real.rpow_le_rpow_of_exponent_le hX
      linarith
    _ = X := Real.rpow_one X

/-- Elementary conductor-height and harmonic collapse in the corrected
fixed-`K` range. -/
private theorem polylog_rowFactor_le
    (Cp K : ℝ) (hCp : 0 < Cp) (hK : 0 < K)
    {q Q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {epsilon X : ℝ}
    (hqQ : q ≤ Q)
    (hQ : Q ≤ ⌊Real.rpow (Real.log X) K⌋₊)
    (hepsilon : 0 < epsilon)
    (hX : Real.exp 1 ≤ X) :
    2 * (1 + (Cp + 306) *
        Real.log ((χ.conductor : ℝ) * (apZeroHeight epsilon X + 4))) *
        (harmonic (⌊2 * apZeroHeight epsilon X⌋₊ + 1) : ℝ) ≤
      (8 * (1 + (Cp + 306) * (K + 5))) * (Real.log X) ^ 2 := by
  let L := Real.log X
  let T := apZeroHeight epsilon X
  have hXpos : 0 < X := (Real.exp_pos 1).trans_le hX
  have hXone : 1 ≤ X := by
    have : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr zero_lt_one
    linarith
  have hX0 : 0 ≤ X := zero_le_one.trans hXone
  have hL : 1 ≤ L := by
    dsimp [L]
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hX
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hLX : L ≤ X := by
    have h := Real.log_le_sub_one_of_pos hXpos
    dsimp [L]
    linarith
  have hQreal : (Q : ℝ) ≤ Real.rpow L K := by
    have hQcast : (Q : ℝ) ≤ (⌊Real.rpow L K⌋₊ : ℕ) := by
      exact_mod_cast hQ
    exact hQcast.trans (Nat.floor_le (Real.rpow_nonneg hL0 _))
  have hqcast : (q : ℝ) ≤ Q := by exact_mod_cast hqQ
  have hqreal : (q : ℝ) ≤ Real.rpow L K := hqcast.trans hQreal
  have hrq : χ.conductor ≤ q := conductor_le_level χ
  have hrreal : (χ.conductor : ℝ) ≤ Real.rpow L K :=
    (by exact_mod_cast hrq : (χ.conductor : ℝ) ≤ q) |>.trans hqreal
  have hLKXK : Real.rpow L K ≤ Real.rpow X K :=
    Real.rpow_le_rpow hL0 hLX hK.le
  have hrXK : (χ.conductor : ℝ) ≤ Real.rpow X K := hrreal.trans hLKXK
  have hT0 : 0 ≤ T := zeroHeight_nonneg epsilon X hX0
  have hTX : T ≤ X := zeroHeight_le_X hepsilon.le hXone
  have hT4 : T + 4 ≤ 5 * X := by nlinarith
  have hscalePos : 0 < (χ.conductor : ℝ) * (T + 4) := by
    exact mul_pos (by exact_mod_cast Nat.pos_of_ne_zero χ.conductor_ne_zero)
      (by linarith)
  have hscaleUpper : (χ.conductor : ℝ) * (T + 4) ≤
      5 * Real.rpow X (K + 1) := by
    calc
      (χ.conductor : ℝ) * (T + 4) ≤ Real.rpow X K * (5 * X) :=
        mul_le_mul hrXK hT4 (by linarith) (Real.rpow_nonneg hX0 _)
      _ = 5 * Real.rpow X (K + 1) := by
        change (X ^ K) * (5 * X) = 5 * (X ^ (K + 1))
        rw [Real.rpow_add hXpos K 1, Real.rpow_one]
        ring
  have hlogscale : Real.log ((χ.conductor : ℝ) * (T + 4)) ≤
      (K + 5) * L := by
    have hpowPos : 0 < (X ^ (K + 1) : ℝ) := Real.rpow_pos_of_pos hXpos _
    have hlog5 : Real.log 5 ≤ 4 * L := by
      have h5 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5)
      nlinarith
    calc
      Real.log ((χ.conductor : ℝ) * (T + 4)) ≤
          Real.log (5 * (X ^ (K + 1) : ℝ)) :=
        Real.log_le_log hscalePos hscaleUpper
      _ = Real.log 5 + (K + 1) * Real.log X := by
        rw [Real.log_mul (by norm_num : (5 : ℝ) ≠ 0) hpowPos.ne',
          Real.log_rpow hXpos]
      _ ≤ (K + 5) * L := by
        dsimp [L] at hlog5 ⊢
        nlinarith
  have hnCast : ((⌊2 * T⌋₊ + 1 : ℕ) : ℝ) ≤ 3 * X := by
    have hfloor : (⌊2 * T⌋₊ : ℝ) ≤ 2 * T :=
      Nat.floor_le (by positivity)
    norm_num at hfloor ⊢
    nlinarith
  have hnPos : (0 : ℝ) < (⌊2 * T⌋₊ + 1 : ℕ) := by positivity
  have hlogn : Real.log ((⌊2 * T⌋₊ + 1 : ℕ) : ℝ) ≤ 3 * L := by
    have hlog := Real.log_le_log hnPos hnCast
    have h3Xpos : 0 < 3 * X := mul_pos (by norm_num) hXpos
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hXpos.ne'] at hlog
    have hlog3 : Real.log 3 ≤ 2 * L := by
      have h3 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
      nlinarith
    dsimp [L] at hlog ⊢
    nlinarith
  have hharm0 := harmonic_nonneg_real (⌊2 * T⌋₊ + 1)
  have hharm : (harmonic (⌊2 * T⌋₊ + 1) : ℝ) ≤ 4 * L := by
    have hh := harmonic_le_one_add_log (⌊2 * T⌋₊ + 1)
    exact hh.trans (by nlinarith)
  have hcoef0 : 0 ≤ 1 + (Cp + 306) *
      Real.log ((χ.conductor : ℝ) * (T + 4)) := by
    have hscale1 : 1 ≤ (χ.conductor : ℝ) * (T + 4) := by
      have hr1 : (1 : ℝ) ≤ χ.conductor := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr χ.conductor_ne_zero
      nlinarith
    have := Real.log_nonneg hscale1
    nlinarith
  have hcoef : 1 + (Cp + 306) *
      Real.log ((χ.conductor : ℝ) * (T + 4)) ≤
      (1 + (Cp + 306) * (K + 5)) * L := by
    have hCK : 0 ≤ Cp + 306 := by linarith
    have hbasecoef : 0 ≤ 1 + (Cp + 306) * (K + 5) := by nlinarith
    calc
      1 + (Cp + 306) * Real.log ((χ.conductor : ℝ) * (T + 4)) ≤
          1 + (Cp + 306) * ((K + 5) * L) := by gcongr
      _ ≤ (1 + (Cp + 306) * (K + 5)) * L := by
        nlinarith
  have hbigcoef : 0 ≤ 1 + (Cp + 306) * (K + 5) := by nlinarith
  have hBL0 : 0 ≤ (1 + (Cp + 306) * (K + 5)) * L :=
    mul_nonneg hbigcoef hL0
  calc
    2 * (1 + (Cp + 306) * Real.log ((χ.conductor : ℝ) * (T + 4))) *
        (harmonic (⌊2 * T⌋₊ + 1) : ℝ) ≤
      2 * ((1 + (Cp + 306) * (K + 5)) * L) *
        (harmonic (⌊2 * T⌋₊ + 1) : ℝ) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hcoef (by norm_num)) hharm0
    _ ≤ 2 * ((1 + (Cp + 306) * (K + 5)) * L) * (4 * L) := by
          exact mul_le_mul_of_nonneg_left hharm
            (mul_nonneg (by norm_num) hBL0)
    _ = (8 * (1 + (Cp + 306) * (K + 5))) * L ^ 2 := by ring


private theorem primitive_energy_le_polylog
    (Cp K : ℝ) (hCp : 0 < Cp) (hK : 0 < K)
    (hcount : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ = 1 → ∀ t : ℝ,
        (closedUnitWindowCount χ 0 t : ℝ) ≤
          Cp * Real.log (arithmeticScale q t))
    {q Q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {epsilon X : ℝ}
    (hqQ : q ≤ Q)
    (hQ : Q ≤ ⌊Real.rpow (Real.log X) K⌋₊)
    (hepsilon : 0 < epsilon)
    (hX : Real.exp 1 ≤ X) :
    (∫⁻ t : ℝ, (primitiveZeroNormField χ X (apZeroHeight epsilon X) t) ^ 2) ≤
      ENNReal.ofReal
        ((1536 * (1 + (Cp + 306) * (K + 5))) * X *
          (Real.log X) ^ 2 *
          primitiveWeightedZeroMass χ X (apZeroHeight epsilon X)) := by
  have hXpos : 0 < X := (Real.exp_pos 1).trans_le hX
  have hT0 : 0 ≤ apZeroHeight epsilon X :=
    zeroHeight_nonneg epsilon X hXpos.le
  have hraw := primitive_energy_le_raw Cp hCp hcount χ hXpos hT0
  have hrow := polylog_rowFactor_le Cp K hCp hK χ hqQ hQ hepsilon hX
  have hmass := zeroMass_nonneg χ (X := X) (T := apZeroHeight epsilon X) hXpos.le
  have hC0 : 0 ≤ 1536 * (1 + (Cp + 306) * (K + 5)) := by
    have : 0 ≤ 1 + (Cp + 306) * (K + 5) := by nlinarith
    positivity
  refine hraw.trans ?_
  apply ENNReal.ofReal_le_ofReal
  calc
    192 * X *
        (2 * (1 + (Cp + 306) *
          Real.log ((χ.conductor : ℝ) * (apZeroHeight epsilon X + 4))) *
          (harmonic (⌊2 * apZeroHeight epsilon X⌋₊ + 1) : ℝ)) *
        primitiveWeightedZeroMass χ X (apZeroHeight epsilon X) ≤
      192 * X *
        ((8 * (1 + (Cp + 306) * (K + 5))) * (Real.log X) ^ 2) *
        primitiveWeightedZeroMass χ X (apZeroHeight epsilon X) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hrow (mul_nonneg (by norm_num) hXpos.le)) hmass
    _ = (1536 * (1 + (Cp + 306) * (K + 5))) * X *
          (Real.log X) ^ 2 *
          primitiveWeightedZeroMass χ X (apZeroHeight epsilon X) := by ring

private theorem zeroFieldEnergyAtLevel_le_polylog
    (Cp K : ℝ) (hCp : 0 < Cp) (hK : 0 < K)
    (hcount : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ = 1 → ∀ t : ℝ,
        (closedUnitWindowCount χ 0 t : ℝ) ≤
          Cp * Real.log (arithmeticScale q t))
    {q Q : ℕ} (hqQ : q ≤ Q)
    {epsilon X : ℝ}
    (hQ : Q ≤ ⌊Real.rpow (Real.log X) K⌋₊)
    (hepsilon : 0 < epsilon)
    (hX : Real.exp 1 ≤ X) :
    zeroFieldEnergyAtLevel q X (apZeroHeight epsilon X) ≤
      ENNReal.ofReal
        ((1536 * (1 + (Cp + 306) * (K + 5))) * X *
          (Real.log X) ^ 2 *
          weightedZeroMassAtLevel q X (apZeroHeight epsilon X)) := by
  by_cases hq0 : q = 0
  · simp [zeroFieldEnergyAtLevel, weightedZeroMassAtLevel, hq0]
  · letI : NeZero q := ⟨hq0⟩
    let C : ℝ := 1536 * (1 + (Cp + 306) * (K + 5))
    have hXpos : 0 < X := (Real.exp_pos 1).trans_le hX
    have hC0 : 0 ≤ C := by
      dsimp [C]
      have : 0 ≤ 1 + (Cp + 306) * (K + 5) := by nlinarith
      positivity
    have hcoef0 : 0 ≤ C * X * (Real.log X) ^ 2 := by positivity
    simp only [zeroFieldEnergyAtLevel, weightedZeroMassAtLevel, hq0,
      dite_false]
    calc
      (∑ χ : DirichletCharacter ℂ q,
          ∫⁻ t : ℝ, (primitiveZeroNormField χ X (apZeroHeight epsilon X) t) ^ 2) ≤
        ∑ χ : DirichletCharacter ℂ q,
          ENNReal.ofReal
            (C * X * (Real.log X) ^ 2 *
              primitiveWeightedZeroMass χ X (apZeroHeight epsilon X)) := by
          apply Finset.sum_le_sum
          intro χ hχ
          exact primitive_energy_le_polylog Cp K hCp hK hcount χ hqQ hQ hepsilon hX
      _ = ENNReal.ofReal
          (∑ χ : DirichletCharacter ℂ q,
            C * X * (Real.log X) ^ 2 *
              primitiveWeightedZeroMass χ X (apZeroHeight epsilon X)) := by
          symm
          apply ENNReal.ofReal_sum_of_nonneg
          intro χ hχ
          exact mul_nonneg hcoef0
            (zeroMass_nonneg χ (X := X) (T := apZeroHeight epsilon X) hXpos.le)
      _ = ENNReal.ofReal
          (C * X * (Real.log X) ^ 2 *
            ∑ χ : DirichletCharacter ℂ q,
              primitiveWeightedZeroMass χ X (apZeroHeight epsilon X)) := by
          congr 1
          rw [Finset.mul_sum]

private theorem apZeroFieldEnergy_le_polylog
    (Cp K : ℝ) (hCp : 0 < Cp) (hK : 0 < K)
    (hcount : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ = 1 → ∀ t : ℝ,
        (closedUnitWindowCount χ 0 t : ℝ) ≤
          Cp * Real.log (arithmeticScale q t))
    {Q : ℕ} {epsilon X : ℝ}
    (hQ : Q ≤ ⌊Real.rpow (Real.log X) K⌋₊)
    (hepsilon : 0 < epsilon)
    (hX : Real.exp 1 ≤ X) :
    apZeroFieldEnergy Q X (apZeroHeight epsilon X) ≤
      ENNReal.ofReal
        ((1536 * (1 + (Cp + 306) * (K + 5))) * X *
          (Real.log X) ^ 2 *
          apWeightedZeroMass Q X (apZeroHeight epsilon X)) := by
  let C : ℝ := 1536 * (1 + (Cp + 306) * (K + 5))
  have hXpos : 0 < X := (Real.exp_pos 1).trans_le hX
  have hC0 : 0 ≤ C := by
    dsimp [C]
    have : 0 ≤ 1 + (Cp + 306) * (K + 5) := by nlinarith
    positivity
  have hcoef0 : 0 ≤ C * X * (Real.log X) ^ 2 := by positivity
  unfold apZeroFieldEnergy apWeightedZeroMass
  calc
    (∑ q ∈ Finset.Icc 1 Q,
        zeroFieldEnergyAtLevel q X (apZeroHeight epsilon X)) ≤
      ∑ q ∈ Finset.Icc 1 Q,
        ENNReal.ofReal
          (C * X * (Real.log X) ^ 2 *
            weightedZeroMassAtLevel q X (apZeroHeight epsilon X)) := by
        apply Finset.sum_le_sum
        intro q hq
        exact zeroFieldEnergyAtLevel_le_polylog Cp K hCp hK hcount
          (Finset.mem_Icc.mp hq).2 hQ hepsilon hX
    _ = ENNReal.ofReal
        (∑ q ∈ Finset.Icc 1 Q,
          C * X * (Real.log X) ^ 2 *
            weightedZeroMassAtLevel q X (apZeroHeight epsilon X)) := by
        symm
        apply ENNReal.ofReal_sum_of_nonneg
        intro q hq
        by_cases hq0 : q = 0
        · simp [weightedZeroMassAtLevel, hq0]
        · letI : NeZero q := ⟨hq0⟩
          have hmassLevel : 0 ≤ weightedZeroMassAtLevel q X (apZeroHeight epsilon X) := by
            simp only [weightedZeroMassAtLevel, hq0, dite_false]
            apply Finset.sum_nonneg
            intro χ hχ
            exact zeroMass_nonneg χ hXpos.le
          exact mul_nonneg hcoef0 hmassLevel
    _ = ENNReal.ofReal
        (C * X * (Real.log X) ^ 2 *
          ∑ q ∈ Finset.Icc 1 Q,
            weightedZeroMassAtLevel q X (apZeroHeight epsilon X)) := by
        congr 1
        rw [Finset.mul_sum]

/-- Premise-free inhabitant of manuscript equation (2.8), with the corrected
fixed-`K` quantifier order and the literal polylogarithmic conductor range. -/
theorem certifiedAPZeroFieldEnergy28 : APZeroFieldEnergy28 := by
  rcases MAPPrincipalZetaFullStrip.certifiedPrincipalFullStripA5 with
    ⟨Cp, hCp, hcount⟩
  intro K hK
  let C : ℝ := 1536 * (1 + (Cp + 306) * (K + 5))
  refine ⟨C, Real.exp 1, ?_, ?_, ?_⟩
  · dsimp [C]
    have : 0 < 1 + (Cp + 306) * (K + 5) := by nlinarith
    positivity
  · have he : 2 ≤ Real.exp 1 := by
      linarith [Real.exp_one_gt_d9]
    exact he
  · intro Q epsilon X hQ hepsilon hepsilonUpper hX
    exact apZeroFieldEnergy_le_polylog Cp K hCp hK hcount hQ hepsilon hX

#print axioms certifiedAPZeroFieldEnergy28

end
end MAPCertifiedAPZeroFieldEnergy28
