import APTruncatedZeroFieldRow
import APSelectedHeightZeroFieldEnergy28

/-!
# Selected-height equation (2.8) for the half-integer Perron field
-/

namespace MAPAPSelectedTruncatedZeroFieldEnergy28

open MeasureTheory Set
open scoped ENNReal BigOperators
open APFoundation APExplicitFormulaMajorantAdapter
open MAPFixedScaleAPZeroRoute MAPAPHalfIntegerAlignedTail
open MAPAPTruncatedZeroFieldRow MAPAPHeightMonotonicity
open DirichletZeros MAPLocalZeroWindow

noncomputable section

/-- Indicator-valued sigma-truncated field consumed by the maximal theorem. -/
def truncatedZeroNormField {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (sigma X T t : ℝ) : ℝ≥0∞ :=
  (Set.Icc (X / 4) (6 * X)).indicator
    (fun u => ENNReal.ofReal ‖perronZeroField chi sigma T u‖) t

/-- Family energy for character-dependent left edges and one common height. -/
def truncatedZeroFieldEnergyAtLevel
    (q : ℕ) (sigma : DirichletCharacter ℂ q → ℝ)
    (X T : ℝ) : ℝ≥0∞ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    ∑ chi : DirichletCharacter ℂ q,
      ∫⁻ t : ℝ, (truncatedZeroNormField chi (sigma chi) X T t) ^ 2

def truncatedAPZeroFieldEnergy
    (Q : ℕ) (sigma : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ)
    (X T : ℝ) : ℝ≥0∞ :=
  ∑ q ∈ Finset.Icc 1 Q,
    truncatedZeroFieldEnergyAtLevel q (sigma q) X T

private theorem truncatedWeightedZeroMass_nonneg
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {sigma X T : ℝ} (hX : 0 ≤ X) :
    0 ≤ truncatedWeightedZeroMass chi sigma X T := by
  unfold truncatedWeightedZeroMass
  apply Finset.sum_nonneg
  intro rho hrho
  exact mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hX _)

/-- The positive-left-edge weighted mass is bounded by the full-strip mass at
the same height. -/
theorem truncatedWeightedZeroMass_le_full
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {sigma X T : ℝ} (hsigma : 0 ≤ sigma) (hX : 0 ≤ X) :
    truncatedWeightedZeroMass chi sigma X T ≤
      primitiveWeightedZeroMass chi X T := by
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  let psi := chi.primitiveCharacter
  let S := zeroSupport psi sigma T
  let U := zeroSupport psi 0 T
  have hsub : S ⊆ U := zeroSupport_subset_full psi hsigma
  have hrewrite : truncatedWeightedZeroMass chi sigma X T =
      ∑ rho ∈ S,
        (zeroMultiplicity psi 0 T rho : ℝ) *
          Real.rpow X (2 * (rho.re - 1)) := by
    unfold truncatedWeightedZeroMass
    apply Finset.sum_congr rfl
    intro rho hrho
    rw [zeroMultiplicity_eq_full_of_mem psi hsigma hrho]
  rw [hrewrite]
  unfold primitiveWeightedZeroMass
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun rho hrhoU hrhoS =>
      mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hX _))

private theorem primitiveWeightedZeroMass_nonneg
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {X T : ℝ} (hX : 0 ≤ X) :
    0 ≤ primitiveWeightedZeroMass chi X T := by
  unfold primitiveWeightedZeroMass
  apply Finset.sum_nonneg
  intro rho hrho
  exact mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hX _)

/-- One-character selected-height truncated equation (2.8). -/
theorem primitive_truncated_energy_selected_le
    (Cp K : ℝ) (hCp : 0 < Cp) (hK : 0 < K)
    (hcount : ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q),
      chi.IsPrimitive → chi = 1 → ∀ t : ℝ,
        (closedUnitWindowCount chi 0 t : ℝ) ≤
          Cp * Real.log (arithmeticScale q t))
    {q Q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {sigma reserve X H T : ℝ}
    (hqQ : q ≤ Q)
    (hQ : Q ≤ ⌊Real.rpow (Real.log X) K⌋₊)
    (hsigma : 0 < sigma)
    (hreserve : 0 < reserve)
    (hH : H = apZeroHeight reserve X)
    (hT : T ∈ Set.Ioo H (H + 1))
    (hX : Real.exp 4 ≤ X) :
    (∫⁻ t : ℝ, (truncatedZeroNormField chi sigma X T t) ^ 2) ≤
      ENNReal.ofReal
        ((1152 * (1 + (Cp + 306) * (K + 3))) * X *
          (Real.log X) ^ 2 *
          primitiveWeightedZeroMass chi X (H + 1)) := by
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  have hXpos : 0 < X := (Real.exp_pos 4).trans_le hX
  have hH0 : 0 ≤ H := by
    rw [hH]
    exact Real.rpow_nonneg hXpos.le _
  have hT0 : 0 ≤ T := hH0.trans hT.1.le
  have hraw := truncated_perron_energy_le_raw Cp hCp hcount chi
    hsigma hXpos hT0
  have hrow := MAPAPSelectedHeightZeroFieldEnergy28.selectedHeight_rowFactor_le
    Cp K hCp hK chi hqQ hQ hreserve hH hT hX
  have hm0 := truncatedWeightedZeroMass_nonneg chi
    (sigma := sigma) (X := X) (T := T) hXpos.le
  have hmfull := truncatedWeightedZeroMass_le_full chi
    (T := T) hsigma.le hXpos.le
  have hmmono := primitiveWeightedZeroMass_mono_height chi hXpos.le hT.2.le
  have hmtop := primitiveWeightedZeroMass_nonneg chi
    (X := X) (T := H + 1) hXpos.le
  change (∫⁻ t : ℝ,
      ((Set.Icc (X / 4) (6 * X)).indicator
        (fun u => ENNReal.ofReal ‖perronZeroField chi sigma T u‖) t) ^ 2) ≤ _
  refine hraw.trans ?_
  apply ENNReal.ofReal_le_ofReal
  calc
    192 * X *
        (2 * (1 + (Cp + 306) *
          Real.log ((chi.conductor : ℝ) * (T + 4))) *
          (harmonic (⌊2 * T⌋₊ + 1) : ℝ)) *
        truncatedWeightedZeroMass chi sigma X T ≤
      192 * X *
        ((6 * (1 + (Cp + 306) * (K + 3))) * (Real.log X) ^ 2) *
        truncatedWeightedZeroMass chi sigma X T := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hrow
          (mul_nonneg (by norm_num) hXpos.le)) hm0
    _ ≤ 192 * X *
        ((6 * (1 + (Cp + 306) * (K + 3))) * (Real.log X) ^ 2) *
        primitiveWeightedZeroMass chi X (H + 1) := by
      gcongr
      exact hmfull.trans hmmono
    _ = (1152 * (1 + (Cp + 306) * (K + 3))) * X *
        (Real.log X) ^ 2 *
        primitiveWeightedZeroMass chi X (H + 1) := by ring

private theorem truncatedEnergyAtLevel_selected_le
    (Cp K : ℝ) (hCp : 0 < Cp) (hK : 0 < K)
    (hcount : ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q),
      chi.IsPrimitive → chi = 1 → ∀ t : ℝ,
        (closedUnitWindowCount chi 0 t : ℝ) ≤
          Cp * Real.log (arithmeticScale q t))
    {q Q : ℕ} (sigma : DirichletCharacter ℂ q → ℝ)
    (hsigma : ∀ chi, 0 < sigma chi)
    (hqQ : q ≤ Q)
    {reserve X H T : ℝ}
    (hQ : Q ≤ ⌊Real.rpow (Real.log X) K⌋₊)
    (hreserve : 0 < reserve)
    (hH : H = apZeroHeight reserve X)
    (hT : T ∈ Set.Ioo H (H + 1))
    (hX : Real.exp 4 ≤ X) :
    truncatedZeroFieldEnergyAtLevel q sigma X T ≤
      ENNReal.ofReal
        ((1152 * (1 + (Cp + 306) * (K + 3))) * X *
          (Real.log X) ^ 2 * weightedZeroMassAtLevel q X (H + 1)) := by
  by_cases hq0 : q = 0
  · simp [truncatedZeroFieldEnergyAtLevel, weightedZeroMassAtLevel, hq0]
  · letI : NeZero q := ⟨hq0⟩
    let C : ℝ := 1152 * (1 + (Cp + 306) * (K + 3))
    have hXpos : 0 < X := (Real.exp_pos 4).trans_le hX
    have hcoef0 : 0 ≤ C * X * (Real.log X) ^ 2 := by
      dsimp [C]
      have : 0 ≤ 1 + (Cp + 306) * (K + 3) := by nlinarith
      positivity
    simp only [truncatedZeroFieldEnergyAtLevel, weightedZeroMassAtLevel,
      hq0, dite_false]
    calc
      (∑ chi : DirichletCharacter ℂ q,
          ∫⁻ t : ℝ, (truncatedZeroNormField chi (sigma chi) X T t) ^ 2) ≤
        ∑ chi : DirichletCharacter ℂ q,
          ENNReal.ofReal (C * X * (Real.log X) ^ 2 *
            primitiveWeightedZeroMass chi X (H + 1)) := by
        apply Finset.sum_le_sum
        intro chi hchi
        exact primitive_truncated_energy_selected_le Cp K hCp hK hcount chi
          hqQ hQ (hsigma chi) hreserve hH hT hX
      _ = ENNReal.ofReal (∑ chi : DirichletCharacter ℂ q,
          C * X * (Real.log X) ^ 2 *
            primitiveWeightedZeroMass chi X (H + 1)) := by
        symm
        apply ENNReal.ofReal_sum_of_nonneg
        intro chi hchi
        exact mul_nonneg hcoef0
          (primitiveWeightedZeroMass_nonneg chi hXpos.le)
      _ = ENNReal.ofReal (C * X * (Real.log X) ^ 2 *
          ∑ chi : DirichletCharacter ℂ q,
            primitiveWeightedZeroMass chi X (H + 1)) := by
        congr 1
        rw [Finset.mul_sum]

/-- Selected-height equation (2.8) for character-dependent Perron edges. -/
def SelectedTruncatedAPZeroFieldEnergy28 : Prop :=
  ∀ K : ℝ, 0 < K →
    ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧
      ∀ (Q : ℕ)
        (sigma : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ)
        (reserve X H T : ℝ),
        Q ≤ ⌊Real.rpow (Real.log X) K⌋₊ →
        (∀ (q : ℕ) (hq : q ∈ Finset.Icc 1 Q)
          (chi : DirichletCharacter ℂ q), 0 < sigma q chi) →
        0 < reserve → reserve ≤ 1 / 10 →
        H = apZeroHeight reserve X →
        T ∈ Set.Ioo H (H + 1) → X0 ≤ X →
        truncatedAPZeroFieldEnergy Q sigma X T ≤
          ENNReal.ofReal
            (C * X * (Real.log X) ^ 2 *
              apWeightedZeroMass Q X (H + 1))

/-- Premise-free sigma-truncated selected-height equation (2.8). -/
theorem certifiedSelectedTruncatedAPZeroFieldEnergy28 :
    SelectedTruncatedAPZeroFieldEnergy28 := by
  rcases MAPPrincipalZetaFullStrip.certifiedPrincipalFullStripA5 with
    ⟨Cp, hCp, hcount⟩
  intro K hK
  let C : ℝ := 1152 * (1 + (Cp + 306) * (K + 3))
  refine ⟨C, Real.exp 4, ?_, ?_, ?_⟩
  · dsimp [C]
    have : 0 < 1 + (Cp + 306) * (K + 3) := by nlinarith
    positivity
  · have he2 : 2 < Real.exp 1 := by nlinarith [Real.exp_one_gt_d9]
    exact he2.le.trans (Real.exp_le_exp.mpr (by norm_num))
  · intro Q sigma reserve X H T hQ hsigma hreserve hreserveCap hH hT hX
    let coef : ℝ := C * X * (Real.log X) ^ 2
    have hXpos : 0 < X := (Real.exp_pos 4).trans_le hX
    have hcoef0 : 0 ≤ coef := by
      dsimp [coef, C]
      have : 0 ≤ 1 + (Cp + 306) * (K + 3) := by nlinarith
      positivity
    unfold truncatedAPZeroFieldEnergy apWeightedZeroMass
    calc
      (∑ q ∈ Finset.Icc 1 Q,
          truncatedZeroFieldEnergyAtLevel q (sigma q) X T) ≤
        ∑ q ∈ Finset.Icc 1 Q,
          ENNReal.ofReal
            (coef * weightedZeroMassAtLevel q X (H + 1)) := by
        apply Finset.sum_le_sum
        intro q hq
        simpa [coef, C] using
          truncatedEnergyAtLevel_selected_le Cp K hCp hK hcount
            (sigma q) (fun chi => hsigma q hq chi)
            (Finset.mem_Icc.mp hq).2 hQ hreserve hH hT hX
      _ = ENNReal.ofReal (∑ q ∈ Finset.Icc 1 Q,
          coef * weightedZeroMassAtLevel q X (H + 1)) := by
        symm
        apply ENNReal.ofReal_sum_of_nonneg
        intro q hq
        exact mul_nonneg hcoef0
          (MAPAPConditionalShortIntervalConnector.weightedZeroMassAtLevel_nonneg
            q hXpos.le (H + 1))
      _ = ENNReal.ofReal (C * X * (Real.log X) ^ 2 *
          ∑ q ∈ Finset.Icc 1 Q,
            weightedZeroMassAtLevel q X (H + 1)) := by
        congr 1
        dsimp [coef]
        rw [Finset.mul_sum]

end
end MAPAPSelectedTruncatedZeroFieldEnergy28

#print axioms MAPAPSelectedTruncatedZeroFieldEnergy28.truncatedWeightedZeroMass_le_full
#print axioms MAPAPSelectedTruncatedZeroFieldEnergy28.primitive_truncated_energy_selected_le
#print axioms MAPAPSelectedTruncatedZeroFieldEnergy28.certifiedSelectedTruncatedAPZeroFieldEnergy28
