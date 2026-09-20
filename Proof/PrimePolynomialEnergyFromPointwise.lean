import ModelOverlapEnergy

/-!
# Pointwise prime-polynomial saving to translated square energy

This isolates the exact quantitative consequence expected from the
Siegel--Walfisz/residue/Abel connector.  It is strictly earlier than the
continuous-kernel, Ramanujan, support, and overlap corrections.
-/

namespace MAPPrimePolynomialEnergyFromPointwise

open AddCircle
open PrimePairEndpoints MAPMajorArcWeld MAPModelOverlapEnergy

noncomputable section

/-- Arbitrary logarithmic saving for the literal prime polynomial on every
reduced paper arc.  This is the clean quantitative collapse of the explicit
envelope produced from `UniformSiegelWalfiszPsi`. -/
def UniformPrimePolynomialLogSaving : Prop :=
  ∀ K B D : ℕ,
    ∃ C X₀ : ℝ, 0 < C ∧ 2 ≤ X₀ ∧
      ∀ X : ℝ, X₀ ≤ X →
      ∀ q a : ℕ, ∀ β : ℝ,
        1 ≤ q → (q : ℝ) ≤ (Real.log X) ^ B →
        a < q → a.Coprime q →
        |β| ≤ paperArcRadius X D →
        ‖primeExponentialSum X
            (rationalCenter q a + (β : UnitAddCircle)) -
          primeMajorCoefficient q *
            MAPContinuousOverlap.dyadicAmplitude X β‖ ≤
          C * X / (Real.log X) ^ K

/-- Exact bookkeeping for the `Q²` rational-arc count and beta radius. -/
theorem coarse_majorArc_error_log_saving
    {X C E : ℝ} {B D K : ℕ}
    (hX : Real.exp 1 ≤ X) (hC : 0 ≤ C) (hE : 0 ≤ E)
    (hEbound : E ≤ C * X / (Real.log X) ^ (2 * B + D + K)) :
    ((paperDenominatorCutoff X B : ℕ) : ℝ) ^ 2 *
        (2 * paperArcRadius X D * (E * (2 * X + E))) ≤
      2 * C * (2 + C) * X / (Real.log X) ^ K := by
  have hXpos : 0 < X := (Real.exp_pos 1).trans_le hX
  have hlog1 : 1 ≤ Real.log X :=
    (Real.le_log_iff_exp_le hXpos).2 hX
  have hlogpos : 0 < Real.log X := zero_lt_one.trans_le hlog1
  have hpowA : 1 ≤ (Real.log X) ^ (2 * B + D + K) := one_le_pow₀ hlog1
  have hEupper : E ≤ C * X := by
    have hCX : 0 ≤ C * X := mul_nonneg hC hXpos.le
    have hdiv : C * X / (Real.log X) ^ (2 * B + D + K) ≤ C * X := by
      exact (div_le_iff₀ (pow_pos hlogpos _)).2
        (le_mul_of_one_le_right hCX hpowA)
    exact hEbound.trans hdiv
  have hQ : ((paperDenominatorCutoff X B : ℕ) : ℝ) ≤
      (Real.log X) ^ B := by
    unfold paperDenominatorCutoff
    exact Nat.floor_le (pow_nonneg hlogpos.le _)
  have hR0 : 0 ≤ paperArcRadius X D := by
    unfold paperArcRadius
    positivity
  have hsum : 2 * X + E ≤ (2 + C) * X := by nlinarith
  have hidentity :
      ((Real.log X) ^ B) ^ 2 *
          (2 * paperArcRadius X D *
            ((C * X / (Real.log X) ^ (2 * B + D + K)) *
              ((2 + C) * X))) =
        2 * C * (2 + C) * X / (Real.log X) ^ K := by
    unfold paperArcRadius
    have hlogne : Real.log X ≠ 0 := hlogpos.ne'
    have hXne : X ≠ 0 := hXpos.ne'
    rw [show 2 * B + D + K = B * 2 + D + K by omega,
      pow_add, pow_add, pow_mul]
    field_simp
  calc
    ((paperDenominatorCutoff X B : ℕ) : ℝ) ^ 2 *
        (2 * paperArcRadius X D * (E * (2 * X + E))) ≤
      ((Real.log X) ^ B) ^ 2 *
        (2 * paperArcRadius X D *
          ((C * X / (Real.log X) ^ (2 * B + D + K)) *
            ((2 + C) * X))) := by
      gcongr
    _ = 2 * C * (2 + C) * X / (Real.log X) ^ K := hidentity

/-- The literal pointwise prime-polynomial family implies exactly the
prime-to-continuous-model square-energy family consumed by the final weld. -/
theorem selectablePrimePolynomialModelErrorEnergy_of_pointwise
    (hPoint : UniformPrimePolynomialLogSaving) :
    SelectablePrimePolynomialModelErrorEnergyFamily := by
  intro A ε hA hε B₀ D₀
  let k : ℕ := ⌈A⌉₊ + 1
  let L : ℕ := 2 * B₀ + D₀ + k
  obtain ⟨Cp, Xp, hCp, hXp, hp⟩ := hPoint L B₀ D₀
  obtain ⟨Xg, hg⟩ := MAPMajorArcPublicLiftBridge.eventually_paperArc_geometry B₀ D₀
  let Ce : ℝ := 2 * Cp * (2 + Cp)
  let C : ℝ := 3 * Ce ^ 2
  let X₀ : ℝ := max (max Xp Xg) 3
  have hCe : 0 < Ce := by dsimp [Ce]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hX₀ : 3 ≤ X₀ := by
    exact le_max_right (max Xp Xg) 3
  refine ⟨B₀, D₀, le_rfl, le_rfl, C, X₀, hC, hX₀, ?_⟩
  intro X H h₀ hXX₀ hlegal
  have hXXp : Xp ≤ X :=
    (le_max_left Xp Xg).trans
      ((le_max_left (max Xp Xg) 3).trans hXX₀)
  have hXXg : Xg ≤ X :=
    (le_max_right Xp Xg).trans
      ((le_max_left (max Xp Xg) 3).trans hXX₀)
  have hXexp : Real.exp 1 ≤ X := by
    have hexp3 : Real.exp 1 ≤ (3 : ℝ) :=
      Real.exp_one_lt_d9.le.trans (by norm_num)
    exact hexp3.trans ((le_max_right (max Xp Xg) 3).trans hXX₀)
  obtain ⟨hX1, hR, hRhalf, hgrowth⟩ := hg X hXXg
  have hlog1 : 1 ≤ Real.log X :=
    (Real.le_log_iff_exp_le ((Real.exp_pos 1).trans_le hXexp)).2 hXexp
  let E : ℝ := Cp * X / (Real.log X) ^ L
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hpointwise : ∀ q a : ℕ, ∀ β : ℝ,
      1 ≤ q → (q : ℝ) ≤ (Real.log X) ^ B₀ →
      a < q → a.Coprime q →
      |β| ≤ paperArcRadius X D₀ →
      ‖primeExponentialSum X
          (rationalCenter q a + (β : UnitAddCircle)) -
        primeMajorCoefficient q *
          MAPContinuousOverlap.dyadicAmplitude X β‖ ≤ E := by
    intro q a β hq hqL ha hcop hβ
    exact hp X hXXp q a β hq hqL ha hcop hβ
  have hmajorPoint : ∀ h : ℤ,
      ‖primePolynomialModelError X B₀ D₀ h‖ ≤
        Ce * X / (Real.log X) ^ k := by
    intro h
    have hcoarse :=
      MAPMajorArcPublicLiftBridge.norm_majorCoefficient_sub_modeledPaperMajorContribution_le_coarse
        (h := h) hX1 hE hRhalf hgrowth hpointwise
    have harith := coarse_majorArc_error_log_saving
      hXexp hCp.le hE (le_rfl : E ≤ Cp * X / (Real.log X) ^ L)
    unfold primePolynomialModelError
    simpa [Ce, E, L, add_assoc, add_comm, add_left_comm] using hcoarse.trans harith
  have hH1 := SupportBoundaryQuantitative.one_le_H_of_legal
    (by linarith : 1 ≤ X) hε hlegal
  have hcard := SupportBoundaryQuantitative.translatedWindow_card_real_le
    (h₀ := h₀) (by linarith : 0 ≤ H)
  have hcard3 : ((translatedWindow H h₀).card : ℝ) ≤ 3 * H :=
    hcard.trans (by linarith)
  have hkA : A ≤ (2 * k : ℕ) := by
    have hceil : A ≤ (⌈A⌉₊ : ℝ) := Nat.le_ceil A
    have hnat : ⌈A⌉₊ ≤ 2 * k := by dsimp [k]; omega
    exact hceil.trans (by exact_mod_cast hnat)
  have hratio :
      1 / (Real.log X) ^ (2 * k) ≤ Real.rpow (Real.log X) (-A) := by
    simpa using
      (pow_div_pow_le_rpow_neg (L := Real.log X) (A := A)
        (m := 0) (n := 2 * k) hlog1 (by omega) hkA)
  unfold primePolynomialModelErrorEnergy
  calc
    (∑ h ∈ translatedWindow H h₀,
        if h = 0 then 0 else ‖primePolynomialModelError X B₀ D₀ h‖ ^ 2) ≤
      ∑ _h ∈ translatedWindow H h₀,
        (Ce * X / (Real.log X) ^ k) ^ 2 := by
      apply Finset.sum_le_sum
      intro h hh
      split_ifs
      · positivity
      · have hpnt := hmajorPoint h
        exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hpnt
    _ = ((translatedWindow H h₀).card : ℝ) *
        (Ce * X / (Real.log X) ^ k) ^ 2 := by simp
    _ ≤ (3 * H) * (Ce * X / (Real.log X) ^ k) ^ 2 := by
      gcongr
    _ = C * H * X ^ 2 * (1 / (Real.log X) ^ (2 * k)) := by
      dsimp [C]
      rw [div_pow, ← pow_mul]
      ring
    _ ≤ C * H * X ^ 2 * Real.rpow (Real.log X) (-A) := by
      exact mul_le_mul_of_nonneg_left hratio (by positivity)

end
end MAPPrimePolynomialEnergyFromPointwise

#print axioms MAPPrimePolynomialEnergyFromPointwise.selectablePrimePolynomialModelErrorEnergy_of_pointwise
