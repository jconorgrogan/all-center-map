import APRegularNearMeshRoute

/-!
# Direct Huxley/Jutila source adapter for the regular near-one mass

The live MAP consumer needs the weighted regular-near mass, not Jutila's
stronger fixed-modulus density theorem on the whole interval.  The certified
mesh theorem already uses Huxley's variable exponent below the first legal
Jutila collar point and Jutila only above it.  This module supplies the exact
source adapter.

Consequently, no Jutila bulk theorem is needed on the live path.  The Jutila
source surface is only the closed collar `279/280 <= sigma <= 1`.
-/

namespace MAPAPRegularNearHuxleyJutilaSourceAdapter

open MAPAPZeroDensityCert
open MAPAPRegularNearMeshRoute
open MAPAPWeightedZeroMassIntegration
open MAPJutilaCollarMeshCutoff
open MAPHuxleyCompactGapExponent
open MAPRelativeNearOneMesh27
open DirichletZeros

noncomputable section

/-- Fixed-modulus Huxley count only on the range assigned to the compact
mesh cells. -/
abbrev HuxleyFixedModulusEventually : Prop :=
  ∃ C R₀ : ℝ, 0 < C ∧ 0 ≤ R₀ ∧
    ∀ (q : ℕ) [NeZero q] (T sigma : ℝ),
      1 ≤ T → 4 / 5 ≤ sigma → sigma ≤ 279 / 280 →
      R₀ ≤ (q : ℝ) * T →
        (ambientZeroCountAtLevel q sigma T : ℝ) ≤
          C * Real.rpow ((q : ℝ) * T)
            (huxleyDensityExponent sigma + huxleySourceEta)

/-- The sole Jutila density fragment retained by the direct weighted route. -/
abbrev JutilaCollarOneTenthEventually : Prop :=
  ∃ C R₀ : ℝ, 0 < C ∧ 0 ≤ R₀ ∧
    ∀ (q : ℕ) [NeZero q] (T sigma : ℝ),
      1 ≤ T → 279 / 280 ≤ sigma → sigma ≤ 1 →
      R₀ ≤ (q : ℝ) * T →
        (ambientZeroCountAtLevel q sigma T : ℝ) ≤
          C * Real.rpow ((q : ℝ) * T)
            ((21 / 10) * (1 - sigma))

/-- At one legal scale, the two literal fixed-modulus sources supply exactly
the primitive-inducer hypotheses of the weighted Huxley/Jutila mesh theorem.
No full-range `21/10` density estimate is constructed. -/
theorem primitiveRegularNearOneRangeMass_le_of_sources
    {CH RH CJ RJ : ℝ}
    (hCH : 0 < CH) (hCJ : 0 < CJ)
    (hHsource : ∀ (r : ℕ) [NeZero r] (S sigma : ℝ),
      1 ≤ S → 4 / 5 ≤ sigma → sigma ≤ 279 / 280 →
      RH ≤ (r : ℝ) * S →
        (ambientZeroCountAtLevel r sigma S : ℝ) ≤
          CH * Real.rpow ((r : ℝ) * S)
            (huxleyDensityExponent sigma + huxleySourceEta))
    (hJsource : ∀ (r : ℕ) [NeZero r] (S sigma : ℝ),
      1 ≤ S → 279 / 280 ≤ sigma → sigma ≤ 1 →
      RJ ≤ (r : ℝ) * S →
        (ambientZeroCountAtLevel r sigma S : ℝ) ≤
          CJ * Real.rpow ((r : ℝ) * S)
            ((21 / 10) * (1 - sigma)))
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {epsilon u omega X T : ℝ} {L : ℕ}
    (hepsilon : 0 ≤ epsilon) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 315)
    (hgap : ∀ rho : ℂ,
      rho ∈ (by
        letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
        let psi := chi.primitiveCharacter
        exact (zeroSupport psi 0 T).filter (fun rho =>
          4 / 5 < rho.re ∧
            ¬ (psi ≠ 1 ∧ psi ^ 2 = 1 ∧ rho.im = 0))) →
      rho.re ≤ 1 - omega)
    (hdepth : relativeDistance L ≤ omega)
    (hmeshGap : ∀ j < L, omega ≤ relativeDistance j)
    (hLlog : (L : ℝ) ≤ Real.log X)
    (hX : 1 ≤ X) (hTone : 1 ≤ T)
    (hScaleToX : (chi.conductor : ℝ) * T ≤
      Real.rpow X (MAPGuthMaynard.tau epsilon + u))
    (hHuxleyScale : RH ≤ (chi.conductor : ℝ) * T)
    (hJutilaScale : RJ ≤ (chi.conductor : ℝ) * T) :
    primitiveRegularNearOneRangeMass chi X T ≤
      Real.log X *
        (CH * Real.rpow X (-huxleyCompactSaving) +
          CJ * Real.rpow X (-(omega / 12))) := by
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  let psi := chi.primitiveCharacter
  apply primitiveRegularNearOneRangeMass_le_huxley_jutila_mesh
    chi hepsilon hu0 hu hgap hdepth hmeshGap hLlog hX
    hCH.le hCJ.le
    (mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans hTone))
    (mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans hTone))
    hScaleToX hScaleToX
  · intro j _hjL hj
    have hrange := huxley_mesh_endpoint_range hj
    have hsingleNat := dirichletZeroCount_le_ambientZeroCountAtLevel
      psi (relativePoint j) T
    have hsingle :
        (primitiveDirichletZeroCount chi (relativePoint j) T : ℝ) ≤
          (ambientZeroCountAtLevel chi.conductor (relativePoint j) T : ℝ) := by
      simpa only [primitiveDirichletZeroCount] using
        (show (dirichletZeroCount psi (relativePoint j) T : ℝ) ≤
          (ambientZeroCountAtLevel chi.conductor (relativePoint j) T : ℝ) by
            exact_mod_cast hsingleNat)
    exact hsingle.trans
      (hHsource chi.conductor T (relativePoint j) hTone hrange.1
        hrange.2.le hHuxleyScale)
  · intro j _hjL hj
    have hsigmaLow := relativePoint_mem_collar hj
    have hsingleNat := dirichletZeroCount_le_ambientZeroCountAtLevel
      psi (relativePoint j) T
    have hsingle :
        (primitiveDirichletZeroCount chi (relativePoint j) T : ℝ) ≤
          (ambientZeroCountAtLevel chi.conductor (relativePoint j) T : ℝ) := by
      simpa only [primitiveDirichletZeroCount] using
        (show (dirichletZeroCount psi (relativePoint j) T : ℝ) ≤
          (ambientZeroCountAtLevel chi.conductor (relativePoint j) T : ℝ) by
            exact_mod_cast hsingleNat)
    exact hsingle.trans
      (hJsource chi.conductor T (relativePoint j) hTone hsigmaLow
        (relativePoint_le_one j) hJutilaScale)

/-- Direct ambient-family weighted-mass theorem.  This is the live replacement
for passing a full-range Jutila density proposition through the regular-near
argument. -/
theorem apRegularNearOneRangeMass_le_of_sources
    {CH RH CJ RJ : ℝ}
    (hCH : 0 < CH) (hCJ : 0 < CJ)
    (hHsource : ∀ (r : ℕ) [NeZero r] (S sigma : ℝ),
      1 ≤ S → 4 / 5 ≤ sigma → sigma ≤ 279 / 280 →
      RH ≤ (r : ℝ) * S →
        (ambientZeroCountAtLevel r sigma S : ℝ) ≤
          CH * Real.rpow ((r : ℝ) * S)
            (huxleyDensityExponent sigma + huxleySourceEta))
    (hJsource : ∀ (r : ℕ) [NeZero r] (S sigma : ℝ),
      1 ≤ S → 279 / 280 ≤ sigma → sigma ≤ 1 →
      RJ ≤ (r : ℝ) * S →
        (ambientZeroCountAtLevel r sigma S : ℝ) ≤
          CJ * Real.rpow ((r : ℝ) * S)
            ((21 / 10) * (1 - sigma)))
    {Q L : ℕ} {epsilon u omega X T : ℝ}
    (hepsilon : 0 ≤ epsilon) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 315)
    (hgap : ∀ (q : ℕ) [NeZero q]
      (chi : DirichletCharacter ℂ q), q ≤ Q → ∀ rho : ℂ,
      rho ∈ (by
        letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
        let psi := chi.primitiveCharacter
        exact (zeroSupport psi 0 T).filter (fun rho =>
          4 / 5 < rho.re ∧
            ¬ (psi ≠ 1 ∧ psi ^ 2 = 1 ∧ rho.im = 0))) →
      rho.re ≤ 1 - omega)
    (hdepth : relativeDistance L ≤ omega)
    (hmeshGap : ∀ j < L, omega ≤ relativeDistance j)
    (hLlog : (L : ℝ) ≤ Real.log X)
    (hX : 1 ≤ X) (hTone : 1 ≤ T)
    (hScaleToX : ∀ (q : ℕ) [NeZero q]
      (chi : DirichletCharacter ℂ q), q ≤ Q →
        (chi.conductor : ℝ) * T ≤
          Real.rpow X (MAPGuthMaynard.tau epsilon + u))
    (hHuxleyScale : ∀ (q : ℕ) [NeZero q]
      (chi : DirichletCharacter ℂ q), q ≤ Q →
        RH ≤ (chi.conductor : ℝ) * T)
    (hJutilaScale : ∀ (q : ℕ) [NeZero q]
      (chi : DirichletCharacter ℂ q), q ≤ Q →
        RJ ≤ (chi.conductor : ℝ) * T) :
    apRegularNearOneRangeMass Q X T ≤
      (Q : ℝ) ^ 2 *
        (Real.log X *
          (CH * Real.rpow X (-huxleyCompactSaving) +
            CJ * Real.rpow X (-(omega / 12)))) := by
  let B : ℝ := Real.log X *
    (CH * Real.rpow X (-huxleyCompactSaving) +
      CJ * Real.rpow X (-(omega / 12)))
  have hlog : 0 ≤ Real.log X := Real.log_nonneg hX
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hprimitive : ∀ (q : ℕ) [NeZero q]
      (chi : DirichletCharacter ℂ q), q ≤ Q →
        primitiveRegularNearOneRangeMass chi X T ≤ B := by
    intro q _inst chi hqQ
    exact primitiveRegularNearOneRangeMass_le_of_sources
      hCH hCJ hHsource hJsource chi hepsilon hu0 hu
      (hgap q chi hqQ) hdepth hmeshGap hLlog hX hTone
      (hScaleToX q chi hqQ) (hHuxleyScale q chi hqQ)
      (hJutilaScale q chi hqQ)
  simpa only [B] using apRegularNearOneRangeMass_le_sq_mul hB hprimitive

end

end MAPAPRegularNearHuxleyJutilaSourceAdapter

#print axioms MAPAPRegularNearHuxleyJutilaSourceAdapter.primitiveRegularNearOneRangeMass_le_of_sources
#print axioms MAPAPRegularNearHuxleyJutilaSourceAdapter.apRegularNearOneRangeMass_le_of_sources
