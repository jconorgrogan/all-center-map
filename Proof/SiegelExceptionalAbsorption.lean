import SiegelExceptionalEndpoint
import PrimitiveEulerZeroTransport

/-!
# Absorbing the single Goldfeld exception

Koukoulopoulos Theorem 12.9 gives the Siegel region for primitive real
characters with at most one exceptional character.  The published proof of
Theorem 12.10 invokes the weak quantitative Theorem 12.8 for that fixed
character.  For the ineffective existence statement, Mathlib's nonvanishing
and continuity at `s = 1` are already sufficient.  This file certifies that
deterministic reduction and leaves only the all-but-one Goldfeld theorem.
-/

namespace MAPGoldfeldSiegel

open Filter Metric

noncomputable section

/-- A primitive real nonprincipal character packaged across varying
conductors. -/
structure PrimitiveRealCharacter where
  level : ℕ
  level_ne_zero : level ≠ 0
  chi : DirichletCharacter ℂ level
  primitive : chi.IsPrimitive
  nonprincipal : chi ≠ 1
  real : chi ^ 2 = 1

namespace PrimitiveRealCharacter

instance (a : PrimitiveRealCharacter) : NeZero a.level := ⟨a.level_ne_zero⟩

/-- The packaged Dirichlet L-function. -/
def LFunction (a : PrimitiveRealCharacter) (s : ℂ) : ℂ :=
  DirichletCharacter.LFunction a.chi s

theorem LFunction_one_ne_zero (a : PrimitiveRealCharacter) :
    a.LFunction 1 ≠ 0 :=
  DirichletCharacter.LFunction_apply_one_ne_zero a.nonprincipal

/-- Every fixed nonprincipal character has a real zero-free neighborhood of
one.  No quantitative character-sum theorem is needed for this fixed-object
statement. -/
theorem exists_real_zeroFree_radius (a : PrimitiveRealCharacter) :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ sigma : ℝ, |sigma - 1| < eta → a.LFunction sigma ≠ 0 := by
  have hcont : ContinuousAt a.LFunction 1 :=
    (DirichletCharacter.differentiableAt_LFunction
      a.chi 1 (.inr a.nonprincipal)).continuousAt
  have hevent : ∀ᶠ s : ℂ in nhds 1, a.LFunction s ≠ 0 :=
    hcont.eventually_ne a.LFunction_one_ne_zero
  rcases Metric.eventually_nhds_iff_ball.mp hevent with ⟨eta, heta, hball⟩
  refine ⟨eta, heta, ?_⟩
  intro sigma hsigma
  apply hball (sigma : ℂ)
  have hdist : dist (sigma : ℂ) (1 : ℂ) = |sigma - 1| := by
    calc
      dist (sigma : ℂ) (1 : ℂ) = dist sigma 1 :=
        Complex.isometry_ofReal.dist_eq sigma 1
      _ = |sigma - 1| := Real.dist_eq sigma 1
  simpa [hdist] using hsigma

end PrimitiveRealCharacter

/-- Source-faithful logical form of Koukoulopoulos Theorem 12.9: for each
positive exponent there is a uniform region for all primitive real
nonprincipal characters, with at most one packaged exception. -/
def GoldfeldPrimitiveAllButOneZeroFree : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ c : ℝ, 0 < c ∧
      ∃ exception : Option PrimitiveRealCharacter,
        ∀ a : PrimitiveRealCharacter, some a ≠ exception →
          ∀ sigma : ℝ,
            1 - c * Real.rpow (a.level : ℝ) (-epsilon) < sigma →
              a.LFunction sigma ≠ 0

/-- The single exceptional character in Theorem 12.9 is absorbed into the
ineffective constant using its fixed zero-free neighborhood at one.  This is
the primitive-character content of Koukoulopoulos Theorem 12.10. -/
theorem GoldfeldPrimitiveAllButOneZeroFree.to_all_primitive
    (hGoldfeld : GoldfeldPrimitiveAllButOneZeroFree) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ c : ℝ, 0 < c ∧
        ∀ a : PrimitiveRealCharacter,
          ∀ sigma : ℝ,
            1 - c * Real.rpow (a.level : ℝ) (-epsilon) < sigma →
              a.LFunction sigma ≠ 0 := by
  intro epsilon hepsilon
  rcases hGoldfeld epsilon hepsilon with ⟨c0, hc0, exception, hregion⟩
  cases exception with
  | none =>
      refine ⟨c0, hc0, ?_⟩
      intro a sigma hsigma
      exact hregion a (by simp) sigma hsigma
  | some exceptional =>
      rcases exceptional.exists_real_zeroFree_radius with ⟨eta, heta, hlocal⟩
      let ce : ℝ := eta * Real.rpow (exceptional.level : ℝ) epsilon
      have hlevel : 0 < (exceptional.level : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero exceptional.level_ne_zero
      have hce : 0 < ce := mul_pos heta (Real.rpow_pos_of_pos hlevel epsilon)
      let c : ℝ := min c0 ce
      have hc : 0 < c := lt_min hc0 hce
      refine ⟨c, hc, ?_⟩
      intro a sigma hsigma
      classical
      by_cases ha : a = exceptional
      · subst a
        by_cases hsigmaOne : 1 ≤ sigma
        · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re
            exceptional.chi (.inl exceptional.nonprincipal) (by simpa using hsigmaOne)
        · apply hlocal sigma
          rw [abs_of_nonpos (by linarith)]
          have hcce : c ≤ ce := min_le_right _ _
          have hpowPos : 0 < Real.rpow (exceptional.level : ℝ) (-epsilon) :=
            Real.rpow_pos_of_pos hlevel (-epsilon)
          have hscaled := mul_le_mul_of_nonneg_right hcce hpowPos.le
          have hcancel : ce * Real.rpow (exceptional.level : ℝ) (-epsilon) = eta := by
            calc
              ce * Real.rpow (exceptional.level : ℝ) (-epsilon) =
                  eta * (Real.rpow (exceptional.level : ℝ) epsilon *
                    Real.rpow (exceptional.level : ℝ) (-epsilon)) := by
                    simp [ce, mul_assoc]
              _ = eta * Real.rpow (exceptional.level : ℝ) (epsilon + -epsilon) := by
                    congr 1
                    exact (Real.rpow_add hlevel epsilon (-epsilon)).symm
              _ = eta := by simp
          rw [hcancel] at hscaled
          linarith
      · have hsource := hregion a (by simpa using ha) sigma
        apply hsource
        have hcc0 : c ≤ c0 := min_le_left _ _
        have hpow0 : 0 ≤ Real.rpow (a.level : ℝ) (-epsilon) :=
          Real.rpow_nonneg (Nat.cast_nonneg a.level) (-epsilon)
        have hscaled := mul_le_mul_of_nonneg_right hcc0 hpow0
        linarith

/-- Koukoulopoulos Theorem 12.10, including its change from primitive
characters to arbitrary real nonprincipal characters.  The uniform constant
is harmlessly shrunk below `1 / 2`; this keeps the finite change-of-level Euler
factors in the already certified half-plane `Re s > 0`. -/
theorem GoldfeldPrimitiveAllButOneZeroFree.to_publishedSiegelRealZeroFreeRegion
    (hGoldfeld : GoldfeldPrimitiveAllButOneZeroFree) :
    MAPSiegelExceptionalEndpoint.PublishedSiegelRealZeroFreeRegion := by
  intro epsilon hepsilon
  rcases hGoldfeld.to_all_primitive epsilon hepsilon with
    ⟨c0, hc0, hprimitive⟩
  let c : ℝ := min c0 (1 / 2)
  have hc : 0 < c := lt_min hc0 (by norm_num)
  refine ⟨c, hc, ?_⟩
  intro q _ chi hchi hreal sigma hsigma
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  have hprimitiveNonprincipal : chi.primitiveCharacter ≠ 1 := by
    exact fun hp => hchi
      ((PrimitiveTruncatedExplicitFormulaBridge.primitiveCharacter_eq_one_iff chi).mp hp)
  have hprimitiveReal : chi.primitiveCharacter ^ 2 = 1 := by
    apply DirichletCharacter.changeLevel_injective chi.conductor_dvd_level
    rw [MonoidHom.map_pow, chi.changeLevel_primitiveCharacter, hreal,
      DirichletCharacter.changeLevel_one]
  let primitive : PrimitiveRealCharacter :=
    { level := chi.conductor
      level_ne_zero := chi.conductor_ne_zero
      chi := chi.primitiveCharacter
      primitive := chi.primitiveCharacter_isPrimitive
      nonprincipal := hprimitiveNonprincipal
      real := hprimitiveReal }
  have hconductorPos : 0 < (chi.conductor : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero chi.conductor_ne_zero
  have hqPos : 0 < (q : ℝ) := by
    exact_mod_cast NeZero.pos q
  have hconductorLe : (chi.conductor : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast ZeroDensityInterface.conductor_le_level chi
  have hnegative : -epsilon ≤ 0 := neg_nonpos.mpr hepsilon.le
  have hpowCompare :
      Real.rpow (q : ℝ) (-epsilon) ≤
        Real.rpow (chi.conductor : ℝ) (-epsilon) :=
    Real.rpow_le_rpow_of_nonpos hconductorPos hconductorLe hnegative
  have hcc0 : c ≤ c0 := min_le_left _ _
  have hpowNonneg : 0 ≤ Real.rpow (q : ℝ) (-epsilon) :=
    Real.rpow_nonneg hqPos.le _
  have hcScale :
      c * Real.rpow (q : ℝ) (-epsilon) ≤
        c0 * Real.rpow (chi.conductor : ℝ) (-epsilon) :=
    calc
      c * Real.rpow (q : ℝ) (-epsilon) ≤
          c0 * Real.rpow (q : ℝ) (-epsilon) :=
        mul_le_mul_of_nonneg_right hcc0 hpowNonneg
      _ ≤ c0 * Real.rpow (chi.conductor : ℝ) (-epsilon) :=
        mul_le_mul_of_nonneg_left hpowCompare hc0.le
  have hprimitiveRegion :
      1 - c0 * Real.rpow (chi.conductor : ℝ) (-epsilon) < sigma := by
    linarith
  have hprimitiveNZ :
      DirichletCharacter.LFunction chi.primitiveCharacter sigma ≠ 0 := by
    exact hprimitive primitive sigma hprimitiveRegion
  have hqOne : (1 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast (NeZero.one_le : 1 ≤ q)
  have hqPowLeOne : Real.rpow (q : ℝ) (-epsilon) ≤ 1 := by
    simpa using Real.rpow_le_rpow_of_exponent_le hqOne hnegative
  have hcHalf : c ≤ 1 / 2 := min_le_right _ _
  have hsigmaPos : 0 < sigma := by
    have hcPowLeHalf : c * Real.rpow (q : ℝ) (-epsilon) ≤ 1 / 2 :=
      calc
        c * Real.rpow (q : ℝ) (-epsilon) ≤ c * 1 :=
          mul_le_mul_of_nonneg_left hqPowLeOne hc.le
        _ ≤ 1 / 2 := by simpa using hcHalf
    linarith
  rw [PrimitiveEulerZeroTransport.LFunction_eq_primitive_mul_eulerCorrection
    chi (Or.inl hprimitiveNonprincipal)]
  exact mul_ne_zero hprimitiveNZ
    (PrimitiveEulerZeroTransport.eulerCorrection_ne_zero chi (by simpa using hsigmaPos))

end
end MAPGoldfeldSiegel

#print axioms MAPGoldfeldSiegel.PrimitiveRealCharacter.exists_real_zeroFree_radius
#print axioms MAPGoldfeldSiegel.GoldfeldPrimitiveAllButOneZeroFree.to_all_primitive
#print axioms MAPGoldfeldSiegel.GoldfeldPrimitiveAllButOneZeroFree.to_publishedSiegelRealZeroFreeRegion
