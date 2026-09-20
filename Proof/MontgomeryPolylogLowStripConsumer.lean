import MontgomeryNeededLowStripBridge

/-! MAP needs arbitrary small power slack at polylogarithmic conductors.
It does not require the classical ninth logarithmic power at every conductor.
This consumer states exactly the weaker density input and splices the existing
principal high-strip estimate without changing the final zero-count target. -/

namespace MAPMontgomeryPolylogLowStripConsumer

open DirichletZeros ZeroDensityArithmetic ZeroDensityInterface

noncomputable section

def PolylogLowStripDensity : Prop :=
  ∀ K delta eta : ℝ, 0 < K → 0 < delta → 0 < eta →
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (T : ℝ) (Q : ℕ) (sigma : ℝ), T₀ ≤ T →
        (Q : ℝ) ≤ Real.rpow (Real.log T) K →
        1 / 2 + delta ≤ sigma → sigma ≤ 7 / 10 →
        ∀ (r : ℕ) [NeZero r] (chi : DirichletCharacter ℂ r),
          chi.IsPrimitive → r ≤ Q →
            (dirichletZeroCount chi sigma T : ℝ) ≤
              C * Real.rpow T (uniformCoeff * (1 - sigma) + eta)

theorem polylogLowStripDensity_of_classical
    (h : MAPMontgomeryNeededLowStrip.MontgomeryNeededLowStripSource) :
    PolylogLowStripDensity :=
  MAPMontgomeryNeededLowStrip.needed_montgomery_to_fixed_primitive_low_strip h

theorem fixedPrimitiveLowStripOrPrincipalDensity_of_polylog_and_zeta
    (hlow : PolylogLowStripDensity)
    (hZeta : ∀ eta : ℝ, 0 < eta →
      ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
        ∀ (T sigma : ℝ), T₀ ≤ T →
          7 / 10 ≤ sigma → sigma ≤ 4 / 5 →
            (dirichletZeroCount (1 : DirichletCharacter ℂ 1) sigma T : ℝ) ≤
              C * Real.rpow T
                (MAPGuthMaynard.densityCoeff * (1 - sigma) + eta)) :
    CGLCompactStripDensityConstructor.FixedPrimitiveLowStripOrPrincipalDensity := by
  intro K delta eta hK hdelta heta
  obtain ⟨Clow, Tlow, hClow, hTlow, hlow⟩ := hlow K delta eta hK hdelta heta
  obtain ⟨Czeta, Tzeta, hCzeta, hTzeta, hzeta⟩ := hZeta eta heta
  refine ⟨max Clow Czeta, max Tlow Tzeta,
    hClow.trans_le (le_max_left _ _), hTlow.trans (le_max_left _ _), ?_⟩
  intro T Q sigma hT hQ hsigmaLow hsigmaHigh r _inst chi hprim hrQ hcase
  have hTlow' : Tlow ≤ T := (le_max_left _ _).trans hT
  have hTzeta' : Tzeta ≤ T := (le_max_right _ _).trans hT
  have hTnonneg : 0 ≤ T := by linarith [hTlow.trans hTlow']
  have hpow : 0 ≤ Real.rpow T
      (MAPGuthMaynard.densityCoeff * (1 - sigma) + eta) :=
    Real.rpow_nonneg hTnonneg _
  by_cases hsplit : sigma ≤ 7 / 10
  · have hraw := hlow T Q sigma hTlow' hQ hsigmaLow hsplit r chi hprim hrQ
    simpa only [ZeroDensityArithmetic.uniformCoeff, MAPGuthMaynard.densityCoeff]
      using hraw.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpow)
  · have hchi : chi = 1 := hcase.resolve_left hsplit
    have hr : r = 1 := by
      rw [DirichletCharacter.isPrimitive_def, hchi,
        DirichletCharacter.conductor_one] at hprim
      exact hprim.symm
    subst r
    subst chi
    exact (hzeta T sigma hTzeta' (le_of_not_ge hsplit) hsigmaHigh).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hpow)

end
end MAPMontgomeryPolylogLowStripConsumer

#print axioms MAPMontgomeryPolylogLowStripConsumer.polylogLowStripDensity_of_classical
#print axioms MAPMontgomeryPolylogLowStripConsumer.fixedPrimitiveLowStripOrPrincipalDensity_of_polylog_and_zeta
