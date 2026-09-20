import NonprincipalTwistedMangoldtPsiCertified
import PrincipalKoukSiegelFormula

/-!
# Certified primitive twisted-Mangoldt source

This is the public join of the primitive nonprincipal contour argument and the
unique conductor-one principal contour argument.  The primary constructors are
premise-free: the principal branch uses the certified zeta `3-4-1` collar and
compactness.  The older Appendix-B-facing adapters are retained for comparison.
-/

namespace MAPPrimitiveTwistedMangoldtCertified

noncomputable section

theorem primitiveTwistedMangoldtPsi :
    ∀ A B : ℕ, ∃ C X0 : ℝ,
      0 < C ∧ 2 ≤ X0 ∧
        ∀ X : ℝ, X0 ≤ X →
        ∀ q : ℕ, 1 ≤ q →
          (q : ℝ) ≤ (Real.log X) ^ B →
        ∀ chi : DirichletCharacter ℂ q, chi.IsPrimitive →
        ∀ t : ℝ, t ∈ Set.Icc X (2 * X) →
          ‖APFoundation.twistedMangoldtSum chi (Finset.Icc 1 ⌊t⌋₊) -
              MAPSiegelWalfiszCharacterReduction.characterMain chi t‖ ≤
            C * X / (Real.log X) ^ A :=
  MAPPrimitiveTwistedMangoldtSourceSplit.primitiveTwistedMangoldtPsi_of_split
    MAPNonprincipalTwistedMangoldtPsiCertified.primitiveNonprincipalTwistedMangoldtPsi
    MAPPrincipalKoukSiegelFormula.primitivePrincipalOneTwistedMangoldtPsi

theorem uniformTwistedMangoldtPsi :
    MAPSiegelWalfiszCharacterReduction.UniformTwistedMangoldtPsi :=
  MAPPrimitiveTwistedMangoldtSourceSplit.uniformTwistedMangoldtPsi_of_split
    MAPNonprincipalTwistedMangoldtPsiCertified.primitiveNonprincipalTwistedMangoldtPsi
    MAPPrincipalKoukSiegelFormula.primitivePrincipalOneTwistedMangoldtPsi

theorem primitiveTwistedMangoldtPsi_of_appendixB
    (hKhale104 : MAPKhaleAppendixBSource.AppendixBCorollary104) :
    ∀ A B : ℕ, ∃ C X0 : ℝ,
      0 < C ∧ 2 ≤ X0 ∧
        ∀ X : ℝ, X0 ≤ X →
        ∀ q : ℕ, 1 ≤ q →
          (q : ℝ) ≤ (Real.log X) ^ B →
        ∀ chi : DirichletCharacter ℂ q, chi.IsPrimitive →
        ∀ t : ℝ, t ∈ Set.Icc X (2 * X) →
          ‖APFoundation.twistedMangoldtSum chi (Finset.Icc 1 ⌊t⌋₊) -
              MAPSiegelWalfiszCharacterReduction.characterMain chi t‖ ≤
            C * X / (Real.log X) ^ A :=
  MAPPrimitiveTwistedMangoldtSourceSplit.primitiveTwistedMangoldtPsi_of_split
    MAPNonprincipalTwistedMangoldtPsiCertified.primitiveNonprincipalTwistedMangoldtPsi
    (MAPPrincipalKoukSiegelFormula.primitivePrincipalOneTwistedMangoldtPsi_of_appendixB
      hKhale104)

theorem uniformTwistedMangoldtPsi_of_appendixB
    (hKhale104 : MAPKhaleAppendixBSource.AppendixBCorollary104) :
    MAPSiegelWalfiszCharacterReduction.UniformTwistedMangoldtPsi :=
  MAPPrimitiveTwistedMangoldtSourceSplit.uniformTwistedMangoldtPsi_of_split
    MAPNonprincipalTwistedMangoldtPsiCertified.primitiveNonprincipalTwistedMangoldtPsi
    (MAPPrincipalKoukSiegelFormula.primitivePrincipalOneTwistedMangoldtPsi_of_appendixB
      hKhale104)

end
end MAPPrimitiveTwistedMangoldtCertified

#print axioms MAPPrimitiveTwistedMangoldtCertified.primitiveTwistedMangoldtPsi_of_appendixB
#print axioms MAPPrimitiveTwistedMangoldtCertified.uniformTwistedMangoldtPsi_of_appendixB
#print axioms MAPPrimitiveTwistedMangoldtCertified.primitiveTwistedMangoldtPsi
#print axioms MAPPrimitiveTwistedMangoldtCertified.uniformTwistedMangoldtPsi
