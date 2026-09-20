import HuxleyDirichletSmoothing
import FunctionalZeroTransport

/-!
# Ordinary primitive functional equation in Huxley's normalization

Huxley 1973 (3.12) applies the primitive functional equation to an ordinary
Dirichlet L-function, whereas Mathlib's strongest exact theorem is stated for
the completed L-function.  This module removes that deterministic connector
and keeps the root number, parity-dependent gamma factors, and conductor
power explicit.
-/

namespace MAPHuxleyPrimitiveFunctionalEquation

open Complex DirichletCharacter

noncomputable section

variable {q : ℕ} [NeZero q]

/-- Exact ordinary-L form of the primitive functional equation.  This is
the source identity used in Huxley (3.12), before any Stirling estimate is
applied to the displayed gamma-factor ratio. -/
theorem LFunction_one_sub_eq_huxleyFactor
    {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.LFunction χ (1 - s) =
      (q : ℂ) ^ (s - 1 / 2) * χ.rootNumber *
        DirichletCharacter.LFunction χ⁻¹ s * χ⁻¹.gammaFactor s /
          χ.gammaFactor (1 - s) := by
  have hq : q ≠ 1 := MAPFunctionalZeroTransport.level_ne_one hχ
  have hleft := DirichletCharacter.LFunction_eq_completed_div_gammaFactor
    χ (1 - s) (Or.inr hq)
  have hright := DirichletCharacter.LFunction_eq_completed_div_gammaFactor
    χ⁻¹ s (Or.inr hq)
  have hgammaInv : χ⁻¹.gammaFactor s ≠ 0 := by
    intro hzero
    have hinv :=
      MAPFunctionalZeroTransport.gammaFactor_inv_ne_zero_of_re_pos χ⁻¹ hs
    apply hinv
    rw [hzero, inv_zero]
  have hcompletedInv :
      DirichletCharacter.completedLFunction χ⁻¹ s =
        DirichletCharacter.LFunction χ⁻¹ s * χ⁻¹.gammaFactor s := by
    rw [hright]
    field_simp [hgammaInv]
  rw [hleft, hprim.completedLFunction_one_sub s, hcompletedInv]
  ring

end


end MAPHuxleyPrimitiveFunctionalEquation

#print axioms MAPHuxleyPrimitiveFunctionalEquation.LFunction_one_sub_eq_huxleyFactor
