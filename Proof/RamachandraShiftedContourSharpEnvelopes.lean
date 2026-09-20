import RamachandraFunctionalFactorSharpStrip
import RamachandraPrimitiveShiftedContourReduction

/-!
# Sharp pointwise envelopes on the two shifted Ramachandra contours

These are geometry adapters from the real-part sharp functional equation
factor to the literal `I₁` and `I₂` contour ordinates.
-/

namespace RamachandraShiftedContourSharpEnvelopes

open Complex
open RamachandraPrimitiveShiftedContourReduction
open BHPRamachandraMeanValueFromDyadicAFE

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The functional-equation argument on the literal long contour. -/
def longFunctionalPoint (sigma t v : ℝ) : ℂ :=
  ramachandraShiftedPoint sigma t +
    ((-(sigma + 1 / 4) : ℝ) : ℂ) + (v : ℂ) * I

theorem longFunctionalPoint_re (sigma t v : ℝ) :
    (longFunctionalPoint sigma t v).re = -(1 / 4 : ℝ) := by
  simp [longFunctionalPoint, ramachandraShiftedPoint]

theorem longFunctionalPoint_im (sigma t v : ℝ) :
    (longFunctionalPoint sigma t v).im = t + v := by
  simp [longFunctionalPoint, ramachandraShiftedPoint]

/-- Exact `3/4` conductor and height powers on the long contour. -/
theorem norm_functionalFactor_longFunctionalPoint_sharp_le
    (psi : DirichletCharacter ℂ d) (hprim : psi.IsPrimitive)
    {sigma t v : ℝ} (hne : t + v ≠ 0) :
    ‖ramachandraFunctionalFactor psi (longFunctionalPoint sigma t v)‖ ≤
      Real.rpow (d : ℝ) (3 / 4) *
        (4 * (Real.rpow 2000 (1 / 4) *
          Real.rpow (2000 * (1 + |t + v|)) (3 / 4))) := by
  have him : (longFunctionalPoint sigma t v).im = t + v :=
    longFunctionalPoint_im sigma t v
  have h := RamachandraFunctionalFactorSharpStrip.norm_ramachandraFunctionalFactor_sharp_le
    psi hprim (z := longFunctionalPoint sigma t v)
      (by rw [longFunctionalPoint_re]) (by rw [longFunctionalPoint_re]; norm_num)
      (by rw [him]; exact abs_pos.mpr hne)
  rw [longFunctionalPoint_re, him] at h
  norm_num at h ⊢
  exact h

/-- The functional-equation argument on the literal near contour. -/
def shortFunctionalPoint (X sigma t v : ℝ) : ℂ :=
  ramachandraShiftedPoint sigma t +
    ((-(Real.log X)⁻¹ : ℝ) : ℂ) + (v : ℂ) * I

theorem shortFunctionalPoint_re (X sigma t v : ℝ) :
    (shortFunctionalPoint X sigma t v).re = sigma - (Real.log X)⁻¹ := by
  simp [shortFunctionalPoint, ramachandraShiftedPoint]
  ring

theorem shortFunctionalPoint_im (X sigma t v : ℝ) :
    (shortFunctionalPoint X sigma t v).im = t + v := by
  simp [shortFunctionalPoint, ramachandraShiftedPoint]

/-- Exact near-line exponent, with the legal real-part conditions exposed
rather than hidden in an asymptotic convention. -/
theorem norm_functionalFactor_shortFunctionalPoint_sharp_le
    (psi : DirichletCharacter ℂ d) (hprim : psi.IsPrimitive)
    {X sigma t v : ℝ}
    (hlo : -(1 / 4 : ℝ) ≤ sigma - (Real.log X)⁻¹)
    (hhi : sigma - (Real.log X)⁻¹ ≤ 1 / 2)
    (hne : t + v ≠ 0) :
    ‖ramachandraFunctionalFactor psi (shortFunctionalPoint X sigma t v)‖ ≤
      Real.rpow (d : ℝ) (1 / 2 - (sigma - (Real.log X)⁻¹)) *
        (4 * (Real.rpow 2000 (1 / 2 + (sigma - (Real.log X)⁻¹)) *
          Real.rpow (2000 * (1 + |t + v|))
            (1 / 2 - (sigma - (Real.log X)⁻¹)))) := by
  have him : (shortFunctionalPoint X sigma t v).im = t + v :=
    shortFunctionalPoint_im X sigma t v
  have h := RamachandraFunctionalFactorSharpStrip.norm_ramachandraFunctionalFactor_sharp_le
    psi hprim (z := shortFunctionalPoint X sigma t v)
      (by rwa [shortFunctionalPoint_re]) (by rwa [shortFunctionalPoint_re])
      (by rw [him]; exact abs_pos.mpr hne)
  rw [shortFunctionalPoint_re, him] at h
  exact h

end
end RamachandraShiftedContourSharpEnvelopes

#print axioms RamachandraShiftedContourSharpEnvelopes.norm_functionalFactor_longFunctionalPoint_sharp_le
#print axioms RamachandraShiftedContourSharpEnvelopes.norm_functionalFactor_shortFunctionalPoint_sharp_le
