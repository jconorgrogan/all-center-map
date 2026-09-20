import KoukTheorem12ThreePrimitive

/-!
# Global-rectangle form of Koukoulopoulos, Theorem 12.3

The logarithmic-derivative proof naturally uses a centered unit window.  This
module transports an arbitrary divisor-backed zero into that window and back,
including equality of analytic multiplicities between the two rectangles.
-/

namespace MAPKoukTheorem12ThreeGlobal

open Complex Set DirichletZeros PrimitiveExplicitFormulaSpine MAPLocalZeroWindow MAPMellinDetectorLeaf
open MAPZeroFreeSiegelSpine MAPKoukTheorem12ThreePrimitive

noncomputable section

/-- A global divisor zero with `Re rho >= 1/2` belongs to its centered local
unit window. -/
theorem mem_centered_of_mem_zeroSupport
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {sigma T : ℝ} {rho : ℂ}
    (hrho : rho ∈ zeroSupport chi sigma T)
    (hre : 1 / 2 ≤ rho.re) :
    rho ∈ centeredUnitWindowSupport chi (1 / 2) rho.im := by
  have hglobalRect := mem_zeroRectangle_of_mem_zeroSupport chi sigma T hrho
  have hheight : |rho.im| ≤ windowHeight (rho.im - 1 / 2) := by
    unfold windowHeight
    rw [abs_le]
    constructor
    · linarith [neg_abs_le (rho.im - 1 / 2)]
    · linarith [le_abs_self (rho.im - 1 / 2)]
  have htargetRect :
      rho ∈ zeroRectangle (1 / 2) (windowHeight (rho.im - 1 / 2)) := by
    rw [zeroRectangle, Complex.mem_reProdIm]
    exact ⟨⟨hre, hglobalRect.1.2⟩, abs_le.mp hheight⟩
  have hzero := regularizedLFunction_eq_zero_of_mem_zeroSupport
    chi sigma T hrho
  rw [centeredUnitWindowSupport, closedUnitWindowSupport, Finset.mem_filter]
  refine ⟨(MAPAPZeroDensityCert.mem_zeroSupport_iff_eq_zero chi
    (1 / 2) (windowHeight (rho.im - 1 / 2)) htargetRect).mpr hzero, ?_⟩
  constructor <;> linarith

/-- The local and global divisor multiplicities of the transported zero are
identical. -/
theorem zeroMultiplicity_global_eq_centered
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {sigma T : ℝ} {rho : ℂ}
    (hrho : rho ∈ zeroSupport chi sigma T)
    (hre : 1 / 2 ≤ rho.re) :
    zeroMultiplicity chi sigma T rho =
      zeroMultiplicity chi (1 / 2)
        (windowHeight (rho.im - 1 / 2)) rho := by
  have hcenter := mem_centered_of_mem_zeroSupport chi hrho hre
  exact zeroMultiplicity_eq_of_mem_rectangles chi
    (mem_zeroRectangle_of_mem_zeroSupport chi sigma T hrho)
    (mem_zeroRectangle_of_mem_zeroSupport chi _ _
      (mem_zeroSupport_of_mem_centeredUnitWindowSupport chi hcenter))

/-- Global-rectangle primitive form of Theorem 12.3. -/
theorem primitive_global_nearOne_zero_is_exceptional
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive) (hchi : chi ≠ 1)
    {sigma T : ℝ} {rho : ℂ}
    (hrho : rho ∈ zeroSupport chi sigma T)
    (hre : 1 / 2 ≤ rho.re)
    (hnear : 1 - rho.re <
      1 / (100000000000 * Real.log (arithmeticScale q rho.im))) :
    chi ^ 2 = 1 ∧ rho.im = 0 ∧
      zeroMultiplicity chi sigma T rho = 1 := by
  have hcenter := mem_centered_of_mem_zeroSupport chi hrho hre
  obtain ⟨hsq, him, hsimple⟩ :=
    primitive_nearOne_zero_is_exceptional chi hprim hchi hcenter hnear
  refine ⟨hsq, him, ?_⟩
  rw [zeroMultiplicity_global_eq_centered chi hrho hre]
  exact hsimple

/-- Every nonexceptional global zero in the near-one half-strip has the
uniform reciprocal-logarithmic gap of Theorem 12.3. -/
theorem primitive_global_regular_zero_gap
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive) (hchi : chi ≠ 1)
    {sigma T : ℝ} {rho : ℂ}
    (hrho : rho ∈ zeroSupport chi sigma T)
    (hre : 1 / 2 ≤ rho.re)
    (hregular : ¬ (chi ^ 2 = 1 ∧ rho.im = 0 ∧
      zeroMultiplicity chi sigma T rho = 1)) :
    1 / (100000000000 * Real.log (arithmeticScale q rho.im)) ≤
      1 - rho.re := by
  by_contra hnot
  have hnear : 1 - rho.re <
      1 / (100000000000 * Real.log (arithmeticScale q rho.im)) :=
    lt_of_not_ge hnot
  exact hregular
    (primitive_global_nearOne_zero_is_exceptional chi hprim hchi
      hrho hre hnear)

#print axioms MAPKoukTheorem12ThreeGlobal.mem_centered_of_mem_zeroSupport
#print axioms MAPKoukTheorem12ThreeGlobal.primitive_global_nearOne_zero_is_exceptional
#print axioms MAPKoukTheorem12ThreeGlobal.primitive_global_regular_zero_gap

end

end MAPKoukTheorem12ThreeGlobal
