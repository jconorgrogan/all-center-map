import LocalZeroCountSlice

/-!
# Appendix A.5 as the local fiber cap in Jutila's collar

Jutila's Lemma 8 is used only to bound the number of zeros belonging to one
character and one short ordinate box.  In the collar used by MAP that box has
length at most one.  The already certified Appendix A.5 unit-window theorem
therefore gives a stronger bound, with analytic multiplicity retained.

This file records the exact subset argument.  It does not assert Jutila's
global density theorem or any detector estimate.
-/

namespace MAPJutilaCollarA5FiberCap

open Complex
open scoped BigOperators
open DirichletZeros MAPLocalZeroWindow MAPPaperWindowVKBypass

noncomputable section

variable {q : ℕ} [NeZero q]

/-- A Jutila-style short box inside the global zero rectangle.  The optional
right edge in the real direction only makes this a smaller subset of the
Appendix A.5 unit window. -/
def collarThinBoxSupport (chi : DirichletCharacter ℂ q)
    (alpha T t width : ℝ) : Finset ℂ :=
  (zeroSupport chi alpha T).filter fun rho =>
    rho.re ≤ alpha + width ∧ t ≤ rho.im ∧ rho.im ≤ t + width

/-- The literal clipped ordinate box in Jutila (1977), equation (3.1).
The real-part condition `alpha ≤ re rho ≤ 1` is already part of
`zeroSupport chi alpha T`; only the clipped interval
`max (-T) (k*Delta) ≤ im rho ≤ min T ((k+1)*Delta)` is added here. -/
def jutilaSourceBoxSupport (chi : DirichletCharacter ℂ q)
    (alpha T Delta : ℝ) (k : ℤ) : Finset ℂ :=
  (zeroSupport chi alpha T).filter fun rho =>
    max (-T) ((k : ℝ) * Delta) ≤ rho.im ∧
      rho.im ≤ min T (((k : ℝ) + 1) * Delta)

/-- Jutila's exact source box is contained in the certified Appendix A.5
unit window based at `k*Delta`.  This is the mechanical source-box
identification that replaces the local-count use of Linnik's Lemma 8. -/
theorem jutilaSourceBoxSupport_subset_globalUnitWindow
    (chi : DirichletCharacter ℂ q) {alpha T Delta : ℝ} {k : ℤ}
    (hDelta0 : 0 ≤ Delta) (hDelta1 : Delta ≤ 1) :
    jutilaSourceBoxSupport chi alpha T Delta k ⊆
      globalUnitWindowSupport chi alpha T ((k : ℝ) * Delta) := by
  intro rho hrho
  rw [jutilaSourceBoxSupport, Finset.mem_filter] at hrho
  rw [globalUnitWindowSupport, Finset.mem_filter]
  refine ⟨hrho.1, ?_, ?_⟩
  · exact (le_max_right (-T) ((k : ℝ) * Delta)).trans hrho.2.1
  · have hupper : rho.im ≤ ((k : ℝ) + 1) * Delta :=
      hrho.2.2.trans (min_le_right _ _)
    have hstep : ((k : ℝ) + 1) * Delta ≤ (k : ℝ) * Delta + 1 := by
      nlinarith
    exact hupper.trans hstep

/-- Every nonnegative box of ordinate length at most one lies in the closed
unit window with the same left endpoint. -/
theorem collarThinBoxSupport_subset_globalUnitWindow
    (chi : DirichletCharacter ℂ q) {alpha T t width : ℝ}
    (hwidth0 : 0 ≤ width) (hwidth1 : width ≤ 1) :
    collarThinBoxSupport chi alpha T t width ⊆
      globalUnitWindowSupport chi alpha T t := by
  intro rho hrho
  rw [collarThinBoxSupport, Finset.mem_filter] at hrho
  rw [globalUnitWindowSupport, Finset.mem_filter]
  exact ⟨hrho.1, hrho.2.2.1, hrho.2.2.2.trans (by linarith)⟩

/-- The multiplicity-weighted content of one collar box is bounded by the
certified A.5 logarithm.  This is the exact analytic replacement for the
local-zero-count role of Jutila's Lemma 8. -/
theorem collarThinBoxMultiplicity_le_log
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {alpha T t width : ℝ} (halpha : 1 / 2 ≤ alpha)
    (hwidth0 : 0 ≤ width) (hwidth1 : width ≤ 1) :
    (∑ rho ∈ collarThinBoxSupport chi alpha T t width,
        (zeroMultiplicity chi alpha T rho : ℝ)) ≤
      153 * Real.log (arithmeticScale q t) := by
  calc
    (∑ rho ∈ collarThinBoxSupport chi alpha T t width,
        (zeroMultiplicity chi alpha T rho : ℝ)) ≤
      ∑ rho ∈ globalUnitWindowSupport chi alpha T t,
        (zeroMultiplicity chi alpha T rho : ℝ) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
            (collarThinBoxSupport_subset_globalUnitWindow chi hwidth0 hwidth1)
          intro _ _ _
          exact Nat.cast_nonneg _
    _ ≤ 153 * Real.log (arithmeticScale q t) :=
      globalUnitWindowCount_le_log chi hchi halpha

/-- The literal equation-(3.1) box has the same multiplicity-weighted A.5
cap.  No invocation of Linnik's Lemma 8 remains in this source step. -/
theorem jutilaSourceBoxMultiplicity_le_log
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {alpha T Delta : ℝ} {k : ℤ} (halpha : 1 / 2 ≤ alpha)
    (hDelta0 : 0 ≤ Delta) (hDelta1 : Delta ≤ 1) :
    (∑ rho ∈ jutilaSourceBoxSupport chi alpha T Delta k,
        (zeroMultiplicity chi alpha T rho : ℝ)) ≤
      153 * Real.log (arithmeticScale q ((k : ℝ) * Delta)) := by
  calc
    (∑ rho ∈ jutilaSourceBoxSupport chi alpha T Delta k,
        (zeroMultiplicity chi alpha T rho : ℝ)) ≤
      ∑ rho ∈ globalUnitWindowSupport chi alpha T ((k : ℝ) * Delta),
        (zeroMultiplicity chi alpha T rho : ℝ) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
            (jutilaSourceBoxSupport_subset_globalUnitWindow chi hDelta0 hDelta1)
          intro _ _ _
          exact Nat.cast_nonneg _
    _ ≤ 153 * Real.log (arithmeticScale q ((k : ℝ) * Delta)) :=
      globalUnitWindowCount_le_log chi hchi halpha

/-- Natural cap convenient for the finite fiber-compression theorem. -/
def collarA5NatCap (q : ℕ) (t : ℝ) : ℕ :=
  ⌈max 0 (153 * Real.log (arithmeticScale q t))⌉₊

theorem collarThinBoxMultiplicity_le_natCap
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {alpha T t width : ℝ} (halpha : 1 / 2 ≤ alpha)
    (hwidth0 : 0 ≤ width) (hwidth1 : width ≤ 1) :
    ∑ rho ∈ collarThinBoxSupport chi alpha T t width,
        zeroMultiplicity chi alpha T rho ≤ collarA5NatCap q t := by
  have hreal := collarThinBoxMultiplicity_le_log chi hchi
    (T := T) (t := t) halpha hwidth0 hwidth1
  have hmax :
      (∑ rho ∈ collarThinBoxSupport chi alpha T t width,
          (zeroMultiplicity chi alpha T rho : ℝ)) ≤
        max 0 (153 * Real.log (arithmeticScale q t)) :=
    hreal.trans (le_max_right _ _)
  have hceil :
      max 0 (153 * Real.log (arithmeticScale q t)) ≤
        (collarA5NatCap q t : ℝ) := Nat.le_ceil _
  exact_mod_cast hmax.trans hceil

/-- Natural-cardinality cap for the literal equation-(3.1) source box. -/
theorem jutilaSourceBoxMultiplicity_le_natCap
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {alpha T Delta : ℝ} {k : ℤ} (halpha : 1 / 2 ≤ alpha)
    (hDelta0 : 0 ≤ Delta) (hDelta1 : Delta ≤ 1) :
    ∑ rho ∈ jutilaSourceBoxSupport chi alpha T Delta k,
        zeroMultiplicity chi alpha T rho ≤
      collarA5NatCap q ((k : ℝ) * Delta) := by
  have hreal := jutilaSourceBoxMultiplicity_le_log chi hchi
    (T := T) (Delta := Delta) (k := k) halpha hDelta0 hDelta1
  have hmax :
      (∑ rho ∈ jutilaSourceBoxSupport chi alpha T Delta k,
          (zeroMultiplicity chi alpha T rho : ℝ)) ≤
        max 0 (153 * Real.log
          (arithmeticScale q ((k : ℝ) * Delta))) :=
    hreal.trans (le_max_right _ _)
  have hceil :
      max 0 (153 * Real.log
          (arithmeticScale q ((k : ℝ) * Delta))) ≤
        (collarA5NatCap q ((k : ℝ) * Delta) : ℝ) := Nat.le_ceil _
  exact_mod_cast hmax.trans hceil

end

end MAPJutilaCollarA5FiberCap

#print axioms MAPJutilaCollarA5FiberCap.collarThinBoxSupport_subset_globalUnitWindow
#print axioms MAPJutilaCollarA5FiberCap.collarThinBoxMultiplicity_le_log
#print axioms MAPJutilaCollarA5FiberCap.collarThinBoxMultiplicity_le_natCap
#print axioms MAPJutilaCollarA5FiberCap.jutilaSourceBoxSupport_subset_globalUnitWindow
#print axioms MAPJutilaCollarA5FiberCap.jutilaSourceBoxMultiplicity_le_log
#print axioms MAPJutilaCollarA5FiberCap.jutilaSourceBoxMultiplicity_le_natCap
