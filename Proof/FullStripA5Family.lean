import FunctionalZeroTransport
import TrivialZeroEndpoint

/-!
# Full-strip local zero count from the upper-half A.5 theorem

The literal zero field uses `0 ≤ Re ρ ≤ 1`, while Appendix A.5 was certified
on `Re ρ ≥ 1/2`.  This file splits a unit window into upper, strict-lower,
and endpoint sectors.  The lower sector is reflected into the inverse
character by the functional equation, preserving multiplicity; the endpoint
sector contributes at most the one simple zero at `0`.
-/

namespace MAPFullStripA5Family

open Complex Set
open DirichletZeros MAPLocalZeroWindow
open scoped BigOperators

noncomputable section

variable {q : ℕ} [NeZero q]

private def fullWindowSupport (χ : DirichletCharacter ℂ q) (t : ℝ) : Finset ℂ :=
  closedUnitWindowSupport χ 0 t

private def upperWindowSupport (χ : DirichletCharacter ℂ q) (t : ℝ) : Finset ℂ :=
  (fullWindowSupport χ t).filter fun ρ => 1 / 2 ≤ ρ.re

private def strictLowerWindowSupport (χ : DirichletCharacter ℂ q) (t : ℝ) : Finset ℂ :=
  (fullWindowSupport χ t).filter fun ρ => 0 < ρ.re ∧ ρ.re < 1 / 2

private def endpointWindowSupport (χ : DirichletCharacter ℂ q) (t : ℝ) : Finset ℂ :=
  (fullWindowSupport χ t).filter fun ρ => ρ.re = 0

private theorem mem_fullWindowSupport_rect
    (χ : DirichletCharacter ℂ q) {t : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ fullWindowSupport χ t) :
    ρ ∈ zeroRectangle 0 (windowHeight t) := by
  exact closedUnitWindowSupport_mem_rectangle χ hρ

private theorem fullWindowSupport_re_nonneg
    (χ : DirichletCharacter ℂ q) {t : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ fullWindowSupport χ t) : 0 ≤ ρ.re := by
  exact (Complex.mem_reProdIm.mp (mem_fullWindowSupport_rect χ hρ)).1.1

private theorem upperWindowSupport_subset
    (χ : DirichletCharacter ℂ q) (t : ℝ) :
    upperWindowSupport χ t ⊆ closedUnitWindowSupport χ (1 / 2) t := by
  intro ρ hρ
  rw [upperWindowSupport, Finset.mem_filter] at hρ
  rw [closedUnitWindowSupport, Finset.mem_filter]
  have hsource : ρ ∈ closedUnitWindowSupport χ 0 t := hρ.1
  have hzero := regularizedLFunction_eq_zero_of_mem_zeroSupport χ 0
    (windowHeight t) (Finset.mem_filter.mp hsource).1
  have hrect0 := closedUnitWindowSupport_mem_rectangle χ hsource
  have hrectHalf : ρ ∈ zeroRectangle (1 / 2) (windowHeight t) := by
    rw [zeroRectangle, Complex.mem_reProdIm] at hrect0 ⊢
    exact ⟨⟨hρ.2, hrect0.1.2⟩, hrect0.2⟩
  refine ⟨(MAPAPZeroDensityCert.mem_zeroSupport_iff_eq_zero χ
    (1 / 2) (windowHeight t) hrectHalf).mpr hzero, ?_⟩
  exact (Finset.mem_filter.mp hsource).2

private theorem upperWindowMultiplicity_eq
    (χ : DirichletCharacter ℂ q) {t : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ upperWindowSupport χ t) :
    zeroMultiplicity χ 0 (windowHeight t) ρ =
      zeroMultiplicity χ (1 / 2) (windowHeight t) ρ := by
  have hsource := (Finset.mem_filter.mp hρ).1
  have htarget := upperWindowSupport_subset χ t hρ
  exact MAPMellinDetectorLeaf.zeroMultiplicity_eq_of_mem_rectangles χ
    (closedUnitWindowSupport_mem_rectangle χ hsource)
    (closedUnitWindowSupport_mem_rectangle χ htarget)

private theorem upperWindow_sum_le
    (χ : DirichletCharacter ℂ q) (t : ℝ) :
    ∑ ρ ∈ upperWindowSupport χ t,
        zeroMultiplicity χ 0 (windowHeight t) ρ ≤
      closedUnitWindowCount χ (1 / 2) t := by
  unfold closedUnitWindowCount
  calc
    ∑ ρ ∈ upperWindowSupport χ t,
        zeroMultiplicity χ 0 (windowHeight t) ρ =
      ∑ ρ ∈ upperWindowSupport χ t,
        zeroMultiplicity χ (1 / 2) (windowHeight t) ρ := by
      apply Finset.sum_congr rfl
      intro ρ hρ
      exact upperWindowMultiplicity_eq χ hρ
    _ ≤ ∑ ρ ∈ closedUnitWindowSupport χ (1 / 2) t,
        zeroMultiplicity χ (1 / 2) (windowHeight t) ρ :=
      Finset.sum_le_sum_of_subset (upperWindowSupport_subset χ t)

private theorem endpointWindowSupport_subset_zero
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    (t : ℝ) : endpointWindowSupport χ t ⊆ {0} := by
  intro ρ hρ
  rw [endpointWindowSupport, Finset.mem_filter] at hρ
  rw [Finset.mem_singleton]
  apply Complex.ext
  · simpa using hρ.2
  · by_contra him
    have hne := MAPTrivialZeroEndpoint.regularizedLFunction_ne_zero_of_re_zero_of_im_ne_zero
      χ hprim hχ hρ.2 him
    have hzero := regularizedLFunction_eq_zero_of_mem_zeroSupport χ 0
      (windowHeight t) (Finset.mem_filter.mp hρ.1).1
    exact hne hzero

private theorem endpointWindow_sum_le_one
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    (t : ℝ) :
    ∑ ρ ∈ endpointWindowSupport χ t,
        zeroMultiplicity χ 0 (windowHeight t) ρ ≤ 1 := by
  calc
    ∑ ρ ∈ endpointWindowSupport χ t,
        zeroMultiplicity χ 0 (windowHeight t) ρ ≤
      ∑ ρ ∈ ({0} : Finset ℂ),
        zeroMultiplicity χ 0 (windowHeight t) ρ :=
      Finset.sum_le_sum_of_subset (endpointWindowSupport_subset_zero χ hprim hχ t)
    _ = zeroMultiplicity χ 0 (windowHeight t) 0 := by simp
    _ ≤ 1 := by
      by_cases hmem : (0 : ℂ) ∈ zeroSupport χ 0 (windowHeight t)
      · exact MAPTrivialZeroEndpoint.zeroMultiplicity_zero_le_one χ hprim hχ hmem
      · have hmem' := hmem
        rw [zeroSupport_mem_iff] at hmem'
        have hz : zeroDivisor χ 0 (windowHeight t) 0 = 0 := by
          simpa using hmem'
        simp [zeroMultiplicity, hz]

private theorem strictLower_reflect_mem
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    {t : ℝ} {ρ : ℂ} (hρ : ρ ∈ strictLowerWindowSupport χ t) :
    1 - ρ ∈ closedUnitWindowSupport χ⁻¹ (1 / 2) (-t - 1) := by
  rw [strictLowerWindowSupport, Finset.mem_filter] at hρ
  let T' : ℝ := windowHeight (-t - 1)
  have hsource := hρ.1
  have hzero := regularizedLFunction_eq_zero_of_mem_zeroSupport χ 0
    (windowHeight t) (Finset.mem_filter.mp hsource).1
  have hreflectZero := MAPFunctionalZeroTransport.regularizedLFunction_one_sub_eq_zero
    hprim hχ hρ.2.1 hρ.2.2 hzero
  have hsourceRect := closedUnitWindowSupport_mem_rectangle χ hsource
  have himSource := (Finset.mem_filter.mp hsource).2
  have hreflectRect : 1 - ρ ∈ zeroRectangle (1 / 2) T' := by
    rw [zeroRectangle, Complex.mem_reProdIm]
    constructor
    · constructor <;> simp <;> linarith
    · dsimp [T', windowHeight]
      simp only [Complex.sub_im, Complex.one_im, zero_sub]
      rw [Set.mem_Icc]
      constructor
      · have habs : -(|-t - 1| + 1) ≤ -ρ.im := by
          have := neg_le_neg himSource.2
          have habs' : t ≤ |-t - 1| := by
            calc t ≤ |t + 1| := by linarith [le_abs_self (t + 1)]
                 _ = |-t - 1| := by
                   rw [show -t - 1 = -(t + 1) by ring, abs_neg]
          linarith
        exact habs
      · have habs : -ρ.im ≤ |-t - 1| + 1 := by
          have := neg_le_neg himSource.1
          have habs' : -t ≤ |-t - 1| + 1 := by
            calc -t = (-t - 1) + 1 := by ring
                 _ ≤ |-t - 1| + 1 := by gcongr; exact le_abs_self _
          linarith
        exact habs
  rw [closedUnitWindowSupport, Finset.mem_filter]
  refine ⟨(MAPAPZeroDensityCert.mem_zeroSupport_iff_eq_zero χ⁻¹
    (1 / 2) T' hreflectRect).mpr hreflectZero, ?_⟩
  simp only [Complex.sub_im, Complex.one_im, zero_sub]
  constructor <;> linarith

private theorem strictLower_reflect_multiplicity_eq
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    {t : ℝ} {ρ : ℂ} (hρ : ρ ∈ strictLowerWindowSupport χ t) :
    zeroMultiplicity χ 0 (windowHeight t) ρ =
      zeroMultiplicity χ⁻¹ (1 / 2) (windowHeight (-t - 1)) (1 - ρ) := by
  have hρstrict := hρ
  rw [strictLowerWindowSupport, Finset.mem_filter] at hρ
  have hsource := hρ.1
  have hold := MAPFunctionalZeroTransport.zeroMultiplicity_one_sub
    hprim hχ (Finset.mem_filter.mp hsource).1 hρ.2.1 hρ.2.2
  have hreflectOld := MAPFunctionalZeroTransport.one_sub_mem_upper_zeroSupport
    hprim hχ (Finset.mem_filter.mp hsource).1 hρ.2.1 hρ.2.2
  have hreflectNew := strictLower_reflect_mem χ hprim hχ hρstrict
  exact hold.trans (MAPMellinDetectorLeaf.zeroMultiplicity_eq_of_mem_rectangles χ⁻¹
    (PrimitiveExplicitFormulaSpine.mem_zeroRectangle_of_mem_zeroSupport χ⁻¹
      (1 / 2) (windowHeight t) hreflectOld)
    (closedUnitWindowSupport_mem_rectangle χ⁻¹ hreflectNew))

private theorem one_sub_injective : Function.Injective (fun ρ : ℂ => 1 - ρ) := by
  exact sub_right_injective

private theorem strictLowerWindow_sum_le
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    (t : ℝ) :
    ∑ ρ ∈ strictLowerWindowSupport χ t,
        zeroMultiplicity χ 0 (windowHeight t) ρ ≤
      closedUnitWindowCount χ⁻¹ (1 / 2) (-t - 1) := by
  let S := strictLowerWindowSupport χ t
  let R : ℂ → ℂ := fun ρ => 1 - ρ
  have hsub : S.image R ⊆ closedUnitWindowSupport χ⁻¹ (1 / 2) (-t - 1) := by
    rw [Finset.image_subset_iff]
    intro ρ hρ
    exact strictLower_reflect_mem χ hprim hχ hρ
  unfold closedUnitWindowCount
  calc
    ∑ ρ ∈ S, zeroMultiplicity χ 0 (windowHeight t) ρ =
      ∑ z ∈ S.image R,
        zeroMultiplicity χ⁻¹ (1 / 2) (windowHeight (-t - 1)) z := by
      rw [Finset.sum_image (one_sub_injective.injOn)]
      apply Finset.sum_congr rfl
      intro ρ hρ
      exact strictLower_reflect_multiplicity_eq χ hprim hχ hρ
    _ ≤ ∑ z ∈ closedUnitWindowSupport χ⁻¹ (1 / 2) (-t - 1),
        zeroMultiplicity χ⁻¹ (1 / 2) (windowHeight (-t - 1)) z :=
      Finset.sum_le_sum_of_subset hsub

/-- Exact structural full-strip count: one endpoint zero, one upper A.5
window for `χ`, and one reflected upper window for `χ⁻¹`. -/
theorem fullStrip_closedUnitWindowCount_le
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    (t : ℝ) :
    closedUnitWindowCount χ 0 t ≤
      1 + closedUnitWindowCount χ (1 / 2) t +
        closedUnitWindowCount χ⁻¹ (1 / 2) (-t - 1) := by
  let S := fullWindowSupport χ t
  let E := endpointWindowSupport χ t
  let L := strictLowerWindowSupport χ t
  let U := upperWindowSupport χ t
  have hpartition : E ∪ L ∪ U = S := by
    ext ρ
    simp only [E, L, U, S, endpointWindowSupport,
      strictLowerWindowSupport, upperWindowSupport, fullWindowSupport,
      Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ((h | h) | h)
      · exact h.1
      · exact h.1
      · exact h.1
    · intro hρ
      have hre0 := fullWindowSupport_re_nonneg χ hρ
      by_cases hhalf : 1 / 2 ≤ ρ.re
      · exact Or.inr ⟨hρ, hhalf⟩
      · by_cases hz : ρ.re = 0
        · exact Or.inl (Or.inl ⟨hρ, hz⟩)
        · exact Or.inl (Or.inr ⟨hρ, lt_of_le_of_ne hre0 (Ne.symm hz),
            lt_of_not_ge hhalf⟩)
  have hdisjEL : Disjoint E L := by
    refine Finset.disjoint_left.mpr ?_
    intro ρ hE hL
    have hE0 := (Finset.mem_filter.mp hE).2
    have hL0 := (Finset.mem_filter.mp hL).2.1
    linarith
  have hdisjELU : Disjoint (E ∪ L) U := by
    refine Finset.disjoint_left.mpr ?_
    intro ρ hEL hU
    have hUhalf := (Finset.mem_filter.mp hU).2
    rcases Finset.mem_union.mp hEL with hE | hL
    · have hE0 := (Finset.mem_filter.mp hE).2
      linarith
    · have hLhalf := (Finset.mem_filter.mp hL).2.2
      linarith
  unfold closedUnitWindowCount
  change (∑ ρ ∈ S, zeroMultiplicity χ 0 (windowHeight t) ρ) ≤ _
  rw [← hpartition, Finset.sum_union hdisjELU, Finset.sum_union hdisjEL]
  have hE := endpointWindow_sum_le_one χ hprim hχ t
  have hL := strictLowerWindow_sum_le χ hprim hχ t
  have hU := upperWindow_sum_le χ t
  unfold closedUnitWindowCount at hL hU
  change (∑ ρ ∈ E, zeroMultiplicity χ 0 (windowHeight t) ρ) ≤ 1 at hE
  change (∑ ρ ∈ L, zeroMultiplicity χ 0 (windowHeight t) ρ) ≤
    (∑ z ∈ closedUnitWindowSupport χ⁻¹ (1 / 2) (-t - 1),
      zeroMultiplicity χ⁻¹ (1 / 2) (windowHeight (-t - 1)) z) at hL
  change (∑ ρ ∈ U, zeroMultiplicity χ 0 (windowHeight t) ρ) ≤
    (∑ z ∈ closedUnitWindowSupport χ (1 / 2) t,
      zeroMultiplicity χ (1 / 2) (windowHeight t) z) at hU
  omega

/-- Numerical full-strip A.5 consequence, retaining the two exact arithmetic
scales needed before the later global `q,T` simplification. -/
theorem certifiedFullStripClosedLocalZeroCount
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    (t : ℝ) :
    (closedUnitWindowCount χ 0 t : ℝ) ≤
      1 + 153 * Real.log (arithmeticScale q t) +
        153 * Real.log (arithmeticScale q (-t - 1)) := by
  have hstruct := fullStrip_closedUnitWindowCount_le χ hprim hχ t
  have hu :=
    MAPAppendixA5ClosedLocalZeroCount.certifiedAppendixA5ClosedLocalZeroCount
      χ hprim hχ (t := t) (by norm_num : (1 / 2 : ℝ) ≤ 1 / 2)
  have hlinv := MAPFunctionalZeroTransport.isPrimitive_inv hprim
  have hinv := MAPFunctionalZeroTransport.inverse_ne_one hχ
  have hl :=
    MAPAppendixA5ClosedLocalZeroCount.certifiedAppendixA5ClosedLocalZeroCount
      χ⁻¹ hlinv hinv (t := -t - 1) (by norm_num : (1 / 2 : ℝ) ≤ 1 / 2)
  exact_mod_cast (show
    (closedUnitWindowCount χ 0 t : ℝ) ≤
      1 + (closedUnitWindowCount χ (1 / 2) t : ℝ) +
        (closedUnitWindowCount χ⁻¹ (1 / 2) (-t - 1) : ℝ) by
      exact_mod_cast hstruct) |>.trans (by linarith)

#print axioms fullStrip_closedUnitWindowCount_le
#print axioms certifiedFullStripClosedLocalZeroCount

end
end MAPFullStripA5Family
