import PrincipalFullStripA5Source
import PrincipalZetaTransport

namespace MAPPrincipalZetaFullStrip

open Complex Set
open DirichletZeros MAPLocalZeroWindow
open scoped BigOperators

noncomputable section

local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩
local notation "χ₁" => (1 : DirichletCharacter ℂ 1)

private def fullWindowSupport (t : ℝ) : Finset ℂ :=
  closedUnitWindowSupport χ₁ 0 t

private def upperWindowSupport (t : ℝ) : Finset ℂ :=
  (fullWindowSupport t).filter fun ρ => 1 / 2 ≤ ρ.re

private def strictLowerWindowSupport (t : ℝ) : Finset ℂ :=
  (fullWindowSupport t).filter fun ρ => 0 < ρ.re ∧ ρ.re < 1 / 2

private def endpointWindowSupport (t : ℝ) : Finset ℂ :=
  (fullWindowSupport t).filter fun ρ => ρ.re = 0

private theorem mem_fullWindowSupport_rect {t : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ fullWindowSupport t) :
    ρ ∈ zeroRectangle 0 (windowHeight t) :=
  closedUnitWindowSupport_mem_rectangle χ₁ hρ

private theorem fullWindowSupport_re_nonneg {t : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ fullWindowSupport t) : 0 ≤ ρ.re :=
  (Complex.mem_reProdIm.mp (mem_fullWindowSupport_rect hρ)).1.1

private theorem upperWindowSupport_subset (t : ℝ) :
    upperWindowSupport t ⊆ closedUnitWindowSupport χ₁ (1 / 2) t := by
  intro ρ hρ
  rw [upperWindowSupport, Finset.mem_filter] at hρ
  rw [closedUnitWindowSupport, Finset.mem_filter]
  have hsource : ρ ∈ closedUnitWindowSupport χ₁ 0 t := hρ.1
  have hzero := regularizedLFunction_eq_zero_of_mem_zeroSupport χ₁ 0
    (windowHeight t) (Finset.mem_filter.mp hsource).1
  have hrect0 := closedUnitWindowSupport_mem_rectangle χ₁ hsource
  have hrectHalf : ρ ∈ zeroRectangle (1 / 2) (windowHeight t) := by
    rw [zeroRectangle, Complex.mem_reProdIm] at hrect0 ⊢
    exact ⟨⟨hρ.2, hrect0.1.2⟩, hrect0.2⟩
  refine ⟨(MAPAPZeroDensityCert.mem_zeroSupport_iff_eq_zero χ₁
    (1 / 2) (windowHeight t) hrectHalf).mpr hzero, ?_⟩
  exact (Finset.mem_filter.mp hsource).2

private theorem upperWindowMultiplicity_eq {t : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ upperWindowSupport t) :
    zeroMultiplicity χ₁ 0 (windowHeight t) ρ =
      zeroMultiplicity χ₁ (1 / 2) (windowHeight t) ρ := by
  have hsource := (Finset.mem_filter.mp hρ).1
  have htarget := upperWindowSupport_subset t hρ
  exact MAPMellinDetectorLeaf.zeroMultiplicity_eq_of_mem_rectangles χ₁
    (closedUnitWindowSupport_mem_rectangle χ₁ hsource)
    (closedUnitWindowSupport_mem_rectangle χ₁ htarget)

private theorem upperWindow_sum_le (t : ℝ) :
    ∑ ρ ∈ upperWindowSupport t,
        zeroMultiplicity χ₁ 0 (windowHeight t) ρ ≤
      closedUnitWindowCount χ₁ (1 / 2) t := by
  unfold closedUnitWindowCount
  calc
    ∑ ρ ∈ upperWindowSupport t,
        zeroMultiplicity χ₁ 0 (windowHeight t) ρ =
      ∑ ρ ∈ upperWindowSupport t,
        zeroMultiplicity χ₁ (1 / 2) (windowHeight t) ρ := by
      apply Finset.sum_congr rfl
      intro ρ hρ
      exact upperWindowMultiplicity_eq hρ
    _ ≤ ∑ ρ ∈ closedUnitWindowSupport χ₁ (1 / 2) t,
        zeroMultiplicity χ₁ (1 / 2) (windowHeight t) ρ :=
      Finset.sum_le_sum_of_subset (upperWindowSupport_subset t)

private theorem endpointWindowSupport_eq_empty (t : ℝ) :
    endpointWindowSupport t = ∅ := by
  apply Finset.not_nonempty_iff_eq_empty.mp
  intro hne
  obtain ⟨ρ, hρ⟩ := hne
  rw [endpointWindowSupport, Finset.mem_filter] at hρ
  have hzero := regularizedLFunction_eq_zero_of_mem_zeroSupport χ₁ 0
    (windowHeight t) (Finset.mem_filter.mp hρ.1).1
  exact MAPPrincipalZetaTransport.principalRegularized_ne_zero_of_re_zero hρ.2
    (by simpa [MAPPrincipalZetaTransport.regularized_principal_eq] using hzero)

private theorem strictLower_reflect_mem {t : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ strictLowerWindowSupport t) :
    1 - ρ ∈ closedUnitWindowSupport χ₁ (1 / 2) (-t - 1) := by
  rw [strictLowerWindowSupport, Finset.mem_filter] at hρ
  let T' : ℝ := windowHeight (-t - 1)
  have hsource := hρ.1
  have hreflectZero := MAPPrincipalZetaTransport.one_sub_mem_upper_zeroSupport
    (Finset.mem_filter.mp hsource).1 hρ.2.1 hρ.2.2
  have hsourceRect := closedUnitWindowSupport_mem_rectangle χ₁ hsource
  have himSource := (Finset.mem_filter.mp hsource).2
  have hreflectRect : 1 - ρ ∈ zeroRectangle (1 / 2) T' := by
    rw [zeroRectangle, Complex.mem_reProdIm]
    constructor
    · constructor <;> simp <;> linarith
    · dsimp [T', windowHeight]
      simp only [Complex.sub_im, Complex.one_im, zero_sub]
      rw [Set.mem_Icc]
      constructor
      · have habs' : t ≤ |-t - 1| := by
          calc t ≤ |t + 1| := by linarith [le_abs_self (t + 1)]
               _ = |-t - 1| := by
                 rw [show -t - 1 = -(t + 1) by ring, abs_neg]
        linarith [himSource.2]
      · have habs' : -t ≤ |-t - 1| + 1 := by
          calc -t = (-t - 1) + 1 := by ring
               _ ≤ |-t - 1| + 1 := by gcongr; exact le_abs_self _
        linarith [himSource.1]
  rw [closedUnitWindowSupport, Finset.mem_filter]
  refine ⟨(MAPAPZeroDensityCert.mem_zeroSupport_iff_eq_zero χ₁
    (1 / 2) T' hreflectRect).mpr ?_, ?_⟩
  · exact regularizedLFunction_eq_zero_of_mem_zeroSupport χ₁
      (1 / 2) (windowHeight t) hreflectZero
  · simp only [Complex.sub_im, Complex.one_im, zero_sub]
    constructor <;> linarith

private theorem strictLower_reflect_multiplicity_eq {t : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ strictLowerWindowSupport t) :
    zeroMultiplicity χ₁ 0 (windowHeight t) ρ =
      zeroMultiplicity χ₁ (1 / 2) (windowHeight (-t - 1)) (1 - ρ) := by
  have hρstrict := hρ
  rw [strictLowerWindowSupport, Finset.mem_filter] at hρ
  have hsource := hρ.1
  have hold := MAPPrincipalZetaTransport.zeroMultiplicity_one_sub
    (Finset.mem_filter.mp hsource).1 hρ.2.1 hρ.2.2
  have hreflectOld := MAPPrincipalZetaTransport.one_sub_mem_upper_zeroSupport
    (Finset.mem_filter.mp hsource).1 hρ.2.1 hρ.2.2
  have hreflectNew := strictLower_reflect_mem hρstrict
  exact hold.trans (MAPMellinDetectorLeaf.zeroMultiplicity_eq_of_mem_rectangles χ₁
    (PrimitiveExplicitFormulaSpine.mem_zeroRectangle_of_mem_zeroSupport χ₁
      (1 / 2) (windowHeight t) hreflectOld)
    (closedUnitWindowSupport_mem_rectangle χ₁ hreflectNew))

private theorem one_sub_injective : Function.Injective (fun ρ : ℂ => 1 - ρ) :=
  sub_right_injective

private theorem strictLowerWindow_sum_le (t : ℝ) :
    ∑ ρ ∈ strictLowerWindowSupport t,
        zeroMultiplicity χ₁ 0 (windowHeight t) ρ ≤
      closedUnitWindowCount χ₁ (1 / 2) (-t - 1) := by
  let S := strictLowerWindowSupport t
  let R : ℂ → ℂ := fun ρ => 1 - ρ
  have hsub : S.image R ⊆ closedUnitWindowSupport χ₁ (1 / 2) (-t - 1) := by
    rw [Finset.image_subset_iff]
    intro ρ hρ
    exact strictLower_reflect_mem hρ
  unfold closedUnitWindowCount
  calc
    ∑ ρ ∈ S, zeroMultiplicity χ₁ 0 (windowHeight t) ρ =
      ∑ z ∈ S.image R,
        zeroMultiplicity χ₁ (1 / 2) (windowHeight (-t - 1)) z := by
      rw [Finset.sum_image (one_sub_injective.injOn)]
      apply Finset.sum_congr rfl
      intro ρ hρ
      exact strictLower_reflect_multiplicity_eq hρ
    _ ≤ ∑ z ∈ closedUnitWindowSupport χ₁ (1 / 2) (-t - 1),
        zeroMultiplicity χ₁ (1 / 2) (windowHeight (-t - 1)) z :=
      Finset.sum_le_sum_of_subset hsub

/-- Exact full-strip count for conductor-one zeta, including multiplicity. -/
theorem principal_fullStrip_closedUnitWindowCount_le (t : ℝ) :
    closedUnitWindowCount χ₁ 0 t ≤
      closedUnitWindowCount χ₁ (1 / 2) t +
        closedUnitWindowCount χ₁ (1 / 2) (-t - 1) := by
  let S := fullWindowSupport t
  let E := endpointWindowSupport t
  let L := strictLowerWindowSupport t
  let U := upperWindowSupport t
  have hpartition : E ∪ L ∪ U = S := by
    ext ρ
    simp only [E, L, U, S, endpointWindowSupport,
      strictLowerWindowSupport, upperWindowSupport, fullWindowSupport,
      Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ((h | h) | h) <;> exact h.1
    · intro hρ
      have hre0 := fullWindowSupport_re_nonneg hρ
      by_cases hhalf : 1 / 2 ≤ ρ.re
      · exact Or.inr ⟨hρ, hhalf⟩
      · by_cases hz : ρ.re = 0
        · exact Or.inl (Or.inl ⟨hρ, hz⟩)
        · exact Or.inl (Or.inr ⟨hρ, lt_of_le_of_ne hre0 (Ne.symm hz),
            lt_of_not_ge hhalf⟩)
  have hdisjEL : Disjoint E L := by
    refine Finset.disjoint_left.mpr ?_
    intro ρ hE hL
    linarith [(Finset.mem_filter.mp hE).2, (Finset.mem_filter.mp hL).2.1]
  have hdisjELU : Disjoint (E ∪ L) U := by
    refine Finset.disjoint_left.mpr ?_
    intro ρ hEL hU
    have hUhalf := (Finset.mem_filter.mp hU).2
    rcases Finset.mem_union.mp hEL with hE | hL
    · linarith [(Finset.mem_filter.mp hE).2]
    · linarith [(Finset.mem_filter.mp hL).2.2]
  unfold closedUnitWindowCount
  change (∑ ρ ∈ S, zeroMultiplicity χ₁ 0 (windowHeight t) ρ) ≤ _
  rw [← hpartition, Finset.sum_union hdisjELU, Finset.sum_union hdisjEL]
  have hE : E = ∅ := endpointWindowSupport_eq_empty t
  have hL := strictLowerWindow_sum_le t
  have hU := upperWindow_sum_le t
  unfold closedUnitWindowCount at hL hU
  change (∑ ρ ∈ L, zeroMultiplicity χ₁ 0 (windowHeight t) ρ) ≤
    (∑ z ∈ closedUnitWindowSupport χ₁ (1 / 2) (-t - 1),
      zeroMultiplicity χ₁ (1 / 2) (windowHeight (-t - 1)) z) at hL
  change (∑ ρ ∈ U, zeroMultiplicity χ₁ 0 (windowHeight t) ρ) ≤
    (∑ z ∈ closedUnitWindowSupport χ₁ (1 / 2) t,
      zeroMultiplicity χ₁ (1 / 2) (windowHeight t) z) at hU
  rw [hE]
  simp only [Finset.sum_empty, zero_add]
  omega

/-- Explicit logarithmic full-strip A.5 count for conductor-one zeta. -/
theorem principal_fullStrip_count_le_log (t : ℝ) :
    (closedUnitWindowCount χ₁ 0 t : ℝ) ≤
      1683 * Real.log (arithmeticScale 1 t) := by
  have hstruct := principal_fullStrip_closedUnitWindowCount_le t
  have hu := MAPPrincipalZetaA5.principal_upper_closedUnitWindowCount_le t
  have hl := MAPPrincipalZetaA5.principal_upper_closedUnitWindowCount_le (-t - 1)
  have hscale : arithmeticScale 1 t = |t| + 2 := by
    simp [arithmeticScale]
  have hscalePos : 0 < |t| + 2 := by linarith [abs_nonneg t]
  have hrefScale : |-t - 1| + 2 ≤ 2 * (|t| + 2) := by
    have habs : |-t - 1| ≤ |t| + 1 := by
      rw [show -t - 1 = -(t + 1) by ring, abs_neg]
      exact (abs_add_le t 1).trans_eq (by norm_num)
    linarith [abs_nonneg t]
  have hlogRef : Real.log (|-t - 1| + 2) ≤
      2 * Real.log (|t| + 2) := by
    have hlog := Real.log_le_log (by positivity : 0 < |-t - 1| + 2) hrefScale
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (by linarith : |t| + 2 ≠ 0)] at hlog
    have hlog2 : Real.log 2 ≤ Real.log (|t| + 2) :=
      Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
    linarith
  have hcast : (closedUnitWindowCount χ₁ 0 t : ℝ) ≤
      (closedUnitWindowCount χ₁ (1 / 2) t : ℝ) +
        (closedUnitWindowCount χ₁ (1 / 2) (-t - 1) : ℝ) := by
    exact_mod_cast hstruct
  rw [hscale]
  exact hcast.trans <| by nlinarith

/-- Premise-free inhabitant of the last conductor-one source boundary. -/
theorem certifiedPrincipalFullStripA5 :
    MAPPrincipalFullStripA5Source.PrincipalFullStripA5 := by
  refine ⟨1683, by norm_num, ?_⟩
  intro q _ χ hprim hχ t
  have hq : q = 1 := by
    rw [DirichletCharacter.isPrimitive_def, hχ,
      DirichletCharacter.conductor_one] at hprim
    exact hprim.symm
  subst q
  have hχ' : χ = (1 : DirichletCharacter ℂ 1) := hχ
  subst χ
  exact principal_fullStrip_count_le_log t

#print axioms principal_fullStrip_closedUnitWindowCount_le
#print axioms principal_fullStrip_count_le_log
#print axioms certifiedPrincipalFullStripA5

end
end MAPPrincipalZetaFullStrip
