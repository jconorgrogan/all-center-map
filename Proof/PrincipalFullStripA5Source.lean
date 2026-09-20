import APZeroFieldEnergy28Grouping

/-!
# The isolated conductor-one source for equation (2.8)

All nonprincipal full-strip local counts are certified in
`FullStripA5Family`.  This file isolates the sole remaining family member:
the primitive principal character, necessarily of conductor one.
-/

namespace MAPPrincipalFullStripA5Source

open Complex Set
open scoped BigOperators ENNReal
open DirichletZeros MAPLocalZeroWindow
open APExplicitFormulaMajorantAdapter

noncomputable section

/-- The smallest remaining analytic source for the complete family version
of equation (2.8): the classical local zero count for the regularized zeta
function.  The apparently level-polymorphic statement still describes only
conductor one, because a primitive principal character has level one. -/
def PrincipalFullStripA5 : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ = 1 → ∀ t : ℝ,
        (closedUnitWindowCount χ 0 t : ℝ) ≤
          C * Real.log (arithmeticScale q t)

variable {q : ℕ} [NeZero q]

private theorem zeroSupport_im_abs_le
    (χ : DirichletCharacter ℂ q) {T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ zeroSupport χ 0 T) : |ρ.im| ≤ T := by
  have hrect := PrimitiveExplicitFormulaSpine.mem_zeroRectangle_of_mem_zeroSupport
    χ 0 T hρ
  exact abs_le.mpr (Complex.mem_reProdIm.mp hrect).2

theorem principal_globalUnitWindowMass_le_uniform
    (C : ℝ) (hC : 0 < C)
    (hcount : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ = 1 → ∀ t : ℝ,
        (closedUnitWindowCount χ 0 t : ℝ) ≤
          C * Real.log (arithmeticScale q t))
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ = 1)
    {T : ℝ} (hT : 0 ≤ T) (a : ℝ) :
    (∑ ρ ∈ MAPPaperWindowVKBypass.globalUnitWindowSupport χ 0 T a,
        (zeroMultiplicity χ 0 T ρ : ℝ)) ≤
      C * Real.log ((q : ℝ) * (T + 4)) := by
  classical
  let S := MAPPaperWindowVKBypass.globalUnitWindowSupport χ 0 T a
  by_cases hS : S.Nonempty
  · obtain ⟨ρ, hρ⟩ := hS
    have hρglobal : ρ ∈ zeroSupport χ 0 T := (Finset.mem_filter.mp hρ).1
    have hρim := zeroSupport_im_abs_le χ hρglobal
    have hρwindow := (Finset.mem_filter.mp hρ).2
    have haLo : -T - 1 ≤ a := by
      have hlow : -T ≤ ρ.im := (abs_le.mp hρim).1
      linarith
    have haHi : a ≤ T := by
      have hhigh : ρ.im ≤ T := (abs_le.mp hρim).2
      linarith
    have habsa : |a| ≤ T + 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hscale : arithmeticScale q a ≤ (q : ℝ) * (T + 4) := by
      unfold arithmeticScale
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have hscalePos : 0 < arithmeticScale q a := by
      unfold arithmeticScale
      exact mul_pos (by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne q)))
        (by linarith [abs_nonneg a])
    have hlog := Real.log_le_log hscalePos hscale
    have hnat := MAPPaperWindowVKBypass.globalUnitWindowCount_le_closed χ 0 T a
    have hslice :
        (∑ ρ ∈ S, (zeroMultiplicity χ 0 T ρ : ℝ)) ≤
          (closedUnitWindowCount χ 0 a : ℝ) := by
      exact_mod_cast hnat
    have hlocal := hcount q χ hprim hχ a
    exact hslice.trans (hlocal.trans
      (mul_le_mul_of_nonneg_left hlog hC.le))
  · have hSempt : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    have hqnat : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    have hq : (1 : ℝ) ≤ q := by exact_mod_cast hqnat
    have hscale1 : 1 ≤ (q : ℝ) * (T + 4) := by nlinarith
    have hlog : 0 ≤ Real.log ((q : ℝ) * (T + 4)) := Real.log_nonneg hscale1
    simp [S, hSempt, mul_nonneg hC.le hlog]

/-- The principal row estimate, conditional only on the isolated zeta A.5
source. -/
theorem reciprocalRow_le_principal
    (hA5 : PrincipalFullStripA5)
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ = 1)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧ ∀ ρ ∈ zeroSupport χ 0 T,
      (∑ ρ' ∈ zeroSupport χ 0 T,
        (zeroMultiplicity χ 0 T ρ' : ℝ) /
          (1 + |ρ'.im - ρ.im|)) ≤
        2 * (C * Real.log ((q : ℝ) * (T + 4))) *
          (harmonic (⌊2 * T⌋₊ + 1) : ℝ) := by
  rcases hA5 with ⟨C, hC, hcount⟩
  refine ⟨C, hC, ?_⟩
  intro ρ hρ
  classical
  apply MAPHarmonicRowGrouping.finite_reciprocal_row_le_harmonic
    (zeroSupport χ 0 T)
    (fun z => (zeroMultiplicity χ 0 T z : ℝ))
    (fun z => z.im) hT
  · have hqnat : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hqnat
    have hscale : 1 ≤ (q : ℝ) * (T + 4) := by nlinarith
    exact mul_nonneg hC.le (Real.log_nonneg hscale)
  · intro z hz
    positivity
  · intro z hz
    exact zeroSupport_im_abs_le χ hz
  · intro a
    exact principal_globalUnitWindowMass_le_uniform
      C hC hcount χ hprim hχ hT a
  · exact hρ

/-- Complete literal principal-character ENNReal energy conditional on the
single zeta local-count source. -/
theorem lintegral_zeroNormField_sq_le_principal
    (hA5 : PrincipalFullStripA5)
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ = 1)
    {X T : ℝ} (hX : 0 < X) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧
      (∫⁻ t : ℝ,
        ((Set.Icc (X / 4) (6 * X)).indicator
          (fun u => ENNReal.ofReal ‖actualZeroField χ 0 T u‖) t) ^ 2) ≤
        ENNReal.ofReal
          (192 * X *
            (2 * (C * Real.log ((q : ℝ) * (T + 4))) *
              (harmonic (⌊2 * T⌋₊ + 1) : ℝ)) *
            (∑ ρ ∈ zeroSupport χ 0 T,
              (zeroMultiplicity χ 0 T ρ : ℝ) *
                Real.rpow X (2 * (ρ.re - 1)))) := by
  rcases reciprocalRow_le_principal hA5 χ hprim hχ hT with
    ⟨C, hC, hrow⟩
  refine ⟨C, hC, ?_⟩
  exact MAPAPZeroFieldEnergy28Grouping.lintegral_zeroNormField_sq_le_of_row
    χ hX hrow

#print axioms principal_globalUnitWindowMass_le_uniform
#print axioms reciprocalRow_le_principal
#print axioms lintegral_zeroNormField_sq_le_principal

end
end MAPPrincipalFullStripA5Source
