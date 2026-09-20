import APTruncatedZeroFieldEnergyCore
import PrincipalZetaFullStrip

/-!
# Full-strip row bounds inherited by the Perron zero support
-/

namespace MAPAPTruncatedZeroFieldRow

open MeasureTheory Set
open scoped ENNReal BigOperators
open APExplicitFormulaMajorantAdapter
open MAPFixedScaleAPZeroRoute MAPAPHalfIntegerAlignedTail
open DirichletZeros MAPLocalZeroWindow

noncomputable section

variable {q : ℕ} [NeZero q]

/-- Positive-left-edge support is a subset of the certified full strip. -/
theorem zeroSupport_subset_full
    (chi : DirichletCharacter ℂ q) {sigma T : ℝ} (hsigma : 0 ≤ sigma) :
    zeroSupport chi sigma T ⊆ zeroSupport chi 0 T :=
  MAPMellinDetectorLeaf.zeroSupport_mono chi hsigma le_rfl

/-- Multiplicity is transported exactly between the nested rectangles. -/
theorem zeroMultiplicity_eq_full_of_mem
    (chi : DirichletCharacter ℂ q) {sigma T : ℝ} (hsigma : 0 ≤ sigma)
    {rho : ℂ} (hrho : rho ∈ zeroSupport chi sigma T) :
    zeroMultiplicity chi sigma T rho = zeroMultiplicity chi 0 T rho := by
  have hinner := (zeroDivisor chi sigma T).supportWithinDomain
    ((zeroSupport_mem_iff chi sigma T rho).mp hrho)
  have houterMem := zeroSupport_subset_full chi hsigma hrho
  have houter := (zeroDivisor chi 0 T).supportWithinDomain
    ((zeroSupport_mem_iff chi 0 T rho).mp houterMem)
  exact (MAPMellinDetectorLeaf.zeroMultiplicity_eq_of_mem_rectangles
    chi houter hinner).symm

/-- Any full-strip reciprocal row bound restricts to the Perron support with
no loss. -/
theorem truncated_reciprocalRow_le_of_full
    (chi : DirichletCharacter ℂ q) {sigma T H : ℝ}
    (hsigma : 0 ≤ sigma)
    (hfull : ∀ rho ∈ zeroSupport chi 0 T,
      (∑ rho' ∈ zeroSupport chi 0 T,
        (zeroMultiplicity chi 0 T rho' : ℝ) /
          (1 + |rho'.im - rho.im|)) ≤ H) :
    ∀ rho ∈ zeroSupport chi sigma T,
      (∑ rho' ∈ zeroSupport chi sigma T,
        (zeroMultiplicity chi sigma T rho' : ℝ) /
          (1 + |rho'.im - rho.im|)) ≤ H := by
  intro rho hrho
  let S := zeroSupport chi sigma T
  let U := zeroSupport chi 0 T
  have hsub : S ⊆ U := zeroSupport_subset_full chi hsigma
  have hrewrite :
      (∑ rho' ∈ S,
        (zeroMultiplicity chi sigma T rho' : ℝ) /
          (1 + |rho'.im - rho.im|)) =
      ∑ rho' ∈ S,
        (zeroMultiplicity chi 0 T rho' : ℝ) /
          (1 + |rho'.im - rho.im|) := by
    apply Finset.sum_congr rfl
    intro rho' hrho'
    rw [zeroMultiplicity_eq_full_of_mem chi hsigma hrho']
  rw [hrewrite]
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun rho' hrho'U hrho'S =>
      div_nonneg (Nat.cast_nonneg _) (by positivity))).trans
    (hfull rho (hsub hrho))

private theorem harmonic_nonneg_real (n : ℕ) :
    (0 : ℝ) ≤ (harmonic n : ℝ) := by
  norm_cast
  unfold harmonic
  positivity

/-- Uniform full-strip row bound, combining certified principal A.5 and the
premise-free nonprincipal count. -/
theorem full_reciprocalRow_le_uniform
    (Cp : ℝ) (hCp : 0 < Cp)
    (hcount : ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q),
      chi.IsPrimitive → chi = 1 → ∀ t : ℝ,
        (closedUnitWindowCount chi 0 t : ℝ) ≤
          Cp * Real.log (arithmeticScale q t))
    (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive) {T : ℝ} (hT : 0 ≤ T) :
    ∀ rho ∈ zeroSupport chi 0 T,
      (∑ rho' ∈ zeroSupport chi 0 T,
        (zeroMultiplicity chi 0 T rho' : ℝ) /
          (1 + |rho'.im - rho.im|)) ≤
      2 * (1 + (Cp + 306) * Real.log ((q : ℝ) * (T + 4))) *
        (harmonic (⌊2 * T⌋₊ + 1) : ℝ) := by
  by_cases hchi : chi = 1
  · have hscale1 : 1 ≤ (q : ℝ) * (T + 4) := by
      have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
      nlinarith
    have hlog := Real.log_nonneg hscale1
    intro rho hrho
    have hrow :
        (∑ rho' ∈ zeroSupport chi 0 T,
          (zeroMultiplicity chi 0 T rho' : ℝ) /
            (1 + |rho'.im - rho.im|)) ≤
        2 * (Cp * Real.log ((q : ℝ) * (T + 4))) *
          (harmonic (⌊2 * T⌋₊ + 1) : ℝ) := by
      apply MAPHarmonicRowGrouping.finite_reciprocal_row_le_harmonic
        (zeroSupport chi 0 T)
        (fun z => (zeroMultiplicity chi 0 T z : ℝ))
        (fun z => z.im) hT
      · exact mul_nonneg hCp.le hlog
      · intro z hz
        positivity
      · intro z hz
        have hrect :=
          PrimitiveExplicitFormulaSpine.mem_zeroRectangle_of_mem_zeroSupport
            chi 0 T hz
        exact abs_le.mpr (Complex.mem_reProdIm.mp hrect).2
      · intro a
        exact MAPPrincipalFullStripA5Source.principal_globalUnitWindowMass_le_uniform
          Cp hCp hcount chi hprim hchi hT a
      · exact hrho
    exact hrow.trans (by
      have hh := harmonic_nonneg_real (⌊2 * T⌋₊ + 1)
      gcongr
      nlinarith)
  · exact fun rho hrho =>
      (MAPAPZeroFieldEnergy28Grouping.reciprocalRow_le_nonprincipal
        chi hprim hchi hT rho hrho).trans (by
          have hscale1 : 1 ≤ (q : ℝ) * (T + 4) := by
            have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
            nlinarith
          have hlog := Real.log_nonneg hscale1
          have hh := harmonic_nonneg_real (⌊2 * T⌋₊ + 1)
          gcongr
          nlinarith)

/-- Weighted mass on the literal Perron support. -/
def truncatedWeightedZeroMass
    (chi : DirichletCharacter ℂ q) (sigma X T : ℝ) : ℝ := by
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  exact ∑ rho ∈ zeroSupport chi.primitiveCharacter sigma T,
    (zeroMultiplicity chi.primitiveCharacter sigma T rho : ℝ) *
      Real.rpow X (2 * (rho.re - 1))

/-- Raw-height equation (2.8) on the sigma-truncated Perron support. -/
theorem truncated_perron_energy_le_raw
    (Cp : ℝ) (hCp : 0 < Cp)
    (hcount : ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q),
      chi.IsPrimitive → chi = 1 → ∀ t : ℝ,
        (closedUnitWindowCount chi 0 t : ℝ) ≤
          Cp * Real.log (arithmeticScale q t))
    (chi : DirichletCharacter ℂ q) [NeZero chi.conductor]
    {sigma X T : ℝ} (hsigma : 0 < sigma)
    (hX : 0 < X) (hT : 0 ≤ T) :
    (∫⁻ t : ℝ,
      ((Set.Icc (X / 4) (6 * X)).indicator
        (fun u => ENNReal.ofReal ‖perronZeroField chi sigma T u‖) t) ^ 2) ≤
      ENNReal.ofReal
        (192 * X *
          (2 * (1 + (Cp + 306) *
            Real.log ((chi.conductor : ℝ) * (T + 4))) *
            (harmonic (⌊2 * T⌋₊ + 1) : ℝ)) *
          truncatedWeightedZeroMass chi sigma X T) := by
  let psi := chi.primitiveCharacter
  let S := zeroSupport psi sigma T
  let mult := zeroMultiplicity psi sigma T
  have hre : ∀ rho ∈ S, 0 ≤ rho.re ∧ rho.re ≤ 1 := by
    intro rho hrho
    have hrect :=
      PrimitiveExplicitFormulaSpine.mem_zeroRectangle_of_mem_zeroSupport
        psi sigma T hrho
    exact ⟨hsigma.le.trans hrect.1.1, hrect.1.2⟩
  have hfull := full_reciprocalRow_le_uniform Cp hCp hcount psi
    chi.primitiveCharacter_isPrimitive hT
  have hrow := truncated_reciprocalRow_le_of_full psi hsigma.le hfull
  simpa only [perronZeroField, S, mult, truncatedWeightedZeroMass, psi] using
    MAPAPTruncatedZeroFieldEnergyCore.lintegral_zeroNormField_sq_le_of_row
      S mult hX hre hrow

end
end MAPAPTruncatedZeroFieldRow

#print axioms MAPAPTruncatedZeroFieldRow.zeroMultiplicity_eq_full_of_mem
#print axioms MAPAPTruncatedZeroFieldRow.truncated_reciprocalRow_le_of_full
#print axioms MAPAPTruncatedZeroFieldRow.full_reciprocalRow_le_uniform
#print axioms MAPAPTruncatedZeroFieldRow.truncated_perron_energy_le_raw
