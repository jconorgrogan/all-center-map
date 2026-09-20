import JutilaP53CanonicalHalaszSource
import JutilaLemma6CanonicalSeriesSmall
import JutilaCollarSourceParameters
import JutilaGappedFixedModulusAggregateP53Adapter

/-! # Canonical quadratic inequality for the actual aggregate zero rows

All detector errors, source legalities, and row geometry are discharged from
the literal regular zero support and the aggregate gap hypothesis. -/
namespace MAPJutilaCanonicalRowsQuadratic
open scoped BigOperators
open Complex Real Filter DirichletZeros
open MAPJutilaP53AggregateCorrelationLeaf MAPJutilaP53CanonicalHalaszSource
open MAPJutilaLemma6CanonicalSeriesSmall MAPJutilaLemma6GenericTailAbsorption
open MAPJutilaCollarSourceParameters MAPJutilaGappedCollarFiniteAggregation
open MAPJutilaGappedFixedModulusAggregateP53Adapter MAPJutilaCollarA5Budget
open MAPJutilaP53SourceScaleEnvelopes
noncomputable section

set_option maxHeartbeats 1200000 in
/-- The fully instantiated source quadratic, with no remaining detector
series, tail, or main-size hypotheses. -/
theorem exists_eventually_canonical_rows_quadratic
    {delta : ℝ} (hdeltaLo : 1/560 ≤ delta) (hdeltaHi : delta ≤ 1/280) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ D : ℝ in atTop,
      ∀ (q : ℕ) [NeZero q] (T sigma omega : ℝ) (rows : Finset (JutilaP53Row q)),
      1 ≤ T → (q : ℝ)*T = D → 1-delta ≤ sigma → sigma ≤ 1 →
      0 ≤ omega → omega ≤ 1-sigma →
      Real.log D ≤ Real.rpow D (a5FiberGapBudget*omega) →
      (∀ row ∈ rows, row.character.IsPrimitive ∧ row.character ≠ 1 ∧
        row.zero ∈ regularCollarSupport row.character sigma T ∧ row.zero.re ≤ 1-omega) →
      FiberwiseOneSeparated rows →
      ((1/16:ℝ)*((Nat.totient q : ℝ)/(q : ℝ))*Real.log (sourceR delta D : ℝ))^2 *
        (rows.card : ℝ)^2 ≤
      (10*Real.rpow (lemmaSixDirectCutoff delta D : ℝ) (2-2*sigma)*
        (1+Real.log (lemmaSixDirectCutoff delta D : ℝ))^4) *
        (sourceSharpResidueBudget (sourceR delta D) delta (sourceZ1 delta D)
          (lemmaSixDirectCutoff delta D : ℝ)*(rows.card : ℝ) +
          (K*Real.rpow ((q : ℝ)*(1+2*T)) (1/2)*
            (2*Real.exp (-((1-delta)^2)*Real.log (sourceZ1 delta D)))*
            ((sourceR delta D : ℝ)^2*(harmonic (sourceR delta D) : ℝ)^8))*(rows.card : ℝ)^2) := by
  classical
  have hdelta : 0 < delta := by linarith
  obtain ⟨K,hK,hquad⟩ := exists_canonical_halasz_source_quadratic hdelta (by linarith)
  refine ⟨K,hK,?_⟩
  filter_upwards [eventually_sourceParameters hdeltaLo hdeltaHi,
    eventually_canonical_directSeries_lt_one hdeltaLo hdeltaHi,
    eventually_canonical_directTail_lt_one hdelta.le,
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (1:ℝ))]
    with D hparams hseries htail hlogOne
  intro q _inst T sigma omega rows hT hDT hsigmaLo hsigmaHi homega hgap hlogGap hrows hsep
  have hgeo := hparams.1
  have hqD : (q : ℝ) ≤ D := by
    rw [← hDT]
    nlinarith [show (0:ℝ) ≤ q from Nat.cast_nonneg q]
  have hsigma0 : 0 ≤ sigma := by linarith
  have homegaPos : 0 < omega := by
    by_contra h
    have hz : omega = 0 := le_antisymm (le_of_not_gt h) homega
    subst omega
    simp only [mul_zero, Real.rpow_eq_pow, Real.rpow_zero] at hlogGap
    linarith
  have hlogGap' : Real.log D ≤ Real.rpow D (omega/140) := by
    convert hlogGap using 1
    congr 1
    unfold a5FiberGapBudget
    ring
  have hrect : ∀ row ∈ rows, row.zero ∈ zeroRectangle sigma T := by
    intro row hr
    have hz : row.zero ∈ zeroSupport row.character sigma T :=
      (Finset.mem_filter.mp (hrows row hr).2.2.1).1
    exact (zeroDivisor row.character sigma T).supportWithinDomain
      ((zeroSupport_mem_iff row.character sigma T row.zero).mp hz)
  have hgeometry : ∀ row ∈ rows, sigma ≤ row.zero.re ∧ row.zero.re ≤ sigma+delta := by
    intro row hr
    have hrc : row.zero.re ∈ Set.Icc sigma 1 := (hrect row hr).1
    exact ⟨hrc.1, by linarith [hrc.2]⟩
  have hheight : ∀ row ∈ rows, |row.zero.im| ≤ T := by
    intro row hr
    exact abs_le.mpr (hrect row hr).2
  have hzero : ∀ row ∈ rows, DirichletCharacter.LFunction row.character row.zero = 0 := by
    intro row hr
    have hz : row.zero ∈ zeroSupport row.character sigma T :=
      (Finset.mem_filter.mp (hrows row hr).2.2.1).1
    have h := regularizedLFunction_eq_zero_of_mem_zeroSupport row.character sigma T hz
    simpa only [regularizedLFunction, if_neg (hrows row hr).2.1] using h
  apply hquad q (sourceR delta D) (lemmaSixDirectCutoff delta D) rows
    (sourceZ1 delta D) (sourceZ2 delta D) (lemmaSixSmoothScale delta D) sigma T
    hgeo.R_one hgeo.x_one hgeo.z1_one hgeo.z12 hgeo.X_two hgeo.separation
    hsigma0 hsigmaHi (by linarith) hheight hgeometry
    (fun chi => by
      convert (hsep chi).1 using 1 <;> congr 1 <;> ext rho <;> simp)
    (fun chi => by
      convert (hsep chi).2 using 1 <;> congr 1 <;> ext rho <;> simp)
    (hparams.2 q (NeZero.pos q) hqD)
  · intro row hr
    exact (hseries q row.character T omega row.zero (hrows row hr).1 (hrows row hr).2.1
      hT hDT homegaPos hlogGap' (hsigmaLo.trans (hgeometry row hr).1)
      (hrows row hr).2.2.2 (hheight row hr) (hzero row hr)).le
  · intro row hr
    exact (htail q row.character (sourceZ1 delta D) (sourceZ2 delta D) row.zero
      hgeo.z1_one hgeo.z12 (hsigma0.trans (hgeometry row hr).1)).le
end
end MAPJutilaCanonicalRowsQuadratic
#print axioms MAPJutilaCanonicalRowsQuadratic.exists_eventually_canonical_rows_quadratic
