import JutilaGappedCollarFiniteAggregation
import JutilaCollarA5Budget

/-!
# Source-minimal p.53 adapter for the live Jutila collar

The finite occupied-box aggregation is now certified independently.  The only
remaining source-facing statement is the p.53 detector/correlation estimate
for a genuinely one-separated selected subsystem of the regular collar.
-/

namespace MAPJutilaGappedCollarSelectedP53Adapter

open Filter
open scoped BigOperators
open DirichletZeros
open MAPJutilaCollarMeshCutoff MAPJutilaCollarA5Budget
open MAPJutilaGappedCollarSourceAdapter
open MAPJutilaGappedCollarFiniteAggregation

noncomputable section

/-- Exact nonprincipal analytic leaf after Appendix A.5 and finite box
aggregation.  Jutila's Lemma 6 and the p.53 argument explicitly assume a
nonprincipal character; retaining that hypothesis here prevents the
conductor-one zeta case from being silently attributed to that proof. -/
def JutilaGappedSelectedSystemP53Eventually : Prop :=
  ∃ Cp R₀ : ℝ, 0 < Cp ∧ 6 ≤ R₀ ∧
    ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q)
      (T sigma omega : ℝ) (W : Finset ℂ),
      chi.IsPrimitive → chi ≠ 1 → 1 ≤ T →
      279 / 280 ≤ sigma → sigma ≤ 1 →
      0 ≤ omega → omega ≤ 1 - sigma →
      R₀ ≤ (q : ℝ) * T →
      Real.log ((q : ℝ) * T) ≤
        Real.rpow ((q : ℝ) * T) (a5FiberGapBudget * omega) →
      (∀ rho : ℂ,
        rho ∈ regularCollarSupport chi sigma T →
        rho.re ≤ 1 - omega) →
      W ⊆ regularCollarSupport chi sigma T →
      CGLProofDAG.OneSeparated (W.image Complex.im) →
      (W.image Complex.im).card = W.card →
      (W.card : ℝ) ≤ Cp * Real.rpow ((q : ℝ) * T)
        ((2 * (1 + 12 * collarDelta) + 4 * detectorLogBudget) *
          (1 - sigma))

/-- The separate conductor-one leaf suppressed in Jutila's proof by the
sentence invoking known zeta-zero results.  A classical zeta density theorem
has a fixed polylogarithmic loss, so that loss is kept explicit as
`(log(qT))^P`.  It is absorbed together with the A.5 multiplicity logarithm,
spending the `1/140` gap reserve exactly once. -/
def JutilaGappedSelectedPrincipalP53Eventually : Prop :=
  ∃ Cp R₀ P : ℝ, 0 < Cp ∧ 6 ≤ R₀ ∧ 0 ≤ P ∧
    ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q)
      (T sigma omega : ℝ) (W : Finset ℂ),
      chi.IsPrimitive → chi = 1 → 1 ≤ T →
      279 / 280 ≤ sigma → sigma ≤ 1 →
      0 ≤ omega → omega ≤ 1 - sigma →
      R₀ ≤ (q : ℝ) * T →
      (∀ rho : ℂ,
        rho ∈ regularCollarSupport chi sigma T →
        rho.re ≤ 1 - omega) →
      W ⊆ regularCollarSupport chi sigma T →
      CGLProofDAG.OneSeparated (W.image Complex.im) →
      (W.image Complex.im).card = W.card →
      (W.card : ℝ) ≤
        Cp * Real.rpow (Real.log ((q : ℝ) * T)) P *
          Real.rpow ((q : ℝ) * T)
            ((2 * (1 + 12 * collarDelta) + 4 * detectorLogBudget) *
              (1 - sigma))

/-- Exact cumulative collar surface produced by combining the nonprincipal
Jutila p.53 estimate, the principal explicit-polylog zeta estimate, and the
certified A.5 finite aggregation.  The caller supplies the one gap-absorption
inequality for the combined logarithmic power `P+1`. -/
def JutilaGappedSplitSelectedCumulativeEventually : Prop :=
  ∃ C R₀ P : ℝ, 0 < C ∧ 6 ≤ R₀ ∧ 0 ≤ P ∧
    ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q)
      (T sigma omega : ℝ),
      chi.IsPrimitive → 1 ≤ T →
      279 / 280 ≤ sigma → sigma ≤ 1 →
      0 ≤ omega → omega ≤ 1 - sigma →
      R₀ ≤ (q : ℝ) * T →
      Real.rpow (Real.log ((q : ℝ) * T)) (P + 1) ≤
        Real.rpow ((q : ℝ) * T) (a5FiberGapBudget * omega) →
      (∀ rho : ℂ,
        rho ∈ regularCollarSupport chi sigma T →
        rho.re ≤ 1 - omega) →
      (primitiveRegularCumulativeCount chi sigma T : ℝ) ≤
        C * Real.rpow ((q : ℝ) * T)
          ((21 / 10) * (1 - sigma))

/-- The split selected-system sources give the exact `21/10` cumulative
regular collar density after the caller proves one combined polylogarithmic
gap absorption. -/
theorem primitiveRegularCumulativeCount_le_of_gappedSelectedP53
    (hnonprincipal : JutilaGappedSelectedSystemP53Eventually)
    (hprincipal : JutilaGappedSelectedPrincipalP53Eventually) :
    JutilaGappedSplitSelectedCumulativeEventually := by
  obtain ⟨Cn, Rn, hCn, hRn, hn⟩ := hnonprincipal
  obtain ⟨Cp, Rp, P, hCp, hRp, hP, hp⟩ := hprincipal
  let Cmax : ℝ := max Cn Cp
  let Rmax : ℝ := max (max Rn Rp) (Real.exp 1)
  refine ⟨6734 * Cmax, Rmax, P, ?_, ?_, hP, ?_⟩
  · dsimp [Cmax]
    positivity
  · exact hRn.trans ((le_max_left Rn Rp).trans (le_max_left _ _))
  intro q _inst chi T sigma omega hprim hT hsigmaLow hsigmaHigh
    homega hgap hscale hpolyGap hregularGap
  let D : ℝ := (q : ℝ) * T
  have hmaxScale : max Rn Rp ≤ D :=
    (le_max_left (max Rn Rp) (Real.exp 1)).trans hscale
  have hRnScale : Rn ≤ D := (le_max_left Rn Rp).trans hmaxScale
  have hRpScale : Rp ≤ D := (le_max_right Rn Rp).trans hmaxScale
  have hDexp : Real.exp 1 ≤ D :=
    (le_max_right (max Rn Rp) (Real.exp 1)).trans hscale
  have hD : 1 < D :=
    (Real.one_lt_exp_iff.mpr zero_lt_one).trans_le hDexp
  have hlogOne : 1 ≤ Real.log D := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hDexp
  have hlogPos : 0 < Real.log D := zero_lt_one.trans_le hlogOne
  have hlogPone : 1 ≤ Real.rpow (Real.log D) P :=
    Real.one_le_rpow hlogOne hP
  have hlogP0 : 0 ≤ Real.rpow (Real.log D) P :=
    Real.rpow_nonneg hlogPos.le P
  have hlog : Real.log D ≤
      Real.rpow D (a5FiberGapBudget * omega) := by
    calc
      Real.log D = Real.rpow (Real.log D) 1 :=
        (Real.rpow_one (Real.log D)).symm
      _ ≤ Real.rpow (Real.log D) (P + 1) := by
        apply Real.rpow_le_rpow_of_exponent_le hlogOne
        linarith
      _ ≤ Real.rpow D (a5FiberGapBudget * omega) := hpolyGap
  obtain ⟨W, hWsub, hWsep, hWcard, hcompress⟩ :=
    exists_selected_regularCollar chi hprim
      ((by norm_num : (1 / 2 : ℝ) ≤ 279 / 280).trans hsigmaLow) hT
  let exponent : ℝ :=
    (2 * (1 + 12 * collarDelta) + 4 * detectorLogBudget) *
      (1 - sigma)
  have hpow0 : 0 ≤ Real.rpow D exponent :=
    Real.rpow_nonneg (zero_le_one.trans hD.le) _
  have hWbound : (W.card : ℝ) ≤
      Cmax * Real.rpow (Real.log D) P * Real.rpow D exponent := by
    by_cases hchi : chi = 1
    · have hb := hp q chi T sigma omega W hprim hchi hT hsigmaLow
        hsigmaHigh homega hgap hRpScale hregularGap hWsub hWsep hWcard
      have hC : Cp ≤ Cmax := le_max_right _ _
      exact hb.trans (by
        dsimp only [D, exponent, Cmax]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hC hlogP0) hpow0)
    · have hb := hn q chi T sigma omega W hprim hchi hT hsigmaLow
        hsigmaHigh homega hgap hRnScale hlog hregularGap hWsub hWsep hWcard
      have hC : Cn ≤ Cmax := le_max_left _ _
      calc
        (W.card : ℝ) ≤ Cn * Real.rpow D exponent := by
          simpa only [D, exponent] using hb
        _ ≤ Cmax * Real.rpow D exponent :=
          mul_le_mul_of_nonneg_right hC hpow0
        _ = Cmax * 1 * Real.rpow D exponent := by ring
        _ ≤ Cmax * Real.rpow (Real.log D) P * Real.rpow D exponent := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hlogPone
              ((le_max_left Cn Cp).trans' hCn.le)) hpow0
  have hcap := regularCollarNatCap_cast_le_log (q := q) hT
    (hRn.trans hRnScale)
  have hcompressR :
      (primitiveRegularCumulativeCount chi sigma T : ℝ) ≤
        6734 * Real.log D * (W.card : ℝ) := by
    have hcast :
        (primitiveRegularCumulativeCount chi sigma T : ℝ) ≤
          ((2 * regularCollarNatCap (q := q) T * W.card : ℕ) : ℝ) := by
      exact_mod_cast hcompress
    calc
      (primitiveRegularCumulativeCount chi sigma T : ℝ) ≤
          ((2 * regularCollarNatCap (q := q) T * W.card : ℕ) : ℝ) := hcast
      _ = 2 * (regularCollarNatCap (q := q) T : ℝ) * (W.card : ℝ) := by
        push_cast
        ring
      _ ≤ 2 * (3367 * Real.log D) * (W.card : ℝ) := by
        gcongr
      _ = 6734 * Real.log D * (W.card : ℝ) := by ring
  let selected : ℝ := Cmax * Real.rpow D exponent
  have hselected0 : 0 ≤ selected := by
    dsimp [selected, Cmax]
    positivity
  have hselected : selected ≤ Cmax * Real.rpow D exponent := le_rfl
  have hlogMul : Real.log D * Real.rpow (Real.log D) P =
      Real.rpow (Real.log D) (P + 1) := by
    calc
      Real.log D * Real.rpow (Real.log D) P =
          Real.rpow (Real.log D) 1 * Real.rpow (Real.log D) P := by
        exact congrArg
          (fun z : ℝ => z * Real.rpow (Real.log D) P)
          (Real.rpow_one (Real.log D)).symm
      _ = Real.rpow (Real.log D) (1 + P) :=
        (Real.rpow_add hlogPos 1 P).symm
      _ = Real.rpow (Real.log D) (P + 1) := by ring_nf
  have htotal :
      (primitiveRegularCumulativeCount chi sigma T : ℝ) ≤
        6734 * Real.rpow (Real.log D) (P + 1) * selected := by
    calc
      (primitiveRegularCumulativeCount chi sigma T : ℝ) ≤
          6734 * Real.log D * (W.card : ℝ) := hcompressR
      _ ≤ 6734 * Real.log D *
          (Cmax * Real.rpow (Real.log D) P * Real.rpow D exponent) := by
        exact mul_le_mul_of_nonneg_left hWbound
          (mul_nonneg (by norm_num) hlogPos.le)
      _ = 6734 *
          (Real.log D * Real.rpow (Real.log D) P) * selected := by
        dsimp [selected]
        ring
      _ = 6734 * Real.rpow (Real.log D) (P + 1) * selected := by
        rw [hlogMul]
  have hfinal := total_le_final_density_of_gapFactor_and_p53
    (D := D) (alpha := sigma) (omega := omega)
    (total := (primitiveRegularCumulativeCount chi sigma T : ℝ))
    (selected := selected) (C := Cmax) (K := 6734)
    (gapFactor := Real.rpow (Real.log D) (P + 1))
    hD hsigmaHigh hgap (le_max_left Cn Cp |>.trans' hCn.le) (by norm_num)
    hselected0 hpolyGap htotal (by simpa only [selected, exponent] using hselected)
  simpa only [D, Cmax, exponent] using hfinal

end

end MAPJutilaGappedCollarSelectedP53Adapter

#print axioms MAPJutilaGappedCollarSelectedP53Adapter.primitiveRegularCumulativeCount_le_of_gappedSelectedP53
