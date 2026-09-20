import JutilaCanonicalRowsQuadratic
import JutilaCanonicalQuadraticAbsorption
import JutilaSourceQEBudget
import JutilaSourceFVBudget

/-! The fixed-modulus nonprincipal collar source, with no analytic or logarithmic budget premises. -/
namespace MAPJutilaGappedAggregateP53Closed
open Filter Real
open MAPJutilaCanonicalRowsQuadratic MAPJutilaCanonicalQuadraticAbsorption
open MAPJutilaSourceQEBudget MAPJutilaSourceFVBudget
open MAPJutilaCollarSourceParameters MAPJutilaLemma6GenericTailAbsorption
open MAPJutilaP53SourceScaleEnvelopes MAPJutilaCollarNoLogBudget
open MAPJutilaP53AggregateCorrelationLeaf MAPJutilaGappedCollarFiniteAggregation
open MAPJutilaGappedFixedModulusAggregateP53Adapter MAPJutilaCollarA5Budget MAPJutilaCollarMeshCutoff
noncomputable section
set_option maxHeartbeats 1600000

private theorem sourceF_nonneg {δ D : ℝ} (hδ : 0 ≤ δ) (hδhi : δ ≤ 1)
    (hgeo : SourceGeometry δ D) :
    0 ≤ sourceSharpResidueBudget (sourceR δ D) δ (sourceZ1 δ D) (lemmaSixDirectCutoff δ D : ℝ) := by
  have hz := hgeo.z1_one
  have hx : sourceZ1 δ D < (lemmaSixDirectCutoff δ D : ℝ) := by linarith [hgeo.separation]
  have hlogz : 0 ≤ Real.log (sourceZ1 δ D) := Real.log_nonneg hz.le
  have hlogx : Real.log (sourceZ1 δ D) ≤ Real.log (lemmaSixDirectCutoff δ D : ℝ) :=
    Real.log_le_log (zero_lt_one.trans hz) hx.le
  have hmass := MAPJutilaSourceFVBudget.integerExponentialMass_nonneg
  unfold sourceSharpResidueBudget
  apply mul_nonneg
  · have hgap : 0 ≤ (1+δ)*Real.log (lemmaSixDirectCutoff δ D : ℝ) - (1-δ)*Real.log (sourceZ1 δ D) := by
      nlinarith [mul_nonneg hδ hlogz, mul_nonneg hδ (hlogz.trans hlogx)]
    positivity
  · unfold harmonic
    positivity

theorem exists_eventually_count_le_logCost {δ : ℝ}
    (hlo : 1/560 ≤ δ) (hhi : δ ≤ 1/280) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ D : ℝ in atTop,
      ∀ (q : ℕ) [NeZero q] (T sigma omega : ℝ) (rows : Finset (JutilaP53Row q)),
      1 ≤ T → (q : ℝ)*T = D → 1-δ ≤ sigma → sigma ≤ 1 →
      0 ≤ omega → omega ≤ 1-sigma →
      Real.log D ≤ Real.rpow D (a5FiberGapBudget*omega) →
      (∀ row ∈ rows, row.character.IsPrimitive ∧ row.character ≠ 1 ∧
        row.zero ∈ regularCollarSupport row.character sigma T ∧ row.zero.re ≤ 1-omega) →
      FiberwiseOneSeparated rows → (rows.card : ℝ) ≤ C * collarLogCost D δ sigma := by
  obtain ⟨K,hK,hquad⟩ := exists_eventually_canonical_rows_quadratic hlo hhi
  obtain ⟨C,hC,hFV⟩ := exists_eventually_sourceFVBudget hlo hhi
  refine ⟨C,hC,?_⟩
  filter_upwards [hquad,hFV,eventually_sourceQE_le_one hlo hhi K hK.le,
    eventually_sourceParameters hlo hhi,eventually_ge_atTop (Real.exp 1)]
    with D hquad hFV hQE hparams hDe
  intro q _inst T sigma omega rows hT hDT hslo hshi homega hgap hlogGap hrows hsep
  have hDp : 0 < D := (Real.exp_pos 1).trans_le hDe
  have hD1 : 1 ≤ D := (Real.one_le_exp (by norm_num : (0:ℝ) ≤ 1)).trans hDe
  have hq : 0 < q := NeZero.pos q
  have hqD : (q : ℝ) ≤ D := by rw [← hDT]; nlinarith [show (0 : ℝ) ≤ q from Nat.cast_nonneg q]
  let Q := sourceQ δ D sigma
  let F := sourceSharpResidueBudget (sourceR δ D) δ (sourceZ1 δ D) (lemmaSixDirectCutoff δ D : ℝ)
  let V := (1/16:ℝ)*((Nat.totient q:ℝ)/(q:ℝ))*Real.log (sourceR δ D : ℝ)
  let E := sourceE K δ D q T
  have hV : 2 ≤ V := by
    have h := hparams.2 q hq hqD
    dsimp [V]
    nlinarith
  have hQ : 0 ≤ Q := by
    dsimp [Q,sourceQ]
    exact mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (pow_nonneg (by linarith [Real.log_nonneg (show (1:ℝ) ≤ lemmaSixDirectCutoff δ D by exact_mod_cast hparams.1.x_one)]) _)
  have hF : 0 ≤ F := sourceF_nonneg (by linarith) (by linarith) hparams.1
  have hquad' : V^2*(rows.card:ℝ)^2 ≤ Q*(F*(rows.card:ℝ)+E*(rows.card:ℝ)^2) := by
    have h := hquad q T sigma omega rows hT hDT hslo hshi homega hgap hlogGap hrows hsep
    simpa [V,Q,F,E,sourceQ,sourceE,Real.sqrt_eq_rpow,mul_assoc] using h
  have hcount := card_le_two_linear_div_detector_sq (Nat.cast_nonneg rows.card) hV
    (mul_nonneg hQ hF) (hQE q T sigma hT hDT hslo) hquad'
  have hfv := hFV q hq hqD sigma hshi
  have hcut := cutoffPower_logCost_le hDp (Real.log_nonneg hD1) hshi hparams.1
  calc
    _ ≤ 2*Q*F/V^2 := hcount
    _ ≤ C*Real.rpow (lemmaSixDirectCutoff δ D : ℝ) (2-2*sigma)*(1+Real.log D)^6 := hfv
    _ ≤ C*collarLogCost D δ sigma := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hcut hC.le

theorem jutilaGappedFixedModulusAggregateP53Eventually :
    JutilaGappedFixedModulusAggregateP53Eventually := by
  obtain ⟨Cf,hCf,hfar⟩ := exists_eventually_count_le_logCost
    (δ := (1/280:ℝ)) (by norm_num) (by norm_num)
  obtain ⟨Cn,hCn,hnear⟩ := exists_eventually_count_le_logCost
    (δ := (1/560:ℝ)) (by norm_num) (by norm_num)
  have hevent : ∀ᶠ D : ℝ in atTop,
      ∀ (q : ℕ) [NeZero q] (T sigma omega : ℝ) (rows : Finset (JutilaP53Row q)),
      1 ≤ T → (q:ℝ)*T=D → (279/280:ℝ) ≤ sigma → sigma ≤ 1 →
      0 ≤ omega → omega ≤ 1-sigma →
      Real.log D ≤ Real.rpow D (a5FiberGapBudget*omega) →
      (∀ row ∈ rows, row.character.IsPrimitive ∧ row.character ≠ 1 ∧
        row.zero ∈ regularCollarSupport row.character sigma T ∧ row.zero.re ≤ 1-omega) →
      FiberwiseOneSeparated rows →
      (rows.card:ℝ) ≤ (64*(Cf+Cn))*Real.rpow D ((293/140)*(1-sigma)) := by
    filter_upwards [hfar,hnear,eventually_collarLogCost_le,eventually_ge_atTop (6:ℝ)]
      with D hfar hnear hlog hD
    intro q _inst T sigma omega rows hT hDT hslo hshi homega hgap hlogGap hrows hsep
    have hlogGap' : Real.log D ≤ Real.rpow D (omega/140) := by
      simpa [a5FiberGapBudget,div_eq_mul_inv,mul_comm] using hlogGap
    have hcost0 : 0 ≤ collarLogCost D (if sigma≤559/560 then 1/280 else 1/560) sigma := by
      unfold collarLogCost
      exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (by linarith) _)
        (Real.rpow_nonneg (Real.log_nonneg (by linarith)) _)) (pow_nonneg (by linarith [Real.log_nonneg (show 1≤D by linarith)]) _)
    have hb : (rows.card:ℝ) ≤ (Cf+Cn)*collarLogCost D (if sigma≤559/560 then 1/280 else 1/560) sigma := by
      by_cases hs : sigma≤559/560
      · have h := hfar q T sigma omega rows hT hDT (by linarith) hshi homega hgap hlogGap hrows hsep
        rw [if_pos hs] at hcost0 ⊢
        exact h.trans (mul_le_mul_of_nonneg_right (by linarith) hcost0)
      · have h := hnear q T sigma omega rows hT hDT (by linarith) hshi homega hgap hlogGap hrows hsep
        rw [if_neg hs] at hcost0 ⊢
        exact h.trans (mul_le_mul_of_nonneg_right (by linarith) hcost0)
    calc
      _ ≤ (Cf+Cn)*collarLogCost D (if sigma≤559/560 then 1/280 else 1/560) sigma := hb
      _ ≤ (Cf+Cn)*(64*Real.rpow D ((293/140)*(1-sigma))) :=
        mul_le_mul_of_nonneg_left (hlog sigma omega hshi homega hgap hlogGap') (by linarith)
      _ = _ := by ring
  obtain ⟨D0,hD0⟩ := Filter.eventually_atTop.mp hevent
  refine ⟨64*(Cf+Cn),max 6 D0,by positivity,le_max_left _ _,?_⟩
  intro q _inst T sigma omega rows hT hslo hshi homega hgap hscale hlogGap hrows hsep
  have h := hD0 ((q:ℝ)*T) ((le_max_right 6 D0).trans hscale)
    q T sigma omega rows hT rfl hslo hshi homega hgap hlogGap hrows hsep
  convert h using 1
  norm_num [collarDelta,detectorLogBudget]

end
end MAPJutilaGappedAggregateP53Closed
#print axioms MAPJutilaGappedAggregateP53Closed.jutilaGappedFixedModulusAggregateP53Eventually
