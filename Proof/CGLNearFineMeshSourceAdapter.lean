import CGLNearFineMesh

/-!
# CGL v2 source adapter for the epsilon-fine near-one compact bridge

This is the source-facing half of `CGLNearFineMesh`.  It extracts one
primitive inducer from the fixed-modulus CGL family, absorbs every conductor
power under `q <= (log X)^K`, and supplies the exact `30/13 + eta` count at
height `X^(tau epsilon)` uniformly from `4/5` through the first Jutila collar
mesh point.

The only analytic premise is `CGLv2Theorem12AllCases`.
-/

namespace MAPCGLNearFineMeshSourceAdapter

open Filter
open CGLMeshFormalization MAPGuthMaynard MAPRelativeNearOneMesh27
open MAPJutilaCollarMeshCutoff MAPAPWeightedZeroMassIntegration
open MAPAPZeroDensityCert
open MAPAPRelativeMeshPrimitiveApplication MAPCGLNearFineMesh
open DirichletZeros

noncomputable section

/-- CGL v2 supplies the primitive-inducer `30/13` count on the whole finite
bridge, with an arbitrarily small fixed loss.  The statement is deliberately
at the MAP height and conductor scale, so no hidden `log T`/`log X`
conversion remains for its consumer. -/
theorem eventually_fixedPrimitiveNearDensity_of_cgl_v2
    (hCGL : CGLv2Theorem12AllCases)
    (K epsilon eta : ℝ)
    (hK : 0 < K) (hepsilon : 0 < epsilon)
    (hepsilonCap : epsilon ≤ 1 / 10) (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ X : ℝ in atTop,
        ∀ (Q : ℕ),
          (Q : ℝ) ≤ Real.rpow (Real.log X) K →
          ∀ sigma : ℝ, 4 / 5 ≤ sigma →
            sigma ≤ relativePoint collarIndex →
            ∀ (r : ℕ) [NeZero r]
              (chi : DirichletCharacter ℂ r),
              chi.IsPrimitive → r ≤ Q →
                (dirichletZeroCount chi sigma
                  (Real.rpow X (tau epsilon)) : ℝ) ≤
                  C * Real.rpow (Real.rpow X (tau epsilon))
                    (densityCoeff * (1 - sigma) + eta) := by
  let sourceEta : ℝ := eta / 4
  let lambda : ℝ := eta / 8
  have hsourceEta : 0 < sourceEta := by
    dsimp [sourceEta]
    positivity
  have hlambda : 0 < lambda := by
    dsimp [lambda]
    positivity
  have htau : 0 < tau epsilon := tau_pos hepsilonCap
  have htauLe : tau epsilon ≤ 1 := by
    unfold tau
    linarith
  obtain ⟨C, Rsource, hC, hRsource, hsource⟩ :=
    hCGL sourceEta hsourceEta
  have hlambdaX : 0 < tau epsilon * lambda := mul_pos htau hlambda
  have hpoly := fixed_polylog_envelopes_eventually_absorbed
    K sourceEta (tau epsilon * lambda) hlambdaX
  have hXlarge : ∀ᶠ X : ℝ in atTop,
      Real.exp 1 ≤ X := eventually_ge_atTop (Real.exp 1)
  have hheight : ∀ᶠ X : ℝ in atTop,
      Rsource ≤ Real.rpow X (tau epsilon) := by
    exact (tendsto_rpow_atTop htau).eventually (eventually_ge_atTop Rsource)
  refine ⟨2 * C, by positivity, ?_⟩
  filter_upwards [hpoly, hXlarge, hheight] with X hpolyX hXlargeX hheightX
  intro Q hQ sigma hsigmaLow hsigmaHigh r _inst chi _hprim hrQ
  have hXpos : 0 < X := (Real.exp_pos 1).trans_le hXlargeX
  have hXone : 1 ≤ X :=
    (Real.one_le_exp zero_le_one).trans hXlargeX
  have hlog : 1 ≤ Real.log X := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hXlargeX
  have hTone : 1 ≤ Real.rpow X (tau epsilon) :=
    Real.one_le_rpow hXone htau.le
  have hrpoly : (r : ℝ) ≤ Real.rpow (Real.log X) K := by
    exact (by exact_mod_cast hrQ : (r : ℝ) ≤ (Q : ℝ)) |>.trans hQ
  have hsigmaHalf : 1 / 2 ≤ sigma := by linarith
  have hsigmaOne : sigma ≤ 1 :=
    hsigmaHigh.trans (relativePoint_le_one collarIndex)
  obtain ⟨hqEtaX, hqFirstX, hqSecondX⟩ :=
    polylog_conductor_powers_fit hK.le hsourceEta.le hlog hrpoly
      hsigmaHalf hsigmaOne hpolyX.1 hpolyX.2.1 hpolyX.2.2
  have hpowRewrite : Real.rpow X (tau epsilon * lambda) =
      Real.rpow (Real.rpow X (tau epsilon)) lambda := by
    exact Real.rpow_mul hXpos.le _ _
  have hqEta : Real.rpow (r : ℝ) sourceEta ≤
      Real.rpow (Real.rpow X (tau epsilon)) lambda := by
    simpa only [hpowRewrite] using hqEtaX
  have hqFirst : Real.rpow (r : ℝ) ((7 / 3) * (1 - sigma)) ≤
      Real.rpow (Real.rpow X (tau epsilon)) lambda := by
    simpa only [hpowRewrite] using hqFirstX
  have hqSecond : Real.rpow (r : ℝ)
      (densityCoeff * (1 - sigma)) ≤
      Real.rpow (Real.rpow X (tau epsilon)) lambda := by
    simpa only [hpowRewrite] using hqSecondX
  have hscale : Rsource ≤ (r : ℝ) * Real.rpow X (tau epsilon) := by
    have hrone : (1 : ℝ) ≤ r := by
      exact_mod_cast (NeZero.one_le : 1 ≤ r)
    calc
      Rsource ≤ Real.rpow X (tau epsilon) := hheightX
      _ = 1 * Real.rpow X (tau epsilon) := by ring
      _ ≤ (r : ℝ) * Real.rpow X (tau epsilon) :=
        mul_le_mul_of_nonneg_right hrone
          (Real.rpow_nonneg hXpos.le _)
  have hsigmaLt : sigma < 1 := by
    have hdist := relativeDistance_pos collarIndex
    unfold relativePoint at hsigmaHigh
    linarith
  have hraw := hsource r (Real.rpow X (tau epsilon)) sigma
    hTone (by linarith) hsigmaLt hscale
  have hsingleNat :=
    dirichletZeroCount_le_ambientZeroCountAtLevel chi sigma
      (Real.rpow X (tau epsilon))
  have hsingle :
      (dirichletZeroCount chi sigma (Real.rpow X (tau epsilon)) : ℝ) ≤
        (ambientZeroCountAtLevel r sigma
          (Real.rpow X (tau epsilon)) : ℝ) := by
    exact_mod_cast hsingleNat
  apply cgl_source_formula_to_fixed_thirty_thirteen
    hTone hC.le hsigmaOne hqEta hqFirst hqSecond
    (targetEta := eta)
  · dsimp [sourceEta, lambda]
    linarith
  · exact hsingle.trans hraw

/-! ## Literal primitive compact-bridge mass -/

/-- The part of one primitive inducer's regular near-one mass lying at or
left of the first Jutila collar mesh point. -/
def primitiveRegularCompactBridgeMass {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (X T : ℝ) : ℝ := by
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  let psi := chi.primitiveCharacter
  exact ∑ rho ∈ (zeroSupport psi 0 T).filter (fun rho =>
      (4 / 5 < rho.re ∧
        ¬ (psi ≠ 1 ∧ psi ^ 2 = 1 ∧ rho.im = 0)) ∧
      rho.re ≤ relativePoint collarIndex),
    (zeroMultiplicity psi 0 T rho : ℝ) *
      Real.rpow X (2 * (rho.re - 1))

/-- The exact finite CGL mesh bounds the literal compact-bridge mass of one
primitive inducer. -/
theorem primitiveRegularCompactBridgeMass_le_of_density
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {epsilon eta X C : ℝ}
    (hepsilon : 0 < epsilon) (hepsilonCap : epsilon ≤ 1 / 10)
    (heta0 : 0 ≤ eta) (heta : eta ≤ epsilon / 2000)
    (hX : 1 ≤ X) (hC : 0 ≤ C)
    (hdensity : ∀ sigma : ℝ, 4 / 5 ≤ sigma →
      sigma ≤ relativePoint collarIndex →
        (primitiveDirichletZeroCount chi sigma
          (Real.rpow X (tau epsilon)) : ℝ) ≤
          C * Real.rpow (Real.rpow X (tau epsilon))
            (densityCoeff * (1 - sigma) + eta)) :
    primitiveRegularCompactBridgeMass chi X
        (Real.rpow X (tau epsilon)) ≤
      (fineCellCount epsilon : ℝ) *
        (C * Real.rpow X (-(epsilon / 400))) := by
  classical
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  let psi := chi.primitiveCharacter
  let S := (zeroSupport psi 0 (Real.rpow X (tau epsilon))).filter
    (fun rho =>
      (4 / 5 < rho.re ∧
        ¬ (psi ≠ 1 ∧ psi ^ 2 = 1 ∧ rho.im = 0)) ∧
      rho.re ≤ relativePoint collarIndex)
  have hmesh := fineCompactMass_le_card_mul
    S (fun rho => zeroMultiplicity psi 0 (Real.rpow X (tau epsilon)) rho)
    Complex.re hepsilon hepsilonCap
    (by
      intro rho hrho
      exact (Finset.mem_filter.mp hrho).2.1.1)
    (by
      intro rho hrho
      exact (Finset.mem_filter.mp hrho).2.2)
    heta0 heta hX hC
  apply (show primitiveRegularCompactBridgeMass chi X
      (Real.rpow X (tau epsilon)) =
        ∑ rho ∈ S,
          (zeroMultiplicity psi 0 (Real.rpow X (tau epsilon)) rho : ℝ) *
            Real.rpow X (2 * (rho.re - 1)) by
      rfl) |>.trans_le
  apply hmesh
  intro j hj
  have hpointLow : 4 / 5 ≤ finePoint epsilon j := by
    dsimp [finePoint]
    exact le_add_of_nonneg_right
      (mul_nonneg (Nat.cast_nonneg j) (fineDelta_pos hepsilon).le)
  have hpointHigh := finePoint_cellCount_left_le_collar hepsilon hj
  have hcount :
      ((∑ rho ∈ S.filter
          (fun rho => finePoint epsilon j ≤ rho.re),
          zeroMultiplicity psi 0 (Real.rpow X (tau epsilon)) rho : ℕ) : ℝ) ≤
        (primitiveDirichletZeroCount chi (finePoint epsilon j)
          (Real.rpow X (tau epsilon)) : ℝ) := by
    have hnat :
        (∑ rho ∈ S.filter
            (fun rho => finePoint epsilon j ≤ rho.re),
            zeroMultiplicity psi 0 (Real.rpow X (tau epsilon)) rho : ℕ) ≤
          primitiveDirichletZeroCount chi (finePoint epsilon j)
            (Real.rpow X (tau epsilon)) := by
      apply fullSubsupportMultiplicity_le_primitiveCount chi
      · intro rho hrho
        exact (Finset.mem_filter.mp (Finset.mem_filter.mp hrho).1).1
      · intro rho hrho
        exact (Finset.mem_filter.mp hrho).2
    exact_mod_cast hnat
  exact hcount.trans (hdensity (finePoint epsilon j)
    hpointLow hpointHigh)

end
end MAPCGLNearFineMeshSourceAdapter

#print axioms MAPCGLNearFineMeshSourceAdapter.eventually_fixedPrimitiveNearDensity_of_cgl_v2
#print axioms MAPCGLNearFineMeshSourceAdapter.primitiveRegularCompactBridgeMass_le_of_density
