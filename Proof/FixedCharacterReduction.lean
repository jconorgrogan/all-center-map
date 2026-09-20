import CGLPoweredToUniformDensity
import CGLMeshFormalization

/-!
# Fixed-character to polylogarithmic-family reduction

This file isolates the genuinely cheap part of the proposed CGL bypass.  A
uniform density estimate for one primitive character may be applied to the
primitive inducer of every ambient character.  The entire family then costs
at most `Q^2`, which is absorbed by half of the epsilon loss when `Q` is
polylogarithmic.

No zero-density estimate is asserted here.  The fixed-primitive estimate is a
local hypothesis of the reduction theorem.
-/

namespace CGLPolylogBypass

open scoped BigOperators
open DirichletZeros ZeroDensityInterface MAPAPZeroDensityCert
open MAPGuthMaynard

noncomputable section

/-- The two fixed-character source curves used on opposite sides of the
Guth--Maynard/Ingham junction. -/
def fixedCharacterCoefficient (sigma : ℝ) : ℝ :=
  if sigma ≤ 7 / 10 then 3 / (2 - sigma) else 15 / (3 + 5 * sigma)

/-- The source curves meet the required `30/13` envelope exactly at
`sigma = 7/10` and cover every MAP compact-strip mesh point. -/
theorem fixedCharacterCoefficient_le_densityCoeff
    {sigma : ℝ} :
    fixedCharacterCoefficient sigma ≤ densityCoeff := by
  by_cases hsplit : sigma ≤ 7 / 10
  · rw [fixedCharacterCoefficient, if_pos hsplit, densityCoeff]
    exact (CGLProofDAG.montgomery_reaches_thirty_thirteenths_iff
      (by linarith)).2 hsplit
  · rw [fixedCharacterCoefficient, if_neg hsplit, densityCoeff]
    have hlow : 7 / 10 ≤ sigma := le_of_not_ge hsplit
    simpa [AppendixTypeIPower.gmCoefficient] using
      (AppendixTypeIPower.gmCoefficient_le_uniformCoeff hlow)

/-- Direct exponent check for every manuscript mesh left endpoint.  It
retains the exact `3 epsilon / 52` reserve without the first CGL hybrid term.
-/
theorem fixed_character_curve_cell_exponent_bound
    {epsilon sigma Delta : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon_le : epsilon ≤ 1 / 10)
    (hsigma_high : sigma ≤ 4 / 5)
    (hDelta : Delta ≤ 3 * epsilon / 52) :
    tau epsilon *
          (fixedCharacterCoefficient sigma * (1 - sigma) + etaZD epsilon) +
        2 * (sigma + Delta - 1) ≤
      -(3 * epsilon / 52) := by
  have htau : 0 ≤ tau epsilon := (tau_pos hepsilon_le).le
  have hone : 0 ≤ 1 - sigma := by linarith
  have hcoeff := fixedCharacterCoefficient_le_densityCoeff (sigma := sigma)
  have hcurve :
      fixedCharacterCoefficient sigma * (1 - sigma) + etaZD epsilon ≤
        densityCoeff * (1 - sigma) + etaZD epsilon := by
    exact add_le_add (mul_le_mul_of_nonneg_right hcoeff hone) le_rfl
  calc
    tau epsilon *
          (fixedCharacterCoefficient sigma * (1 - sigma) + etaZD epsilon) +
        2 * (sigma + Delta - 1) ≤
      tau epsilon * (densityCoeff * (1 - sigma) + etaZD epsilon) +
        2 * (sigma + Delta - 1) := by
          exact add_le_add (mul_le_mul_of_nonneg_left hcurve htau) le_rfl
    _ ≤ -(3 * epsilon / 52) :=
      paper_cell_exponent_bound hepsilon hepsilon_le hsigma_high hDelta

/-- There are at most `Q^2` ambient character/modulus pairs at positive
levels at most `Q`. -/
theorem sum_card_dirichletCharacters_Icc_le_sq (Q : ℕ) :
    ∑ q ∈ Finset.Icc 1 Q, Nat.card (DirichletCharacter ℂ q) ≤ Q ^ 2 := by
  calc
    ∑ q ∈ Finset.Icc 1 Q, Nat.card (DirichletCharacter ℂ q) ≤
        ∑ _q ∈ Finset.Icc 1 Q, Q := by
      apply Finset.sum_le_sum
      intro q hq
      have hq0 : q ≠ 0 := by
        have : 1 ≤ q := (Finset.mem_Icc.mp hq).1
        omega
      letI : NeZero q := ⟨hq0⟩
      calc
        Nat.card (DirichletCharacter ℂ q) = q.totient :=
          DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
        _ ≤ q := Nat.totient_le q
        _ ≤ Q := (Finset.mem_Icc.mp hq).2
    _ = (Finset.Icc 1 Q).card * Q := by simp
    _ ≤ Q * Q := by
      gcongr
      simp
    _ = Q ^ 2 := by ring

/-- Summing a common bound for every primitive inducer costs only `Q^2`.

The hypothesis is stated at the actual conductor and requires primitivity;
thus the conclusion is not obtained by silently assuming a theorem for
ambient characters. -/
theorem fixed_primitive_bound_to_family
    {Q : ℕ} {T sigma B : ℝ} (hB : 0 ≤ B)
    (hfixed : ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r),
      χ.IsPrimitive → r ≤ Q →
        (dirichletZeroCount χ sigma T : ℝ) ≤ B) :
    (polylogFamilyZeroCount Q sigma T : ℝ) ≤ (Q : ℝ) ^ 2 * B := by
  classical
  unfold polylogFamilyZeroCount
  push_cast
  calc
    (∑ q ∈ Finset.Icc 1 Q, (zeroCountAtLevel q sigma T : ℝ)) ≤
        ∑ q ∈ Finset.Icc 1 Q,
          (Nat.card (DirichletCharacter ℂ q) : ℝ) * B := by
      apply Finset.sum_le_sum
      intro q hq
      have hq0 : q ≠ 0 := by
        have : 1 ≤ q := (Finset.mem_Icc.mp hq).1
        omega
      letI : NeZero q := ⟨hq0⟩
      rw [zeroCountAtLevel_eq]
      push_cast
      calc
        (∑ χ : DirichletCharacter ℂ q,
            (primitiveDirichletZeroCount χ sigma T : ℝ)) ≤
            ∑ _χ : DirichletCharacter ℂ q, B := by
          apply Finset.sum_le_sum
          intro χ _
          letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
          simpa only [primitiveDirichletZeroCount] using
            hfixed χ.conductor χ.primitiveCharacter
              χ.primitiveCharacter_isPrimitive
              ((conductor_le_level χ).trans (Finset.mem_Icc.mp hq).2)
        _ = (Nat.card (DirichletCharacter ℂ q) : ℝ) * B := by
          simp [Nat.card_eq_fintype_card]
    _ = ((∑ q ∈ Finset.Icc 1 Q,
          Nat.card (DirichletCharacter ℂ q) : ℕ) : ℝ) * B := by
      push_cast
      rw [Finset.sum_mul]
    _ ≤ (Q : ℝ) ^ 2 * B := by
      apply mul_le_mul_of_nonneg_right _ hB
      exact_mod_cast sum_card_dirichletCharacters_Icc_le_sq Q

/-- The exact loss allocation used by the bypass: half of `eta` is spent on
the individual analytic theorem and half absorbs the polylogarithmic family.
-/
theorem fixed_primitive_thirty_thirteen_to_polylog_family
    {Q : ℕ} {T sigma eta C : ℝ}
    (hT : 1 ≤ T) (hC : 0 ≤ C)
    (hQloss : (Q : ℝ) ^ 2 ≤ Real.rpow T (eta / 2))
    (hfixed : ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r),
      χ.IsPrimitive → r ≤ Q →
        (dirichletZeroCount χ sigma T : ℝ) ≤
          C * Real.rpow T
            (densityCoeff * (1 - sigma) + eta / 2)) :
    (polylogFamilyZeroCount Q sigma T : ℝ) ≤
      C * Real.rpow T (densityCoeff * (1 - sigma) + eta) := by
  have hB : 0 ≤ C * Real.rpow T
      (densityCoeff * (1 - sigma) + eta / 2) :=
    mul_nonneg hC (Real.rpow_nonneg (zero_le_one.trans hT) _)
  have hfamily := fixed_primitive_bound_to_family hB hfixed
  calc
    (polylogFamilyZeroCount Q sigma T : ℝ) ≤
        (Q : ℝ) ^ 2 *
          (C * Real.rpow T
            (densityCoeff * (1 - sigma) + eta / 2)) := hfamily
    _ ≤ Real.rpow T (eta / 2) *
          (C * Real.rpow T
            (densityCoeff * (1 - sigma) + eta / 2)) := by
      exact mul_le_mul_of_nonneg_right hQloss hB
    _ = C * Real.rpow T (densityCoeff * (1 - sigma) + eta) := by
      have hTpos : 0 < T := zero_lt_one.trans_le hT
      calc
        Real.rpow T (eta / 2) *
            (C * Real.rpow T
              (densityCoeff * (1 - sigma) + eta / 2)) =
            C * (Real.rpow T (eta / 2) *
              Real.rpow T (densityCoeff * (1 - sigma) + eta / 2)) := by
                ring
        _ = C * Real.rpow T
              (eta / 2 + (densityCoeff * (1 - sigma) + eta / 2)) := by
                exact congrArg (fun z : ℝ => C * z)
                  (Real.rpow_add hTpos (eta / 2)
                    (densityCoeff * (1 - sigma) + eta / 2)).symm
        _ = C * Real.rpow T (densityCoeff * (1 - sigma) + eta) := by
                congr 2
                ring

/-- The smallest reusable analytic boundary for the bypass.  Unlike the CGL
all-cases proposition, it asks only for the primitive, fixed-character
`30/13` estimate in the compact strip and only at polylogarithmic conductor.
-/
def FixedPrimitivePolylogDensity : Prop :=
  ∀ K delta eta : ℝ, 0 < K → 0 < delta → 0 < eta →
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (T : ℝ) (Q : ℕ) (sigma : ℝ), T₀ ≤ T →
        (Q : ℝ) ≤ Real.rpow (Real.log T) K →
        1 / 2 + delta ≤ sigma → sigma ≤ 4 / 5 →
        ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r),
          χ.IsPrimitive → r ≤ Q →
            (dirichletZeroCount χ sigma T : ℝ) ≤
              C * Real.rpow T
                (densityCoeff * (1 - sigma) + eta)

/-- The fixed-character boundary implies the exact primitive-inducer family
proposition already consumed by the MAP development.  This theorem performs
both missing finite steps: summing all levels/characters and absorbing the
resulting `Q^2` into the remaining half-loss. -/
theorem fixedPrimitivePolylogDensity_to_project_target
    (hfixed : FixedPrimitivePolylogDensity) :
    PolylogConductorDensity := by
  intro K delta eta hK hdelta heta
  obtain ⟨C, Tsource, hC, hTsource, hsource⟩ :=
    hfixed K delta (eta / 2) hK hdelta (half_pos heta)
  have hpoly := ZeroDensityArithmetic.polylog_absorption
    (2 * K) (eta / 2) (half_pos heta)
  obtain ⟨Tpoly, hTpoly⟩ := Filter.eventually_atTop.1 hpoly
  let T₀ := max Tsource (max Tpoly 2)
  refine ⟨C, T₀, hC, ?_, ?_⟩
  · exact (le_max_right Tpoly 2).trans
      (le_max_right Tsource (max Tpoly 2))
  intro T Q sigma hT hQ hsigma_low hsigma_high
  have hTsource' : Tsource ≤ T := (le_max_left _ _).trans hT
  have hTpoly' : Tpoly ≤ T :=
    (le_trans (le_max_left Tpoly 2) (le_max_right Tsource (max Tpoly 2))).trans hT
  have hTtwo : 2 ≤ T :=
    (le_trans (le_max_right Tpoly 2) (le_max_right Tsource (max Tpoly 2))).trans hT
  have hlogpos : 0 < Real.log T := Real.log_pos (by linarith)
  have hQnonneg : 0 ≤ (Q : ℝ) := Nat.cast_nonneg Q
  have hQloss : (Q : ℝ) ^ 2 ≤ Real.rpow T (eta / 2) := by
    calc
      (Q : ℝ) ^ 2 ≤ (Real.rpow (Real.log T) K) ^ 2 := by
        have hbase : 0 ≤ Real.rpow (Real.log T) K :=
          Real.rpow_nonneg hlogpos.le K
        nlinarith [sq_nonneg
          ((Q : ℝ) + Real.rpow (Real.log T) K)]
      _ = Real.rpow (Real.log T) (2 * K) := by
        calc
          (Real.rpow (Real.log T) K) ^ 2 =
              Real.rpow (Real.log T) K * Real.rpow (Real.log T) K :=
                pow_two _
          _ = Real.rpow (Real.log T) (K + K) :=
                (Real.rpow_add hlogpos K K).symm
          _ = Real.rpow (Real.log T) (2 * K) := by
                congr 1
                ring
      _ ≤ Real.rpow T (eta / 2) := hTpoly T hTpoly'
  have hsource' :
      ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r),
        χ.IsPrimitive → r ≤ Q →
          (dirichletZeroCount χ sigma T : ℝ) ≤
            C * Real.rpow T
              (densityCoeff * (1 - sigma) + eta / 2) :=
    hsource T Q sigma hTsource' hQ hsigma_low hsigma_high
  have hfamily := fixed_primitive_thirty_thirteen_to_polylog_family
    (by linarith : 1 ≤ T) hC.le hQloss hsource'
  simpa [ZeroDensityArithmetic.uniformCoeff, densityCoeff] using hfamily

/-- Once the individual fixed-character theorem has been summed, the exact
paper mesh saving follows with no CGL first hybrid term. -/
theorem fixed_primitive_density_implies_map_cell_saving
    {Q : ℕ} {epsilon sigma Delta eta X C : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon_le : epsilon ≤ 1 / 10)
    (hsigma_high : sigma ≤ 4 / 5)
    (hDelta : Delta ≤ 3 * epsilon / 52)
    (hX : 1 ≤ X) (hC : 0 ≤ C)
    (hQloss : (Q : ℝ) ^ 2 ≤
      Real.rpow (Real.rpow X (tau epsilon)) (eta / 2))
    (hfixed : ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r),
      χ.IsPrimitive → r ≤ Q →
        (dirichletZeroCount χ sigma (Real.rpow X (tau epsilon)) : ℝ) ≤
          C * Real.rpow (Real.rpow X (tau epsilon))
            (densityCoeff * (1 - sigma) + eta / 2))
    (heta_budget : eta ≤ etaZD epsilon) :
    (polylogFamilyZeroCount Q sigma (Real.rpow X (tau epsilon)) : ℝ) *
        Real.rpow X (2 * (sigma + Delta - 1)) ≤
      C * Real.rpow X (-(3 * epsilon / 52)) := by
  have htau : 0 < tau epsilon := tau_pos hepsilon_le
  have hT : 1 ≤ Real.rpow X (tau epsilon) := by
    exact Real.one_le_rpow hX htau.le
  have hfamily := fixed_primitive_thirty_thirteen_to_polylog_family
    hT hC hQloss hfixed
  have hetaexp :
      densityCoeff * (1 - sigma) + eta ≤
        densityCoeff * (1 - sigma) + etaZD epsilon := by linarith
  have hfamily' :
      (polylogFamilyZeroCount Q sigma (Real.rpow X (tau epsilon)) : ℝ) ≤
        C * Real.rpow (Real.rpow X (tau epsilon))
          (densityCoeff * (1 - sigma) + etaZD epsilon) := by
    exact hfamily.trans <| mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hT hetaexp) hC
  exact densityAtHeight_mul_weight_le hepsilon hepsilon_le hsigma_high
    hDelta hX hC hfamily'

end
end CGLPolylogBypass

#print axioms CGLPolylogBypass.fixed_primitive_bound_to_family
#print axioms CGLPolylogBypass.fixed_primitive_thirty_thirteen_to_polylog_family
#print axioms CGLPolylogBypass.fixedPrimitivePolylogDensity_to_project_target
#print axioms CGLPolylogBypass.fixed_primitive_density_implies_map_cell_saving
#print axioms CGLPolylogBypass.fixed_character_curve_cell_exponent_bound
