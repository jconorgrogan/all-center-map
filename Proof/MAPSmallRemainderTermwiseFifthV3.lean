import MAPSmallRemainderMassBudgetV3

/-!
# Constructor `/5` field for the literal small-remainder mass

`MAPSmallRemainderMassBudgetV3.exists_small_remainder_budget_thirtieth`
already bounds the genuine `smallRemainderMass` of `MAPHBPerronSourceData`
(not `ordinarySlidingMass`) after a single `H⁻²` factor
`dynamicV3Normalization = d(q)⁴ / (q U²)` with `U = |β| H`.  That
producer yields `/30` of `X (log X)⁻ᴬ`.

This module converts that inequality into the termwise constructor
obligation

```
dynamicV3Normalization p * ∑ smallRemainderMass ≤ budget / 5
```

at `budget = Cred · X · (log X)⁻ᴬ`.  It does not import the full
termwise constructor: the normalization is definitionally the same
formula as
`MAPDynamicHBTermwiseBudgetConstructorV3.dynamicV3Normalization`.

Prime-power equality is retained from Loop 1.  No second `H⁻²` is
applied.  The height range remains Corollary 5.3 `1 ≤ H ≤ X`, hence the
MAP aperture `H ≤ X/2`.
-/

namespace MAPSmallRemainderTermwiseFifthV3

open scoped BigOperators
open MAPMRTCorollary53Source MAPHBPerronSourceData
open MAPSmallRemainderMassBudgetV3

noncomputable section

set_option maxHeartbeats 400000
set_option linter.unusedVariables false

/-! ## Normalization: `H⁻²` once, via `U = |β| H` -/

theorem dynamicV3Normalization_eq_divisor_div_qU2
    (p : Corollary53Input) :
    dynamicV3Normalization p =
      (divisorCount p.q : ℝ) ^ 4 /
        (p.q * stationaryWidth p.beta p.H ^ 2) :=
  rfl

theorem stationaryWidth_eq_abs_mul_H (beta H : ℝ) :
    stationaryWidth beta H = |beta| * H :=
  rfl

/-- One `H⁻²` factor, written as `U⁻²`.  No second copy is applied to
`smallRemainderMass`. -/
theorem dynamicV3Normalization_eq_one_H_inv_sq
    (p : Corollary53Input) :
    dynamicV3Normalization p =
      (divisorCount p.q : ℝ) ^ 4 /
        (p.q * (|p.beta| * p.H) ^ 2) := by
  unfold dynamicV3Normalization stationaryWidth
  rfl

/-! ## Prime-power equality retained from Loop 1 -/

theorem smallRemainderMass_eq_primePower
    {p : Corollary53Input}
    (hf : p.f = mapMangoldtCoeff p.X)
    (hX : 0 ≤ p.X) (heta : 0 < p.eta) (hetaOne : p.eta ≤ 1)
    (component : OuterComponent) :
    smallRemainderMass p component =
      ∑ z ∈ primePowerModulusFactorizations p.q,
        componentIntegral p.X p.H z.1 z.2 p.f p.beta p.eta component :=
  MAPSmallRemainderMassBudgetV3.smallRemainderMass_eq_primePower
    hf hX heta hetaOne component

/-! ## Literal constructor field -/

/-- Left-hand side of `DynamicV3TermwiseBudget.small_remainder`. -/
def constructorSmallRemainderField (p : Corollary53Input) : ℝ :=
  dynamicV3Normalization p *
    ∑ component : OuterComponent, smallRemainderMass p component

theorem constructorSmallRemainderField_eq (p : Corollary53Input) :
    constructorSmallRemainderField p =
      dynamicV3Normalization p *
        ∑ component : OuterComponent, smallRemainderMass p component :=
  rfl

/-! ## `/30` to `/5` arithmetic -/

theorem budget_thirtieth_le_fifth {budget : ℝ} (h0 : 0 ≤ budget) :
    budget / 30 ≤ budget / 5 :=
  div_le_div_of_nonneg_left h0 (by norm_num : (0 : ℝ) < 5)
    (by norm_num : (5 : ℝ) ≤ 30)

/-- `1/30 ≤ Cred/5` follows from `Cred ≥ 1`.  The far-budget existential
`0 < Cred` may be instantiated at `Cred = 1`. -/
theorem thirtieth_scalar_le_cred_fifth
    {X A Cred : ℝ} (hX : 0 ≤ X)
    (hpow : 0 ≤ Real.rpow (Real.log X) (-A))
    (hCred : (1 : ℝ) ≤ Cred) :
    X * Real.rpow (Real.log X) (-A) / 30 ≤
      Cred * X * Real.rpow (Real.log X) (-A) / 5 := by
  have hz : 0 ≤ X * Real.rpow (Real.log X) (-A) :=
    mul_nonneg hX hpow
  have h30to5 : X * Real.rpow (Real.log X) (-A) / 30 ≤
      X * Real.rpow (Real.log X) (-A) / 5 :=
    budget_thirtieth_le_fifth hz
  have hzCred : X * Real.rpow (Real.log X) (-A) ≤
      Cred * (X * Real.rpow (Real.log X) (-A)) := by
    calc
      X * Real.rpow (Real.log X) (-A) =
          (1 : ℝ) * (X * Real.rpow (Real.log X) (-A)) := by ring
      _ ≤ Cred * (X * Real.rpow (Real.log X) (-A)) :=
        mul_le_mul_of_nonneg_right hCred hz
  have hCred5 : X * Real.rpow (Real.log X) (-A) / 5 ≤
      Cred * (X * Real.rpow (Real.log X) (-A)) / 5 :=
    div_le_div_of_nonneg_right hzCred (by norm_num : (0 : ℝ) ≤ 5)
  have hmul : Cred * (X * Real.rpow (Real.log X) (-A)) =
      Cred * X * Real.rpow (Real.log X) (-A) := by ring
  calc
    X * Real.rpow (Real.log X) (-A) / 30 ≤
        X * Real.rpow (Real.log X) (-A) / 5 := h30to5
    _ ≤ Cred * (X * Real.rpow (Real.log X) (-A)) / 5 := hCred5
    _ = Cred * X * Real.rpow (Real.log X) (-A) / 5 := by rw [hmul]

/-- Pointwise filling of `DynamicV3TermwiseBudget.small_remainder` from a
`/30` bound on the same normalized mass. -/
theorem small_remainder_of_thirtieth
    {p : Corollary53Input} {budget : ℝ}
    (h0 : 0 ≤ budget)
    (h : constructorSmallRemainderField p ≤ budget / 30) :
    constructorSmallRemainderField p ≤ budget / 5 :=
  h.trans (budget_thirtieth_le_fifth h0)

theorem small_remainder_of_thirtieth_expanded
    {p : Corollary53Input} {budget : ℝ}
    (h0 : 0 ≤ budget)
    (h : dynamicV3Normalization p *
          (∑ component : OuterComponent, smallRemainderMass p component) ≤
        budget / 30) :
    dynamicV3Normalization p *
      (∑ component : OuterComponent, smallRemainderMass p component) ≤
      budget / 5 :=
  small_remainder_of_thirtieth (p := p) h0 h

/-- Cred-budget form matching `UniformDynamicV3TermwiseFarBudget`. -/
theorem small_remainder_of_unit_thirtieth
    {p : Corollary53Input} {A Cred : ℝ}
    (hCred : 1 ≤ Cred)
    (hX : 0 ≤ p.X)
    (hlog : 0 ≤ Real.rpow (Real.log p.X) (-A))
    (h : dynamicV3Normalization p *
          (∑ component : OuterComponent, smallRemainderMass p component) ≤
        p.X * Real.rpow (Real.log p.X) (-A) / 30) :
    dynamicV3Normalization p *
      (∑ component : OuterComponent, smallRemainderMass p component) ≤
      Cred * p.X * Real.rpow (Real.log p.X) (-A) / 5 :=
  h.trans (thirtieth_scalar_le_cred_fifth hX hlog hCred)

/-! ## Uniform producers, Type-II quantifier order -/

/-- Uniform `/5` producer for `DynamicV3TermwiseBudget.small_remainder`
at budget `X (log X)⁻ᴬ`. -/
theorem exists_small_remainder_termwise_fifth (A : ℝ) :
    ∃ B₀ : ℕ, ∀ B : ℕ, B₀ ≤ B →
      ∃ Cc₀ : ℕ, ∀ Cc : ℕ, Cc₀ ≤ Cc →
        ∃ X₀ : ℝ, 3 ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
          ∀ (p : Corollary53Input) [NeZero p.q]
            (hp : Corollary53Admissible 1 1 p) (hpX : p.X = X)
            (hf : p.f = mapMangoldtCoeff p.X)
            (heta : p.eta = 1 / Real.sqrt ((Real.log p.X) ^ B))
            (hqQ : (p.q : ℝ) ≤ (Real.log p.X) ^ B)
            (hbeta : |p.beta| ≤ 1 / ((p.q : ℝ) * (Real.log p.X) ^ B))
            (hfar : 2 * (Real.log p.X) ^ Cc < stationaryWidth p.beta p.H),
            dynamicV3Normalization p *
              (∑ component : OuterComponent,
                smallRemainderMass p component) ≤
              p.X * Real.rpow (Real.log p.X) (-A) / 5 := by
  obtain ⟨B₀, hB⟩ := exists_small_remainder_budget_thirtieth A
  refine ⟨B₀, ?_⟩
  intro B hB0
  obtain ⟨Cc₀, hCc⟩ := hB B hB0
  refine ⟨Cc₀, ?_⟩
  intro Cc hCc0
  obtain ⟨X₀, hX0, hpt⟩ := hCc Cc hCc0
  refine ⟨X₀, hX0, ?_⟩
  intro X hXle p _inst hp hpX hf heta hqQ hbeta hfar
  have h30 := hpt X hXle p hp hpX hf heta hqQ hbeta hfar
  have hX3 : 3 ≤ p.X := hpX.symm ▸ (hX0.trans hXle)
  have hx : 0 ≤ p.X := le_trans (by norm_num : (0 : ℝ) ≤ 3) hX3
  have hX1 : (1 : ℝ) < p.X := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 3) hX3
  have hlog : 0 < Real.log p.X := Real.log_pos hX1
  have hr : 0 ≤ Real.rpow (Real.log p.X) (-A) :=
    Real.rpow_nonneg hlog.le _
  have hbudget : 0 ≤ p.X * Real.rpow (Real.log p.X) (-A) :=
    mul_nonneg hx hr
  exact small_remainder_of_thirtieth_expanded hbudget h30

/-- Same slot with the existential Cred-budget of
`UniformDynamicV3TermwiseFarBudget`.  Any `Cred ≥ 1` is admissible. -/
theorem exists_small_remainder_termwise_fifth_cred
    (A Cred : ℝ) (hCred : 1 ≤ Cred) :
    ∃ B₀ : ℕ, ∀ B : ℕ, B₀ ≤ B →
      ∃ Cc₀ : ℕ, ∀ Cc : ℕ, Cc₀ ≤ Cc →
        ∃ X₀ : ℝ, 3 ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
          ∀ (p : Corollary53Input) [NeZero p.q]
            (hp : Corollary53Admissible 1 1 p) (hpX : p.X = X)
            (hf : p.f = mapMangoldtCoeff p.X)
            (heta : p.eta = 1 / Real.sqrt ((Real.log p.X) ^ B))
            (hqQ : (p.q : ℝ) ≤ (Real.log p.X) ^ B)
            (hbeta : |p.beta| ≤ 1 / ((p.q : ℝ) * (Real.log p.X) ^ B))
            (hfar : 2 * (Real.log p.X) ^ Cc < stationaryWidth p.beta p.H),
            dynamicV3Normalization p *
              (∑ component : OuterComponent,
                smallRemainderMass p component) ≤
              Cred * p.X * Real.rpow (Real.log p.X) (-A) / 5 := by
  obtain ⟨B₀, hB⟩ := exists_small_remainder_budget_thirtieth A
  refine ⟨B₀, ?_⟩
  intro B hB0
  obtain ⟨Cc₀, hCc⟩ := hB B hB0
  refine ⟨Cc₀, ?_⟩
  intro Cc hCc0
  obtain ⟨X₀, hX0, hpt⟩ := hCc Cc hCc0
  refine ⟨X₀, hX0, ?_⟩
  intro X hXle p _inst hp hpX hf heta hqQ hbeta hfar
  have h30 := hpt X hXle p hp hpX hf heta hqQ hbeta hfar
  have hX3 : 3 ≤ p.X := hpX.symm ▸ (hX0.trans hXle)
  have hx : 0 ≤ p.X := le_trans (by norm_num : (0 : ℝ) ≤ 3) hX3
  have hX1 : (1 : ℝ) < p.X := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 3) hX3
  have hlog : 0 < Real.log p.X := Real.log_pos hX1
  have hr : 0 ≤ Real.rpow (Real.log p.X) (-A) :=
    Real.rpow_nonneg hlog.le _
  exact small_remainder_of_unit_thirtieth hCred hx hr h30

/-- Half-range specialization: the constructor slot remains available
when `H ≤ X/2`, including the MAP base aperture. -/
theorem exists_small_remainder_termwise_fifth_halfRange (A : ℝ) :
    ∃ B₀ : ℕ, ∀ B : ℕ, B₀ ≤ B →
      ∃ Cc₀ : ℕ, ∀ Cc : ℕ, Cc₀ ≤ Cc →
        ∃ X₀ : ℝ, 3 ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
          ∀ (p : Corollary53Input) [NeZero p.q]
            (hp : Corollary53Admissible 1 1 p) (hpX : p.X = X)
            (hf : p.f = mapMangoldtCoeff p.X)
            (hHalf : p.H ≤ p.X / 2)
            (heta : p.eta = 1 / Real.sqrt ((Real.log p.X) ^ B))
            (hqQ : (p.q : ℝ) ≤ (Real.log p.X) ^ B)
            (hbeta : |p.beta| ≤ 1 / ((p.q : ℝ) * (Real.log p.X) ^ B))
            (hfar : 2 * (Real.log p.X) ^ Cc < stationaryWidth p.beta p.H),
            dynamicV3Normalization p *
              (∑ component : OuterComponent,
                smallRemainderMass p component) ≤
              p.X * Real.rpow (Real.log p.X) (-A) / 5 := by
  obtain ⟨B₀, hB⟩ := exists_small_remainder_termwise_fifth A
  refine ⟨B₀, ?_⟩
  intro B hB0
  obtain ⟨Cc₀, hCc⟩ := hB B hB0
  refine ⟨Cc₀, ?_⟩
  intro Cc hCc0
  obtain ⟨X₀, hX0, hpt⟩ := hCc Cc hCc0
  refine ⟨X₀, hX0, ?_⟩
  intro X hXle p _inst hp hpX hf _hHalf heta hqQ hbeta hfar
  exact hpt X hXle p hp hpX hf heta hqQ hbeta hfar

/-- Cred form on the half-range `H ≤ X/2`. -/
theorem exists_small_remainder_termwise_fifth_cred_halfRange
    (A Cred : ℝ) (hCred : 1 ≤ Cred) :
    ∃ B₀ : ℕ, ∀ B : ℕ, B₀ ≤ B →
      ∃ Cc₀ : ℕ, ∀ Cc : ℕ, Cc₀ ≤ Cc →
        ∃ X₀ : ℝ, 3 ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
          ∀ (p : Corollary53Input) [NeZero p.q]
            (hp : Corollary53Admissible 1 1 p) (hpX : p.X = X)
            (hf : p.f = mapMangoldtCoeff p.X)
            (hHalf : p.H ≤ p.X / 2)
            (heta : p.eta = 1 / Real.sqrt ((Real.log p.X) ^ B))
            (hqQ : (p.q : ℝ) ≤ (Real.log p.X) ^ B)
            (hbeta : |p.beta| ≤ 1 / ((p.q : ℝ) * (Real.log p.X) ^ B))
            (hfar : 2 * (Real.log p.X) ^ Cc < stationaryWidth p.beta p.H),
            dynamicV3Normalization p *
              (∑ component : OuterComponent,
                smallRemainderMass p component) ≤
              Cred * p.X * Real.rpow (Real.log p.X) (-A) / 5 := by
  obtain ⟨B₀, hB⟩ := exists_small_remainder_termwise_fifth_cred A Cred hCred
  refine ⟨B₀, ?_⟩
  intro B hB0
  obtain ⟨Cc₀, hCc⟩ := hB B hB0
  refine ⟨Cc₀, ?_⟩
  intro Cc hCc0
  obtain ⟨X₀, hX0, hpt⟩ := hCc Cc hCc0
  refine ⟨X₀, hX0, ?_⟩
  intro X hXle p _inst hp hpX hf _hHalf heta hqQ hbeta hfar
  exact hpt X hXle p hp hpX hf heta hqQ hbeta hfar

end
end MAPSmallRemainderTermwiseFifthV3

#print axioms MAPSmallRemainderTermwiseFifthV3.dynamicV3Normalization_eq_one_H_inv_sq
#print axioms MAPSmallRemainderTermwiseFifthV3.smallRemainderMass_eq_primePower
#print axioms MAPSmallRemainderTermwiseFifthV3.small_remainder_of_thirtieth_expanded
#print axioms MAPSmallRemainderTermwiseFifthV3.small_remainder_of_unit_thirtieth
#print axioms MAPSmallRemainderTermwiseFifthV3.exists_small_remainder_termwise_fifth
#print axioms MAPSmallRemainderTermwiseFifthV3.exists_small_remainder_termwise_fifth_cred
#print axioms MAPSmallRemainderTermwiseFifthV3.exists_small_remainder_termwise_fifth_halfRange
#print axioms MAPSmallRemainderTermwiseFifthV3.exists_small_remainder_termwise_fifth_cred_halfRange
