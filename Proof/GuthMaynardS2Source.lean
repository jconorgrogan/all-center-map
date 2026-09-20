import GuthMaynardSourceLemmas
import FixedCharacterPoweredBridge

/-!
# The Guth--Maynard `S₂` branch below Theorem 1.1

This file follows Section 6 and the two `S₂` terms in equation (12.1) of
Guth--Maynard, *New large value estimates for Dirichlet polynomials*.

The source uses an arbitrary integer `k`.  For the range needed in
Proposition 3.1, `k = 2` already suffices.  Keeping this smaller power matters
for the CGL detector: it shows that the `S₂` branch does not cause the
critical `3/130` deficit and does not need the full `k = 4` chosen for the
paper's final display.

The finite Holder step (6.2) is proved below.  After it, the two genuinely
analytic inputs in the literal source are exactly:

* Lemma 6.2, the reflection/approximate-functional-equation bound for
  `sum_{m != 0} Fourier(h_t)(mN)` (pp. 16--20);
* Heath--Brown's difference-set mean square, quoted as Theorem 1.6 and used
  in (6.3) (pp. 4 and 18--19).

No detector-specific property removes either input: Section 6 is downstream
of the arbitrary coefficient having already disappeared into the trace.
-/

namespace GuthMaynardS2Source

open scoped BigOperators

noncomputable section

/-! ## The actual finite Holder step at `k = 2` -/

/-- The squared `k = 2` instance of Guth--Maynard (6.2).  Applying this to
the pair index set `W x W` and to the norm of the length-`M` polynomial gives
the factor `|W|^2` on the right, hence `|W|` after taking square roots.

This is a theorem about the literal finite sum, not a proposition-valued
placeholder for the analytic estimate (6.3). -/
theorem holder_kTwo_squared
    {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    (∑ i ∈ s, ‖f i‖ ^ 2) ^ 2 ≤
      (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 4 := by
  calc
    (∑ i ∈ s, ‖f i‖ ^ 2) ^ 2 ≤
        (s.card : ℝ) * ∑ i ∈ s, (‖f i‖ ^ 2) ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    _ = (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 4 := by
      apply congrArg (fun x : ℝ => (s.card : ℝ) * x)
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- Pair specialization of `holder_kTwo_squared`.  This is the exact
cardinality normalization behind the `|W|^(2-2/k)` factor in (6.2) when
`k = 2`. -/
theorem holder_kTwo_pair_squared
    {ι : Type*} (W : Finset ι) (F : ι → ι → ℂ) :
    (∑ x ∈ W, ∑ y ∈ W, ‖F x y‖ ^ 2) ^ 2 ≤
      (W.card : ℝ) ^ 2 * ∑ x ∈ W, ∑ y ∈ W, ‖F x y‖ ^ 4 := by
  let P : Finset (ι × ι) := W ×ˢ W
  have h := holder_kTwo_squared P (fun p => F p.1 p.2)
  simpa [P, Finset.sum_product, pow_two] using h

/-! ## Exact `S₂` exponents after (12.1) -/

/-- The first `S₂` exponent in (12.1), after `k = 2` and `T = N^(6/5)`:
`T^(2/3) N^((4-6σ)2/3)`. -/
def firstS2Exponent (σ : ℝ) : ℝ :=
  (6 / 5 : ℝ) * (2 / 3) + (4 - 6 * σ) * (2 / 3)

/-- The second `S₂` exponent in (12.1), after `k = 2` and `T = N^(6/5)`:
`N^((5-6σ)8/11) T^(2/11)`. -/
def secondS2Exponent (σ : ℝ) : ℝ :=
  (5 - 6 * σ) * (8 / 11) + (6 / 5 : ℝ) * (2 / 11)

/-- Proposition 3.1's target exponent after `T = N^(6/5)`. -/
def targetExponent (σ : ℝ) : ℝ :=
  (18 - 20 * σ) / 5

/-- The first `S₂` term has a uniform `2/15` exponent reserve. -/
theorem target_sub_firstS2Exponent (σ : ℝ) :
    targetExponent σ - firstS2Exponent σ = 2 / 15 := by
  simp [targetExponent, firstS2Exponent]
  ring

/-- The second `S₂` term meets the target exactly at `σ = 7/10` and has
strict reserve above that endpoint. -/
theorem target_sub_secondS2Exponent (σ : ℝ) :
    targetExponent σ - secondS2Exponent σ =
      (4 / 11) * (σ - 7 / 10) := by
  simp [targetExponent, secondS2Exponent]
  ring

/-- Thus `k = 2` controls both `S₂` terms throughout the exact range of
Guth--Maynard Proposition 3.1. -/
theorem kTwo_s2_exponents_le_target
    {σ : ℝ} (hσ : 7 / 10 ≤ σ) :
    firstS2Exponent σ ≤ targetExponent σ ∧
      secondS2Exponent σ ≤ targetExponent σ := by
  constructor
  · rw [← sub_nonneg]
    rw [target_sub_firstS2Exponent]
    norm_num
  · rw [← sub_nonneg]
    rw [target_sub_secondS2Exponent]
    positivity

/-- Constant-sensitive insertion of just the two `S₂` powers into the
Proposition 3.1 target.  This is their exact contribution to the finite
post-(12.1) sum when `k = 2`. -/
theorem kTwo_s2_rpow_sum_le_two_target
    {N σ : ℝ} (hN : 1 ≤ N) (hσ : 7 / 10 ≤ σ) :
    Real.rpow N (firstS2Exponent σ) +
        Real.rpow N (secondS2Exponent σ) ≤
      2 * Real.rpow N (targetExponent σ) := by
  obtain ⟨hfirst, hsecond⟩ := kTwo_s2_exponents_le_target hσ
  have h1 := Real.rpow_le_rpow_of_exponent_le hN hfirst
  have h2 := Real.rpow_le_rpow_of_exponent_le hN hsecond
  calc
    Real.rpow N (firstS2Exponent σ) +
        Real.rpow N (secondS2Exponent σ) ≤
      Real.rpow N (targetExponent σ) +
        Real.rpow N (targetExponent σ) := add_le_add h1 h2
    _ = 2 * Real.rpow N (targetExponent σ) := by ring

/-- At the detector-critical point `σ = 3/4`, the second (closer) `S₂` term
still has reserve `1/55`. -/
theorem critical_secondS2_reserve :
    targetExponent (3 / 4) - secondS2Exponent (3 / 4) = 1 / 55 := by
  norm_num [targetExponent, secondS2Exponent]

/-! ## Clean death tests for cheaper substitutes -/

/-- Using only `k = 1` in the second `S₂` term misses the target at the
critical point by exactly `1/35`.  Some nontrivial difference-set input is
therefore required even though `k = 4` is unnecessary. -/
theorem kOne_secondS2_critical_excess :
    ((5 - 6 * (3 / 4 : ℝ)) * (4 / 7) + (6 / 5 : ℝ) * (2 / 7)) -
      targetExponent (3 / 4) = 1 / 35 := by
  norm_num [targetExponent]

/-- A direct application of the ordinary one-separated mean-square theorem
after the `k = 2` Holder step produces
`T^(1/3) N^((10-12σ)/3)`.  At the critical point this is too large by
`2/15`.  Thus the already certified ordinary discrete mean square cannot
replace Heath--Brown's difference-set estimate in this branch. -/
theorem ordinary_meanSquare_kTwo_critical_excess :
    ((6 / 5 : ℝ) * (1 / 3) + (10 - 12 * (3 / 4)) / 3) -
      targetExponent (3 / 4) = 2 / 15 := by
  norm_num [targetExponent]

/-- Replacing Heath--Brown (6.3) by the completely trivial pair bound gives
the exponent `T N^(4-6σ)`, which misses the critical target by `1/10` after
`T = N^(6/5)`. -/
theorem trivial_pair_bound_critical_excess :
    ((6 / 5 : ℝ) + 4 - 6 * (3 / 4)) - targetExponent (3 / 4) = 1 / 10 := by
  norm_num [targetExponent]

end

end GuthMaynardS2Source

#print axioms GuthMaynardS2Source.holder_kTwo_squared
#print axioms GuthMaynardS2Source.holder_kTwo_pair_squared
#print axioms GuthMaynardS2Source.kTwo_s2_exponents_le_target
#print axioms GuthMaynardS2Source.kTwo_s2_rpow_sum_le_two_target
#print axioms GuthMaynardS2Source.critical_secondS2_reserve
#print axioms GuthMaynardS2Source.kOne_secondS2_critical_excess
#print axioms GuthMaynardS2Source.ordinary_meanSquare_kTwo_critical_excess
#print axioms GuthMaynardS2Source.trivial_pair_bound_critical_excess
