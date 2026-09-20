import MontgomeryLowStripBridge
import MontgomeryNeededLowStripBridge

/-!
# Montgomery Theorem 12.1: exact parameter and endpoint audit

Primary source: H. L. Montgomery, *Topics in Multiplicative Number Theory*,
Lecture Notes in Mathematics 227, Springer (1971), Theorem 12.1, pp. 98 and
103--110.  Equation (12.9) is the fixed-modulus all-character estimate

`sum_(chi mod q) N(sigma,T,chi)
  << (q*T)^(3*(1-sigma)/(2-sigma)) * log(q*T)^9`

for `q >= 1`, `T >= 2`, and the closed strip
`1/2 <= sigma <= 4/5`.  The proof thins ordinates with (12.27)--(12.28),
uses Theorems 7.6 and 8.3 and Corollary 10.4 in the two detector branches,
and combines (12.28), (12.33), and (12.39) on p. 110.

The p. 110 choice is

`X = (q*T)^(1/2)`,
`Y = (q*T)^(3/(2*(2-sigma)))`.

This file certifies the complete parameter algebra, legal source range, and
the exact failure of the old curve to cover MAP's conductor-one high strip.
It deliberately does not package the unformalized combination of
(12.28), (12.33), and (12.39) as a theorem or axiom.
-/

namespace MAPMontgomeryTheorem12SourceDAG

open MAPMontgomeryLowStrip ZeroDensityArithmetic
open DirichletZeros MAPAPZeroDensityCert

noncomputable section

/-- Product carrying both modulus and symmetric zero height in Theorem 12.1. -/
def sourceScale (q : ℕ) (T : ℝ) : ℝ := (q : ℝ) * T

/-- Montgomery's p. 110 mollifier cutoff `X`. -/
def sourceX (q : ℕ) (T : ℝ) : ℝ :=
  Real.rpow (sourceScale q T) (1 / 2)

/-- Montgomery's p. 110 detector cutoff `Y` for equation (12.9). -/
def sourceY (q : ℕ) (T sigma : ℝ) : ℝ :=
  Real.rpow (sourceScale q T) (3 / (2 * (2 - sigma)))

theorem sourceScale_pos {q : ℕ} [NeZero q] {T : ℝ} (hT : 0 < T) :
    0 < sourceScale q T := by
  unfold sourceScale
  exact mul_pos (by exact_mod_cast NeZero.pos q) hT

/-- The detector exponent lies in the exact interval `[1,5/4]` on the
published low strip. -/
theorem sourceY_exponent_mem
    {sigma : ℝ} (hsigmaLow : 1 / 2 ≤ sigma)
    (hsigmaHigh : sigma ≤ 4 / 5) :
    1 ≤ 3 / (2 * (2 - sigma)) ∧
      3 / (2 * (2 - sigma)) ≤ 5 / 4 := by
  have hden : 0 < 2 * (2 - sigma) := by nlinarith
  constructor
  · rw [le_div_iff₀ hden]
    linarith
  · rw [div_le_iff₀ hden]
    linarith

/-- Under the theorem's minimal hypotheses the printed p. 110 choices obey
`1 <= X <= Y <= (qT)^(5/4)`.  The stronger inequality `2 <= X` would require
`4 <= qT`; at the corner `qT = 2` one only has `X = sqrt 2`, so any source
lemma needing `2 <= X` must include a finite-range patch. -/
theorem source_parameter_range
    {q : ℕ} [NeZero q] {T sigma : ℝ}
    (hT : 2 ≤ T) (hsigmaLow : 1 / 2 ≤ sigma)
    (hsigmaHigh : sigma ≤ 4 / 5) :
    1 ≤ sourceX q T ∧
      sourceX q T ≤ sourceY q T sigma ∧
      sourceY q T sigma ≤ Real.rpow (sourceScale q T) (5 / 4) := by
  have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hscaleTwo : 2 ≤ sourceScale q T := by
    unfold sourceScale
    nlinarith [mul_le_mul hqOne hT (by norm_num : (0 : ℝ) ≤ 2)
      (by exact_mod_cast (Nat.zero_le q) : (0 : ℝ) ≤ q)]
  have hscaleOne : 1 ≤ sourceScale q T := by linarith
  have hscaleNonneg : 0 ≤ sourceScale q T := hscaleOne.trans' zero_le_one
  obtain ⟨hexpOne, hexpFive⟩ :=
    sourceY_exponent_mem hsigmaLow hsigmaHigh
  have hhalfExp : (1 / 2 : ℝ) ≤ 3 / (2 * (2 - sigma)) := by
    linarith
  refine ⟨?_, ?_, ?_⟩
  · unfold sourceX
    exact Real.one_le_rpow hscaleOne (by norm_num)
  · unfold sourceX sourceY
    exact Real.rpow_le_rpow_of_exponent_le hscaleOne hhalfExp
  · unfold sourceY
    exact Real.rpow_le_rpow_of_exponent_le hscaleOne hexpFive

/-- The p. 110 choice of `Y` produces exactly the Ingham exponent, with no
epsilon or logarithmic loss hidden in the algebra. -/
theorem sourceY_power_eq_ingham
    {q : ℕ} [NeZero q] {T sigma : ℝ}
    (hT : 0 < T) (hsigmaHigh : sigma < 2) :
    Real.rpow (sourceY q T sigma) (2 * (1 - sigma)) =
      Real.rpow (sourceScale q T) (inghamExponent sigma) := by
  have hscale := sourceScale_pos (q := q) hT
  have hden : 2 - sigma ≠ 0 := by linarith
  unfold sourceY
  calc
    Real.rpow (Real.rpow (sourceScale q T) (3 / (2 * (2 - sigma))))
        (2 * (1 - sigma)) =
        Real.rpow (sourceScale q T)
          ((3 / (2 * (2 - sigma))) * (2 * (1 - sigma))) :=
      (Real.rpow_mul hscale.le _ _).symm
    _ = Real.rpow (sourceScale q T) (inghamExponent sigma) := by
      apply congrArg (Real.rpow (sourceScale q T))
      rw [inghamExponent_eq]
      field_simp

/-- On Montgomery's published low strip the terminal detector cutoff is at
least the full hybrid scale `qT`.  This is the scalar comparison used when
the `qT * Y^(1-2*sigma)` contribution is merged into the
`Y^(2*(1-sigma))` contribution on p. 110. -/
theorem sourceScale_le_sourceY
    {q : ℕ} [NeZero q] {T sigma : ℝ}
    (hT : 2 ≤ T) (hsigmaLow : 1 / 2 ≤ sigma)
    (hsigmaHigh : sigma ≤ 4 / 5) :
    sourceScale q T ≤ sourceY q T sigma := by
  have hscaleOne : 1 ≤ sourceScale q T := by
    have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
    unfold sourceScale
    nlinarith [mul_le_mul hqOne hT (by norm_num : (0 : ℝ) ≤ 2)
      (by exact_mod_cast (Nat.zero_le q) : (0 : ℝ) ≤ q)]
  have hexp := (sourceY_exponent_mem hsigmaLow hsigmaHigh).1
  unfold sourceY
  simpa only [Real.rpow_one] using
    (Real.rpow_le_rpow_of_exponent_le hscaleOne hexp)

/-- Exact terminal absorption of the hybrid-scale term.  This is the
source-level power comparison behind the last combination of (12.33) and
(12.39); it does not assume a zero-density estimate. -/
theorem sourceScale_mul_sourceY_power_le
    {q : ℕ} [NeZero q] {T sigma : ℝ}
    (hT : 2 ≤ T) (hsigmaLow : 1 / 2 ≤ sigma)
    (hsigmaHigh : sigma ≤ 4 / 5) :
    sourceScale q T * Real.rpow (sourceY q T sigma) (1 - 2 * sigma) ≤
      Real.rpow (sourceY q T sigma) (2 * (1 - sigma)) := by
  have hscalePos : 0 < sourceScale q T :=
    sourceScale_pos (q := q) (by linarith)
  have hYpos : 0 < sourceY q T sigma := by
    unfold sourceY
    exact Real.rpow_pos_of_pos hscalePos _
  have hscaleY := sourceScale_le_sourceY (q := q) (T := T) (sigma := sigma)
    hT hsigmaLow hsigmaHigh
  calc
    sourceScale q T * Real.rpow (sourceY q T sigma) (1 - 2 * sigma) ≤
        sourceY q T sigma *
          Real.rpow (sourceY q T sigma) (1 - 2 * sigma) := by
      exact mul_le_mul_of_nonneg_right hscaleY
        (Real.rpow_nonneg hYpos.le _)
    _ = Real.rpow (sourceY q T sigma) (2 * (1 - sigma)) := by
      calc
        sourceY q T sigma *
            Real.rpow (sourceY q T sigma) (1 - 2 * sigma) =
            Real.rpow (sourceY q T sigma) (1 + (1 - 2 * sigma)) := by
          simpa only [Real.rpow_one] using
            (Real.rpow_add hYpos 1 (1 - 2 * sigma)).symm
        _ = Real.rpow (sourceY q T sigma) (2 * (1 - sigma)) := by
          congr 1
          ring

/-! ## Exact principal/nonprincipal family bookkeeping -/

/-- The part of Montgomery's fixed-modulus family count supported on
nonprincipal ambient characters. -/
def nonprincipalAmbientZeroCountAtLevel
    (q : ℕ) [NeZero q] (sigma T : ℝ) : ℕ :=
  ∑ chi ∈ (Finset.univ.erase (1 : DirichletCharacter ℂ q)),
    dirichletZeroCount chi sigma T

/-- The ambient family is exactly its principal row plus the nonprincipal
rows.  This identity is needed because the certified detector dichotomy has
the hypothesis `chi != 1`, whereas `ambientZeroCountAtLevel` includes the
principal character. -/
theorem ambientZeroCountAtLevel_eq_principal_add_nonprincipal
    (q : ℕ) [NeZero q] (sigma T : ℝ) :
    ambientZeroCountAtLevel q sigma T =
      dirichletZeroCount (1 : DirichletCharacter ℂ q) sigma T +
        nonprincipalAmbientZeroCountAtLevel q sigma T := by
  classical
  simp only [ambientZeroCountAtLevel, NeZero.ne q, dite_false,
    nonprincipalAmbientZeroCountAtLevel]
  rw [add_comm]
  exact (Finset.sum_erase_add
    (Finset.univ : Finset (DirichletCharacter ℂ q))
    (fun chi => dirichletZeroCount chi sigma T)
    (Finset.mem_univ (1 : DirichletCharacter ℂ q))).symm

/-- Exact post-optimization rewrite of the last source inequality.  Its
hypothesis is intentionally local and parameterized by the printed `Y`: the
still-unformalized analytic work is the derivation of that hypothesis from
the thinned zero sets and the three cited mean-value inputs. -/
theorem theorem12_9_rewrite_of_parameter_bound
    {q : ℕ} [NeZero q] {T sigma C : ℝ}
    (hT : 0 < T) (hsigmaHigh : sigma < 2)
    (hfinal : (ambientZeroCountAtLevel q sigma T : ℝ) ≤
      C * Real.rpow (sourceY q T sigma) (2 * (1 - sigma)) *
        (Real.log (sourceScale q T)) ^ 9) :
    (ambientZeroCountAtLevel q sigma T : ℝ) ≤
      C * Real.rpow (sourceScale q T) (inghamExponent sigma) *
        (Real.log (sourceScale q T)) ^ 9 := by
  rw [sourceY_power_eq_ingham hT hsigmaHigh] at hfinal
  exact hfinal

/-- The literal pre-optimization `Y`-bound on the range actually consumed by
MAP constructs the canonical low-strip source.  This is only a quantifier and
exponent-rewrite weld: all analytic content remains visible in `hfinal`. -/
theorem neededLowStripSource_of_parameter_bound
    (hfinal : ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (q : ℕ) [NeZero q] (T sigma : ℝ),
        2 ≤ T → 1 / 2 ≤ sigma → sigma ≤ 7 / 10 →
          (ambientZeroCountAtLevel q sigma T : ℝ) ≤
            C₀ * Real.rpow (sourceY q T sigma) (2 * (1 - sigma)) *
              (Real.log (sourceScale q T)) ^ 9) :
    MAPMontgomeryNeededLowStrip.MontgomeryNeededLowStripSource := by
  obtain ⟨C₀, hC₀, hbound⟩ := hfinal
  refine ⟨C₀, hC₀, ?_⟩
  intro q _inst T sigma hT hsigmaLow hsigmaHigh
  have hraw := hbound q T sigma hT hsigmaLow hsigmaHigh
  have hrewrite := theorem12_9_rewrite_of_parameter_bound
    (q := q) (T := T) (sigma := sigma) (C := C₀)
    (by linarith : 0 < T) (by linarith : sigma < 2) hraw
  simpa [sourceScale, MAPMontgomeryLowStrip.inghamExponent,
    MAPMontgomeryNeededLowStrip.inghamExponent] using hrewrite

/-- Deterministic terminal family summation with the principal row kept
explicit.  The two hypotheses are strictly before the ambient conclusion:
the first is the output of the nonprincipal detector-family assembly, and
the second is the separate regularized-principal row estimate. -/
theorem neededLowStripSource_of_separate_parameter_bounds
    (hnonprincipal : ∃ Cnp : ℝ, 0 < Cnp ∧
      ∀ (q : ℕ) [NeZero q] (T sigma : ℝ),
        2 ≤ T → 1 / 2 ≤ sigma → sigma ≤ 7 / 10 →
          (nonprincipalAmbientZeroCountAtLevel q sigma T : ℝ) ≤
            Cnp * Real.rpow (sourceY q T sigma) (2 * (1 - sigma)) *
              (Real.log (sourceScale q T)) ^ 9)
    (hprincipal : ∃ Cpr : ℝ, 0 < Cpr ∧
      ∀ (q : ℕ) [NeZero q] (T sigma : ℝ),
        2 ≤ T → 1 / 2 ≤ sigma → sigma ≤ 7 / 10 →
          (dirichletZeroCount
              (1 : DirichletCharacter ℂ q) sigma T : ℝ) ≤
            Cpr * Real.rpow (sourceY q T sigma) (2 * (1 - sigma)) *
              (Real.log (sourceScale q T)) ^ 9) :
    MAPMontgomeryNeededLowStrip.MontgomeryNeededLowStripSource := by
  obtain ⟨Cnp, hCnp, hnp⟩ := hnonprincipal
  obtain ⟨Cpr, hCpr, hpr⟩ := hprincipal
  apply neededLowStripSource_of_parameter_bound
  refine ⟨Cnp + Cpr, add_pos hCnp hCpr, ?_⟩
  intro q _inst T sigma hT hsigmaLow hsigmaHigh
  have hsplit := ambientZeroCountAtLevel_eq_principal_add_nonprincipal
    q sigma T
  have hnp' := hnp q T sigma hT hsigmaLow hsigmaHigh
  have hpr' := hpr q T sigma hT hsigmaLow hsigmaHigh
  rw [hsplit]
  push_cast
  calc
    (dirichletZeroCount (1 : DirichletCharacter ℂ q) sigma T : ℝ) +
        (nonprincipalAmbientZeroCountAtLevel q sigma T : ℝ) ≤
      Cpr * Real.rpow (sourceY q T sigma) (2 * (1 - sigma)) *
          (Real.log (sourceScale q T)) ^ 9 +
        Cnp * Real.rpow (sourceY q T sigma) (2 * (1 - sigma)) *
          (Real.log (sourceScale q T)) ^ 9 := add_le_add hpr' hnp'
    _ = (Cnp + Cpr) *
        Real.rpow (sourceY q T sigma) (2 * (1 - sigma)) *
          (Real.log (sourceScale q T)) ^ 9 := by ring

/-! ## Hostile high-strip death test -/

theorem ingham_at_four_fifths :
    inghamExponent (4 / 5 : ℝ) = 1 / 2 := by
  norm_num [inghamExponent, inghamCoeff]

theorem map_uniform_at_four_fifths :
    uniformCoeff * (1 - (4 / 5 : ℝ)) = 6 / 13 := by
  norm_num [uniformCoeff]

theorem map_uniform_strictly_below_ingham_at_four_fifths :
    uniformCoeff * (1 - (4 / 5 : ℝ)) <
      inghamExponent (4 / 5 : ℝ) := by
  rw [ingham_at_four_fifths, map_uniform_at_four_fifths]
  norm_num

/-- Consequently Montgomery (12.9), even if fully certified, cannot inhabit
the principal high-strip branch needed by MAP.  A separate zeta/GM density
argument is logically necessary. -/
theorem not_ingham_below_uniform_on_high_strip :
    ¬ (∀ sigma : ℝ, 7 / 10 ≤ sigma → sigma ≤ 4 / 5 →
      inghamExponent sigma ≤ uniformCoeff * (1 - sigma)) := by
  intro h
  have hbad := h (4 / 5) (by norm_num) (by norm_num)
  linarith [map_uniform_strictly_below_ingham_at_four_fifths]

theorem gm_at_four_fifths :
    gmCoeff (4 / 5 : ℝ) * (1 - 4 / 5) = 3 / 7 := by
  norm_num [gmCoeff]

theorem gm_fits_map_at_four_fifths :
    gmCoeff (4 / 5 : ℝ) * (1 - 4 / 5) <
      uniformCoeff * (1 - 4 / 5) := by
  rw [gm_at_four_fifths, map_uniform_at_four_fifths]
  norm_num

end
end MAPMontgomeryTheorem12SourceDAG

#print axioms MAPMontgomeryTheorem12SourceDAG.sourceY_exponent_mem
#print axioms MAPMontgomeryTheorem12SourceDAG.source_parameter_range
#print axioms MAPMontgomeryTheorem12SourceDAG.sourceY_power_eq_ingham
#print axioms MAPMontgomeryTheorem12SourceDAG.sourceScale_le_sourceY
#print axioms MAPMontgomeryTheorem12SourceDAG.sourceScale_mul_sourceY_power_le
#print axioms MAPMontgomeryTheorem12SourceDAG.ambientZeroCountAtLevel_eq_principal_add_nonprincipal
#print axioms MAPMontgomeryTheorem12SourceDAG.neededLowStripSource_of_separate_parameter_bounds
#print axioms MAPMontgomeryTheorem12SourceDAG.theorem12_9_rewrite_of_parameter_bound
#print axioms MAPMontgomeryTheorem12SourceDAG.neededLowStripSource_of_parameter_bound
#print axioms MAPMontgomeryTheorem12SourceDAG.not_ingham_below_uniform_on_high_strip
