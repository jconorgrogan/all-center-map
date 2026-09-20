import FixedCharacterReduction
import JutilaDeterministicCore
import PostA5CrowdingDeterministic

/-!
# Fixed-modulus specialization of Huxley 1975, Theorem 1

This module records the exact deterministic specialization of Huxley's
notation (2.1)--(2.14) and the algebra which turns the two terms in (2.20)
into the fixed-modulus Halasz--Montgomery large-value shape used by CGL.

No large-value or zero-density proposition is asserted.  The remaining
analytic input is Huxley's reflected correlation estimate, first exposed in
1975 Lemma 2, equations (2.18)--(2.19).
-/

namespace MAPHuxleyFixedModulusSpecialization

open scoped BigOperators
open DirichletZeros MAPAPZeroDensityCert

noncomputable section

/-! ## Literal fixed-modulus aggregate conventions -/

/-- A point `(s,chi)` in Huxley's aggregate, with the real and imaginary
parts separated to keep the source inequalities literal. -/
structure AggregatePoint (Character : Type*) where
  sigma : ℝ
  t : ℝ
  character : Character

/-- The specialization `Q=q0=q` of Huxley's conditions (2.3)--(2.6).

`proper` retains the source's primitive-character convention.  The strip is
`0 <= Re s <= 1/log(qT)`, the ordinates have diameter at most `T`, and
distinct points carrying the same character are one-separated. -/
structure FixedModulusAggregate (Character : Type*) [DecidableEq Character]
    (modulus : Character → ℕ) (proper : Character → Prop)
    (q : ℕ) (T ell : ℝ) where
  points : Finset (AggregatePoint Character)
  modulus_eq : ∀ p ∈ points, modulus p.character = q
  proper_character : ∀ p ∈ points, proper p.character
  strip : ∀ p ∈ points, 0 ≤ p.sigma ∧ p.sigma ≤ ell⁻¹
  height_diameter : ∀ p ∈ points, ∀ p' ∈ points, |p.t - p'.t| ≤ T
  same_character_oneSeparated :
    ∀ p ∈ points, ∀ p' ∈ points,
      p ≠ p' → p.character = p'.character → 1 ≤ |p.t - p'.t|

/-- The congruence condition in (2.3) is automatic after `Q=q0=q`. -/
theorem fixed_modulus_congruence (q : ℕ) : q % q = 0 := by
  exact Nat.mod_self q

/-- Huxley's hybrid base `D=Q^2*T/q0` becomes exactly `qT` when
`Q=q0=q`. -/
theorem fixed_modulus_hybridBase {q T : ℝ} (hq : 0 < q) :
    q ^ 2 * T / q = q * T := by
  field_simp [hq.ne']

/-! ## Exact algebra after Huxley (2.20) -/

/-- The literal right side of Huxley (2.20), before its absolute implied
constant.  `deltaTwo` and `deltaThree` are the divisor-function maxima
`Delta_2` and `Delta_3`, and `ell=log D`. -/
def theoremOneRawTerms
    (G V N D deltaTwo deltaThree ell : ℝ) : ℝ :=
  G * (V ^ 2)⁻¹ * N * ell ^ 2 +
    G ^ 3 * (V ^ 6)⁻¹ * N * D * Real.sqrt deltaTwo * deltaThree * ell ^ 11

/-- The common subpower overhead left after the two terms of (2.20) are
put into the CGL normalization. -/
def theoremOneOverhead (deltaTwo deltaThree ell : ℝ) : ℝ :=
  ell ^ 2 + Real.sqrt deltaTwo * deltaThree * ell ^ 11

/-- Exact deterministic specialization of (2.20): `G<=N` turns its first
term into `N^2 V^-2` and its reflected term into `D N^4 V^-6`.

This theorem starts from a numerical instance of Huxley's source inequality;
it does not declare that source inequality as a theorem-valued proposition. -/
theorem theoremOneRawTerms_le_fixedModulusShape
    {G V N D deltaTwo deltaThree ell : ℝ}
    (hG : 0 ≤ G) (hGN : G ≤ N) (hN : 0 ≤ N) (hD : 0 ≤ D)
    (hdeltaThree : 0 ≤ deltaThree)
    (hell : 0 ≤ ell) :
    theoremOneRawTerms G V N D deltaTwo deltaThree ell ≤
      theoremOneOverhead deltaTwo deltaThree ell *
        (N ^ 2 * (V ^ 2)⁻¹ + D * N ^ 4 * (V ^ 6)⁻¹) := by
  have hV2 : 0 ≤ (V ^ 2)⁻¹ := by positivity
  have hV6 : 0 ≤ (V ^ 6)⁻¹ := by positivity
  have hsqrt : 0 ≤ Real.sqrt deltaTwo := Real.sqrt_nonneg _
  have hGpow : G ^ 3 ≤ N ^ 3 := by
    exact pow_le_pow_left₀ hG hGN 3
  have hfirst :
      G * (V ^ 2)⁻¹ * N * ell ^ 2 ≤ ell ^ 2 * (N ^ 2 * (V ^ 2)⁻¹) := by
    have hGNmul : G * N ≤ N * N := mul_le_mul_of_nonneg_right hGN hN
    have hscaled := mul_le_mul_of_nonneg_right hGNmul hV2
    have hellsq : 0 ≤ ell ^ 2 := sq_nonneg ell
    calc
      G * (V ^ 2)⁻¹ * N * ell ^ 2 = ell ^ 2 * ((G * N) * (V ^ 2)⁻¹) := by ring
      _ ≤ ell ^ 2 * ((N * N) * (V ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left hscaled hellsq
      _ = ell ^ 2 * (N ^ 2 * (V ^ 2)⁻¹) := by ring
  have hdeltaFactor :
      0 ≤ Real.sqrt deltaTwo * deltaThree * ell ^ 11 := by positivity
  have hGNpow : G ^ 3 * N ≤ N ^ 3 * N :=
    mul_le_mul_of_nonneg_right hGpow hN
  have hrestFactor :
      0 ≤ (V ^ 6)⁻¹ * D * (Real.sqrt deltaTwo * deltaThree * ell ^ 11) := by
    positivity
  have hreflected :
      G ^ 3 * (V ^ 6)⁻¹ * N * D * Real.sqrt deltaTwo * deltaThree * ell ^ 11 ≤
        (Real.sqrt deltaTwo * deltaThree * ell ^ 11) *
          (D * N ^ 4 * (V ^ 6)⁻¹) := by
    have hscaled := mul_le_mul_of_nonneg_right hGNpow hrestFactor
    calc
      G ^ 3 * (V ^ 6)⁻¹ * N * D * Real.sqrt deltaTwo * deltaThree * ell ^ 11 =
          (G ^ 3 * N) *
            ((V ^ 6)⁻¹ * D * (Real.sqrt deltaTwo * deltaThree * ell ^ 11)) := by
              ring
      _ ≤ (N ^ 3 * N) *
            ((V ^ 6)⁻¹ * D * (Real.sqrt deltaTwo * deltaThree * ell ^ 11)) := hscaled
      _ = (Real.sqrt deltaTwo * deltaThree * ell ^ 11) *
            (D * N ^ 4 * (V ^ 6)⁻¹) := by ring
  have hA : 0 ≤ N ^ 2 * (V ^ 2)⁻¹ := by positivity
  have hB : 0 ≤ D * N ^ 4 * (V ^ 6)⁻¹ := by positivity
  unfold theoremOneRawTerms theoremOneOverhead
  calc
    G * (V ^ 2)⁻¹ * N * ell ^ 2 +
        G ^ 3 * (V ^ 6)⁻¹ * N * D * Real.sqrt deltaTwo * deltaThree * ell ^ 11 ≤
      ell ^ 2 * (N ^ 2 * (V ^ 2)⁻¹) +
        (Real.sqrt deltaTwo * deltaThree * ell ^ 11) *
          (D * N ^ 4 * (V ^ 6)⁻¹) := add_le_add hfirst hreflected
    _ ≤ (ell ^ 2 + Real.sqrt deltaTwo * deltaThree * ell ^ 11) *
        (N ^ 2 * (V ^ 2)⁻¹ + D * N ^ 4 * (V ^ 6)⁻¹) := by
      nlinarith [mul_nonneg (sq_nonneg ell) hB, mul_nonneg hdeltaFactor hA]

/-- Multiplying the preceding pointwise algebra by Huxley's nonnegative
absolute constant preserves the fixed-modulus two-term shape. -/
theorem theoremOneBound_to_fixedModulusShape
    {R C G V N D deltaTwo deltaThree ell : ℝ}
    (hC : 0 ≤ C)
    (hG : 0 ≤ G) (hGN : G ≤ N) (hN : 0 ≤ N) (hD : 0 ≤ D)
    (hdeltaThree : 0 ≤ deltaThree)
    (hell : 0 ≤ ell)
    (hsource : R ≤ C * theoremOneRawTerms G V N D deltaTwo deltaThree ell) :
    R ≤ C * theoremOneOverhead deltaTwo deltaThree ell *
      (N ^ 2 * (V ^ 2)⁻¹ + D * N ^ 4 * (V ^ 6)⁻¹) := by
  calc
    R ≤ C * theoremOneRawTerms G V N D deltaTwo deltaThree ell := hsource
    _ ≤ C * (theoremOneOverhead deltaTwo deltaThree ell *
        (N ^ 2 * (V ^ 2)⁻¹ + D * N ^ 4 * (V ^ 6)⁻¹)) := by
      exact mul_le_mul_of_nonneg_left
        (theoremOneRawTerms_le_fixedModulusShape
          hG hGN hN hD hdeltaThree hell) hC
    _ = C * theoremOneOverhead deltaTwo deltaThree ell *
        (N ^ 2 * (V ^ 2)⁻¹ + D * N ^ 4 * (V ^ 6)⁻¹) := by ring

/-! ## Ambient-character conductor recovery -/

/-- Restoring every ambient character modulo one fixed `q` from its
primitive inducer costs at most `q`, with analytic multiplicity unchanged.
This is the fixed-level counterpart of `fixed_primitive_bound_to_family`. -/
theorem fixedLevel_conductorRecovery
    {q : ℕ} [NeZero q] {sigma T B : ℝ} (hB : 0 ≤ B)
    (hprimitive : ∀ chi : DirichletCharacter ℂ q,
      (primitiveDirichletZeroCount chi sigma T : ℝ) ≤ B) :
    (zeroCountAtLevel q sigma T : ℝ) ≤ (q : ℝ) * B := by
  rw [zeroCountAtLevel_eq]
  push_cast
  calc
    (∑ chi : DirichletCharacter ℂ q,
        (primitiveDirichletZeroCount chi sigma T : ℝ)) ≤
      ∑ _chi : DirichletCharacter ℂ q, B := by
        apply Finset.sum_le_sum
        intro chi _
        exact hprimitive chi
    _ = (Nat.card (DirichletCharacter ℂ q) : ℝ) * B := by
      simp [Nat.card_eq_fintype_card]
    _ ≤ (q : ℝ) * B := by
      apply mul_le_mul_of_nonneg_right _ hB
      exact_mod_cast (show Nat.card (DirichletCharacter ℂ q) ≤ q by
        rw [DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
        exact Nat.totient_le q)

end

end MAPHuxleyFixedModulusSpecialization

#print axioms MAPHuxleyFixedModulusSpecialization.fixed_modulus_hybridBase
#print axioms MAPHuxleyFixedModulusSpecialization.theoremOneRawTerms_le_fixedModulusShape
#print axioms MAPHuxleyFixedModulusSpecialization.theoremOneBound_to_fixedModulusShape
#print axioms MAPHuxleyFixedModulusSpecialization.fixedLevel_conductorRecovery
