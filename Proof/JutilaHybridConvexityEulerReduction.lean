import PrimitiveEulerZeroTransport
import PrimitiveTruncatedExplicitFormulaBridge

/-!
# The ambient-to-primitive Euler-factor reduction in Jutila's p. 48 bound

Jutila states the hybrid convexity estimate for every character at one fixed
ambient modulus.  The functional equation, however, is naturally available
for the primitive inducer.  This module proves the exact deterministic bridge
between those conventions in the closed half-strip `0 <= Re s`.

No convexity estimate is assumed here.  The only loss is the literal number
of missing Euler factors, `2 ^ #(prime factors of q)`.  Absorbing this loss
into an arbitrary conductor epsilon is a separate elementary divisor-bound
step; keeping it visible prevents a primitive/ambient convention from being
silently changed.
-/

namespace MAPJutilaHybridConvexityEulerReduction

open Complex

noncomputable section

variable {q : ℕ} [NeZero q]

/-- In the nonnegative half-plane, every missing Euler factor introduced by
change of level has norm at most two. -/
theorem norm_eulerFactor_le_two
    (chi : DirichletCharacter ℂ q) {p : ℕ}
    (hp : p ∈ q.primeFactors) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖1 - chi.primitiveCharacter p * (p : ℂ) ^ (-s)‖ ≤ 2 := by
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpPos : 0 < (p : ℝ) := by exact_mod_cast hpPrime.pos
  have hpOne : (1 : ℝ) ≤ p := by exact_mod_cast hpPrime.one_le
  have hpow : ‖(p : ℂ) ^ (-s)‖ ≤ 1 := by
    change ‖((p : ℝ) : ℂ) ^ (-s)‖ ≤ 1
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hpPos]
    exact Real.rpow_le_one_of_one_le_of_nonpos hpOne (by simpa using neg_nonpos.mpr hs)
  have hchar : ‖chi.primitiveCharacter p‖ ≤ 1 :=
    chi.primitiveCharacter.norm_le_one p
  calc
    ‖1 - chi.primitiveCharacter p * (p : ℂ) ^ (-s)‖ ≤
        ‖(1 : ℂ)‖ + ‖chi.primitiveCharacter p * (p : ℂ) ^ (-s)‖ :=
      norm_sub_le _ _
    _ = 1 + ‖chi.primitiveCharacter p‖ * ‖(p : ℂ) ^ (-s)‖ := by
      rw [norm_one, norm_mul]
    _ ≤ 1 + 1 * 1 := by gcongr
    _ = 2 := by norm_num

/-- Exact finite-product cost of passing from a primitive inducer to its
ambient character.  The cardinality is deliberately retained rather than
hidden in `q^ε`. -/
theorem norm_eulerCorrection_le_two_pow_card
    (chi : DirichletCharacter ℂ q) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖PrimitiveEulerZeroTransport.eulerCorrection chi s‖ ≤
      (2 : ℝ) ^ q.primeFactors.card := by
  unfold PrimitiveEulerZeroTransport.eulerCorrection
  calc
    ‖∏ p ∈ q.primeFactors,
        (1 - chi.primitiveCharacter p * (p : ℂ) ^ (-s))‖ ≤
      ∏ p ∈ q.primeFactors,
        ‖(1 - chi.primitiveCharacter p * (p : ℂ) ^ (-s))‖ :=
      Finset.norm_prod_le _ _
    _ ≤ ∏ _p ∈ q.primeFactors, (2 : ℝ) := by
      exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        (fun p hp => norm_eulerFactor_le_two chi hp hs)
    _ = (2 : ℝ) ^ q.primeFactors.card := by simp

/-- Pointwise ambient-to-primitive norm comparison for a nonprincipal
character.  This is the precise convention bridge needed before applying a
primitive functional-equation convexity estimate. -/
theorem norm_LFunction_le_primitive_mul_two_pow_card
    (chi : DirichletCharacter ℂ q) [NeZero chi.conductor] (hchi : chi ≠ 1)
    {s : ℂ} (hs : 0 ≤ s.re) :
    ‖DirichletCharacter.LFunction chi s‖ ≤
      ‖DirichletCharacter.LFunction chi.primitiveCharacter s‖ *
        (2 : ℝ) ^ q.primeFactors.card := by
  have hprim : chi.primitiveCharacter ≠ 1 := by
    intro hp
    exact hchi
      ((PrimitiveTruncatedExplicitFormulaBridge.primitiveCharacter_eq_one_iff chi).mp hp)
  rw [PrimitiveEulerZeroTransport.LFunction_eq_primitive_mul_eulerCorrection
    chi (Or.inl hprim), norm_mul]
  exact mul_le_mul_of_nonneg_left
    (norm_eulerCorrection_le_two_pow_card chi hs) (norm_nonneg _)

end

end MAPJutilaHybridConvexityEulerReduction

#print axioms MAPJutilaHybridConvexityEulerReduction.norm_eulerFactor_le_two
#print axioms MAPJutilaHybridConvexityEulerReduction.norm_eulerCorrection_le_two_pow_card
#print axioms MAPJutilaHybridConvexityEulerReduction.norm_LFunction_le_primitive_mul_two_pow_card
