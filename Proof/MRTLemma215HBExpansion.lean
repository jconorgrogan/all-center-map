import MRTLemma215DyadicPartition

/-!
# Exact dyadic expansion of the eight-term Heath--Brown source

This file turns the already-certified real Heath--Brown identity into the
complex arithmetic-function ring used by the source Dirichlet polynomials.
It then replaces every factor by its exact unit-plus-dyadic-shell expansion.
No Type classification or analytic estimate is asserted here.
-/

namespace MRTLemma215HBExpansion

open scoped BigOperators ArithmeticFunction
open ArithmeticFunction
open MAPHeathBrownFiniteIdentity MAPHBPerronSourceData
open MRTLemma215DyadicPartition

noncomputable section

def complexHBSignedArithmetic (X : ℝ) (k : ℕ) : ArithmeticFunction ℂ :=
  complexifyArithmetic
    ((((-1 : ArithmeticFunction ℝ) ^ k *
        ((8).choose (k + 1) : ArithmeticFunction ℝ)) *
      (ArithmeticFunction.log *
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ k *
        realTruncatedMoebius (hbCutoff X) ^ (k + 1))))

@[simp] theorem complexHBSignedArithmetic_apply
    (X : ℝ) (k n : ℕ) :
    complexHBSignedArithmetic X k n = hbSignedTerm X k n := by
  rfl

def complexHBScalar (k : ℕ) : ArithmeticFunction ℂ :=
  complexifyArithmetic
    ((-1 : ArithmeticFunction ℝ) ^ k *
      ((8).choose (k + 1) : ArithmeticFunction ℝ))

def complexLogAF : ArithmeticFunction ℂ :=
  complexifyArithmetic ArithmeticFunction.log

def complexZetaAF : ArithmeticFunction ℂ :=
  complexifyArithmetic (ArithmeticFunction.zeta : ArithmeticFunction ℝ)

def complexTruncatedMoebiusAF (X : ℝ) : ArithmeticFunction ℂ :=
  complexifyArithmetic (realTruncatedMoebius (hbCutoff X))

theorem complexHBSignedArithmetic_eq_factorized (X : ℝ) (k : ℕ) :
    complexHBSignedArithmetic X k =
      complexHBScalar k *
        (complexLogAF * complexZetaAF ^ k *
          complexTruncatedMoebiusAF X ^ (k + 1)) := by
  unfold complexHBSignedArithmetic complexHBScalar complexLogAF
    complexZetaAF complexTruncatedMoebiusAF
  simp only [complexifyArithmetic_mul, complexifyArithmetic_pow]

theorem complexTruncatedMoebiusAF_eq_truncation
    {X : ℝ} (hX : 0 ≤ X) :
    complexTruncatedMoebiusAF X =
      truncatedComplexArithmetic ⌊hbCutoff X⌋₊ (complexTruncatedMoebiusAF X) := by
  have hcut : 0 ≤ hbCutoff X := Real.rpow_nonneg (by positivity) _
  ext n
  change complexTruncatedMoebiusAF X n =
    if 1 ≤ n ∧ n ≤ ⌊hbCutoff X⌋₊ then complexTruncatedMoebiusAF X n else 0
  by_cases hn0 : n = 0
  · subst n
    exact (complexTruncatedMoebiusAF X).map_zero'
  by_cases hn : n ≤ ⌊hbCutoff X⌋₊
  · rw [if_pos ⟨Nat.one_le_iff_ne_zero.mpr hn0, hn⟩]
  · rw [if_neg (fun h => hn h.2)]
    unfold complexTruncatedMoebiusAF complexifyArithmetic realTruncatedMoebius
    change (((if (n : ℝ) ≤ hbCutoff X then
      (ArithmeticFunction.moebius n : ℝ) else 0 : ℝ)) : ℂ) = 0
    rw [if_neg]
    · norm_num
    · exact fun h => hn ((Nat.le_floor_iff hcut).2 h)

def hbFactorCutoff (X : ℝ) : ℕ := ⌊2 * X⌋₊

def dyadicHBLog (X : ℝ) : ArithmeticFunction ℂ :=
  truncatedComplexArithmetic (hbFactorCutoff X) complexLogAF

def dyadicHBZeta (X : ℝ) : ArithmeticFunction ℂ :=
  truncatedComplexArithmetic (hbFactorCutoff X) complexZetaAF

def dyadicHBMoebius (X : ℝ) : ArithmeticFunction ℂ :=
  truncatedComplexArithmetic ⌊hbCutoff X⌋₊ (complexTruncatedMoebiusAF X)

/-- The unflattened but exact shell expansion of one signed HB term.  It is
the input to the finite Type-II/Type-d grouping argument in MRT Lemma 2.15. -/
def expandedHBSignedArithmetic (X : ℝ) (k : ℕ) : ArithmeticFunction ℂ :=
  complexHBScalar k *
    (dyadicHBLog X * dyadicHBZeta X ^ k * dyadicHBMoebius X ^ (k + 1))

theorem complexHBSignedArithmetic_apply_eq_expanded
    {X : ℝ} (hX : 0 ≤ X) (k : ℕ) {n : ℕ}
    (hn1 : 1 ≤ n) (hnX : n ≤ hbFactorCutoff X) :
    complexHBSignedArithmetic X k n = expandedHBSignedArithmetic X k n := by
  rw [complexHBSignedArithmetic_eq_factorized]
  unfold expandedHBSignedArithmetic dyadicHBLog dyadicHBZeta dyadicHBMoebius
  apply mul_apply_congr_on_divisors
  · intro d hd
    rfl
  · intro d hd
    apply mul_apply_congr_on_divisors
    · intro e he
      apply mul_apply_congr_on_divisors
      · intro a ha
        by_cases ha0 : a = 0
        · subst a
          exact complexLogAF.map_zero'.trans
            (truncatedComplexArithmetic (hbFactorCutoff X) complexLogAF).map_zero'.symm
        · exact (truncatedComplexArithmetic_apply_of_mem complexLogAF
            (Nat.one_le_iff_ne_zero.mpr ha0) (ha.trans (he.trans (hd.trans hnX)))).symm
      · intro a ha
        apply pow_apply_congr_on_divisors
        intro b hb
        by_cases hb0 : b = 0
        · subst b
          exact complexZetaAF.map_zero'.trans
            (truncatedComplexArithmetic (hbFactorCutoff X) complexZetaAF).map_zero'.symm
        · exact (truncatedComplexArithmetic_apply_of_mem complexZetaAF
            (Nat.one_le_iff_ne_zero.mpr hb0)
            (hb.trans (ha.trans (he.trans (hd.trans hnX))))).symm
    · intro a ha
      apply pow_apply_congr_on_divisors
      intro b hb
      rw [← complexTruncatedMoebiusAF_eq_truncation hX]

/-- Every factor in the exact expansion is now literally unit plus standard
positive dyadic shells. -/
theorem expandedHBSignedArithmetic_eq_unit_shell_form
    {X : ℝ} (hX : 0 ≤ X) (k : ℕ) :
    expandedHBSignedArithmetic X k =
      complexHBScalar k *
        ((sourceUnitArithmetic (hbFactorCutoff X) complexLogAF +
            ∑ j : Fin (sourceDyadicCount (hbFactorCutoff X)),
              sourceDyadicArithmetic (hbFactorCutoff X) complexLogAF j) *
          (sourceUnitArithmetic (hbFactorCutoff X) complexZetaAF +
            ∑ j : Fin (sourceDyadicCount (hbFactorCutoff X)),
              sourceDyadicArithmetic (hbFactorCutoff X) complexZetaAF j) ^ k *
          (sourceUnitArithmetic ⌊hbCutoff X⌋₊ (complexTruncatedMoebiusAF X) +
            ∑ j : Fin (sourceDyadicCount ⌊hbCutoff X⌋₊),
              sourceDyadicArithmetic ⌊hbCutoff X⌋₊
                (complexTruncatedMoebiusAF X) j) ^ (k + 1)) := by
  unfold expandedHBSignedArithmetic dyadicHBLog dyadicHBZeta dyadicHBMoebius
  rw [truncatedComplexArithmetic_eq_unit_add_sum,
    truncatedComplexArithmetic_eq_unit_add_sum,
    truncatedComplexArithmetic_eq_unit_add_sum]

end
end MRTLemma215HBExpansion

#print axioms MRTLemma215HBExpansion.complexHBSignedArithmetic_apply_eq_expanded
#print axioms MRTLemma215HBExpansion.expandedHBSignedArithmetic_eq_unit_shell_form
