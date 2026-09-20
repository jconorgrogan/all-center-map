import MRTLemma215DynamicHighProvenanceV3

/-!
# Exact re-dyadicization of the Type-d complement

After selecting the shortest high beta factor, the remaining convolution has
a literal finite upper support product.  This module partitions that complete
convolution into standard `(N,2N]` cells with no truncation error and proves
the exact two-factor packet identity used before Perron removal.
-/

namespace MRTLemma215ComplementDyadicV3

open scoped ArithmeticFunction BigOperators
open ArithmeticFunction
open MAPHBPerronSourceData
open MRTLemma215DyadicPartition MRTLemma215DynamicSupportV3
open MRTLemma215DynamicRegroupingV3

noncomputable section

theorem factorConvolution_truncation_eq_self
    (head : NatDyadicFactor) (tail : List NatDyadicFactor)
    (hone : ∀ f ∈ head :: tail, 1 ≤ f.length) :
    truncatedComplexArithmetic (factorUpperProduct (head :: tail))
        (factorConvolution (head :: tail)) =
      factorConvolution (head :: tail) := by
  ext n
  change (if 1 ≤ n ∧ n ≤ factorUpperProduct (head :: tail) then
      factorConvolution (head :: tail) n else 0) =
    factorConvolution (head :: tail) n
  by_cases hn : 1 ≤ n ∧ n ≤ factorUpperProduct (head :: tail)
  · rw [if_pos hn]
  · rw [if_neg hn]
    by_cases hn0 : n = 0
    · subst n
      exact (factorConvolution (head :: tail)).map_zero'.symm
    · have hnUpper : factorUpperProduct (head :: tail) < n := by
        by_contra h
        apply hn
        exact ⟨Nat.one_le_iff_ne_zero.mpr hn0, le_of_not_gt h⟩
      exact (factorConvolution_zero_of_upperProduct_lt head tail hnUpper).symm

theorem sourceUnitArithmetic_factorConvolution_eq_zero
    (head : NatDyadicFactor) (tail : List NatDyadicFactor)
    (hone : ∀ f ∈ head :: tail, 1 ≤ f.length) :
    sourceUnitArithmetic (factorUpperProduct (head :: tail))
      (factorConvolution (head :: tail)) = 0 := by
  ext n
  change (if n = 1 ∧ 1 ≤ factorUpperProduct (head :: tail) then
      factorConvolution (head :: tail) n else 0) = 0
  by_cases hn : n = 1 ∧ 1 ≤ factorUpperProduct (head :: tail)
  · rw [if_pos hn]
    rw [hn.1]
    apply factorConvolution_zero_of_le head tail
    have hlower : 1 ≤ factorLowerProduct (head :: tail) := by
      rw [factorLowerProduct_cons]
      apply Nat.one_le_iff_ne_zero.mpr
      apply Nat.mul_ne_zero
      · exact Nat.ne_of_gt (hone head (by simp))
      · apply Nat.ne_of_gt
        apply List.prod_pos
        intro x hx
        obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hx
        exact hone f (by simp [hf])
    exact hlower
  · rw [if_neg hn]

/-- A nonempty literal factor convolution is exactly the sum of its standard
dyadic output shells up to its honest upper support product. -/
theorem factorConvolution_eq_sum_sourceDyadicArithmetic
    (head : NatDyadicFactor) (tail : List NatDyadicFactor)
    (hone : ∀ f ∈ head :: tail, 1 ≤ f.length) :
    factorConvolution (head :: tail) =
      ∑ j : Fin (sourceDyadicCount (factorUpperProduct (head :: tail))),
        sourceDyadicArithmetic (factorUpperProduct (head :: tail))
          (factorConvolution (head :: tail)) j := by
  have hsplit := truncatedComplexArithmetic_eq_unit_add_sum
    (factorUpperProduct (head :: tail)) (factorConvolution (head :: tail))
  rw [factorConvolution_truncation_eq_self head tail hone,
    sourceUnitArithmetic_factorConvolution_eq_zero head tail hone,
    zero_add] at hsplit
  exact hsplit

theorem mul_factorConvolution_eq_sum_dyadicComplement
    (short : NatDyadicFactor)
    (head : NatDyadicFactor) (tail : List NatDyadicFactor)
    (hone : ∀ f ∈ head :: tail, 1 ≤ f.length) :
    short.coeff * factorConvolution (head :: tail) =
      ∑ j : Fin (sourceDyadicCount (factorUpperProduct (head :: tail))),
        short.coeff *
          sourceDyadicArithmetic (factorUpperProduct (head :: tail))
            (factorConvolution (head :: tail)) j := by
  have hsplit := factorConvolution_eq_sum_sourceDyadicArithmetic
    head tail hone
  calc
    short.coeff * factorConvolution (head :: tail) =
        short.coeff *
          (∑ j : Fin (sourceDyadicCount (factorUpperProduct (head :: tail))),
            sourceDyadicArithmetic (factorUpperProduct (head :: tail))
              (factorConvolution (head :: tail)) j) :=
      congrArg (fun F : ArithmeticFunction ℂ => short.coeff * F) hsplit
    _ = ∑ j : Fin (sourceDyadicCount (factorUpperProduct (head :: tail))),
        short.coeff *
          sourceDyadicArithmetic (factorUpperProduct (head :: tail))
            (factorConvolution (head :: tail)) j := by
      rw [Finset.mul_sum]

/-- Every emitted complementary cell has its advertised natural dyadic
support, ready for the packet-indexed V2 Perron constructor. -/
theorem dyadicComplement_supported
    (head : NatDyadicFactor) (tail : List NatDyadicFactor)
    (j : Fin (sourceDyadicCount (factorUpperProduct (head :: tail)))) :
    SupportedNatDyadic (2 ^ (j : ℕ))
      (sourceDyadicArithmetic (factorUpperProduct (head :: tail))
        (factorConvolution (head :: tail)) j) :=
  sourceDyadicArithmetic_supported _ _ j

end
end MRTLemma215ComplementDyadicV3

#print axioms MRTLemma215ComplementDyadicV3.factorConvolution_eq_sum_sourceDyadicArithmetic
#print axioms MRTLemma215ComplementDyadicV3.mul_factorConvolution_eq_sum_dyadicComplement
