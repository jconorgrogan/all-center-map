import MRTLemma215ScaleClassifierV3

/-!
# Lower-support product for dynamic HB components

This is the exact support mechanism behind the `j >= m` vanishing branch of
MRT Lemma 2.15.  It is stated for a literal list of dyadic arithmetic
functions, so the eventual component adapter need only identify its active
shell list.
-/

namespace MRTLemma215DynamicSupportV3

open scoped ArithmeticFunction BigOperators
open ArithmeticFunction
open MAPMRTCorollary25TypeD1LiteralWeld
open MAPHBPerronSourceData

noncomputable section

structure NatDyadicFactor where
  length : ℕ
  coeff : ArithmeticFunction ℂ
  support : SupportedNatDyadic length coeff

def factorConvolution : List NatDyadicFactor → ArithmeticFunction ℂ
  | [] => 1
  | f :: factors => f.coeff * factorConvolution factors

def factorLowerProduct (factors : List NatDyadicFactor) : ℕ :=
  (factors.map NatDyadicFactor.length).prod

/-- Literal upper endpoint of the product block of a factor list.  A factor
supported on `(M,2M]` has upper endpoint `2M`, so this keeps every dyadic
dilation visible rather than hiding it in asymptotic notation. -/
def factorUpperProduct (factors : List NatDyadicFactor) : ℕ :=
  (factors.map (fun f => 2 * f.length)).prod

@[simp] theorem factorLowerProduct_nil : factorLowerProduct [] = 1 := rfl

@[simp] theorem factorLowerProduct_cons
    (f : NatDyadicFactor) (factors : List NatDyadicFactor) :
    factorLowerProduct (f :: factors) =
      f.length * factorLowerProduct factors := by
  simp [factorLowerProduct]

@[simp] theorem factorUpperProduct_nil : factorUpperProduct [] = 1 := rfl

@[simp] theorem factorUpperProduct_cons
    (f : NatDyadicFactor) (factors : List NatDyadicFactor) :
    factorUpperProduct (f :: factors) =
      (2 * f.length) * factorUpperProduct factors := by
  simp [factorUpperProduct]

/-- The literal upper product is exactly the lower product times one factor
of two for every active dyadic shell. -/
theorem factorUpperProduct_eq_pow_mul_lowerProduct
    (factors : List NatDyadicFactor) :
    factorUpperProduct factors =
      2 ^ factors.length * factorLowerProduct factors := by
  induction factors with
  | nil => simp
  | cons f factors ih =>
      rw [factorUpperProduct_cons, ih, factorLowerProduct_cons]
      simp only [List.length_cons, pow_succ]
      ac_rfl

/-- A nonempty convolution of `(N,2N]` factors vanishes at every index no
larger than the product of the lower endpoints.  The strict lower endpoint
is retained exactly. -/
theorem factorConvolution_zero_of_le
    (head : NatDyadicFactor) (tail : List NatDyadicFactor) {n : ℕ}
    (hn : n ≤ factorLowerProduct (head :: tail)) :
    factorConvolution (head :: tail) n = 0 := by
  induction tail generalizing head n with
  | nil =>
      have hnHead : n ≤ head.length := by
        simpa using hn
      have hout : ¬ n ∈ DeterminantCountWeld.dyadic head.length := by
        intro hmem
        have hlower := (Finset.mem_Ioc.mp hmem).1
        omega
      simpa [factorConvolution] using head.support n hout
  | cons next rest ih =>
      rw [factorConvolution, ArithmeticFunction.mul_apply]
      apply Finset.sum_eq_zero
      intro z hz
      have hmul : z.1 * z.2 = n :=
        (Nat.mem_divisorsAntidiagonal.mp hz).1
      by_cases hleft : z.1 ≤ head.length
      · have hout : ¬ z.1 ∈ DeterminantCountWeld.dyadic head.length := by
          intro hmem
          have hlower := (Finset.mem_Ioc.mp hmem).1
          omega
        rw [head.support z.1 hout]
        simp
      · have hright : z.2 ≤ factorLowerProduct (next :: rest) := by
          by_contra h
          have hleftStrict : head.length < z.1 := lt_of_not_ge hleft
          have hrightStrict : factorLowerProduct (next :: rest) < z.2 :=
            lt_of_not_ge h
          have hprodStrict := Nat.mul_lt_mul_of_lt_of_lt
            hleftStrict hrightStrict
          rw [factorLowerProduct_cons, hmul] at hprodStrict
          exact (not_lt_of_ge hn) hprodStrict
        have hzero := ih next hright
        rw [hzero]
        simp

/-- An arbitrary arithmetic scalar on the left cannot move the lower support
of the nonempty factor convolution downward. -/
theorem scalar_mul_factorConvolution_zero_of_le
    (scalar : ArithmeticFunction ℂ)
    (head : NatDyadicFactor) (tail : List NatDyadicFactor) {n : ℕ}
    (hn : n ≤ factorLowerProduct (head :: tail)) :
    (scalar * factorConvolution (head :: tail)) n = 0 := by
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro z hz
  have hright : z.2 ≤ n :=
    MAPHeathBrownFiniteIdentity.antidiagonal_right_le hz
  have hzero := factorConvolution_zero_of_le head tail (hright.trans hn)
  rw [hzero]
  simp

/-- A nonempty convolution of `(N,2N]` factors vanishes above the literal
product of their upper endpoints. -/
theorem factorConvolution_zero_of_upperProduct_lt
    (head : NatDyadicFactor) (tail : List NatDyadicFactor) {n : ℕ}
    (hn : factorUpperProduct (head :: tail) < n) :
    factorConvolution (head :: tail) n = 0 := by
  induction tail generalizing head n with
  | nil =>
      have hn' : 2 * head.length < n := by simpa using hn
      have hout : ¬ n ∈ DeterminantCountWeld.dyadic head.length := by
        intro hmem
        have hupper := (Finset.mem_Ioc.mp hmem).2
        exact (not_lt_of_ge hupper) hn'
      simpa [factorConvolution] using head.support n hout
  | cons next rest ih =>
      rw [factorConvolution, ArithmeticFunction.mul_apply]
      apply Finset.sum_eq_zero
      intro z hz
      have hmul : z.1 * z.2 = n :=
        (Nat.mem_divisorsAntidiagonal.mp hz).1
      by_cases hleft : z.1 ≤ 2 * head.length
      · have hright : factorUpperProduct (next :: rest) < z.2 := by
          by_contra h
          have hrightLe : z.2 ≤ factorUpperProduct (next :: rest) :=
            le_of_not_gt h
          have hprodLe := Nat.mul_le_mul hleft hrightLe
          rw [hmul, factorUpperProduct_cons] at hprodLe
          exact (not_le_of_gt hn) hprodLe
        have hzero := ih next hright
        rw [hzero]
        simp
      · have hout : ¬ z.1 ∈ DeterminantCountWeld.dyadic head.length := by
          intro hmem
          exact hleft (Finset.mem_Ioc.mp hmem).2
        rw [head.support z.1 hout]
        simp

/-- If the lower support product already exceeds `2X`, the masked component
is identically zero on `(X,2X]`. -/
theorem masked_factorConvolution_eq_zero_of_twoX_lt
    {X : ℝ} (hX : 0 ≤ X)
    (head : NatDyadicFactor) (tail : List NatDyadicFactor)
    (hprod : 2 * X < factorLowerProduct (head :: tail)) (n : ℕ) :
    (if n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊ then
      factorConvolution (head :: tail) n else 0) = 0 := by
  by_cases hn : n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊
  · rw [if_pos hn]
    have htwoNonneg : 0 ≤ 2 * X := by positivity
    have hnReal : (n : ℝ) ≤ 2 * X := by
      have : (n : ℝ) ≤ (⌊2 * X⌋₊ : ℝ) := by
        exact_mod_cast (Finset.mem_Ioc.mp hn).2
      exact this.trans (Nat.floor_le htwoNonneg)
    have hnProdReal : (n : ℝ) < factorLowerProduct (head :: tail) :=
      hnReal.trans_lt hprod
    have hnProd : n ≤ factorLowerProduct (head :: tail) := by
      exact_mod_cast hnProdReal.le
    exact factorConvolution_zero_of_le head tail hnProd
  · rw [if_neg hn]

theorem masked_scalar_mul_factorConvolution_eq_zero_of_twoX_lt
    {X : ℝ} (hX : 0 ≤ X) (scalar : ArithmeticFunction ℂ)
    (head : NatDyadicFactor) (tail : List NatDyadicFactor)
    (hprod : 2 * X < factorLowerProduct (head :: tail)) (n : ℕ) :
    (if n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊ then
      (scalar * factorConvolution (head :: tail)) n else 0) = 0 := by
  by_cases hn : n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊
  · rw [if_pos hn]
    have htwoNonneg : 0 ≤ 2 * X := by positivity
    have hnReal : (n : ℝ) ≤ 2 * X := by
      have : (n : ℝ) ≤ (⌊2 * X⌋₊ : ℝ) := by
        exact_mod_cast (Finset.mem_Ioc.mp hn).2
      exact this.trans (Nat.floor_le htwoNonneg)
    have hnProdReal : (n : ℝ) < factorLowerProduct (head :: tail) :=
      hnReal.trans_lt hprod
    have hnProd : n ≤ factorLowerProduct (head :: tail) := by
      exact_mod_cast hnProdReal.le
    exact scalar_mul_factorConvolution_zero_of_le scalar head tail hnProd
  · rw [if_neg hn]

end
end MRTLemma215DynamicSupportV3

#print axioms MRTLemma215DynamicSupportV3.factorConvolution_zero_of_le
#print axioms MRTLemma215DynamicSupportV3.masked_factorConvolution_eq_zero_of_twoX_lt
#print axioms MRTLemma215DynamicSupportV3.masked_scalar_mul_factorConvolution_eq_zero_of_twoX_lt
