import MRTDynamicD12FactorExtraction
import MRTProposition61TypeD1Factorization
import MRTProposition61TypeIIFullNormWeldV3
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-! # Exact finite-prefix evaluation of the dynamic d1/d2 convolution -/
namespace MRTDynamicD12PolynomialFactorization

open scoped ArithmeticFunction BigOperators
open ArithmeticFunction MixedMeanFrontend
open MAPMRTCorollary25 MAPMRTCorollary25Instantiation
open MAPMRTProposition61TypeD1Factorization
open MAPMRTLemma210OrthogonalityReduction
open MRTProposition61TypeIILemma210InstantiationV3
open MRTLemma215DynamicSupportV3

noncomputable section

/-- Critical normalization as an arithmetic function, including the unit. -/
def normalizedAF {q : ℕ} (chi : DirichletCharacter ℂ q) (t : ℝ)
    (f : ArithmeticFunction ℂ) : ArithmeticFunction ℂ where
  toFun n := normalizedTwistedTerm (fun n => chi n) f n t
  map_zero' := by simp [normalizedTwistedTerm, characterTwist]

theorem normalizedAF_mul {q : ℕ} (chi : DirichletCharacter ℂ q) (t : ℝ)
    (f g : ArithmeticFunction ℂ) :
    normalizedAF chi t (f * g) = normalizedAF chi t f * normalizedAF chi t g := by
  ext n
  change normalizedTwistedTerm (fun n => chi n) ((f * g : ArithmeticFunction ℂ) : ℕ → ℂ) n t = _
  rw [ArithmeticFunction.mul_apply]
  change normalizedTwistedTerm (fun n => chi n) ((f * g : ArithmeticFunction ℂ) : ℕ → ℂ) n t =
    ∑ p ∈ n.divisorsAntidiagonal,
      normalizedTwistedTerm (fun n => chi n) f p.1 t *
      normalizedTwistedTerm (fun n => chi n) g p.2 t
  calc
    _ = ∑ p ∈ n.divisorsAntidiagonal,
        (chi n * (f p.1 * g p.2) / (Real.sqrt (n : ℝ) : ℂ)) * mellinPhase n t := by
      unfold normalizedTwistedTerm characterTwist
      rw [ArithmeticFunction.mul_apply, Finset.mul_sum, Finset.sum_div, Finset.sum_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p hp
      have hp0 := Nat.ne_zero_of_mem_divisorsAntidiagonal hp
      have hprod := (Nat.mem_divisorsAntidiagonal.mp hp).1
      symm
      simpa only [hprod] using normalizedTwistedTerm_mul
        (fun m n => by simpa only [Nat.cast_mul] using chi.map_mul (m : ZMod q) (n : ZMod q))
        (alpha := (f : ℕ → ℂ)) (beta := (g : ℕ → ℂ))
        (Nat.pos_of_ne_zero hp0.1) (Nat.pos_of_ne_zero hp0.2) t

/-- Multiplication of finite supported arithmetic functions evaluates exactly
as the product of their finite sums. No dyadic nonempty-support convention is
needed, so an empty classifier prefix contributes its actual unit term. -/
theorem sum_Ioc_mul_of_support
    {A B : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (f g : ArithmeticFunction ℂ)
    (hf : ∀ n, A < n → f n = 0) (hg : ∀ n, B < n → g n = 0) :
    (∑ n ∈ Finset.Ioc 0 (A * B), (f * g) n) =
      (∑ n ∈ Finset.Ioc 0 A, f n) * (∑ n ∈ Finset.Ioc 0 B, g n) := by
  rw [sum_Ioc_mul_eq_sum_prod_filter, Finset.sum_mul_sum,
    ← Finset.sum_product (Finset.Ioc 0 A) (Finset.Ioc 0 B) (fun p : ℕ × ℕ => f p.1 * g p.2)]
  symm
  apply Finset.sum_subset
  · intro p hp
    have h := Finset.mem_product.mp hp
    have ha := Finset.mem_Ioc.mp h.1
    have hb := Finset.mem_Ioc.mp h.2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_Ioc.mpr ⟨ha.1, ?_⟩,
      Finset.mem_Ioc.mpr ⟨hb.1, ?_⟩⟩, Nat.mul_le_mul ha.2 hb.2⟩
    · exact ha.2.trans (Nat.le_mul_of_pos_right A (by omega))
    · exact hb.2.trans (Nat.le_mul_of_pos_left B (by omega))
  · intro p hp hnot
    have hp' := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
    have hp1 := Finset.mem_Ioc.mp hp'.1
    have hp2 := Finset.mem_Ioc.mp hp'.2
    by_cases ha : p.1 ≤ A
    · have hb : B < p.2 := by
        by_contra h
        apply hnot
        exact Finset.mem_product.mpr ⟨Finset.mem_Ioc.mpr ⟨hp1.1, ha⟩,
          Finset.mem_Ioc.mpr ⟨hp2.1, by omega⟩⟩
      rw [hg _ hb, mul_zero]
    · rw [hf _ (by omega), zero_mul]

/-- Source-normalized finite prefix polynomial of an arbitrary coefficient. -/
def prefixPolynomial (q N : ℕ) (f : ArithmeticFunction ℂ)
    (chi : DirichletCharacter ℂ q) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc 0 N, normalizedAF chi t f n

theorem prefixPolynomial_mul {q A B : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B)
    (f g : ArithmeticFunction ℂ)
    (hf : ∀ n, A < n → f n = 0) (hg : ∀ n, B < n → g n = 0)
    (chi : DirichletCharacter ℂ q) (t : ℝ) :
    prefixPolynomial q (A * B) (f * g) chi t =
      prefixPolynomial q A f chi t * prefixPolynomial q B g chi t := by
  unfold prefixPolynomial
  rw [normalizedAF_mul]
  apply sum_Ioc_mul_of_support hA hB
  · intro n hn
    simp [normalizedAF, normalizedTwistedTerm, characterTwist, hf n hn]
  · intro n hn
    simp [normalizedAF, normalizedTwistedTerm, characterTwist, hg n hn]

/-- Exact agreement with the normalization used by the proved mean square. -/
theorem prefixPolynomial_eq_twistedFinitePolynomial {q N : ℕ}
    (f : ArithmeticFunction ℂ) (chi : DirichletCharacter ℂ q) (t : ℝ) :
    prefixPolynomial q N f chi t =
      twistedFinitePolynomial q (Finset.Icc 1 N)
        (criticalDyadicCoefficient f) chi t := by
  unfold prefixPolynomial twistedFinitePolynomial
  have hset : Finset.Ioc 0 N = Finset.Icc 1 N := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  rw [hset]
  apply Finset.sum_congr rfl
  intro n hn
  change normalizedTwistedTerm (fun n => chi n) f n t = _
  unfold normalizedTwistedTerm characterTwist criticalDyadicCoefficient
    twistedPhase mellinPhase
  congr 1
  · ring
  · congr 1
    push_cast
    ring

/-- The upper support bound also covers the empty prefix, whose coefficient
is the arithmetic unit supported at one. -/
theorem factorConvolution_zero_above_upper (factors : List NatDyadicFactor)
    {n : ℕ} (hn : factorUpperProduct factors < n) :
    factorConvolution factors n = 0 := by
  cases factors with
  | nil =>
      have hn1 : n ≠ 1 := by simpa using (ne_of_gt hn)
      simp [factorConvolution, ArithmeticFunction.one_apply, hn1]
  | cons f factors => exact factorConvolution_zero_of_upperProduct_lt f factors hn

theorem factorUpperProduct_pos (factors : List NatDyadicFactor)
    (hone : ∀ f ∈ factors, 1 ≤ f.length) : 1 ≤ factorUpperProduct factors := by
  induction factors with
  | nil => simp
  | cons f factors ih =>
      rw [factorUpperProduct_cons]
      have hf := hone f (by simp)
      have ht := ih (fun g hg => hone g (by simp [hg]))
      exact Nat.succ_le_iff.mpr (Nat.mul_pos (by omega) (by omega))

/-- Exact product of every original normalized factor, without collecting
or forgetting any smooth factor in the tail. -/
theorem prefixPolynomial_factorConvolution {q : ℕ}
    (factors : List NatDyadicFactor) (hone : ∀ f ∈ factors, 1 ≤ f.length)
    (chi : DirichletCharacter ℂ q) (t : ℝ) :
    prefixPolynomial q (factorUpperProduct factors) (factorConvolution factors) chi t =
      (factors.map (fun f => prefixPolynomial q (2*f.length) f.coeff chi t)).prod := by
  induction factors with
  | nil =>
      have hset : Finset.Ioc 0 1 = ({1} : Finset ℕ) := by decide
      simp [factorUpperProduct, factorConvolution, prefixPolynomial, hset, normalizedAF,
        normalizedTwistedTerm, characterTwist, mellinPhase]
  | cons f factors ih =>
      have hf := hone f (by simp)
      have htail : ∀ g ∈ factors, 1 ≤ g.length := fun g hg => hone g (by simp [hg])
      rw [factorUpperProduct_cons, factorConvolution,
        prefixPolynomial_mul (by omega : 1 ≤ 2*f.length)
          (factorUpperProduct_pos factors htail) f.coeff (factorConvolution factors)
          (fun n hn => f.support n (by
            intro h
            have := (Finset.mem_Ioc.mp h).2
            omega))
          (fun n hn => factorConvolution_zero_above_upper factors hn), ih htail]
      rfl

/-- Finite prefix evaluation commutes with an actual scalar coefficient. -/
theorem prefixPolynomial_smul {q N : ℕ} (c : ℂ) (f : ArithmeticFunction ℂ)
    (chi : DirichletCharacter ℂ q) (t : ℝ) :
    prefixPolynomial q N (c • f) chi t = c * prefixPolynomial q N f chi t := by
  unfold prefixPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  change normalizedTwistedTerm (fun n => chi n) ((c • f : ArithmeticFunction ℂ) : ℕ → ℂ) n t =
    c * normalizedTwistedTerm (fun n => chi n) f n t
  simp only [normalizedTwistedTerm, characterTwist, ArithmeticFunction.smul_map, smul_eq_mul]
  ring


/-- The source smooth-shell evaluator and finite-prefix evaluator coincide. -/
theorem prefixPolynomial_eq_dyadicFactorPolynomial {q N : ℕ}
    (f : ArithmeticFunction ℂ) (hf : MAPHBPerronSourceData.SupportedNatDyadic N f)
    (chi : DirichletCharacter ℂ q) (t : ℝ) :
    prefixPolynomial q (2*N) f chi t =
      dyadicFactorPolynomial (N : ℝ) (fun n => chi n) f t := by
  rw [← halfLineDirichletPolynomial_eq_dyadicFactorPolynomial
    (MAPHBPerronSourceData.supportedDyadic_coe_of_supportedNatDyadic hf)]
  unfold prefixPolynomial halfLineDirichletPolynomial
  have hset : Finset.Ioc 0 (2*N) = Finset.Icc 1 (2*N) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  have hceil : ⌈(2 : ℝ) * N⌉₊ = 2*N := by
    rw [← Nat.cast_ofNat (n := 2), ← Nat.cast_mul, Nat.ceil_natCast]
  rw [hset, hceil]
  apply Finset.sum_congr rfl
  intro n hn
  rfl


/-- Scalar-weighted short prefix times every retained tail factor. -/
theorem prefixPolynomial_scalar_prefix_tail {q : ℕ}
    (c : ℂ) (factors : List NatDyadicFactor)
    (hone : ∀ f ∈ factors, 1 ≤ f.length) (s : ℕ)
    (chi : DirichletCharacter ℂ q) (t : ℝ) :
    prefixPolynomial q (factorUpperProduct factors) (c • factorConvolution factors) chi t =
      prefixPolynomial q (factorUpperProduct (factors.take s))
        (c • factorConvolution (factors.take s)) chi t *
      ((factors.drop s).map
        (fun f => prefixPolynomial q (2*f.length) f.coeff chi t)).prod := by
  have hsmall : ∀ f ∈ factors.take s, 1 ≤ f.length :=
    fun f hf => hone f (List.mem_of_mem_take hf)
  rw [prefixPolynomial_smul, prefixPolynomial_smul,
    prefixPolynomial_factorConvolution factors hone,
    prefixPolynomial_factorConvolution (factors.take s) hsmall]
  have hprod :
      (factors.map (fun f => prefixPolynomial q (2*f.length) f.coeff chi t)).prod =
      ((factors.take s).map (fun f => prefixPolynomial q (2*f.length) f.coeff chi t)).prod *
      ((factors.drop s).map (fun f => prefixPolynomial q (2*f.length) f.coeff chi t)).prod := by
    rw [← List.prod_append, ← List.map_append, List.take_append_drop]
  rw [hprod]
  ring


end
end MRTDynamicD12PolynomialFactorization

#print axioms MRTDynamicD12PolynomialFactorization.normalizedAF_mul
#print axioms MRTDynamicD12PolynomialFactorization.prefixPolynomial_mul
#print axioms MRTDynamicD12PolynomialFactorization.prefixPolynomial_eq_twistedFinitePolynomial

#print axioms MRTDynamicD12PolynomialFactorization.prefixPolynomial_factorConvolution

#print axioms MRTDynamicD12PolynomialFactorization.prefixPolynomial_scalar_prefix_tail
