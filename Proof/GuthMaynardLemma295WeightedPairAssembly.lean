import GuthMaynardLemma295PairMajorant
import GuthMaynardLemma62PairAssembly

/-!
# Weighted pair assembly in Jutila Lemma 29.5

This file performs the weighted Cauchy--Schwarz and finite Fubini step after
the reflected approximate functional equation.  The exact Cauchy weight has
total mass at most `pi`; the common Mellin shift is removed by the certified
finite Gram majorant.
-/

namespace GuthMaynardLemma295WeightedPairAssembly

open scoped BigOperators
open MeasureTheory
open GuthMaynardJutilaReflection2941
open GuthMaynardLemma295PairMajorant
open GuthMaynardLemma62PairAssembly

noncomputable section

/-- The complete central-integral pair moment is at most `N*pi^2` times the
coefficient-one reflected prefix moment. -/
theorem centralMajorant_pairMoment_le
    {N : ℝ} (hN : 0 ≤ N) (M R : ℝ) (G : Finset ℝ) :
    (∑ g₁ ∈ G, ∑ g₂ ∈ G,
      (lemma295CentralMajorant N M (g₁ - g₂) R) ^ 2) ≤
      N * Real.pi ^ 2 * jutilaReflectedPrefixMoment M G := by
  let w : ℝ → ℝ := fun t => (1 + t ^ 2)⁻¹
  let f : ℝ → ℝ → ℝ → ℝ := fun g₁ g₂ t =>
    ‖lemma295ReflectedPolynomial M ((g₁ - g₂) + t)‖
  have hw : Continuous w := by
    dsimp [w]
    apply Continuous.inv₀
    · fun_prop
    · intro t
      positivity
  have hf : ∀ g₁ g₂, Continuous (f g₁ g₂) := by
    intro g₁ g₂
    dsimp [f]
    unfold lemma295ReflectedPolynomial
      GuthMaynardHeathBrownMajorant.dirichletPhase
    fun_prop
  have hw0 : ∀ t, 0 ≤ w t := by
    intro t
    dsimp [w]
    positivity
  have hf0 : ∀ g₁ g₂ t, 0 ≤ f g₁ g₂ t := by
    intro g₁ g₂ t
    exact norm_nonneg _
  have hweighted := finitePair_weighted_integral_sq_le G
    (w := w) (f := f) (R := R)
    (Q := jutilaReflectedPrefixMoment M G)
    hw hf hw0 hf0 (fun t => by
      simpa [f] using shifted_reflected_pairMoment_le_prefix M t G)
  let A : ℝ := ∫ t : ℝ in Set.Ioc (-R) R, w t
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact integral_nonneg hw0
  have hAle : A ≤ Real.pi := by
    dsimp [A, w]
    calc
      (∫ t : ℝ in Set.Ioc (-R) R, (1 + t ^ 2)⁻¹) ≤
          ∫ t : ℝ, (1 + t ^ 2)⁻¹ :=
        setIntegral_le_integral integrable_inv_one_add_sq
          (Filter.Eventually.of_forall fun t => by positivity)
      _ = Real.pi := integral_univ_inv_one_add_sq
  have hAsq : A ^ 2 ≤ Real.pi ^ 2 :=
    pow_le_pow_left₀ hA0 hAle 2
  have hprefix0 : 0 ≤ jutilaReflectedPrefixMoment M G :=
    jutilaReflectedPrefixMoment_nonneg M G
  have hsqrt : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN
  have hcentralEq :
      (∑ g₁ ∈ G, ∑ g₂ ∈ G,
        (lemma295CentralMajorant N M (g₁ - g₂) R) ^ 2) =
      N * ∑ g₁ ∈ G, ∑ g₂ ∈ G,
        (∫ t : ℝ in Set.Ioc (-R) R, w t * f g₁ g₂ t) ^ 2 := by
    unfold lemma295CentralMajorant
    simp_rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro g₁ hg₁
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro g₂ hg₂
    rw [mul_pow, hsqrt]
    congr 1
    congr 1
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    dsimp [w, f]
    rw [div_eq_mul_inv]
    ring
  rw [hcentralEq]
  calc
    N * ∑ g₁ ∈ G, ∑ g₂ ∈ G,
        (∫ t : ℝ in Set.Ioc (-R) R, w t * f g₁ g₂ t) ^ 2 ≤
      N * (A ^ 2 * jutilaReflectedPrefixMoment M G) :=
        mul_le_mul_of_nonneg_left (by simpa [A] using hweighted) hN
    _ ≤ N * (Real.pi ^ 2 * jutilaReflectedPrefixMoment M G) := by
      gcongr
    _ = N * Real.pi ^ 2 * jutilaReflectedPrefixMoment M G := by ring

end

end GuthMaynardLemma295WeightedPairAssembly

#print axioms GuthMaynardLemma295WeightedPairAssembly.centralMajorant_pairMoment_le
