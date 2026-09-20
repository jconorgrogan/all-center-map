import GuthMaynardSourceLemmas
import FixedCharacterPoweredBridge

/-!
# Deterministic inequalities in Guth--Maynard Lemma 9.2

This module starts the proof of the iterative `J(f)` estimate at its literal
Cauchy--Schwarz steps (source equations (9.8) and (9.12), extracted TeX lines
1571--1574 and 1651--1655).  It also isolates the exact square-root bootstrap
used to pass from Lemma 9.2 to Proposition 9.1.

No Fourier decay, Poisson summation, divisor bound, or affine counting estimate
is assumed or restated here.
-/

namespace GuthMaynardJIteration

open scoped BigOperators Interval
open MeasureTheory
open CGLProofDAG

noncomputable section

/-! ## Finite Cauchy--Schwarz used in the frequency sums -/

/-- Squared triangle plus finite Cauchy--Schwarz.  This is the exact abstract
inequality used twice when the proof squares the outer `(m₁, ell)` sum. -/
theorem norm_finset_sum_sq_le_card_mul_sum_norm_sq
    {ι E : Type*} [NormedAddCommGroup E]
    (s : Finset ι) (F : ι → E) :
    ‖∑ i ∈ s, F i‖ ^ 2 ≤
      (s.card : ℝ) * ∑ i ∈ s, ‖F i‖ ^ 2 := by
  have htriangle : ‖∑ i ∈ s, F i‖ ≤ ∑ i ∈ s, ‖F i‖ :=
    norm_sum_le _ _
  have hsum_nonneg : 0 ≤ ∑ i ∈ s, ‖F i‖ :=
    Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hcs : (∑ i ∈ s, ‖F i‖) ^ 2 ≤
      (s.card : ℝ) * ∑ i ∈ s, ‖F i‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  nlinarith [norm_nonneg (∑ i ∈ s, F i)]

/-- If all summands have norm at most `B`, the same step gives the explicit
cardinality-square bound used in the low-frequency region. -/
theorem norm_finset_sum_sq_le_card_sq_mul
    {ι E : Type*} [NormedAddCommGroup E]
    (s : Finset ι) (F : ι → E) {B : ℝ}
    (hFB : ∀ i ∈ s, ‖F i‖ ≤ B) :
    ‖∑ i ∈ s, F i‖ ^ 2 ≤ (s.card : ℝ) ^ 2 * B ^ 2 := by
  calc
    ‖∑ i ∈ s, F i‖ ^ 2 ≤
        (s.card : ℝ) * ∑ i ∈ s, ‖F i‖ ^ 2 :=
      norm_finset_sum_sq_le_card_mul_sum_norm_sq s F
    _ ≤ (s.card : ℝ) * ∑ _i ∈ s, B ^ 2 := by
      gcongr with i hi
      exact hFB i hi
    _ = (s.card : ℝ) ^ 2 * B ^ 2 := by
      simp
      ring

/-! ## The exact factorization count in the medium-frequency range -/

/-- A finite collection of signed integer divisors of a nonzero integer has
at most two representatives for each positive divisor of its absolute value.
This is the exact finite counting statement behind source TeX 1585. -/
theorem card_signed_divisors_le_two_mul_card_divisors
    {s : ℤ} (hs : s ≠ 0) (D : Finset ℤ)
    (hD : ∀ d ∈ D, d ∣ s) :
    D.card ≤ 2 * s.natAbs.divisors.card := by
  let signs : Finset ℤ := {-1, 1}
  let target : Finset (ℤ × ℕ) := signs ×ˢ s.natAbs.divisors
  let encode : ℤ → ℤ × ℕ := fun d ↦ (d.sign, d.natAbs)
  have hmaps : Set.MapsTo encode (D : Set ℤ) (target : Set (ℤ × ℕ)) := by
    intro d hd
    have hdD : d ∈ D := hd
    have hdvd := hD d hdD
    have hd0 : d ≠ 0 := by
      intro hdzero
      subst d
      exact hs (by simpa using hdvd)
    have hsign : d.sign ∈ signs := by
      simp only [signs, Finset.mem_insert, Finset.mem_singleton]
      by_cases hdpos : 0 < d
      · exact Or.inr (Int.sign_eq_one_iff_pos.mpr hdpos)
      · exact Or.inl (Int.sign_eq_neg_one_iff_neg.mpr (lt_of_le_of_ne
          (le_of_not_gt hdpos) hd0))
    have hsabs : s.natAbs ≠ 0 := by
      simpa using hs
    have habs : d.natAbs ∈ s.natAbs.divisors :=
      Nat.mem_divisors.mpr ⟨Int.natAbs_dvd_natAbs.mpr hdvd, hsabs⟩
    exact Finset.mem_product.mpr ⟨hsign, habs⟩
  have hinj : Set.InjOn encode (D : Set ℤ) := by
    intro a ha b hb hab
    have hsign : a.sign = b.sign := congrArg Prod.fst hab
    have habs : a.natAbs = b.natAbs := congrArg Prod.snd hab
    have ha0 : a ≠ 0 := by
      intro hazero
      subst a
      exact hs (by simpa using hD 0 ha)
    rcases Int.natAbs_eq_natAbs_iff.mp habs with rfl | hneg
    · rfl
    · have hbnega : b = -a := by omega
      have hsignneg : a.sign = -a.sign := by
        calc
          a.sign = b.sign := hsign
          _ = (-a).sign := by rw [hbnega]
          _ = -a.sign := Int.sign_neg a
      have : a.sign = 0 := by omega
      exact (ha0 (Int.sign_eq_zero_iff_zero.mp this)).elim
  have hcard := Finset.card_le_card_of_injOn encode hmaps hinj
  simpa [target, signs] using hcard

/-- Away from zero, the order-two convolution divisor majorant is the ordinary
positive divisor count. -/
theorem orderedDivisorCount_two_eq_card_divisors
    {n : ℕ} (hn : n ≠ 0) :
    orderedDivisorCount 2 n = n.divisors.card := by
  rw [FixedCharacterPoweredBridge.orderedDivisorCount_eq_tauAF]
  rw [show 2 = 1 + 1 by omega, MixedMellinCert.tauAF_succ_apply]
  rw [Finset.card_eq_sum_ones]
  apply Finset.sum_congr rfl
  intro d hd
  have hdvd : d ∣ n := (Nat.mem_divisors.mp hd).1
  have hd0 : d ≠ 0 := fun h ↦ hn (by simpa [h] using hdvd)
  simp [MixedMellinCert.tauAF, ArithmeticFunction.zeta_apply, hd0]

/-- The exact signed factor count has the uniform subpower loss used in the
medium-frequency Cauchy--Schwarz step.  This discharges the source assertion
that a nonzero `s` has `T^o(1)` factorizations once `|s|` is polynomial in `T`;
the remaining conversion from `|s|^eta` to a chosen `T`-loss is exponent
bookkeeping. -/
theorem card_signed_divisors_subpolynomial :
    ∀ η : ℝ, 0 < η →
      ∃ C : ℝ, 0 < C ∧
        ∀ (s : ℤ) (D : Finset ℤ), s ≠ 0 →
          (∀ d ∈ D, d ∣ s) →
          (D.card : ℝ) ≤ C * Real.rpow s.natAbs η := by
  intro η hη
  obtain ⟨C, hC, hsub⟩ :=
    FixedCharacterPoweredBridge.orderedDivisorCount_subpolynomial
      2 (by norm_num) η hη
  refine ⟨2 * C, by positivity, ?_⟩
  intro s D hs hD
  have hsabs : s.natAbs ≠ 0 := by simpa using hs
  have hcardNat := card_signed_divisors_le_two_mul_card_divisors hs D hD
  have hcard : (D.card : ℝ) ≤ 2 * (s.natAbs.divisors.card : ℝ) := by
    exact_mod_cast hcardNat
  have hdiv : (s.natAbs.divisors.card : ℝ) ≤
      C * Real.rpow s.natAbs η := by
    rw [← orderedDivisorCount_two_eq_card_divisors hsabs]
    exact hsub s.natAbs (Nat.pos_of_ne_zero hsabs)
  calc
    (D.card : ℝ) ≤ 2 * (s.natAbs.divisors.card : ℝ) := hcard
    _ ≤ 2 * (C * Real.rpow s.natAbs η) :=
      mul_le_mul_of_nonneg_left hdiv (by norm_num)
    _ = (2 * C) * Real.rpow s.natAbs η := by ring

/-! ## Integral Cauchy--Schwarz used in equation (9.12) -/

/-- Compact-interval Cauchy--Schwarz in exactly the squared form needed after
the affine counting expression has been reached. -/
theorem intervalIntegral_mul_sq_le
    {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    {a b : ℝ} (hab : a ≤ b) :
    (∫ x in a..b, f x * g x) ^ 2 ≤
      (∫ x in a..b, f x ^ 2) * (∫ x in a..b, g x ^ 2) := by
  let μ : Measure ℝ := volume.restrict (Set.Ioc a b)
  have hfm : MemLp f 2 μ := by
    apply (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).2
    exact (hf.pow 2).intervalIntegrable a b |>.1
  have hgm : MemLp g 2 μ := by
    apply (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).2
    exact (hg.pow 2).intervalIntegrable a b |>.1
  have hpq : Real.HolderConjugate 2 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) hpq
    (Filter.Eventually.of_forall hf0) (Filter.Eventually.of_forall hg0)
    (by simpa using hfm) (by simpa using hgm)
  dsimp [μ] at hh
  simp_rw [intervalIntegral.integral_of_le hab]
  simp only [Real.rpow_two, one_div] at hh
  have hrpow (x : ℝ) : x ^ (2 : ℝ)⁻¹ = Real.sqrt x := by
    rw [Real.sqrt_eq_rpow]
    norm_num
  rw [hrpow, hrpow] at hh
  have hI : 0 ≤ ∫ x in Set.Ioc a b, f x * g x :=
    integral_nonneg fun x ↦ mul_nonneg (hf0 x) (hg0 x)
  have hA : 0 ≤ ∫ x in Set.Ioc a b, f x ^ 2 :=
    integral_nonneg fun x ↦ sq_nonneg _
  have hB : 0 ≤ ∫ x in Set.Ioc a b, g x ^ 2 :=
    integral_nonneg fun x ↦ sq_nonneg _
  nlinarith [Real.sq_sqrt hA, Real.sq_sqrt hB,
    sq_nonneg (Real.sqrt (∫ x in Set.Ioc a b, f x ^ 2) -
      Real.sqrt (∫ x in Set.Ioc a b, g x ^ 2))]

/-! ## Exact square-root bootstrap after Lemma 9.2 -/

/-- The numerical core of the downward-epsilon induction.  If the iterative
lemma gives `J <= A + sqrt B * sqrt Jnext` and the induction hypothesis gives
`Jnext <= K * (A+B)`, then the mixed term costs only `sqrt K`, not `K`.

This is the step responsible for the source's `3*epsilon/2 -> 3*epsilon/4`
gain. -/
theorem iterative_sqrt_bootstrap
    {A B J Jnext K : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hJnext : 0 ≤ Jnext) (hK : 0 ≤ K)
    (hiter : J ≤ A + Real.sqrt B * Real.sqrt Jnext)
    (hnext : Jnext ≤ K * (A + B)) :
    J ≤ A + Real.sqrt K * (A + B) := by
  have hAB : 0 ≤ A + B := add_nonneg hA hB
  have hBK : 0 ≤ B * K := mul_nonneg hB hK
  have hprod : B * Jnext ≤ K * (A + B) ^ 2 := by
    calc
      B * Jnext ≤ B * (K * (A + B)) :=
        mul_le_mul_of_nonneg_left hnext hB
      _ = K * B * (A + B) := by ring
      _ ≤ K * (A + B) * (A + B) := by
        gcongr
        linarith
      _ = K * (A + B) ^ 2 := by ring
  have hsqrtB : 0 ≤ Real.sqrt B := Real.sqrt_nonneg _
  have hsqrtJ : 0 ≤ Real.sqrt Jnext := Real.sqrt_nonneg _
  have hsqrtK : 0 ≤ Real.sqrt K := Real.sqrt_nonneg _
  have hleftsq : (Real.sqrt B * Real.sqrt Jnext) ^ 2 = B * Jnext := by
    rw [mul_pow, Real.sq_sqrt hB, Real.sq_sqrt hJnext]
  have hrightsq : (Real.sqrt K * (A + B)) ^ 2 = K * (A + B) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hK]
  have hmixed : Real.sqrt B * Real.sqrt Jnext ≤
      Real.sqrt K * (A + B) := by
    apply (sq_le_sq₀ (mul_nonneg hsqrtB hsqrtJ)
      (mul_nonneg hsqrtK hAB)).mp
    rw [hleftsq, hrightsq]
    exact hprod
  exact hiter.trans (by linarith)

end

end GuthMaynardJIteration

#print axioms GuthMaynardJIteration.norm_finset_sum_sq_le_card_mul_sum_norm_sq
#print axioms GuthMaynardJIteration.norm_finset_sum_sq_le_card_sq_mul
#print axioms GuthMaynardJIteration.card_signed_divisors_le_two_mul_card_divisors
#print axioms GuthMaynardJIteration.orderedDivisorCount_two_eq_card_divisors
#print axioms GuthMaynardJIteration.card_signed_divisors_subpolynomial
#print axioms GuthMaynardJIteration.intervalIntegral_mul_sq_le
#print axioms GuthMaynardJIteration.iterative_sqrt_bootstrap
