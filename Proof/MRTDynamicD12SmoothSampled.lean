import Mathlib.Algebra.BigOperators.Module
import MRTProposition61TypeD1Factorization
import RamachandraTheorem6Unconditional

namespace MRTDynamicD12SmoothSampled
open scoped BigOperators
open MAPMRTLemma210OrthogonalityReduction MAPMRTLemma211AllCharacterSource
open MAPMRTProposition61TypeD1Factorization MAPMRTCorollary25TypeD1CoefficientBound
open MAPMRTCorollary25Instantiation MixedMeanFrontend
open MAPMRTProposition61TypeD1FirstInequality
noncomputable section

/-- A clipped smooth interval, including the actual upper cutoff. -/
def smoothIntervalPolynomial (q L U : ℕ) (chi : DirichletCharacter ℂ q) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc L U, normalizedTwistedTerm (fun n ↦ chi n) (fun _ ↦ 1) n t

theorem normalized_one_eq_prefixTerm {q : ℕ} (chi : DirichletCharacter ℂ q)
    (n : ℕ) (t : ℝ) :
    normalizedTwistedTerm (fun n ↦ chi n) (fun _ ↦ 1) n t =
      (criticalPrefixCoefficient n * chi n) * twistedPhase n t := by
  unfold normalizedTwistedTerm characterTwist criticalPrefixCoefficient twistedPhase mellinPhase
  congr 1
  · ring
  · congr 1
    push_cast
    ring

/-- Exact prefix subtraction for arbitrary clipped endpoints; no compatibility
with an analytic moment range is asserted here. -/
theorem smoothIntervalPolynomial_eq_prefix_sub {q L U : ℕ} (hLU : L ≤ U)
    (chi : DirichletCharacter ℂ q) (t : ℝ) :
    smoothIntervalPolynomial q L U chi t =
      criticalPrefixPolynomial q U chi t - criticalPrefixPolynomial q L chi t := by
  unfold smoothIntervalPolynomial criticalPrefixPolynomial twistedFinitePolynomial prefixSupport
  simp_rw [normalized_one_eq_prefixTerm]
  have hs : Finset.Icc 1 L ⊆ Finset.Icc 1 U := by
    intro n hn
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1,
      (Finset.mem_Icc.mp hn).2.trans hLU⟩
  have heq : Finset.Ioc L U = Finset.Icc 1 U \ Finset.Icc 1 L := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_sdiff, Finset.mem_Icc]
    omega
  rw [heq]
  exact eq_sub_iff_add_eq.mpr (Finset.sum_sdiff hs)

/-- The closed carrier does not introduce the left endpoint: the source one
coefficient enforces the strict dyadic boundary. -/
theorem dyadicOne_eq_smoothInterval {q : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (chi : DirichletCharacter ℂ q) (t : ℝ) :
    dyadicFactorPolynomial M (fun n ↦ chi n) (dyadicOneCoefficient M) t =
      smoothIntervalPolynomial q ⌊M⌋₊ ⌊2 * M⌋₊ chi t := by
  classical
  have hsub : Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊ ⊆ realDyadicSupport M := by
    intro n hn
    have hmem := Finset.mem_Ioc.mp hn
    have hlo : M < (n : ℝ) := (Nat.floor_lt hM).mp hmem.1
    have hhi : (n : ℝ) ≤ 2 * M := (Nat.le_floor_iff (by positivity)).mp hmem.2
    apply mem_realDyadicSupport.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨by omega, ?_⟩, hlo.le, hhi⟩
    exact_mod_cast hhi.trans (Nat.le_ceil (2 * M))
  unfold dyadicFactorPolynomial smoothIntervalPolynomial
  rw [← Finset.sum_subset hsub]
  · apply Finset.sum_congr rfl
    intro n hn
    have hn' := Finset.mem_Ioc.mp hn
    have hlo := (Nat.floor_lt hM).mp hn'.1
    have hhi := (Nat.le_floor_iff (show 0 ≤ 2 * M by positivity)).mp hn'.2
    simp [normalizedTwistedTerm, characterTwist, dyadicOneCoefficient, hlo, hhi]
  · intro n hn hnout
    have hnot : ¬ (M < (n : ℝ) ∧ (n : ℝ) ≤ 2 * M) := by
      intro h
      apply hnout
      exact Finset.mem_Ioc.mpr ⟨(Nat.floor_lt hM).mpr h.1,
        (Nat.le_floor_iff (by positivity)).mpr h.2⟩
    simp [normalizedTwistedTerm, characterTwist, dyadicOneCoefficient, hnot]

theorem dyadicOne_eq_prefix_sub {q : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (chi : DirichletCharacter ℂ q) (t : ℝ) :
    dyadicFactorPolynomial M (fun n ↦ chi n) (dyadicOneCoefficient M) t =
      criticalPrefixPolynomial q ⌊2 * M⌋₊ chi t -
        criticalPrefixPolynomial q ⌊M⌋₊ chi t := by
  rw [dyadicOne_eq_smoothInterval hM, smoothIntervalPolynomial_eq_prefix_sub
    (Nat.floor_mono (by linarith : M ≤ 2 * M))]

/-- Literal logarithmic factor on arbitrary clipped integer endpoints. -/
def smoothLogIntervalPolynomial (q L U : ℕ) (chi : DirichletCharacter ℂ q)
    (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc L U, (Real.log (n : ℝ) : ℂ) *
    normalizedTwistedTerm (fun n ↦ chi n) (fun _ ↦ 1) n t

theorem dyadicLog_eq_smoothLogInterval {q : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (chi : DirichletCharacter ℂ q) (t : ℝ) :
    dyadicFactorPolynomial M (fun n ↦ chi n) (dyadicLogCoefficient M) t =
      smoothLogIntervalPolynomial q ⌊M⌋₊ ⌊2 * M⌋₊ chi t := by
  classical
  have hsub : Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊ ⊆ realDyadicSupport M := by
    intro n hn
    have hmem := Finset.mem_Ioc.mp hn
    have hlo : M < (n : ℝ) := (Nat.floor_lt hM).mp hmem.1
    have hhi : (n : ℝ) ≤ 2 * M := (Nat.le_floor_iff (by positivity)).mp hmem.2
    apply mem_realDyadicSupport.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨by omega, ?_⟩, hlo.le, hhi⟩
    exact_mod_cast hhi.trans (Nat.le_ceil (2 * M))
  unfold dyadicFactorPolynomial smoothLogIntervalPolynomial
  rw [← Finset.sum_subset hsub]
  · apply Finset.sum_congr rfl
    intro n hn
    have hn' := Finset.mem_Ioc.mp hn
    have hlo := (Nat.floor_lt hM).mp hn'.1
    have hhi := (Nat.le_floor_iff (show 0 ≤ 2 * M by positivity)).mp hn'.2
    simp [normalizedTwistedTerm, characterTwist, dyadicLogCoefficient, hlo, hhi]
    ring
  · intro n hn hnout
    have hnot : ¬ (M < (n : ℝ) ∧ (n : ℝ) ≤ 2 * M) := by
      intro h
      apply hnout
      exact Finset.mem_Ioc.mpr ⟨(Nat.floor_lt hM).mpr h.1,
        (Nat.le_floor_iff (by positivity)).mpr h.2⟩
    simp [normalizedTwistedTerm, characterTwist, dyadicLogCoefficient, hnot]

theorem range_normalized_one_eq_prefix {q : ℕ} (chi : DirichletCharacter ℂ q)
    (J : ℕ) (t : ℝ) :
    (∑ n ∈ Finset.range (J + 1),
      normalizedTwistedTerm (fun n ↦ chi n) (fun _ ↦ 1) n t) =
      criticalPrefixPolynomial q J chi t := by
  have heq : Finset.range (J + 1) = insert 0 (Finset.Icc 1 J) := by
    ext n
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [heq, Finset.sum_insert (by simp)]
  simp only [normalizedTwistedTerm, characterTwist, Nat.cast_zero, Real.sqrt_zero,
    Complex.ofReal_zero, div_zero, zero_mul, zero_add]
  unfold criticalPrefixPolynomial twistedFinitePolynomial prefixSupport
  apply Finset.sum_congr rfl
  intro n hn
  exact normalized_one_eq_prefixTerm chi n t

/-- Finite Abel identity with literal critical prefixes. The lower term and
all intermediate prefixes are explicit, so top-cutoff clipping is exact. -/
theorem smoothLogInterval_eq_abel {q L U : ℕ} (hLU : L < U)
    (chi : DirichletCharacter ℂ q) (t : ℝ) :
    smoothLogIntervalPolynomial q L U chi t =
      (Real.log (U : ℝ) : ℂ) * criticalPrefixPolynomial q U chi t -
      (Real.log ((L + 1 : ℕ) : ℝ) : ℂ) * criticalPrefixPolynomial q L chi t -
      ∑ n ∈ Finset.Ioc L (U - 1),
        ((Real.log ((n + 1 : ℕ) : ℝ) : ℂ) - (Real.log (n : ℝ) : ℂ)) *
          criticalPrefixPolynomial q n chi t := by
  have hb := Finset.sum_Ioc_by_parts
    (fun n ↦ (Real.log (n : ℝ) : ℂ))
    (fun n ↦ normalizedTwistedTerm (fun n ↦ chi n) (fun _ ↦ 1) n t) hLU
  simp only [smul_eq_mul, range_normalized_one_eq_prefix] at hb
  exact hb

/-- Exact total variation cost of finite Abel summation. -/
def logAbelVariation (L U : ℕ) : ℝ :=
  |Real.log (U : ℝ)| + |Real.log ((L + 1 : ℕ) : ℝ)| +
    ∑ n ∈ Finset.Ioc L (U - 1),
      |Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ)|

theorem logAbelVariation_eq {L U : ℕ} (hLU : L < U) :
    logAbelVariation L U = 2 * Real.log (U : ℝ) := by
  have hU : (1 : ℝ) ≤ U := by exact_mod_cast (show 1 ≤ U by omega)
  have hL : (1 : ℝ) ≤ (L + 1 : ℕ) := by exact_mod_cast (show 1 ≤ L + 1 by omega)
  unfold logAbelVariation
  rw [abs_of_nonneg (Real.log_nonneg hU), abs_of_nonneg (Real.log_nonneg hL)]
  have hsum : (∑ n ∈ Finset.Ioc L (U - 1),
      |Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ)|) =
      Real.log (U : ℝ) - Real.log ((L + 1 : ℕ) : ℝ) := by
    have heq : Finset.Ioc L (U - 1) = Finset.Ico (L + 1) U := by
      ext n
      simp only [Finset.mem_Ioc, Finset.mem_Ico]
      omega
    rw [heq]
    calc
      _ = ∑ n ∈ Finset.Ico (L + 1) U,
          (Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ)) := by
        apply Finset.sum_congr rfl
        intro n hn
        have hnpos : (0 : ℝ) < n := by
          exact_mod_cast (show 0 < n from lt_of_lt_of_le (by omega) (Finset.mem_Ico.mp hn).1)
        apply abs_of_nonneg
        exact sub_nonneg.mpr (Real.log_le_log hnpos (by exact_mod_cast Nat.le_succ n))
      _ = _ := Finset.sum_Ico_sub (fun n ↦ Real.log (n : ℝ)) (by omega)
  rw [hsum]
  ring

theorem smoothLogInterval_norm_le_prefix_bound {q L U : ℕ} (hLU : L < U)
    (chi : DirichletCharacter ℂ q) (t V : ℝ)
    (hprefix : ∀ J ∈ Finset.Icc L U, ‖criticalPrefixPolynomial q J chi t‖ ≤ V) :
    ‖smoothLogIntervalPolynomial q L U chi t‖ ≤ logAbelVariation L U * V := by
  rw [smoothLogInterval_eq_abel hLU]
  have hL := hprefix L (Finset.mem_Icc.mpr ⟨le_rfl, hLU.le⟩)
  have hU := hprefix U (Finset.mem_Icc.mpr ⟨hLU.le, le_rfl⟩)
  calc
    _ ≤ ‖(Real.log (U : ℝ) : ℂ) * criticalPrefixPolynomial q U chi t -
          (Real.log ((L + 1 : ℕ) : ℝ) : ℂ) * criticalPrefixPolynomial q L chi t‖ +
        ‖∑ n ∈ Finset.Ioc L (U - 1),
          ((Real.log ((n + 1 : ℕ) : ℝ) : ℂ) - (Real.log (n : ℝ) : ℂ)) *
            criticalPrefixPolynomial q n chi t‖ := norm_sub_le _ _
    _ ≤ (‖(Real.log (U : ℝ) : ℂ) * criticalPrefixPolynomial q U chi t‖ +
          ‖(Real.log ((L + 1 : ℕ) : ℝ) : ℂ) * criticalPrefixPolynomial q L chi t‖) +
        ∑ n ∈ Finset.Ioc L (U - 1),
          ‖((Real.log ((n + 1 : ℕ) : ℝ) : ℂ) - (Real.log (n : ℝ) : ℂ)) *
            criticalPrefixPolynomial q n chi t‖ :=
      add_le_add (norm_sub_le _ _) (norm_sum_le _ _)
    _ ≤ (|Real.log (U : ℝ)| * V + |Real.log ((L + 1 : ℕ) : ℝ)| * V) +
        ∑ n ∈ Finset.Ioc L (U - 1),
          |Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ)| * V := by
      simp only [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      apply add_le_add
      · exact add_le_add (mul_le_mul_of_nonneg_left hU (abs_nonneg _))
          (mul_le_mul_of_nonneg_left hL (abs_nonneg _))
      · apply Finset.sum_le_sum
        intro n hn
        have hn' := Finset.mem_Ioc.mp hn
        exact mul_le_mul_of_nonneg_left
          (hprefix n (Finset.mem_Icc.mpr ⟨hn'.1.le, by omega⟩)) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; unfold logAbelVariation; ring

theorem norm_sub_fourth_le (a b : ℂ) :
    ‖a - b‖ ^ 4 ≤ 8 * (‖a‖ ^ 4 + ‖b‖ ^ 4) := by
  have h := pow_le_pow_left₀ (norm_nonneg (a - b)) (norm_sub_le a b) 4
  have hsq := sq_nonneg (‖a‖ - ‖b‖)
  have hsq2 := sq_nonneg (‖a‖ ^ 2 - ‖b‖ ^ 2)
  have hprod := mul_nonneg hsq (sq_nonneg (‖a‖ + ‖b‖))
  nlinarith

theorem smoothInterval_fourth_le {q L U : ℕ} (hLU : L ≤ U)
    (chi : DirichletCharacter ℂ q) (t : ℝ) :
    ‖smoothIntervalPolynomial q L U chi t‖ ^ 4 ≤
      8 * (‖criticalPrefixPolynomial q U chi t‖ ^ 4 +
        ‖criticalPrefixPolynomial q L chi t‖ ^ 4) := by
  rw [smoothIntervalPolynomial_eq_prefix_sub hLU]
  exact norm_sub_fourth_le _ _

theorem smoothLogInterval_fourth_le_prefix_bound {q L U : ℕ} (hLU : L < U)
    (chi : DirichletCharacter ℂ q) (t V : ℝ)
    (hprefix : ∀ J ∈ Finset.Icc L U, ‖criticalPrefixPolynomial q J chi t‖ ≤ V) :
    ‖smoothLogIntervalPolynomial q L U chi t‖ ^ 4 ≤
      16 * Real.log (U : ℝ) ^ 4 * V ^ 4 := by
  have h := smoothLogInterval_norm_le_prefix_bound hLU chi t V hprefix
  rw [logAbelVariation_eq hLU] at h
  have hp := pow_le_pow_left₀ (norm_nonneg _) h 4
  nlinarith [hp]

 theorem smoothInterval_sampled_le {q L U : ℕ} [NeZero q] (hLU : L ≤ U)
    (S : Finset (DirichletCharacter ℂ q × ℝ))
    (left right : DirichletCharacter ℂ q × ℝ → ℝ)
    (hlen : ∀ z ∈ S, left z ≤ right z) :
    bhpSampledPieceMass (fun chi t ↦ ‖smoothIntervalPolynomial q L U chi t‖)
      S left right ≤
    8 * (bhpSampledPieceMass (fun chi t ↦ ‖criticalPrefixPolynomial q U chi t‖)
      S left right +
      bhpSampledPieceMass (fun chi t ↦ ‖criticalPrefixPolynomial q L chi t‖)
      S left right) := by
  have hc (chi : DirichletCharacter ℂ q) (J : ℕ) :
      Continuous (fun t ↦ ‖criticalPrefixPolynomial q J chi t‖ ^ 4) := by
    unfold criticalPrefixPolynomial twistedFinitePolynomial twistedPhase
    fun_prop
  have hd (chi : DirichletCharacter ℂ q) :
      Continuous (fun t ↦ ‖smoothIntervalPolynomial q L U chi t‖ ^ 4) := by
    simp_rw [smoothIntervalPolynomial_eq_prefix_sub hLU]
    unfold criticalPrefixPolynomial twistedFinitePolynomial twistedPhase
    fun_prop
  unfold bhpSampledPieceMass
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z hz
  calc
    _ ≤ ∫ t in left z..right z,
        8 * (‖criticalPrefixPolynomial q U z.1 t‖ ^ 4 +
          ‖criticalPrefixPolynomial q L z.1 t‖ ^ 4) := by
      apply intervalIntegral.integral_mono_on (hlen z hz)
        ((hd z.1).intervalIntegrable _ _)
        ((continuous_const.mul ((hc z.1 U).add (hc z.1 L))).intervalIntegrable _ _)
      intro t ht
      exact smoothInterval_fourth_le hLU z.1 t
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
        ((hc z.1 U).intervalIntegrable _ _) ((hc z.1 L).intervalIntegrable _ _)]

open MAPPolylogCor212SplitDefinitions MAPPolylogCor212SplitSampled

/-- Exact sampled source RHS, preserving cutoff and principal-character errors. -/
def sampledBudgetShape (q J : ℕ) (T A : ℝ) : ℝ :=
  (q : ℝ) * T + (A * (q : ℝ) * T) *
    ((q : ℝ)^2 / T^2 + (J : ℝ)^2 / T^4 + 1 / (J : ℝ)^2) +
    (J : ℝ)^2 * ((A * (q : ℝ) * T) * (16 / T^4))

/-- Both literal endpoint ranges and both prefix sampling conditions are
retained. No dyadic-factor maximizer is substituted for a prefix maximizer. -/
theorem smoothInterval_sampled_budget :
    ∃ C : ℝ, 0 < C ∧ ∃ B : ℕ, 4 ≤ B ∧
    ∀ {X H Q lambda V T K : ℝ} {q L U : ℕ} [NeZero q]
      {S : Finset (DirichletCharacter ℂ q × ℝ)}
      {left right : DirichletCharacter ℂ q × ℝ → ℝ} {A : ℝ},
      L ≤ U →
      MAPTypeD12MomentRange X H Q lambda V T K q L →
      MAPTypeD12MomentRange X H Q lambda V T K q U →
      (∀ z ∈ S, 0 ≤ right z - left z ∧ right z - left z ≤ 1) →
      (∀ J ∈ ({L, U} : Finset ℕ), ∀ z ∈ S, ∀ t ∈ Set.Icc (left z) (right z),
        ‖criticalPrefixPolynomial q J z.1 t‖ ^ 4 ≤
          ‖criticalPrefixPolynomial q J z.1 z.2‖ ^ 4) →
      (∀ z ∈ S, T / 2 ≤ |z.2|) → (∀ z ∈ S, |z.2| ≤ T) →
      (S.card : ℝ) ≤ A * (q : ℝ) * T → SameCharacterOneSeparated S →
      bhpSampledPieceMass (fun chi t ↦ ‖smoothIntervalPolynomial q L U chi t‖)
        S left right ≤ C * (1 + Real.log X)^B *
          (sampledBudgetShape q U T A + sampledBudgetShape q L T A) := by
  classical
  obtain ⟨C, hC, B, hB, hb⟩ :=
    RamachandraTheorem6Unconditional.mapLowTypeD12SampledBudget_proved
  refine ⟨8 * C, by positivity, B, hB, ?_⟩
  intro X H Q lambda V T K q L U inst S left right A hLU hL hU hlen hmax ha hh hn hs
  have bL := hb hL hlen (hmax L (by simp)) ha hh hn hs
  have bU := hb hU hlen (hmax U (by simp)) ha hh hn hs
  have hd := smoothInterval_sampled_le hLU S left right
    (fun z hz ↦ by linarith [(hlen z hz).1])
  change _ ≤ C * (1 + Real.log X)^B * sampledBudgetShape q L T A at bL
  change _ ≤ C * (1 + Real.log X)^B * sampledBudgetShape q U T A at bU
  calc
    _ ≤ 8 * (_ + _) := hd
    _ ≤ 8 * (C * (1 + Real.log X)^B * sampledBudgetShape q U T A +
        C * (1 + Real.log X)^B * sampledBudgetShape q L T A) := by linarith
    _ = _ := by ring

end
end MRTDynamicD12SmoothSampled
