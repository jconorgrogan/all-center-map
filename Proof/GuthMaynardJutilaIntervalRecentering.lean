import GuthMaynardLengthComparison
import GuthMaynardJutilaReflection2941

/-!
# Recentering the Heath--Brown interval for the Jutila moment

The public Heath--Brown interface allows the ordinate set to lie in an
arbitrary interval `[x,x+T]`, whereas Jutila's Lemma 29.10 is stated for a
subset of `(0,T]`.  This file supplies the exact finite translation needed
between those conventions.  Translation preserves the one-spacing, the
cardinality, and the Jutila difference moment; adding one to every translated
ordinate puts even a point at the left endpoint strictly above zero.
-/

namespace GuthMaynardJutilaIntervalRecentering

open scoped BigOperators
open CGLProofDAG
open GuthMaynardHeathBrownInterface
open GuthMaynardHeathBrownMajorant
open GuthMaynardLengthComparison

noncomputable section

/-- The affine translation `t ↦ t-x+1`, as an embedding. -/
def intervalRecenterEmbedding (x : ℝ) : ℝ ↪ ℝ where
  toFun t := t - x + 1
  inj' := by
    intro t u h
    linarith

/-- Recenter an arbitrary interval `[x,x+T]` into `(0,T+1]`. -/
def intervalRecenter (x : ℝ) (W : Finset ℝ) : Finset ℝ :=
  W.map (intervalRecenterEmbedding x)

@[simp]
theorem intervalRecenterEmbedding_apply (x t : ℝ) :
    intervalRecenterEmbedding x t = t - x + 1 := rfl

@[simp]
theorem card_intervalRecenter (x : ℝ) (W : Finset ℝ) :
    (intervalRecenter x W).card = W.card := by
  simp [intervalRecenter]

theorem intervalRecenter_oneSeparated
    {W : Finset ℝ} (hsep : OneSeparated W) (x : ℝ) :
    OneSeparated (intervalRecenter x W) := by
  intro t ht u hu htu
  obtain ⟨t₀, ht₀, rfl⟩ := Finset.mem_map.mp ht
  obtain ⟨u₀, hu₀, rfl⟩ := Finset.mem_map.mp hu
  have hne : t₀ ≠ u₀ := by
    intro h
    subst u₀
    exact htu rfl
  simpa only [intervalRecenterEmbedding_apply,
    show t₀ - x + 1 - (u₀ - x + 1) = t₀ - u₀ by ring] using
      hsep t₀ ht₀ u₀ hu₀ hne

theorem intervalRecenter_inOpenClosedZero
    {W : Finset ℝ} {T x : ℝ}
    (hinterval : ∀ t ∈ W, x ≤ t ∧ t ≤ x + T) :
    GuthMaynardJutilaReflection2941.InOpenClosedZeroT
      (intervalRecenter x W) (T + 1) := by
  intro t ht
  obtain ⟨t₀, ht₀, rfl⟩ := Finset.mem_map.mp ht
  have hb := hinterval t₀ ht₀
  constructor <;> simp only [intervalRecenterEmbedding_apply] <;> linarith

/-- The Dirichlet phase changes by a common unit scalar under translation. -/
theorem dirichletPhase_intervalRecenter
    (n : ℕ) (x t : ℝ) :
    dirichletPhase n (t - x + 1) =
      dirichletPhase n (1 - x) * dirichletPhase n t := by
  unfold dirichletPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem norm_dirichletPhase_intervalRecenter_factor (n : ℕ) (x : ℝ) :
    ‖dirichletPhase n (1 - x)‖ = 1 := by
  unfold dirichletPhase
  simpa using Complex.norm_exp_ofReal_mul_I ((1 - x) * Real.log n)

/-- A common translation of both ordinate variables leaves every Jutila
difference polynomial norm unchanged. -/
theorem norm_gramPolynomial_intervalRecenter
    (S : Finset ℕ) (a : ℕ → ℂ) (x t u : ℝ) :
    ‖gramPolynomial S a dirichletPhase (t - x + 1) (u - x + 1)‖ =
      ‖gramPolynomial S a dirichletPhase t u‖ := by
  have hpoly :
      gramPolynomial S a dirichletPhase (t - x + 1) (u - x + 1) =
        gramPolynomial S a dirichletPhase t u := by
    unfold gramPolynomial
    apply Finset.sum_congr rfl
    intro n hn
    rw [dirichletPhase_intervalRecenter,
      dirichletPhase_intervalRecenter, star_mul]
    have hunit : dirichletPhase n (1 - x) *
        star (dirichletPhase n (1 - x)) = 1 := by
      change dirichletPhase n (1 - x) *
        (starRingEnd ℂ) (dirichletPhase n (1 - x)) = 1
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq,
        norm_dirichletPhase_intervalRecenter_factor]
      norm_num
    calc
      a n * (dirichletPhase n (1 - x) * dirichletPhase n t) *
          (star (dirichletPhase n u) *
            star (dirichletPhase n (1 - x))) =
        (dirichletPhase n (1 - x) *
          star (dirichletPhase n (1 - x))) *
          (a n * dirichletPhase n t * star (dirichletPhase n u)) := by
            ring
      _ = a n * dirichletPhase n t * star (dirichletPhase n u) := by
        rw [hunit, one_mul]
  rw [hpoly]

/-- The complete coefficient-one Jutila moment is translation invariant. -/
theorem jutilaSecondMoment_intervalRecenter
    (M x : ℝ) (W : Finset ℝ) :
    jutilaSecondMoment M (intervalRecenter x W) =
      jutilaSecondMoment M W := by
  unfold jutilaSecondMoment realGramQuadratic intervalRecenter
  simp only [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.sum_congr rfl
  intro u hu
  simp only [intervalRecenterEmbedding_apply]
  rw [norm_gramPolynomial_intervalRecenter]

end

end GuthMaynardJutilaIntervalRecentering

#print axioms GuthMaynardJutilaIntervalRecentering.intervalRecenter_oneSeparated
#print axioms GuthMaynardJutilaIntervalRecentering.intervalRecenter_inOpenClosedZero
#print axioms GuthMaynardJutilaIntervalRecentering.jutilaSecondMoment_intervalRecenter
