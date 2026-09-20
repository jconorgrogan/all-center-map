import Mathlib

/-!
# A finite Fejer kernel on the normalized additive circle

This file develops the algebraic and Haar-normalization part of the finite
harmonic localization bridge directly from finite sums.  The convention is
that `dirichletBlock H` contains the frequencies `0, ..., H - 1`, and
`fejerKernel H = H⁻¹ |dirichletBlock H|²`.
-/

namespace FejerLocalMass

open AddCircle MeasureTheory
open scoped BigOperators ComplexConjugate

noncomputable section

/-- The one-sided Dirichlet block with exactly `H` frequencies. -/
def dirichletBlock (H : ℕ) (x : UnitAddCircle) : ℂ :=
  ∑ j ∈ Finset.range H, fourier (j : ℤ) x

/-- The Fejer kernel `H⁻¹ |1 + e(x) + ... + e((H-1)x)|²`.

At `H = 0` this is totalized to zero by the field inverse convention.
-/
def fejerKernel (H : ℕ) (x : UnitAddCircle) : ℂ :=
  (H : ℂ)⁻¹ * dirichletBlock H x * conj (dirichletBlock H x)

/-- Number of ordered pairs in `[0,H)²` with prescribed difference. -/
def pairMultiplicity (H : ℕ) (k : ℤ) : ℕ :=
  ((Finset.range H ×ˢ Finset.range H).filter
    (fun p => (p.1 : ℤ) - (p.2 : ℤ) = k)).card

theorem dirichletBlock_continuous (H : ℕ) : Continuous (dirichletBlock H) := by
  change Continuous (fun x : UnitAddCircle =>
    ∑ j ∈ Finset.range H, fourier (j : ℤ) x)
  fun_prop

theorem fejerKernel_continuous (H : ℕ) : Continuous (fejerKernel H) := by
  change Continuous (fun x : UnitAddCircle =>
    (H : ℂ)⁻¹ * dirichletBlock H x * conj (dirichletBlock H x))
  have hd := dirichletBlock_continuous H
  fun_prop

/-- The kernel is literally a nonnegative real number. -/
theorem fejerKernel_eq_normSq (H : ℕ) (x : UnitAddCircle) :
    fejerKernel H x = ((H : ℝ)⁻¹ * ‖dirichletBlock H x‖ ^ 2 : ℝ) := by
  rw [fejerKernel, mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast]

theorem fejerKernel_re_nonneg (H : ℕ) (x : UnitAddCircle) :
    0 ≤ (fejerKernel H x).re := by
  rw [fejerKernel_eq_normSq]
  simp only [Complex.ofReal_re]
  positivity

theorem fejerKernel_im_eq_zero (H : ℕ) (x : UnitAddCircle) :
    (fejerKernel H x).im = 0 := by
  rw [fejerKernel_eq_normSq]
  exact Complex.ofReal_im _

/-- Expanding the square gives a finite double sum of characters. -/
theorem fejerKernel_eq_doubleSum (H : ℕ) (x : UnitAddCircle) :
    fejerKernel H x =
      (H : ℂ)⁻¹ *
        ∑ j ∈ Finset.range H, ∑ l ∈ Finset.range H,
          fourier ((j : ℤ) - (l : ℤ)) x := by
  rw [fejerKernel, dirichletBlock, map_sum]
  calc
    ((H : ℂ)⁻¹ * ∑ j ∈ Finset.range H, fourier (j : ℤ) x) *
        ∑ l ∈ Finset.range H, conj (fourier (l : ℤ) x) =
      (H : ℂ)⁻¹ * ((∑ j ∈ Finset.range H, fourier (j : ℤ) x) *
        ∑ l ∈ Finset.range H, conj (fourier (l : ℤ) x)) := by ring
    _ = (H : ℂ)⁻¹ * ∑ j ∈ Finset.range H, ∑ l ∈ Finset.range H,
        fourier (j : ℤ) x * conj (fourier (l : ℤ) x) := by
      rw [Finset.sum_mul_sum]
    _ = (H : ℂ)⁻¹ * ∑ j ∈ Finset.range H, ∑ l ∈ Finset.range H,
        fourier ((j : ℤ) - (l : ℤ)) x := by
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro l hl
      rw [← fourier_neg, ← fourier_add]
      congr 2

/-- Exact Fourier coefficient of the finite Fejer kernel, in pair-count form. -/
theorem fourierCoeff_fejerKernel (H : ℕ) (k : ℤ) :
    fourierCoeff (fejerKernel H) k =
      (H : ℂ)⁻¹ * (pairMultiplicity H k : ℂ) := by
  have hfun : fejerKernel H = fun x =>
      (H : ℂ)⁻¹ *
        ∑ j ∈ Finset.range H, ∑ l ∈ Finset.range H,
          fourier ((j : ℤ) - (l : ℤ)) x := by
    funext x
    exact fejerKernel_eq_doubleSum H x
  rw [hfun, fourierCoeff.const_mul]
  have houter :
      (fun x : UnitAddCircle =>
        ∑ j ∈ Finset.range H, ∑ l ∈ Finset.range H,
          fourier ((j : ℤ) - (l : ℤ)) x) =
        ∑ j ∈ Finset.range H, (fun x : UnitAddCircle =>
          ∑ l ∈ Finset.range H, fourier ((j : ℤ) - (l : ℤ)) x) := by
    funext x
    simp
  rw [houter, fourierCoeff.sum]
  · have hcount : (pairMultiplicity H k : ℂ) =
        ∑ j ∈ Finset.range H, ∑ l ∈ Finset.range H,
          if (j : ℤ) - (l : ℤ) = k then 1 else 0 := by
      calc
        (pairMultiplicity H k : ℂ) =
            ∑ p ∈ Finset.range H ×ˢ Finset.range H,
              if (p.1 : ℤ) - (p.2 : ℤ) = k then 1 else 0 := by
          simp [pairMultiplicity]
        _ = ∑ j ∈ Finset.range H, ∑ l ∈ Finset.range H,
              if (j : ℤ) - (l : ℤ) = k then 1 else 0 := by
          exact Finset.sum_product _ _ _
    simp only [Finset.sum_apply]
    rw [hcount]
    congr 1
    have hinnerk (j : ℕ) :
        fourierCoeff (fun x : UnitAddCircle =>
          ∑ l ∈ Finset.range H, fourier ((j : ℤ) - (l : ℤ)) x) k =
          ∑ l ∈ Finset.range H,
            if (j : ℤ) - (l : ℤ) = k then 1 else 0 := by
      have hinner := fourierCoeff.sum (T := (1 : ℝ)) (Finset.range H)
        (fun (l : ℕ) (x : UnitAddCircle) => fourier ((j : ℤ) - (l : ℤ)) x)
        (fun l hl =>
          (map_continuous (fourier ((j : ℤ) - (l : ℤ)))).integrable_of_hasCompactSupport
            (HasCompactSupport.of_support_subset_isCompact isCompact_univ (Set.subset_univ _)))
      have hinner_at_k := congrFun hinner k
      have hsumfun :
          (fun x : UnitAddCircle =>
            ∑ l ∈ Finset.range H, fourier ((j : ℤ) - (l : ℤ)) x) =
            ∑ l ∈ Finset.range H, (fun x : UnitAddCircle =>
              fourier ((j : ℤ) - (l : ℤ)) x) := by
        funext x
        simp
      rw [hsumfun, hinner_at_k]
      simp only [Finset.sum_apply]
      simp_rw [fourierCoeff_fourier, Pi.single_apply]
      simp only [eq_comm]
    exact Finset.sum_congr rfl (fun j hj => hinnerk j)
  · intro j hj
    apply Continuous.integrable_of_hasCompactSupport
    · fun_prop
    · exact HasCompactSupport.of_support_subset_isCompact isCompact_univ (Set.subset_univ _)

/-- Only differences of two elements of `[0,H)` can occur. -/
theorem pairMultiplicity_eq_zero_of_natAbs_ge
    (H : ℕ) (k : ℤ) (hk : H ≤ k.natAbs) :
    pairMultiplicity H k = 0 := by
  rw [pairMultiplicity, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p hp
  simp only [Finset.mem_product, Finset.mem_range] at hp
  intro hdiff
  have h₁ : p.1 < H := hp.1
  have h₂ : p.2 < H := hp.2
  have hbound : ((p.1 : ℤ) - (p.2 : ℤ)).natAbs < H := by
    omega
  omega

theorem fourierCoeff_fejerKernel_eq_zero_of_natAbs_ge
    (H : ℕ) (k : ℤ) (hk : H ≤ k.natAbs) :
    fourierCoeff (fejerKernel H) k = 0 := by
  rw [fourierCoeff_fejerKernel, pairMultiplicity_eq_zero_of_natAbs_ge H k hk]
  simp

/-- There are exactly `H` diagonal pairs, so the constant coefficient is one
when `H > 0`. -/
theorem pairMultiplicity_zero (H : ℕ) : pairMultiplicity H 0 = H := by
  rw [pairMultiplicity]
  classical
  have heq :
      ((Finset.range H ×ˢ Finset.range H).filter
        (fun p => (p.1 : ℤ) - (p.2 : ℤ) = 0)) =
        (Finset.range H).image (fun j => (j, j)) := by
    ext p
    rcases p with ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range,
      Finset.mem_image]
    constructor
    · rintro ⟨⟨ha, hb⟩, hsub⟩
      have hcast : (a : ℤ) = (b : ℤ) := sub_eq_zero.mp hsub
      have hab : a = b := by exact_mod_cast hcast
      subst b
      exact ⟨a, ha, rfl⟩
    · rintro ⟨j, hj, heq⟩
      have hja : j = a := congrArg Prod.fst heq
      have hjb : j = b := congrArg Prod.snd heq
      subst a
      subst b
      exact ⟨⟨hj, hj⟩, sub_self _⟩
  rw [heq, Finset.card_image_of_injective]
  · exact Finset.card_range H
  · intro a b hab
    exact congrArg Prod.fst hab

theorem fourierCoeff_fejerKernel_zero {H : ℕ} (hH : 0 < H) :
    fourierCoeff (fejerKernel H) 0 = 1 := by
  rw [fourierCoeff_fejerKernel, pairMultiplicity_zero]
  norm_cast
  exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hH.ne')

/-- Normalization is with respect to probability Haar measure: the integral
is exactly one, with no hidden circumference factor. -/
theorem integral_fejerKernel {H : ℕ} (hH : 0 < H) :
    ∫ x : UnitAddCircle, fejerKernel H x ∂haarAddCircle = 1 := by
  have hzero := fourierCoeff_fejerKernel_zero hH
  simpa [fourierCoeff] using hzero

end

end FejerLocalMass
