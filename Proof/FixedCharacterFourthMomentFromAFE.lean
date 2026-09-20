import RecenteredSampling
import Mathlib.Algebra.Order.Chebyshev

/-!
# Fixed-character fourth moments from a squared approximate functional equation

This file isolates the deterministic part of the low-strip Type-II route.  A
finite family of Dirichlet polynomials which pointwise majorizes `|L|^2`
turns the fourth moment into a sum of polynomial mean squares.  The latter are
already unconditional in `RecenteredSampling`.

No approximate functional equation is asserted here.  The source-facing AFE
contract at the end is deliberately structural: it asks for actual finite
polynomials, their lengths, their coefficient energies, and a pointwise
majorant.  It is not a restatement of the desired fourth moment or zero-density
estimate.
-/

namespace FixedCharacterFourthMomentFromAFE

open scoped BigOperators
open CGLProofDAG DiscreteMeanValueSourceLeaf

noncomputable section

/-- Translate a symmetric ordinate set `W subset [-T,T]` into `[0,2T]`, the
literal range of the certified discrete mean-square theorem. -/
def shiftedOrdinateSet (W : Finset ℝ) (T : ℝ) : Finset ℝ :=
  W.image (fun t => t + T)

theorem shiftedOrdinateSet_oneSeparated
    {W : Finset ℝ} {T : ℝ} (hsep : OneSeparated W) :
    OneSeparated (shiftedOrdinateSet W T) := by
  classical
  intro u hu v hv huv
  rw [shiftedOrdinateSet, Finset.mem_image] at hu hv
  obtain ⟨t, ht, rfl⟩ := hu
  obtain ⟨s, hs, rfl⟩ := hv
  have hts : t ≠ s := by
    intro h
    apply huv
    rw [h]
  simpa only [add_sub_add_right_eq_sub] using hsep t ht s hs hts

theorem shiftedOrdinateSet_height
    {W : Finset ℝ} {T : ℝ}
    (hheight : ∀ t ∈ W, |t| ≤ T) :
    ∀ u ∈ shiftedOrdinateSet W T, 0 ≤ u ∧ u ≤ 2 * T := by
  classical
  intro u hu
  rw [shiftedOrdinateSet, Finset.mem_image] at hu
  obtain ⟨t, ht, rfl⟩ := hu
  have habs := hheight t ht
  rw [abs_le] at habs
  constructor <;> linarith

theorem sum_shiftedOrdinateSet
    {W : Finset ℝ} {T : ℝ} (F : ℝ → ℝ) :
    (∑ u ∈ shiftedOrdinateSet W T, F u) =
      ∑ t ∈ W, F (t + T) := by
  classical
  unfold shiftedOrdinateSet
  rw [Finset.sum_image]
  intro x hx y hy hxy
  linarith

/-- The opposite phase orientation, sending `t` to `T-t`. -/
def reflectedOrdinateSet (W : Finset ℝ) (T : ℝ) : Finset ℝ :=
  W.image (fun t => T - t)

theorem reflectedOrdinateSet_oneSeparated
    {W : Finset ℝ} {T : ℝ} (hsep : OneSeparated W) :
    OneSeparated (reflectedOrdinateSet W T) := by
  classical
  intro u hu v hv huv
  rw [reflectedOrdinateSet, Finset.mem_image] at hu hv
  obtain ⟨t, ht, rfl⟩ := hu
  obtain ⟨s, hs, rfl⟩ := hv
  have hts : t ≠ s := by
    intro h
    apply huv
    rw [h]
  simpa only [sub_sub_sub_cancel_left, abs_sub_comm] using hsep t ht s hs hts

theorem reflectedOrdinateSet_height
    {W : Finset ℝ} {T : ℝ}
    (hheight : ∀ t ∈ W, |t| ≤ T) :
    ∀ u ∈ reflectedOrdinateSet W T, 0 ≤ u ∧ u ≤ 2 * T := by
  classical
  intro u hu
  rw [reflectedOrdinateSet, Finset.mem_image] at hu
  obtain ⟨t, ht, rfl⟩ := hu
  have habs := hheight t ht
  rw [abs_le] at habs
  constructor <;> linarith

theorem sum_reflectedOrdinateSet
    {W : Finset ℝ} {T : ℝ} (F : ℝ → ℝ) :
    (∑ u ∈ reflectedOrdinateSet W T, F u) =
      ∑ t ∈ W, F (T - t) := by
  classical
  unfold reflectedOrdinateSet
  rw [Finset.sum_image]
  intro x hx y hy hxy
  linarith

/-- Boolean phase orientation for the two halves of an approximate functional
equation.  Both orientations land in `[0,2T]` and preserve separation. -/
def orientedTime (forward : Bool) (T t : ℝ) : ℝ :=
  if forward then t + T else T - t

def orientedOrdinateSet (forward : Bool) (W : Finset ℝ) (T : ℝ) : Finset ℝ :=
  W.image (orientedTime forward T)

theorem orientedOrdinateSet_oneSeparated
    (forward : Bool) {W : Finset ℝ} {T : ℝ} (hsep : OneSeparated W) :
    OneSeparated (orientedOrdinateSet forward W T) := by
  cases forward with
  | false =>
      change OneSeparated (reflectedOrdinateSet W T)
      exact reflectedOrdinateSet_oneSeparated hsep
  | true =>
      change OneSeparated (shiftedOrdinateSet W T)
      exact shiftedOrdinateSet_oneSeparated hsep

theorem orientedOrdinateSet_height
    (forward : Bool) {W : Finset ℝ} {T : ℝ}
    (hheight : ∀ t ∈ W, |t| ≤ T) :
    ∀ u ∈ orientedOrdinateSet forward W T, 0 ≤ u ∧ u ≤ 2 * T := by
  cases forward
  · change ∀ u ∈ reflectedOrdinateSet W T, 0 ≤ u ∧ u ≤ 2 * T
    exact reflectedOrdinateSet_height hheight
  · change ∀ u ∈ shiftedOrdinateSet W T, 0 ≤ u ∧ u ≤ 2 * T
    exact shiftedOrdinateSet_height hheight

theorem sum_orientedOrdinateSet
    (forward : Bool) {W : Finset ℝ} {T : ℝ} (F : ℝ → ℝ) :
    (∑ u ∈ orientedOrdinateSet forward W T, F u) =
      ∑ t ∈ W, F (orientedTime forward T t) := by
  cases forward
  · change (∑ u ∈ reflectedOrdinateSet W T, F u) =
      ∑ t ∈ W, F (T - t)
    exact sum_reflectedOrdinateSet (W := W) (T := T) F
  · change (∑ u ∈ shiftedOrdinateSet W T, F u) =
      ∑ t ∈ W, F (t + T)
    exact sum_shiftedOrdinateSet (W := W) (T := T) F

/-- The exact deterministic fourth-moment deduction.  The two factors of `J`
come respectively from Cauchy at each ordinate and from summing the `J`
polynomial mean-square estimates. -/
theorem fourthMoment_le_of_squaredPolynomialMajorant
    {r J : ℕ} [NeZero r]
    (chi : DirichletCharacter ℂ r)
    {T eta C T₀ M D : ℝ}
    (forward : Fin J → Bool) (N : Fin J → ℕ)
    (b : Fin J → ℕ → ℂ) (W : Finset ℝ)
    (hsource : 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (S : ℝ) (N' : ℕ) (b' : ℕ → ℂ) (W' : Finset ℝ),
        T₀ ≤ S → 1 ≤ N' → OneSeparated W' →
        (∀ u ∈ W', 0 ≤ u ∧ u ≤ S) →
        (∑ u ∈ W', ‖dirichletPolynomial b' N' u‖ ^ 2) ≤
          C * Real.rpow S eta * ((N' : ℝ) + S) *
            coefficientEnergy b' N')
    (hT : 0 ≤ T) (hT₀ : T₀ ≤ 2 * T)
    (hsep : OneSeparated W)
    (hheight : ∀ t ∈ W, |t| ≤ T)
    (hN : ∀ j, 1 ≤ N j)
    (hNmax : ∀ j, (N j : ℝ) ≤ M)
    (hM : 0 ≤ M)
    (henergy : ∀ j, coefficientEnergy (b j) (N j) ≤ D)
    (hmajor : ∀ t ∈ W,
      ‖DirichletCharacter.LFunction chi
          (((1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ ^ 2 ≤
        ∑ j : Fin J, ‖dirichletPolynomial (b j) (N j)
          (orientedTime (forward j) T t)‖) :
    (∑ t ∈ W, ‖DirichletCharacter.LFunction chi
        (((1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ ^ 4) ≤
      (J : ℝ) ^ 2 * C * Real.rpow (2 * T) eta * (M + 2 * T) * D := by
  classical
  have hpoly (j : Fin J) :
      (∑ t ∈ W, ‖dirichletPolynomial (b j) (N j)
        (orientedTime (forward j) T t)‖ ^ 2) ≤
        C * Real.rpow (2 * T) eta * ((N j : ℝ) + 2 * T) *
          coefficientEnergy (b j) (N j) := by
    let W' := orientedOrdinateSet (forward j) W T
    have hsep' : OneSeparated W' :=
      orientedOrdinateSet_oneSeparated (forward j) hsep
    have hheight' : ∀ u ∈ W', 0 ≤ u ∧ u ≤ 2 * T :=
      orientedOrdinateSet_height (forward j) hheight
    have hs := hsource.2.2 (2 * T) (N j) (b j) W' hT₀ (hN j)
      hsep' hheight'
    rw [sum_orientedOrdinateSet (forward j)
      (W := W) (T := T)
      (fun u => ‖dirichletPolynomial (b j) (N j) u‖ ^ 2)] at hs
    exact hs
  have hcommon0 :
      0 ≤ C * Real.rpow (2 * T) eta :=
    mul_nonneg hsource.1.le (Real.rpow_nonneg (by positivity) _)
  have hpolyCommon (j : Fin J) :
      (∑ t ∈ W, ‖dirichletPolynomial (b j) (N j)
        (orientedTime (forward j) T t)‖ ^ 2) ≤
        C * Real.rpow (2 * T) eta * (M + 2 * T) * D := by
    calc
      _ ≤ C * Real.rpow (2 * T) eta * ((N j : ℝ) + 2 * T) *
          coefficientEnergy (b j) (N j) := hpoly j
      _ ≤ C * Real.rpow (2 * T) eta * (M + 2 * T) *
          coefficientEnergy (b j) (N j) := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left (by linarith [hNmax j]) hcommon0
        · unfold coefficientEnergy
          positivity
      _ ≤ C * Real.rpow (2 * T) eta * (M + 2 * T) * D := by
        exact mul_le_mul_of_nonneg_left (henergy j)
          (mul_nonneg hcommon0 (by linarith))
  have hpoint (t : ℝ) (ht : t ∈ W) :
      ‖DirichletCharacter.LFunction chi
          (((1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ ^ 4 ≤
        (J : ℝ) * ∑ j : Fin J,
          ‖dirichletPolynomial (b j) (N j)
            (orientedTime (forward j) T t)‖ ^ 2 := by
    let A : ℝ := ‖DirichletCharacter.LFunction chi
      (((1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ ^ 2
    let P : ℝ := ∑ j : Fin J,
      ‖dirichletPolynomial (b j) (N j) (orientedTime (forward j) T t)‖
    have hAP : A ≤ P := hmajor t ht
    have hA0 : 0 ≤ A := by dsimp [A]; positivity
    have hP0 : 0 ≤ P := by dsimp [P]; positivity
    have hsq : A ^ 2 ≤ P ^ 2 := (sq_le_sq₀ hA0 hP0).2 hAP
    have hcauchy : P ^ 2 ≤ (J : ℝ) * ∑ j : Fin J,
        ‖dirichletPolynomial (b j) (N j)
          (orientedTime (forward j) T t)‖ ^ 2 := by
      simpa [P] using (sq_sum_le_card_mul_sum_sq
        (s := (Finset.univ : Finset (Fin J)))
        (f := fun j : Fin J =>
          ‖dirichletPolynomial (b j) (N j)
            (orientedTime (forward j) T t)‖))
    calc
      ‖DirichletCharacter.LFunction chi
          (((1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ ^ 4 = A ^ 2 := by
            dsimp [A]
            ring
      _ ≤ P ^ 2 := hsq
      _ ≤ _ := hcauchy
  calc
    (∑ t ∈ W, ‖DirichletCharacter.LFunction chi
        (((1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ ^ 4) ≤
        ∑ t ∈ W, (J : ℝ) * ∑ j : Fin J,
          ‖dirichletPolynomial (b j) (N j)
            (orientedTime (forward j) T t)‖ ^ 2 := by
      exact Finset.sum_le_sum fun t ht => hpoint t ht
    _ = (J : ℝ) * ∑ j : Fin J, ∑ t ∈ W,
          ‖dirichletPolynomial (b j) (N j)
            (orientedTime (forward j) T t)‖ ^ 2 := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
    _ ≤ (J : ℝ) * ∑ _j : Fin J,
          (C * Real.rpow (2 * T) eta * (M + 2 * T) * D) := by
      gcongr with j
      exact hpolyCommon j
    _ = (J : ℝ) ^ 2 * C * Real.rpow (2 * T) eta *
          (M + 2 * T) * D := by
      simp
      ring

/-- Source-faithful weighted version of the deterministic fourth-moment
assembly.  It retains each block's exact `(N_j+2T) * energy_j` cost instead of
replacing all lengths and energies by separate maxima. -/
theorem fourthMoment_le_of_squaredPolynomialWeightedEnergy
    {r J : ℕ} [NeZero r]
    (chi : DirichletCharacter ℂ r)
    {T eta C T₀ : ℝ}
    (forward : Fin J → Bool) (N : Fin J → ℕ)
    (b : Fin J → ℕ → ℂ) (W : Finset ℝ)
    (hsource : 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (S : ℝ) (N' : ℕ) (b' : ℕ → ℂ) (W' : Finset ℝ),
        T₀ ≤ S → 1 ≤ N' → OneSeparated W' →
        (∀ u ∈ W', 0 ≤ u ∧ u ≤ S) →
        (∑ u ∈ W', ‖dirichletPolynomial b' N' u‖ ^ 2) ≤
          C * Real.rpow S eta * ((N' : ℝ) + S) *
            coefficientEnergy b' N')
    (hT₀ : T₀ ≤ 2 * T)
    (hsep : OneSeparated W)
    (hheight : ∀ t ∈ W, |t| ≤ T)
    (hN : ∀ j, 1 ≤ N j)
    (hmajor : ∀ t ∈ W,
      ‖DirichletCharacter.LFunction chi
          (((1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ ^ 2 ≤
        ∑ j : Fin J, ‖dirichletPolynomial (b j) (N j)
          (orientedTime (forward j) T t)‖) :
    (∑ t ∈ W, ‖DirichletCharacter.LFunction chi
        (((1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ ^ 4) ≤
      (J : ℝ) * C * Real.rpow (2 * T) eta *
        ∑ j : Fin J,
          (((N j : ℝ) + 2 * T) * coefficientEnergy (b j) (N j)) := by
  classical
  have hpoly (j : Fin J) :
      (∑ t ∈ W, ‖dirichletPolynomial (b j) (N j)
        (orientedTime (forward j) T t)‖ ^ 2) ≤
        C * Real.rpow (2 * T) eta * ((N j : ℝ) + 2 * T) *
          coefficientEnergy (b j) (N j) := by
    let W' := orientedOrdinateSet (forward j) W T
    have hsep' : OneSeparated W' :=
      orientedOrdinateSet_oneSeparated (forward j) hsep
    have hheight' : ∀ u ∈ W', 0 ≤ u ∧ u ≤ 2 * T :=
      orientedOrdinateSet_height (forward j) hheight
    have hs := hsource.2.2 (2 * T) (N j) (b j) W' hT₀ (hN j)
      hsep' hheight'
    rw [sum_orientedOrdinateSet (forward j)
      (W := W) (T := T)
      (fun u => ‖dirichletPolynomial (b j) (N j) u‖ ^ 2)] at hs
    exact hs
  have hpoint (t : ℝ) (ht : t ∈ W) :
      ‖DirichletCharacter.LFunction chi
          (((1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ ^ 4 ≤
        (J : ℝ) * ∑ j : Fin J,
          ‖dirichletPolynomial (b j) (N j)
            (orientedTime (forward j) T t)‖ ^ 2 := by
    let A : ℝ := ‖DirichletCharacter.LFunction chi
      (((1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ ^ 2
    let P : ℝ := ∑ j : Fin J,
      ‖dirichletPolynomial (b j) (N j) (orientedTime (forward j) T t)‖
    have hAP : A ≤ P := hmajor t ht
    have hA0 : 0 ≤ A := by dsimp [A]; positivity
    have hP0 : 0 ≤ P := by dsimp [P]; positivity
    have hsq : A ^ 2 ≤ P ^ 2 := (sq_le_sq₀ hA0 hP0).2 hAP
    have hcauchy : P ^ 2 ≤ (J : ℝ) * ∑ j : Fin J,
        ‖dirichletPolynomial (b j) (N j)
          (orientedTime (forward j) T t)‖ ^ 2 := by
      simpa [P] using (sq_sum_le_card_mul_sum_sq
        (s := (Finset.univ : Finset (Fin J)))
        (f := fun j : Fin J =>
          ‖dirichletPolynomial (b j) (N j)
            (orientedTime (forward j) T t)‖))
    calc
      ‖DirichletCharacter.LFunction chi
          (((1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ ^ 4 = A ^ 2 := by
        dsimp [A]
        ring
      _ ≤ P ^ 2 := hsq
      _ ≤ _ := hcauchy
  calc
    (∑ t ∈ W, ‖DirichletCharacter.LFunction chi
        (((1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ ^ 4) ≤
        ∑ t ∈ W, (J : ℝ) * ∑ j : Fin J,
          ‖dirichletPolynomial (b j) (N j)
            (orientedTime (forward j) T t)‖ ^ 2 := by
      exact Finset.sum_le_sum fun t ht => hpoint t ht
    _ = (J : ℝ) * ∑ j : Fin J, ∑ t ∈ W,
          ‖dirichletPolynomial (b j) (N j)
            (orientedTime (forward j) T t)‖ ^ 2 := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
    _ ≤ (J : ℝ) * ∑ j : Fin J,
          (C * Real.rpow (2 * T) eta * ((N j : ℝ) + 2 * T) *
            coefficientEnergy (b j) (N j)) := by
      gcongr with j
      exact hpoly j
    _ = (J : ℝ) * C * Real.rpow (2 * T) eta *
          ∑ j : Fin J,
            (((N j : ℝ) + 2 * T) * coefficientEnergy (b j) (N j)) := by
      rw [Finset.mul_sum]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring

/-- The source-facing analytic leaf for the +EV fixed-character bypass.  It is
an explicit squared approximate functional equation in dyadic-polynomial form,
restricted to primitive nonprincipal characters.  `J^2 D` records both the
Cauchy cost and total coefficient-energy budget. -/
def NonprincipalSquaredDyadicAFE : Prop :=
  ∀ theta : ℝ, 0 < theta →
    ∃ T₀ : ℝ, 2 ≤ T₀ ∧
      ∀ (T : ℝ) (r : ℕ) [NeZero r]
        (chi : DirichletCharacter ℂ r),
        T₀ ≤ T → chi.IsPrimitive → chi ≠ 1 →
        ∃ (J : ℕ) (forward : Fin J → Bool) (N : Fin J → ℕ)
          (b : Fin J → ℕ → ℂ) (D : ℝ),
          0 < J ∧ 0 ≤ D ∧
          (J : ℝ) ^ 2 * D ≤ Real.rpow ((r : ℝ) * T) theta ∧
          (∀ j, 1 ≤ N j) ∧
          (∀ j, (N j : ℝ) ≤ (r : ℝ) * T) ∧
          (∀ j, coefficientEnergy (b j) (N j) ≤ D) ∧
          ∀ t : ℝ, |t| ≤ T →
            ‖DirichletCharacter.LFunction chi
                (((1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ ^ 2 ≤
              ∑ j : Fin J,
                ‖dirichletPolynomial (b j) (N j)
                  (orientedTime (forward j) T t)‖

/-! The preceding contract has the unnaturally sharp literal cutoff
`N_j <= rT`.  A fixed-kernel approximate functional equation naturally gives
an arbitrarily small power enlargement.  The following exponent calculation
shows that this enlargement fits comfortably inside the fourth-moment epsilon
reserve. -/

theorem weakenedAFE_exponent_identity (epsilon : ℝ) :
    1 + epsilon / 8 + 2 * (epsilon / 8) = 1 + 3 * epsilon / 8 := by
  ring

theorem weakenedAFE_exponent_lt_target {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    1 + epsilon / 8 + 2 * (epsilon / 8) < 1 + epsilon := by
  linarith

/-- Source-faithful corrected AFE surface.  Compared with
`NonprincipalSquaredDyadicAFE`, lengths may be `S^(1+theta)`, where
`S=rT`.  The finite family is the controlled low-rank/partial-summation
decomposition of the height-dependent AFE weights; its Cauchy and energy cost
is charged by `J^2 D <= S^theta`. -/
def NonprincipalWeightedLowRankSquaredAFE : Prop :=
  ∀ theta : ℝ, 0 < theta →
    ∃ T₀ : ℝ, 2 ≤ T₀ ∧
      ∀ (T : ℝ) (r : ℕ) [NeZero r]
        (chi : DirichletCharacter ℂ r),
        T₀ ≤ T → chi.IsPrimitive → chi ≠ 1 →
        ∃ (J : ℕ) (forward : Fin J → Bool) (N : Fin J → ℕ)
          (b : Fin J → ℕ → ℂ) (D : ℝ),
          0 < J ∧ 0 ≤ D ∧
          (J : ℝ) ^ 2 * D ≤ Real.rpow ((r : ℝ) * T) theta ∧
          (∀ j, 1 ≤ N j) ∧
          (∀ j, (N j : ℝ) ≤
            Real.rpow ((r : ℝ) * T) (1 + theta)) ∧
          (∀ j, coefficientEnergy (b j) (N j) ≤ D) ∧
          ∀ t : ℝ, |t| ≤ T →
            ‖DirichletCharacter.LFunction chi
                (((1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ ^ 2 ≤
              ∑ j : Fin J,
                ‖dirichletPolynomial (b j) (N j)
                  (orientedTime (forward j) T t)‖

/-- Ramachandra-faithful Mellin-block surface.  It keeps the exact
length-energy compensation used by the source: long tail blocks are legal
when their coefficient energy decays.  This is weaker and more faithful than
either a hard length cutoff or a `max energy` budget. -/
def NonprincipalSeparatedMellinBlockAFE : Prop :=
  ∀ theta : ℝ, 0 < theta →
    ∃ T₀ : ℝ, 3 ≤ T₀ ∧
      ∀ (T : ℝ) (r : ℕ) [NeZero r]
        (chi : DirichletCharacter ℂ r),
        T₀ ≤ T → chi.IsPrimitive → chi ≠ 1 →
        ∃ (J : ℕ) (forward : Fin J → Bool) (N : Fin J → ℕ)
          (b : Fin J → ℕ → ℂ),
          0 < J ∧
          (∀ j, 1 ≤ N j) ∧
          (J : ℝ) * (∑ j : Fin J,
            (((N j : ℝ) + 2 * T) * coefficientEnergy (b j) (N j))) ≤
              Real.rpow ((r : ℝ) * T) (1 + theta) ∧
          ∀ t : ℝ, |t| ≤ T →
            ‖DirichletCharacter.LFunction chi
                (((1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ ^ 2 ≤
              ∑ j : Fin J,
                ‖dirichletPolynomial (b j) (N j)
                  (orientedTime (forward j) T t)‖

/-- The fixed-character fourth-moment conclusion needed by the Type-II branch,
with the principal character kept out explicitly. -/
def NonprincipalFixedCharacterDiscreteFourthMoment : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (T : ℝ) (r : ℕ) [NeZero r]
        (chi : DirichletCharacter ℂ r) (W : Finset ℝ),
        T₀ ≤ T → chi.IsPrimitive → chi ≠ 1 → OneSeparated W →
        (∀ t ∈ W, |t| ≤ T) →
        (∑ t ∈ W, ‖DirichletCharacter.LFunction chi
          (((1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ ^ 4) ≤
          C * Real.rpow ((r : ℝ) * T) (1 + epsilon)

/-- Once the explicit squared AFE is supplied, the nonprincipal separated
fourth moment follows from the already-certified finite Hilbert inequality and
discrete Dirichlet mean square.  Thus the AFE is the first unproved analytic
leaf in this bypass. -/
theorem nonprincipalFourthMoment_of_squaredDyadicAFE
    (hAFE : NonprincipalSquaredDyadicAFE) :
    NonprincipalFixedCharacterDiscreteFourthMoment := by
  intro epsilon hepsilon
  let eta : ℝ := epsilon / 4
  have heta : 0 < eta := by dsimp [eta]; linarith
  have hmean : DiscreteDirichletMeanSquare :=
    RecenteredSampling.discreteDirichletMeanSquare_of_hilbert
      MontgomeryVaughanFiniteReduction.finiteLogHilbertInequality_via_integerHilbert
  obtain ⟨Cmv, Tmv, hCmv, hTmv, hmv⟩ := hmean eta heta
  obtain ⟨Tafe, hTafe, hafe⟩ := hAFE eta heta
  let C : ℝ := 3 * Cmv * Real.rpow 2 eta
  let T₀ : ℝ := max Tmv Tafe
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hT₀ : 2 ≤ T₀ := by
    dsimp [T₀]
    exact hTmv.trans (le_max_left _ _)
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro T r _inst chi W hT hprimitive hnonprincipal hsep hheight
  have hTmv' : Tmv ≤ T := (le_max_left Tmv Tafe).trans hT
  have hTafe' : Tafe ≤ T := (le_max_right Tmv Tafe).trans hT
  have hTtwo : 2 ≤ T := hT₀.trans hT
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hTtwo
  have hrNat : 0 < r := NeZero.pos r
  have hr : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hrNat
  let S : ℝ := (r : ℝ) * T
  have hSpos : 0 < S := mul_pos (by exact_mod_cast hrNat) hTpos
  have hSone : 1 ≤ S := by
    dsimp [S]
    nlinarith [mul_le_mul_of_nonneg_right hr hTpos.le]
  obtain ⟨J, forward, N, b, D, hJ, hD, hbudget, hN, hNmax,
      henergy, hmajor⟩ :=
    hafe T r chi hTafe' hprimitive hnonprincipal
  have hsource : 0 < Cmv ∧ 2 ≤ Tmv ∧
      ∀ (S' : ℝ) (N' : ℕ) (b' : ℕ → ℂ) (W' : Finset ℝ),
        Tmv ≤ S' → 1 ≤ N' → OneSeparated W' →
        (∀ u ∈ W', 0 ≤ u ∧ u ≤ S') →
        (∑ u ∈ W', ‖dirichletPolynomial b' N' u‖ ^ 2) ≤
          Cmv * Real.rpow S' eta * ((N' : ℝ) + S') *
            coefficientEnergy b' N' :=
    ⟨hCmv, hTmv, hmv⟩
  have hraw := fourthMoment_le_of_squaredPolynomialMajorant
    (chi := chi) (forward := forward) (N := N) (b := b) (W := W)
    (C := Cmv) (T₀ := Tmv) (eta := eta) (M := S) (D := D)
    hsource hTpos.le (by linarith) hsep hheight hN hNmax hSpos.le
    henergy (fun t ht => hmajor t (hheight t ht))
  have hTleS : T ≤ S := by
    dsimp [S]
    nlinarith [mul_le_mul_of_nonneg_right hr hTpos.le]
  have htwoTle : 2 * T ≤ 2 * S := by linarith
  have hrpowTwoT : Real.rpow (2 * T) eta ≤ Real.rpow (2 * S) eta :=
    Real.rpow_le_rpow (by positivity) htwoTle heta.le
  have hlength : S + 2 * T ≤ 3 * S := by linarith
  have hbudget0 : 0 ≤ (J : ℝ) ^ 2 * D :=
    mul_nonneg (sq_nonneg _) hD
  have hfactor0 :
      0 ≤ Cmv * Real.rpow (2 * T) eta * (S + 2 * T) := by
    exact mul_nonneg
      (mul_nonneg hCmv.le (Real.rpow_nonneg (by positivity) _))
      (by linarith)
  have hSrpow0 : 0 ≤ Real.rpow S eta :=
    Real.rpow_nonneg hSpos.le _
  have hbase :
      Cmv * Real.rpow (2 * T) eta * (S + 2 * T) ≤
        Cmv * Real.rpow (2 * S) eta * (3 * S) := by
    calc
      Cmv * Real.rpow (2 * T) eta * (S + 2 * T) ≤
          Cmv * Real.rpow (2 * S) eta * (S + 2 * T) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hrpowTwoT hCmv.le) (by linarith)
      _ ≤ Cmv * Real.rpow (2 * S) eta * (3 * S) := by
        exact mul_le_mul_of_nonneg_left hlength
          (mul_nonneg hCmv.le (Real.rpow_nonneg (by positivity) _))
  have hcombined :
      (J : ℝ) ^ 2 * Cmv * Real.rpow (2 * T) eta *
          (S + 2 * T) * D ≤
        Cmv * Real.rpow (2 * S) eta * (3 * S) *
          Real.rpow S eta := by
    calc
      (J : ℝ) ^ 2 * Cmv * Real.rpow (2 * T) eta *
          (S + 2 * T) * D =
          (Cmv * Real.rpow (2 * T) eta * (S + 2 * T)) *
            ((J : ℝ) ^ 2 * D) := by ring
      _ ≤ (Cmv * Real.rpow (2 * T) eta * (S + 2 * T)) *
            Real.rpow S eta :=
        mul_le_mul_of_nonneg_left hbudget hfactor0
      _ ≤ (Cmv * Real.rpow (2 * S) eta * (3 * S)) *
            Real.rpow S eta := by
        exact mul_le_mul_of_nonneg_right hbase hSrpow0
      _ = Cmv * Real.rpow (2 * S) eta * (3 * S) *
            Real.rpow S eta := by ring
  have hmulRpow : Real.rpow (2 * S) eta =
      Real.rpow 2 eta * Real.rpow S eta := by
    exact Real.mul_rpow (by norm_num) hSpos.le
  have hpowCombine :
      Real.rpow S eta * S * Real.rpow S eta =
        Real.rpow S (1 + 2 * eta) := by
    have hee : Real.rpow S eta * Real.rpow S eta =
        Real.rpow S (eta + eta) := (Real.rpow_add hSpos eta eta).symm
    have hone : Real.rpow S (1 : ℝ) = S := Real.rpow_one S
    have hrest : Real.rpow S (1 : ℝ) * Real.rpow S (eta + eta) =
        Real.rpow S (1 + (eta + eta)) :=
      (Real.rpow_add hSpos 1 (eta + eta)).symm
    calc
      Real.rpow S eta * S * Real.rpow S eta =
          S * (Real.rpow S eta * Real.rpow S eta) := by ring
      _ = S * Real.rpow S (eta + eta) := by rw [hee]
      _ = Real.rpow S 1 * Real.rpow S (eta + eta) := by rw [hone]
      _ = Real.rpow S (1 + (eta + eta)) := hrest
      _ = Real.rpow S (1 + 2 * eta) := by
            congr 1
            ring
  have hexponent : 1 + 2 * eta ≤ 1 + epsilon := by
    dsimp [eta]
    linarith
  have hpowMono : Real.rpow S (1 + 2 * eta) ≤
      Real.rpow S (1 + epsilon) :=
    Real.rpow_le_rpow_of_exponent_le hSone hexponent
  calc
    (∑ t ∈ W, ‖DirichletCharacter.LFunction chi
        (((1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ ^ 4) ≤
        (J : ℝ) ^ 2 * Cmv * Real.rpow (2 * T) eta *
          (S + 2 * T) * D := hraw
    _ ≤ Cmv * Real.rpow (2 * S) eta * (3 * S) *
          Real.rpow S eta := hcombined
    _ = C * Real.rpow S (1 + 2 * eta) := by
      rw [hmulRpow]
      calc
        Cmv * (Real.rpow 2 eta * Real.rpow S eta) * (3 * S) *
            Real.rpow S eta =
            C * (Real.rpow S eta * S * Real.rpow S eta) := by
              dsimp [C]
              ring
        _ = C * Real.rpow S (1 + 2 * eta) := by rw [hpowCombine]
    _ ≤ C * Real.rpow S (1 + epsilon) :=
      mul_le_mul_of_nonneg_left hpowMono hC.le
    _ = C * Real.rpow ((r : ℝ) * T) (1 + epsilon) := by rfl

/-- The corrected weighted/low-rank AFE still implies the same fourth moment.
The extra length exponent costs one `theta`, while the energy complexity costs
another; together with the mean-square loss the pre-absorption exponent is
`1 + eta + 2*theta`. -/
theorem nonprincipalFourthMoment_of_weightedLowRankSquaredAFE
    (hAFE : NonprincipalWeightedLowRankSquaredAFE) :
    NonprincipalFixedCharacterDiscreteFourthMoment := by
  intro epsilon hepsilon
  let eta : ℝ := epsilon / 8
  let theta : ℝ := epsilon / 8
  have heta : 0 < eta := by dsimp [eta]; linarith
  have htheta : 0 < theta := by dsimp [theta]; linarith
  have hmean : DiscreteDirichletMeanSquare :=
    RecenteredSampling.discreteDirichletMeanSquare_of_hilbert
      MontgomeryVaughanFiniteReduction.finiteLogHilbertInequality_via_integerHilbert
  obtain ⟨Cmv, Tmv, hCmv, hTmv, hmv⟩ := hmean eta heta
  obtain ⟨Tafe, hTafe, hafe⟩ := hAFE theta htheta
  let C : ℝ := 3 * Cmv * Real.rpow 2 eta
  let T₀ : ℝ := max Tmv Tafe
  have hC : 0 < C := by dsimp [C]; positivity
  have hT₀ : 2 ≤ T₀ := by
    dsimp [T₀]
    exact hTmv.trans (le_max_left _ _)
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro T r _inst chi W hT hprimitive hnonprincipal hsep hheight
  have hTafe' : Tafe ≤ T := (le_max_right Tmv Tafe).trans hT
  have hTtwo : 2 ≤ T := hT₀.trans hT
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hTtwo
  have hrNat : 0 < r := NeZero.pos r
  have hr : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hrNat
  let S : ℝ := (r : ℝ) * T
  let M : ℝ := Real.rpow S (1 + theta)
  have hSpos : 0 < S := mul_pos (by exact_mod_cast hrNat) hTpos
  have hSone : 1 ≤ S := by
    dsimp [S]
    nlinarith [mul_le_mul_of_nonneg_right hr hTpos.le]
  have hM0 : 0 ≤ M := Real.rpow_nonneg hSpos.le _
  have hSleM : S ≤ M := by
    calc
      S = Real.rpow S 1 := (Real.rpow_one S).symm
      _ ≤ Real.rpow S (1 + theta) :=
        Real.rpow_le_rpow_of_exponent_le hSone (by linarith)
      _ = M := by rfl
  obtain ⟨J, forward, N, b, D, hJ, hD, hbudget, hN, hNmax,
      henergy, hmajor⟩ := hafe T r chi hTafe' hprimitive hnonprincipal
  have hTmv' : Tmv ≤ T := (le_max_left Tmv Tafe).trans hT
  have hsource : 0 < Cmv ∧ 2 ≤ Tmv ∧
      ∀ (S' : ℝ) (N' : ℕ) (b' : ℕ → ℂ) (W' : Finset ℝ),
        Tmv ≤ S' → 1 ≤ N' → OneSeparated W' →
        (∀ u ∈ W', 0 ≤ u ∧ u ≤ S') →
        (∑ u ∈ W', ‖dirichletPolynomial b' N' u‖ ^ 2) ≤
          Cmv * Real.rpow S' eta * ((N' : ℝ) + S') *
            coefficientEnergy b' N' :=
    ⟨hCmv, hTmv, hmv⟩
  have hraw := fourthMoment_le_of_squaredPolynomialMajorant
    (chi := chi) (forward := forward) (N := N) (b := b) (W := W)
    (C := Cmv) (T₀ := Tmv) (eta := eta) (M := M) (D := D)
    hsource hTpos.le (by linarith [hTmv']) hsep hheight hN
    (fun j => by simpa [M, S] using hNmax j) hM0 henergy
    (fun t ht => hmajor t (hheight t ht))
  have hTleS : T ≤ S := by
    dsimp [S]
    nlinarith [mul_le_mul_of_nonneg_right hr hTpos.le]
  have htwoTle : 2 * T ≤ 2 * S := by linarith
  have hrpowTwoT : Real.rpow (2 * T) eta ≤ Real.rpow (2 * S) eta :=
    Real.rpow_le_rpow (by positivity) htwoTle heta.le
  have hlength : M + 2 * T ≤ 3 * M := by linarith
  have hfactor0 :
      0 ≤ Cmv * Real.rpow (2 * T) eta * (M + 2 * T) := by
    exact mul_nonneg
      (mul_nonneg hCmv.le (Real.rpow_nonneg (by positivity) _))
      (by positivity)
  have hSrpowTheta0 : 0 ≤ Real.rpow S theta :=
    Real.rpow_nonneg hSpos.le _
  have hbase :
      Cmv * Real.rpow (2 * T) eta * (M + 2 * T) ≤
        Cmv * Real.rpow (2 * S) eta * (3 * M) := by
    calc
      Cmv * Real.rpow (2 * T) eta * (M + 2 * T) ≤
          Cmv * Real.rpow (2 * S) eta * (M + 2 * T) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hrpowTwoT hCmv.le) (by positivity)
      _ ≤ Cmv * Real.rpow (2 * S) eta * (3 * M) := by
        exact mul_le_mul_of_nonneg_left hlength
          (mul_nonneg hCmv.le (Real.rpow_nonneg (by positivity) _))
  have hcombined :
      (J : ℝ) ^ 2 * Cmv * Real.rpow (2 * T) eta *
          (M + 2 * T) * D ≤
        Cmv * Real.rpow (2 * S) eta * (3 * M) *
          Real.rpow S theta := by
    calc
      (J : ℝ) ^ 2 * Cmv * Real.rpow (2 * T) eta *
          (M + 2 * T) * D =
          (Cmv * Real.rpow (2 * T) eta * (M + 2 * T)) *
            ((J : ℝ) ^ 2 * D) := by ring
      _ ≤ (Cmv * Real.rpow (2 * T) eta * (M + 2 * T)) *
            Real.rpow S theta := by
        exact mul_le_mul_of_nonneg_left (by simpa [S] using hbudget) hfactor0
      _ ≤ (Cmv * Real.rpow (2 * S) eta * (3 * M)) *
            Real.rpow S theta :=
        mul_le_mul_of_nonneg_right hbase hSrpowTheta0
      _ = Cmv * Real.rpow (2 * S) eta * (3 * M) *
            Real.rpow S theta := by ring
  have hmulRpow : Real.rpow (2 * S) eta =
      Real.rpow 2 eta * Real.rpow S eta :=
    Real.mul_rpow (by norm_num) hSpos.le
  have hpowCombine :
      Real.rpow S eta * M * Real.rpow S theta =
        Real.rpow S (1 + eta + 2 * theta) := by
    dsimp [M]
    calc
      Real.rpow S eta * Real.rpow S (1 + theta) * Real.rpow S theta =
          Real.rpow S (eta + (1 + theta)) * Real.rpow S theta := by
        congr 1
        exact (Real.rpow_add hSpos eta (1 + theta)).symm
      _ = Real.rpow S ((eta + (1 + theta)) + theta) :=
        (Real.rpow_add hSpos (eta + (1 + theta)) theta).symm
      _ = Real.rpow S (1 + eta + 2 * theta) := by
        congr 1
        ring
  have hexponent : 1 + eta + 2 * theta ≤ 1 + epsilon := by
    dsimp [eta, theta]
    linarith
  have hpowMono : Real.rpow S (1 + eta + 2 * theta) ≤
      Real.rpow S (1 + epsilon) :=
    Real.rpow_le_rpow_of_exponent_le hSone hexponent
  calc
    (∑ t ∈ W, ‖DirichletCharacter.LFunction chi
        (((1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ ^ 4) ≤
        (J : ℝ) ^ 2 * Cmv * Real.rpow (2 * T) eta *
          (M + 2 * T) * D := hraw
    _ ≤ Cmv * Real.rpow (2 * S) eta * (3 * M) *
          Real.rpow S theta := hcombined
    _ = C * Real.rpow S (1 + eta + 2 * theta) := by
      rw [hmulRpow]
      calc
        Cmv * (Real.rpow 2 eta * Real.rpow S eta) * (3 * M) *
            Real.rpow S theta =
            C * (Real.rpow S eta * M * Real.rpow S theta) := by
          dsimp [C]
          ring
        _ = C * Real.rpow S (1 + eta + 2 * theta) := by rw [hpowCombine]
    _ ≤ C * Real.rpow S (1 + epsilon) :=
      mul_le_mul_of_nonneg_left hpowMono hC.le
    _ = C * Real.rpow ((r : ℝ) * T) (1 + epsilon) := by rfl

/-- Ramachandra's exact length-energy block budget implies the separated
fourth moment directly.  Only one Cauchy factor `J` is charged; no maximum
length or maximum energy is introduced. -/
theorem nonprincipalFourthMoment_of_separatedMellinBlockAFE
    (hAFE : NonprincipalSeparatedMellinBlockAFE) :
    NonprincipalFixedCharacterDiscreteFourthMoment := by
  intro epsilon hepsilon
  let eta : ℝ := epsilon / 4
  let theta : ℝ := epsilon / 4
  have heta : 0 < eta := by dsimp [eta]; linarith
  have htheta : 0 < theta := by dsimp [theta]; linarith
  have hmean : DiscreteDirichletMeanSquare :=
    RecenteredSampling.discreteDirichletMeanSquare_of_hilbert
      MontgomeryVaughanFiniteReduction.finiteLogHilbertInequality_via_integerHilbert
  obtain ⟨Cmv, Tmv, hCmv, hTmv, hmv⟩ := hmean eta heta
  obtain ⟨Tafe, hTafe, hafe⟩ := hAFE theta htheta
  let C : ℝ := Cmv * Real.rpow 2 eta
  let T₀ : ℝ := max Tmv Tafe
  have hC : 0 < C := by dsimp [C]; positivity
  have hT₀ : 2 ≤ T₀ := by
    exact hTmv.trans (le_max_left _ _)
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro T r _inst chi W hT hprimitive hnonprincipal hsep hheight
  have hTmv' : Tmv ≤ T := (le_max_left Tmv Tafe).trans hT
  have hTafe' : Tafe ≤ T := (le_max_right Tmv Tafe).trans hT
  have hTtwo : 2 ≤ T := hT₀.trans hT
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hTtwo
  have hrNat : 0 < r := NeZero.pos r
  have hr : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hrNat
  let S : ℝ := (r : ℝ) * T
  have hSpos : 0 < S := mul_pos (by exact_mod_cast hrNat) hTpos
  have hSone : 1 ≤ S := by
    dsimp [S]
    nlinarith [mul_le_mul_of_nonneg_right hr hTpos.le]
  obtain ⟨J, forward, N, b, hJ, hN, hbudget, hmajor⟩ :=
    hafe T r chi hTafe' hprimitive hnonprincipal
  have hsource : 0 < Cmv ∧ 2 ≤ Tmv ∧
      ∀ (S' : ℝ) (N' : ℕ) (b' : ℕ → ℂ) (W' : Finset ℝ),
        Tmv ≤ S' → 1 ≤ N' → OneSeparated W' →
        (∀ u ∈ W', 0 ≤ u ∧ u ≤ S') →
        (∑ u ∈ W', ‖dirichletPolynomial b' N' u‖ ^ 2) ≤
          Cmv * Real.rpow S' eta * ((N' : ℝ) + S') *
            coefficientEnergy b' N' :=
    ⟨hCmv, hTmv, hmv⟩
  have hraw := fourthMoment_le_of_squaredPolynomialWeightedEnergy
    (chi := chi) (forward := forward) (N := N) (b := b) (W := W)
    (C := Cmv) (T₀ := Tmv) (eta := eta) hsource
    (by linarith [hTmv']) hsep hheight hN
    (fun t ht => hmajor t (hheight t ht))
  have hTleS : T ≤ S := by
    dsimp [S]
    nlinarith [mul_le_mul_of_nonneg_right hr hTpos.le]
  have htwoTle : 2 * T ≤ 2 * S := by linarith
  have hrpowTwoT : Real.rpow (2 * T) eta ≤ Real.rpow (2 * S) eta :=
    Real.rpow_le_rpow (by positivity) htwoTle heta.le
  have hbudget' :
      (J : ℝ) * (∑ j : Fin J,
        (((N j : ℝ) + 2 * T) * coefficientEnergy (b j) (N j))) ≤
        Real.rpow S (1 + theta) := by
    simpa [S] using hbudget
  have hcombined :
      (J : ℝ) * Cmv * Real.rpow (2 * T) eta *
          (∑ j : Fin J,
            (((N j : ℝ) + 2 * T) * coefficientEnergy (b j) (N j))) ≤
        Cmv * Real.rpow (2 * S) eta * Real.rpow S (1 + theta) := by
    calc
      (J : ℝ) * Cmv * Real.rpow (2 * T) eta *
          (∑ j : Fin J,
            (((N j : ℝ) + 2 * T) * coefficientEnergy (b j) (N j))) =
          (Cmv * Real.rpow (2 * T) eta) *
            ((J : ℝ) * (∑ j : Fin J,
              (((N j : ℝ) + 2 * T) * coefficientEnergy (b j) (N j)))) := by
        ring
      _ ≤ (Cmv * Real.rpow (2 * T) eta) * Real.rpow S (1 + theta) :=
        mul_le_mul_of_nonneg_left hbudget'
          (mul_nonneg hCmv.le (Real.rpow_nonneg (by positivity) _))
      _ ≤ (Cmv * Real.rpow (2 * S) eta) * Real.rpow S (1 + theta) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hrpowTwoT hCmv.le)
          (Real.rpow_nonneg hSpos.le _)
  have hmulTwo : Real.rpow (2 * S) eta =
      Real.rpow 2 eta * Real.rpow S eta :=
    Real.mul_rpow (by norm_num) hSpos.le
  have hpowCombine : Real.rpow S eta * Real.rpow S (1 + theta) =
      Real.rpow S (1 + eta + theta) := by
    calc
      Real.rpow S eta * Real.rpow S (1 + theta) =
          Real.rpow S (eta + (1 + theta)) :=
        (Real.rpow_add hSpos eta (1 + theta)).symm
      _ = Real.rpow S (1 + eta + theta) := by congr 1 <;> ring
  have hexponent : 1 + eta + theta ≤ 1 + epsilon := by
    dsimp [eta, theta]
    linarith
  have hpowMono : Real.rpow S (1 + eta + theta) ≤
      Real.rpow S (1 + epsilon) :=
    Real.rpow_le_rpow_of_exponent_le hSone hexponent
  calc
    (∑ t ∈ W, ‖DirichletCharacter.LFunction chi
        (((1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ ^ 4) ≤
        (J : ℝ) * Cmv * Real.rpow (2 * T) eta *
          ∑ j : Fin J,
            (((N j : ℝ) + 2 * T) * coefficientEnergy (b j) (N j)) := hraw
    _ ≤ Cmv * Real.rpow (2 * S) eta * Real.rpow S (1 + theta) :=
      hcombined
    _ = C * Real.rpow S (1 + eta + theta) := by
      rw [hmulTwo]
      calc
        Cmv * (Real.rpow 2 eta * Real.rpow S eta) *
            Real.rpow S (1 + theta) =
            C * (Real.rpow S eta * Real.rpow S (1 + theta)) := by
          dsimp [C]
          ring
        _ = C * Real.rpow S (1 + eta + theta) := by rw [hpowCombine]
    _ ≤ C * Real.rpow S (1 + epsilon) :=
      mul_le_mul_of_nonneg_left hpowMono hC.le
    _ = C * Real.rpow ((r : ℝ) * T) (1 + epsilon) := by rfl

end

end FixedCharacterFourthMomentFromAFE

#print axioms FixedCharacterFourthMomentFromAFE.shiftedOrdinateSet_oneSeparated
#print axioms FixedCharacterFourthMomentFromAFE.shiftedOrdinateSet_height
#print axioms FixedCharacterFourthMomentFromAFE.sum_shiftedOrdinateSet
#print axioms FixedCharacterFourthMomentFromAFE.orientedOrdinateSet_oneSeparated
#print axioms FixedCharacterFourthMomentFromAFE.orientedOrdinateSet_height
#print axioms FixedCharacterFourthMomentFromAFE.sum_orientedOrdinateSet
#print axioms FixedCharacterFourthMomentFromAFE.fourthMoment_le_of_squaredPolynomialMajorant
#print axioms FixedCharacterFourthMomentFromAFE.nonprincipalFourthMoment_of_squaredDyadicAFE
#print axioms FixedCharacterFourthMomentFromAFE.weakenedAFE_exponent_lt_target
#print axioms FixedCharacterFourthMomentFromAFE.nonprincipalFourthMoment_of_weightedLowRankSquaredAFE
#print axioms FixedCharacterFourthMomentFromAFE.fourthMoment_le_of_squaredPolynomialWeightedEnergy
#print axioms FixedCharacterFourthMomentFromAFE.nonprincipalFourthMoment_of_separatedMellinBlockAFE
