import GuthMaynardS3Assembly
import GuthMaynardHeathBrownMajorant

/-!
# Dyadic difference-class algebra in Guth--Maynard Lemma 11.6

After Theorem 1.6 is applied to one multiplicity class `U_B`, the source uses
only `B*|U_B| <= |W|^2` and `B^2*|U_B| <= E(W)`.  This file certifies the
nonlinear `3/4,1/2,5/4` interpolation which produces the third term in the
published fourth-moment estimate.
-/

namespace GuthMaynardLemma116

noncomputable section

/-- The literal dyadic class of integer difference bins whose multiplicity is
between `B` and `2B`. -/
def dyadicMultiplicityClass {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (r : ι → ℕ) (B : ℕ) : Finset ι :=
  I.filter fun u => B ≤ r u ∧ r u < 2*B

/-- The finite set of dyadic exponents actually occurring among nonempty
fibres.  Indexing by exponents makes the logarithmic loss in the source's
`\lessapprox sup_B` step explicit. -/
def activeDyadicExponents {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (r : ι → ℕ) : Finset ℕ :=
  (I.filter fun u => r u ≠ 0).image fun u => Nat.log2 (r u)

/-- Every nonempty fibre lies in the class selected by its binary logarithm.
This is the exact power-of-two cover used before the Cauchy step in Lemma
11.6. -/
theorem mem_dyadicMultiplicityClass_two_pow_log2
    {ι : Type*} [DecidableEq ι]
    {I : Finset ι} {r : ι → ℕ} {u : ι}
    (hu : u ∈ I) (hr : r u ≠ 0) :
    u ∈ dyadicMultiplicityClass I r (2 ^ Nat.log2 (r u)) := by
  apply Finset.mem_filter.mpr
  refine ⟨hu, ?_, ?_⟩
  · rw [Nat.log2_eq_log_two]
    exact Nat.pow_log_le_self 2 hr
  have hlt := Nat.lt_pow_succ_log_self Nat.one_lt_two (r u)
  rw [Nat.log2_eq_log_two]
  simpa [pow_succ, Nat.mul_comm] using hlt

theorem log2_mem_activeDyadicExponents
    {ι : Type*} [DecidableEq ι]
    {I : Finset ι} {r : ι → ℕ} {u : ι}
    (hu : u ∈ I) (hr : r u ≠ 0) :
    Nat.log2 (r u) ∈ activeDyadicExponents I r := by
  unfold activeDyadicExponents
  exact Finset.mem_image.mpr ⟨u, Finset.mem_filter.mpr ⟨hu, hr⟩, rfl⟩

/-- If all multiplicities are at most `R`, there are at most
`log₂ R + 1` active classes.  This exposes, rather than hides, the sole
logarithmic factor absorbed by the source's `T^{o(1)}` notation. -/
theorem card_activeDyadicExponents_le_log2_add_one
    {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (r : ι → ℕ) (R : ℕ)
    (hrR : ∀ u ∈ I, r u ≤ R) :
    (activeDyadicExponents I r).card ≤ Nat.log2 R + 1 := by
  have hsubset : activeDyadicExponents I r ⊆ Finset.range (Nat.log2 R + 1) := by
    intro j hj
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hj
    have hu' := Finset.mem_filter.mp hu
    apply Finset.mem_range.mpr
    apply Nat.lt_succ_of_le
    rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
    exact Nat.log_mono_right (hrR u hu'.1)
  have hcard := Finset.card_le_card hsubset
  simpa using hcard

/-- First class budget in Lemma 11.6: `B |U_B|` is at most the total number
of representations. -/
theorem dyadicMultiplicityClass_mul_card_le_sum
    {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (r : ι → ℕ) (B : ℕ) :
    B * (dyadicMultiplicityClass I r B).card ≤ ∑ u ∈ I, r u := by
  let U := dyadicMultiplicityClass I r B
  have hpoint : ∀ u ∈ U, B ≤ r u := by
    intro u hu
    exact (Finset.mem_filter.mp hu).2.1
  have hclass : B * U.card ≤ ∑ u ∈ U, r u := by
    simpa [Nat.mul_comm] using Finset.sum_le_sum hpoint
  have hsubset : U ⊆ I := Finset.filter_subset _ _
  have hsum : (∑ u ∈ U, r u) ≤ ∑ u ∈ I, r u := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun _ _ _ => Nat.zero_le _)
  exact hclass.trans hsum

/-- Second class budget in Lemma 11.6: `B^2 |U_B|` is at most the exact
floor-bin energy `sum r(u)^2`. -/
theorem dyadicMultiplicityClass_sq_mul_card_le_energy
    {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (r : ι → ℕ) (B : ℕ) :
    B^2 * (dyadicMultiplicityClass I r B).card ≤
      ∑ u ∈ I, (r u)^2 := by
  let U := dyadicMultiplicityClass I r B
  have hpoint : ∀ u ∈ U, B^2 ≤ (r u)^2 := by
    intro u hu
    exact Nat.pow_le_pow_left ((Finset.mem_filter.mp hu).2.1) 2
  have hclass : B^2 * U.card ≤ ∑ u ∈ U, (r u)^2 := by
    simpa [Nat.mul_comm] using Finset.sum_le_sum hpoint
  have hsubset : U ⊆ I := Finset.filter_subset _ _
  have hsum : (∑ u ∈ U, (r u)^2) ≤ ∑ u ∈ I, (r u)^2 := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun _ _ _ => Nat.zero_le _)
  exact hclass.trans hsum

theorem sum_image_fiber_card_eq_card
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (f : α → β) :
    (∑ y ∈ S.image f, (S.filter fun x => f x = y).card) = S.card := by
  calc
    (∑ y ∈ S.image f, (S.filter fun x => f x = y).card) =
        ∑ y ∈ S.image f, ∑ x ∈ S, if f x = y then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro y hy
      exact (Finset.sum_boole (fun x => f x = y) S).symm
    _ = ∑ x ∈ S, ∑ y ∈ S.image f, if f x = y then 1 else 0 :=
      Finset.sum_comm
    _ = ∑ _x ∈ S, 1 := by
      apply Finset.sum_congr rfl
      intro x hx
      have hmem : f x ∈ S.image f := Finset.mem_image.mpr ⟨x, hx, rfl⟩
      simp [hmem]
    _ = S.card := by simp

theorem sum_image_fiber_card_sq_eq_equalPair_card
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (f : α → β) :
    (∑ y ∈ S.image f, ((S.filter fun x => f x = y).card)^2) =
      ((S.product S).filter fun p => f p.1 = f p.2).card := by
  classical
  calc
    (∑ y ∈ S.image f, ((S.filter fun x => f x = y).card)^2) =
      ∑ y ∈ S.image f, ∑ x ∈ S, ∑ z ∈ S,
        if f x = y ∧ f z = y then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [pow_two]
          rw [show (S.filter fun x => f x = y).card =
              ∑ x ∈ S, if f x = y then 1 else 0 from
                (Finset.sum_boole (fun x => f x = y) S).symm]
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro x hx
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro z hz
          by_cases hx' : f x = y <;> by_cases hz' : f z = y <;>
            simp [hx', hz']
    _ = ∑ x ∈ S, ∑ z ∈ S, ∑ y ∈ S.image f,
        if f x = y ∧ f z = y then 1 else 0 := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro x hx
          rw [Finset.sum_comm]
    _ = ∑ x ∈ S, ∑ z ∈ S, if f x = f z then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro x hx
          apply Finset.sum_congr rfl
          intro z hz
          by_cases heq : f x = f z
          · rw [if_pos heq]
            have hm : f x ∈ S.image f := Finset.mem_image.mpr ⟨x, hx, rfl⟩
            have hcollapse : (fun y : β =>
                if f x = y ∧ f z = y then 1 else 0) =
                (fun y : β => if f x = y then 1 else 0) := by
              funext y
              by_cases hxy : f x = y
              · have hzy : f z = y := heq.symm.trans hxy
                simp [hxy, hzy]
              · simp [hxy]
            rw [hcollapse, Finset.sum_boole]
            rw [show (S.image f).filter (fun y => f x = y) = {f x} by
              ext y
              simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_singleton]
              constructor
              · intro hy
                exact hy.2.symm
              · intro hy
                subst y
                exact ⟨⟨x, hx, rfl⟩, rfl⟩]
            simp
          · rw [if_neg heq]
            apply Finset.sum_eq_zero
            intro y hy
            by_cases hboth : f x = y ∧ f z = y
            · exact (heq (hboth.1.trans hboth.2.symm)).elim
            · simp [hboth]
    _ = ((S.product S).filter fun p => f p.1 = f p.2).card := by
          rw [show ((S.product S).filter fun p => f p.1 = f p.2).card =
            ∑ p ∈ S.product S, if f p.1 = f p.2 then 1 else 0 from
              (Finset.sum_boole (fun p : α × α => f p.1 = f p.2)
                (S.product S)).symm]
          exact (Finset.sum_product S S
            (fun p : α × α => if f p.1 = f p.2 then 1 else 0)).symm

/-- Integer bin of one ordered difference, exactly as in the definition of
`U_B` in the proof of Lemma 11.6. -/
def floorDifference (p : ℝ × ℝ) : ℤ := ⌊p.1-p.2⌋

def floorDifferenceBins (W : Finset ℝ) : Finset ℤ :=
  (W.product W).image floorDifference

def floorDifferenceMultiplicity (W : Finset ℝ) (u : ℤ) : ℕ :=
  ((W.product W).filter fun p => floorDifference p = u).card

def floorDifferenceEnergy (W : Finset ℝ) : ℕ :=
  ∑ u ∈ floorDifferenceBins W, (floorDifferenceMultiplicity W u)^2

def approximateDifferenceEnergy (W : Finset ℝ) : ℕ :=
  (((W.product W).product (W.product W)).filter fun pq =>
    |(pq.1.1-pq.1.2)-(pq.2.1-pq.2.2)| < 1).card

/-- The real sample set to which Heath--Brown is applied in Lemma 11.6.
Multiplicity is kept in the separate weight `B`; the sample ordinates are the
integer difference bins themselves. -/
def floorDifferenceDyadicRealClass (W : Finset ℝ) (B : ℕ) : Finset ℝ :=
  (dyadicMultiplicityClass (floorDifferenceBins W)
    (floorDifferenceMultiplicity W) B).image fun u : ℤ => (u : ℝ)

theorem card_floorDifferenceDyadicRealClass (W : Finset ℝ) (B : ℕ) :
    (floorDifferenceDyadicRealClass W B).card =
      (dyadicMultiplicityClass (floorDifferenceBins W)
        (floorDifferenceMultiplicity W) B).card := by
  unfold floorDifferenceDyadicRealClass
  rw [Finset.card_image_iff.mpr]
  intro u hu v hv huv
  exact Int.cast_injective huv

/-- Distinct integer bins are one-separated, exactly the spacing hypothesis
of Heath--Brown's theorem. -/
theorem floorDifferenceDyadicRealClass_oneSeparated (W : Finset ℝ) (B : ℕ) :
    CGLProofDAG.OneSeparated (floorDifferenceDyadicRealClass W B) := by
  intro t ht u hu htu
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp ht
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hu
  have hab : a ≠ b := by
    intro h
    apply htu
    exact_mod_cast h
  have hab' : a < b ∨ b < a := lt_or_gt_of_ne hab
  rcases hab' with hab' | hab'
  · have hone : a + 1 ≤ b := by omega
    have honeR : (a : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast hone
    rw [abs_of_nonpos (by linarith : (a : ℝ) - (b : ℝ) ≤ 0)]
    linarith
  · have hone : b + 1 ≤ a := by omega
    have honeR : (b : ℝ) + 1 ≤ (a : ℝ) := by exact_mod_cast hone
    rw [abs_of_nonneg (by linarith : 0 ≤ (a : ℝ) - (b : ℝ))]
    linarith

/-- If the original ordinates occupy an interval of length `T`, their integer
difference bins occupy the explicit interval `[-T-1,T]`, of length `2T+1`.
The extra one is the honest floor endpoint loss. -/
theorem floorDifferenceDyadicRealClass_contained
    {W : Finset ℝ} {T : ℝ}
    (hW : GuthMaynardHeathBrownInterface.ContainedInIntervalOfLength W T) (B : ℕ) :
    GuthMaynardHeathBrownInterface.ContainedInIntervalOfLength
      (floorDifferenceDyadicRealClass W B) (2*T+1) := by
  obtain ⟨x, hx⟩ := hW
  refine ⟨-T-1, ?_⟩
  intro y hy
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
  have haClass := (Finset.mem_filter.mp ha).1
  obtain ⟨p, hp, hpFloor⟩ := Finset.mem_image.mp haClass
  have hpW := Finset.mem_product.mp hp
  have hp1 := hx p.1 hpW.1
  have hp2 := hx p.2 hpW.2
  have hdiffLo : -T ≤ p.1-p.2 := by linarith
  have hdiffHi : p.1-p.2 ≤ T := by linarith
  have hfloorLo : -T-1 ≤ ((⌊p.1-p.2⌋ : ℤ) : ℝ) := by
    have hlt := Int.lt_floor_add_one (p.1-p.2)
    linarith
  have hfloorHi : ((⌊p.1-p.2⌋ : ℤ) : ℝ) ≤ T := by
    exact (Int.floor_le (p.1-p.2)).trans hdiffHi
  have hcast : (a : ℝ) = ((⌊p.1-p.2⌋ : ℤ) : ℝ) := by
    exact_mod_cast hpFloor.symm
  rw [hcast]
  constructor
  · exact hfloorLo
  · linarith

/-- Exact Lemma 11.6 consumer of the coefficient-one Heath--Brown core.
All spacing and aperture hypotheses for the difference-bin class are
constructed here; the only remaining analytic input is the shared
`HeathBrownOneCoefficientCore`. -/
theorem floorDifferenceDyadicRealClass_heathBrown_of_core
    (hcore : GuthMaynardHeathBrownMajorant.HeathBrownOneCoefficientCore)
    {eta : ℝ} (heta : 0 < eta) :
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (T : ℝ) (M : ℕ) (W : Finset ℝ) (B : ℕ),
        T₀ ≤ 2*T+1 → 1 ≤ M →
        GuthMaynardHeathBrownInterface.ContainedInIntervalOfLength W T →
        GuthMaynardHeathBrownInterface.differenceQuadraticForm
            (fun _ => (1 : ℂ)) M (floorDifferenceDyadicRealClass W B) ≤
          C * Real.rpow (2*T+1) eta *
            GuthMaynardHeathBrownMajorant.heathBrownShape (2*T+1) M
              (floorDifferenceDyadicRealClass W B) := by
  obtain ⟨C, T₀, hC, hT₀, hbound⟩ := hcore eta heta
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro T M W B hT hM hW
  exact hbound (2*T+1) M (floorDifferenceDyadicRealClass W B)
    hT hM (floorDifferenceDyadicRealClass_oneSeparated W B)
    (floorDifferenceDyadicRealClass_contained hW B)

theorem abs_sub_lt_one_of_floor_eq
    {x y : ℝ} (hfloor : ⌊x⌋ = ⌊y⌋) : |x-y| < 1 := by
  have hxlo : ((⌊x⌋ : ℤ) : ℝ) ≤ x := Int.floor_le x
  have hxhi : x < ((⌊x⌋ : ℤ) : ℝ)+1 := Int.lt_floor_add_one x
  have hylo : ((⌊y⌋ : ℤ) : ℝ) ≤ y := Int.floor_le y
  have hyhi : y < ((⌊y⌋ : ℤ) : ℝ)+1 := Int.lt_floor_add_one y
  rw [hfloor] at hxlo hxhi
  rw [abs_lt]
  constructor <;> linarith

/-- Every pair of representations counted by one floor bin is a literal
unit-collar additive-energy quadruple. -/
theorem floorDifference_eq_implies_unit_collar
    {p q : ℝ × ℝ} (h : floorDifference p = floorDifference q) :
    |(p.1-p.2)-(q.1-q.2)| < 1 := by
  exact abs_sub_lt_one_of_floor_eq h

theorem floorDifferenceEnergy_le_approximateDifferenceEnergy
    (W : Finset ℝ) :
    floorDifferenceEnergy W ≤ approximateDifferenceEnergy W := by
  rw [show floorDifferenceEnergy W =
      (((W.product W).product (W.product W)).filter fun pq =>
        floorDifference pq.1 = floorDifference pq.2).card by
    exact sum_image_fiber_card_sq_eq_equalPair_card
      (W.product W) floorDifference]
  apply Finset.card_le_card
  intro pq hpq
  have hmem := Finset.mem_filter.mp hpq
  apply Finset.mem_filter.mpr
  exact ⟨hmem.1, floorDifference_eq_implies_unit_collar hmem.2⟩

/-- The exact normalization behind `B |U_B| <= |W|^2`: all ordered pairs
occur in exactly one integer difference bin. -/
theorem sum_floorDifferenceMultiplicity_eq_card_sq (W : Finset ℝ) :
    (∑ u ∈ floorDifferenceBins W, floorDifferenceMultiplicity W u) =
      W.card^2 := by
  rw [show (∑ u ∈ floorDifferenceBins W,
      floorDifferenceMultiplicity W u) = (W.product W).card by
    exact sum_image_fiber_card_eq_card (W.product W) floorDifference]
  simp [pow_two]

/-- The two multiplicity budgets in their literal floor-difference
specialization. -/
theorem floorDifference_dyadic_class_budgets (W : Finset ℝ) (B : ℕ) :
    B * (dyadicMultiplicityClass (floorDifferenceBins W)
      (floorDifferenceMultiplicity W) B).card ≤ W.card^2 ∧
    B^2 * (dyadicMultiplicityClass (floorDifferenceBins W)
      (floorDifferenceMultiplicity W) B).card ≤ floorDifferenceEnergy W := by
  constructor
  · rw [← sum_floorDifferenceMultiplicity_eq_card_sq]
    exact dyadicMultiplicityClass_mul_card_le_sum
      (floorDifferenceBins W) (floorDifferenceMultiplicity W) B
  · exact dyadicMultiplicityClass_sq_mul_card_le_energy
      (floorDifferenceBins W) (floorDifferenceMultiplicity W) B

/-- Source-normalized version of both class budgets, with the second budget
landing in the literal unit-collar additive energy rather than the auxiliary
floor-bin energy. -/
theorem floorDifference_dyadic_class_source_budgets (W : Finset ℝ) (B : ℕ) :
    B * (dyadicMultiplicityClass (floorDifferenceBins W)
      (floorDifferenceMultiplicity W) B).card ≤ W.card^2 ∧
    B^2 * (dyadicMultiplicityClass (floorDifferenceBins W)
      (floorDifferenceMultiplicity W) B).card ≤ approximateDifferenceEnergy W := by
  have h := floorDifference_dyadic_class_budgets W B
  exact ⟨h.1, h.2.trans (floorDifferenceEnergy_le_approximateDifferenceEnergy W)⟩

theorem dyadic_class_interpolation_identity
    {B U : ℝ} (hB : 0 < B) (hU : 0 < U) :
    B^2 * Real.rpow U (5/4 : ℝ) =
      Real.rpow (B^2*U) (3/4 : ℝ) * Real.sqrt (B*U) := by
  rw [Real.sqrt_eq_rpow]
  have hB0 := hB.le
  have hU0 := hU.le
  have hB2 : 0 ≤ B^2 := sq_nonneg B
  change B^2 * U ^ (5/4 : ℝ) =
    (B^2*U) ^ (3/4 : ℝ) * (B*U) ^ (1/2 : ℝ)
  rw [Real.mul_rpow (z := (3/4 : ℝ)) hB2 hU0]
  rw [Real.mul_rpow (z := (1/2 : ℝ)) hB0 hU0]
  have hpowB2 : (B^2 : ℝ) ^ (3/4 : ℝ) =
      B ^ (3/2 : ℝ) := by
    rw [← Real.rpow_natCast B 2, ← Real.rpow_mul hB0]
    congr 1
    ring
  rw [hpowB2]
  have hBadd : B ^ (3/2 : ℝ) * B ^ (1/2 : ℝ) = B^2 := by
    rw [← Real.rpow_add hB]
    norm_num
  have hUadd : U ^ (3/4 : ℝ) * U ^ (1/2 : ℝ) =
      U ^ (5/4 : ℝ) := by
    rw [← Real.rpow_add hU]
    congr 1
    ring
  rw [← hUadd]
  calc
    B ^ 2 * (U ^ (3 / 4 : ℝ) * U ^ (1 / 2 : ℝ)) =
        (B ^ (3/2 : ℝ) * B ^ (1/2 : ℝ)) *
          (U ^ (3/4 : ℝ) * U ^ (1/2 : ℝ)) := by rw [hBadd]
    _ = (B ^ (3/2 : ℝ) * U ^ (3/4 : ℝ)) *
          (B ^ (1/2 : ℝ) * U ^ (1/2 : ℝ)) := by ring

/-- The exact final three-term simplification in Lemma 11.6 for one dyadic
multiplicity class. -/
theorem dyadic_class_heathBrown_shape_le_energy_shape
    {B U R E M T : ℝ}
    (hB : 0 < B) (hU : 0 < U) (hR : 0 ≤ R) (hE : 0 ≤ E)
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hcount : B*U ≤ R^2) (henergy : B^2*U ≤ E) :
    B^2 * (U^2*M + U*M^2 +
      Real.rpow U (5/4 : ℝ)*Real.rpow T (1/2 : ℝ)*M) ≤
      R^4*M + E*M^2 +
        Real.rpow E (3/4 : ℝ)*R*Real.rpow T (1/2 : ℝ)*M := by
  have hBU0 : 0 ≤ B*U := mul_nonneg hB.le hU.le
  have hterm1 : B^2*U^2 ≤ R^4 := by
    have hs := pow_le_pow_left₀ hBU0 hcount 2
    nlinarith
  have hterm2 : B^2*U ≤ E := henergy
  have hfactorE : Real.rpow (B^2*U) (3/4 : ℝ) ≤
      Real.rpow E (3/4 : ℝ) :=
    Real.rpow_le_rpow (mul_nonneg (sq_nonneg B) hU.le) henergy (by norm_num)
  have hfactorR : Real.sqrt (B*U) ≤ R := by
    rw [Real.sqrt_le_iff]
    exact ⟨hR, by simpa [pow_two] using hcount⟩
  have hinterp : B^2 * Real.rpow U (5/4 : ℝ) ≤
      Real.rpow E (3/4 : ℝ)*R := by
    rw [dyadic_class_interpolation_identity hB hU]
    exact mul_le_mul hfactorE hfactorR (Real.sqrt_nonneg _)
      (Real.rpow_nonneg hE _)
  have hTM : 0 ≤ Real.rpow T (1/2 : ℝ)*M :=
    mul_nonneg (Real.rpow_nonneg hT _) hM
  calc
    B^2 * (U^2*M + U*M^2 +
        Real.rpow U (5/4 : ℝ)*Real.rpow T (1/2 : ℝ)*M) =
      (B^2*U^2)*M + (B^2*U)*M^2 +
        (B^2*Real.rpow U (5/4 : ℝ)) *
          (Real.rpow T (1/2 : ℝ)*M) := by ring
    _ ≤ R^4*M + E*M^2 +
        (Real.rpow E (3/4 : ℝ)*R) *
          (Real.rpow T (1/2 : ℝ)*M) := by gcongr
    _ = _ := by ring

/-- Fully source-facing class simplification: the literal floor-difference
class and literal unit-collar energy satisfy the complete final inequality of
the Lemma 11.6 class calculation. -/
theorem floorDifference_dyadic_class_heathBrown_shape_le
    (W : Finset ℝ) {B : ℕ} (hB : 0 < B) {M T : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) :
    let U := (dyadicMultiplicityClass (floorDifferenceBins W)
      (floorDifferenceMultiplicity W) B).card
    (B:ℝ)^2 * ((U:ℝ)^2*M + (U:ℝ)*M^2 +
      Real.rpow (U:ℝ) (5/4 : ℝ)*Real.rpow T (1/2 : ℝ)*M) ≤
      (W.card:ℝ)^4*M + (approximateDifferenceEnergy W:ℝ)*M^2 +
        Real.rpow (approximateDifferenceEnergy W:ℝ) (3/4 : ℝ) *
          (W.card:ℝ)*Real.rpow T (1/2 : ℝ)*M := by
  dsimp only
  let U := (dyadicMultiplicityClass (floorDifferenceBins W)
    (floorDifferenceMultiplicity W) B).card
  by_cases hUzero : U = 0
  · simp [U, hUzero]
    positivity
  · have hU : (0:ℝ) < U := by exact_mod_cast Nat.pos_of_ne_zero hUzero
    have hBR : (0:ℝ) < B := by exact_mod_cast hB
    have hbudgets := floorDifference_dyadic_class_source_budgets W B
    have hcount : (B:ℝ)*(U:ℝ) ≤ (W.card:ℝ)^2 := by
      exact_mod_cast hbudgets.1
    have henergy : (B:ℝ)^2*(U:ℝ) ≤
        (approximateDifferenceEnergy W:ℝ) := by
      exact_mod_cast hbudgets.2
    exact dyadic_class_heathBrown_shape_le_energy_shape hBR hU
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) hM hT hcount henergy

end

end GuthMaynardLemma116

#print axioms GuthMaynardLemma116.dyadic_class_interpolation_identity
#print axioms GuthMaynardLemma116.dyadic_class_heathBrown_shape_le_energy_shape
#print axioms GuthMaynardLemma116.dyadicMultiplicityClass_mul_card_le_sum
#print axioms GuthMaynardLemma116.dyadicMultiplicityClass_sq_mul_card_le_energy
#print axioms GuthMaynardLemma116.sum_floorDifferenceMultiplicity_eq_card_sq
#print axioms GuthMaynardLemma116.floorDifference_dyadic_class_budgets
#print axioms GuthMaynardLemma116.floorDifference_eq_implies_unit_collar
#print axioms GuthMaynardLemma116.floorDifferenceEnergy_le_approximateDifferenceEnergy
#print axioms GuthMaynardLemma116.floorDifference_dyadic_class_source_budgets
#print axioms GuthMaynardLemma116.floorDifference_dyadic_class_heathBrown_shape_le
#print axioms GuthMaynardLemma116.card_floorDifferenceDyadicRealClass
#print axioms GuthMaynardLemma116.floorDifferenceDyadicRealClass_oneSeparated
#print axioms GuthMaynardLemma116.floorDifferenceDyadicRealClass_contained
#print axioms GuthMaynardLemma116.floorDifferenceDyadicRealClass_heathBrown_of_core
#print axioms GuthMaynardLemma116.mem_dyadicMultiplicityClass_two_pow_log2
#print axioms GuthMaynardLemma116.log2_mem_activeDyadicExponents
#print axioms GuthMaynardLemma116.card_activeDyadicExponents_le_log2_add_one
