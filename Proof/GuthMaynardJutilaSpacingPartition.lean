import GuthMaynardJutilaReflection2941
import PostA5LongSpacingAssembly
import GuthMaynardJIterationDeterministic

/-!
# From one-spacing to the `T^delta` spacing in Lemma 29.10

Lemma 29.26 is stated for a one-separated set, while Lemma 29.10 is stated
for a `T^delta`-separated set.  The source calls their passage routine.  This
module certifies its finite core: color floor bins modulo a prescribed natural
number, prove every color is long-separated, and bound the full positive Gram
energy by the number of colors times the sum of the monochromatic energies.
-/

namespace GuthMaynardJutilaSpacingPartition

open scoped BigOperators
open CGLProofDAG
open GuthMaynardHeathBrownMajorant
open PostA5LongSpacingAssembly
open GuthMaynardJutilaReflection2941
open GuthMaynardLengthComparison

noncomputable section

def colorFiber {κ : Type*} [DecidableEq κ]
    {m : ℕ} (color : κ → Fin m) (W : Finset κ) (i : Fin m) : Finset κ :=
  W.filter (fun t => color t = i)

theorem gramKernel_eq_sum_colorFibers
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    {m : ℕ} (color : κ → Fin m) (S : Finset ι) (W : Finset κ)
    (z : ι → κ → ℂ) (n r : ι) :
    gramKernel W z n r =
      ∑ i : Fin m, gramKernel (colorFiber color W i) z n r := by
  classical
  have hfiber := Finset.sum_fiberwise W color
    (fun t => z n t * star (z r t))
  unfold gramKernel colorFiber
  simpa [Finset.filter_filter, and_comm] using hfiber.symm

/-- Positive Gram energy loses at most the number of colors under a finite
partition.  This is the exact Hilbert--Schmidt Cauchy step hidden in the
one-spaced to long-spaced passage. -/
theorem realGramQuadratic_le_card_mul_sum_colorFibers
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    {m : ℕ} (color : κ → Fin m) (S : Finset ι) (W : Finset κ)
    (b : ι → ℝ) (z : ι → κ → ℂ)
    (hb : ∀ n ∈ S, 0 ≤ b n) :
    realGramQuadratic S W (fun n => (b n : ℂ)) z ≤
      (m : ℝ) * ∑ i : Fin m,
        realGramQuadratic S (colorFiber color W i)
          (fun n => (b n : ℂ)) z := by
  rw [← absoluteCoefficientMajorant_real_nonnegative_eq S W b z hb]
  have hfiberEq (i : Fin m) :
      absoluteCoefficientMajorant S (colorFiber color W i)
          (fun n => (b n : ℂ)) z =
        realGramQuadratic S (colorFiber color W i)
          (fun n => (b n : ℂ)) z :=
    absoluteCoefficientMajorant_real_nonnegative_eq
      S (colorFiber color W i) b z hb
  unfold absoluteCoefficientMajorant
  calc
    (∑ n ∈ S, ∑ r ∈ S,
        ‖(b n : ℂ)‖ * ‖(b r : ℂ)‖ * ‖gramKernel W z n r‖ ^ 2) ≤
      ∑ n ∈ S, ∑ r ∈ S,
        ‖(b n : ℂ)‖ * ‖(b r : ℂ)‖ *
          ((m : ℝ) * ∑ i : Fin m,
            ‖gramKernel (colorFiber color W i) z n r‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro n hn
      apply Finset.sum_le_sum
      intro r hr
      have hcs :
          ‖∑ i : Fin m, gramKernel (colorFiber color W i) z n r‖ ^ 2 ≤
            (m : ℝ) * ∑ i : Fin m,
              ‖gramKernel (colorFiber color W i) z n r‖ ^ 2 := by
        simpa using
          (GuthMaynardJIteration.norm_finset_sum_sq_le_card_mul_sum_norm_sq
            (Finset.univ : Finset (Fin m))
            (fun i => gramKernel (colorFiber color W i) z n r))
      rw [← gramKernel_eq_sum_colorFibers color S W z n r] at hcs
      exact mul_le_mul_of_nonneg_left hcs (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = (m : ℝ) * ∑ i : Fin m,
        realGramQuadratic S (colorFiber color W i)
          (fun n => (b n : ℂ)) z := by
      simp_rw [← hfiberEq]
      unfold absoluteCoefficientMajorant
      let F : ι → ι → Fin m → ℝ := fun n r i =>
        ‖(b n : ℂ)‖ * ‖(b r : ℂ)‖ *
          ‖gramKernel (colorFiber color W i) z n r‖ ^ 2
      change
        (∑ n ∈ S, ∑ r ∈ S,
          ‖(b n : ℂ)‖ * ‖(b r : ℂ)‖ *
            ((m : ℝ) * ∑ i : Fin m,
              ‖gramKernel (colorFiber color W i) z n r‖ ^ 2)) =
          (m : ℝ) * ∑ i : Fin m, ∑ n ∈ S, ∑ r ∈ S, F n r i
      calc
        _ = ∑ n ∈ S, ∑ r ∈ S, ∑ i : Fin m, (m : ℝ) * F n r i := by
          apply Finset.sum_congr rfl
          intro n hn
          apply Finset.sum_congr rfl
          intro r hr
          rw [Finset.mul_sum]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          dsimp [F]
          ring
        _ = ∑ n ∈ S, ∑ i : Fin m, ∑ r ∈ S, (m : ℝ) * F n r i := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [Finset.sum_comm]
        _ = ∑ i : Fin m, ∑ n ∈ S, ∑ r ∈ S, (m : ℝ) * F n r i := by
          rw [Finset.sum_comm]
        _ = (m : ℝ) * ∑ i : Fin m, ∑ n ∈ S, ∑ r ∈ S, F n r i := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro n hn
          rw [Finset.mul_sum]

def realFloorResidue {m : ℕ} (hm : 0 < m) (t : ℝ) : Fin m :=
  floorBinResidue m hm (Int.floor t)

theorem floor_ne_of_oneSeparated
    {W : Finset ℝ} (hsep : OneSeparated W)
    {t u : ℝ} (ht : t ∈ W) (hu : u ∈ W) (htu : t ≠ u) :
    Int.floor t ≠ Int.floor u := by
  intro hfloor
  have htlo := Int.floor_le t
  have hthi := Int.lt_floor_add_one t
  have hulo := Int.floor_le u
  have huhi := Int.lt_floor_add_one u
  rw [hfloor] at htlo hthi
  have hdiff : |t - u| < 1 := by
    rcases le_total t u with htu' | hut'
    · rw [abs_of_nonpos (sub_nonpos.mpr htu')]
      linarith
    · rw [abs_of_nonneg (sub_nonneg.mpr hut')]
      linarith
  exact (not_lt_of_ge (hsep t ht u hu htu)) hdiff

/-- Points in one residue color are separated by at least `m-1`. -/
theorem colorFiber_longSeparated
    {W : Finset ℝ} (hsep : OneSeparated W)
    {m : ℕ} (hm : 0 < m) (i : Fin m) :
    ∀ t ∈ colorFiber (realFloorResidue hm) W i,
      ∀ u ∈ colorFiber (realFloorResidue hm) W i,
        t ≠ u → (m : ℝ) - 1 ≤ |t - u| := by
  intro t ht u hu htu
  have ht' := Finset.mem_filter.mp ht
  have hu' := Finset.mem_filter.mp hu
  have hfloorNe := floor_ne_of_oneSeparated hsep ht'.1 hu'.1 htu
  have hres : floorBinResidue m hm (Int.floor t) =
      floorBinResidue m hm (Int.floor u) := ht'.2.trans hu'.2.symm
  have hbin := floorBin_gap_of_same_residue hm hfloorNe hres
  have htlo := Int.floor_le t
  have hthi := Int.lt_floor_add_one t
  have hulo := Int.floor_le u
  have huhi := Int.lt_floor_add_one u
  change (m : ℝ) ≤ |((Int.floor t : ℤ) : ℝ) - ((Int.floor u : ℤ) : ℝ)| at hbin
  rcases le_total t u with htu' | hut'
  · rw [abs_of_nonpos (sub_nonpos.mpr htu')] 
    rw [abs_of_nonpos] at hbin
    · linarith
    · have hfloorMono :
          (((Int.floor t : ℤ) : ℝ)) ≤ ((Int.floor u : ℤ) : ℝ) := by
          exact_mod_cast Int.floor_mono htu'
      linarith
  · rw [abs_of_nonneg (sub_nonneg.mpr hut')]
    rw [abs_of_nonneg] at hbin
    · linarith
    · have hfloorMono :
          (((Int.floor u : ℤ) : ℝ)) ≤ ((Int.floor t : ℤ) : ℝ) := by
          exact_mod_cast Int.floor_mono hut'
      linarith

def powerSpacingColorCount (T delta : ℝ) : ℕ :=
  Nat.ceil (max 0 (Real.rpow T delta) + 1)

theorem powerSpacingColorCount_pos (T delta : ℝ) :
    0 < powerSpacingColorCount T delta := by
  unfold powerSpacingColorCount
  have hceil : max 0 (Real.rpow T delta) + 1 ≤
      (Nat.ceil (max 0 (Real.rpow T delta) + 1) : ℝ) := Nat.le_ceil _
  have hpow : 0 ≤ max 0 (Real.rpow T delta) := le_max_left _ _
  by_contra h
  have hz : Nat.ceil (max 0 (Real.rpow T delta) + 1) = 0 :=
    Nat.eq_zero_of_not_pos h
  rw [hz] at hceil
  norm_num at hceil
  have hstrict : 0 < max 0 (Real.rpow T delta) + 1 := by linarith
  exact (not_lt_of_ge hceil) hstrict

theorem powerSpacingColorCount_cast_le
    {T delta : ℝ} (hT : 1 ≤ T) (hdelta : 0 ≤ delta) :
    (powerSpacingColorCount T delta : ℝ) ≤
      3 * Real.rpow T delta := by
  have hpow : 1 ≤ Real.rpow T delta := Real.one_le_rpow hT hdelta
  have hmax : max 0 (Real.rpow T delta) = Real.rpow T delta :=
    max_eq_right (le_trans zero_le_one hpow)
  have hx : 0 ≤ max 0 (Real.rpow T delta) + 1 := by positivity
  have hceil0 := Nat.ceil_lt_add_one hx
  change (Nat.ceil (max 0 (Real.rpow T delta) + 1) : ℝ) <
    (max 0 (Real.rpow T delta) + 1) + 1 at hceil0
  rw [hmax] at hceil0
  unfold powerSpacingColorCount
  rw [hmax]
  nlinarith

def powerSpacingColor
    (T delta : ℝ) (t : ℝ) : Fin (powerSpacingColorCount T delta) :=
  realFloorResidue (powerSpacingColorCount_pos T delta) t

theorem powerSpacingColorFiber_TPowerSeparated
    {W : Finset ℝ} (hsep : OneSeparated W)
    {T delta : ℝ} (i : Fin (powerSpacingColorCount T delta)) :
    TPowerSeparated (colorFiber (powerSpacingColor T delta) W i) T delta := by
  intro t ht u hu htu
  have hgap := colorFiber_longSeparated hsep
    (powerSpacingColorCount_pos T delta) i t ht u hu htu
  have hceil0 : max 0 (Real.rpow T delta) + 1 ≤
      (powerSpacingColorCount T delta : ℝ) := by
    unfold powerSpacingColorCount
    exact Nat.le_ceil _
  have htoMax : Real.rpow T delta + 1 ≤
      max 0 (Real.rpow T delta) + 1 :=
    by simpa [add_comm] using
      (add_le_add_right (le_max_right (0 : ℝ) (Real.rpow T delta)) 1)
  have hceil : Real.rpow T delta + 1 ≤
      (powerSpacingColorCount T delta : ℝ) := htoMax.trans hceil0
  exact hceil |> fun h => by linarith

/-- Exact positive-energy partition for Jutila's coefficient-one moment. -/
theorem jutilaSecondMoment_le_powerSpacingColor_sum
    (M T delta : ℝ) (W : Finset ℝ) :
    jutilaSecondMoment M W ≤
      (powerSpacingColorCount T delta : ℝ) *
        ∑ i : Fin (powerSpacingColorCount T delta),
          jutilaSecondMoment M
            (colorFiber (powerSpacingColor T delta) W i) := by
  unfold jutilaSecondMoment
  exact realGramQuadratic_le_card_mul_sum_colorFibers
    (powerSpacingColor T delta) (realDyadicIoc M) W
    inverseSqrtWeight dirichletPhase
    (fun n hn => inverseSqrtWeight_nonneg n)

end

end GuthMaynardJutilaSpacingPartition

#print axioms GuthMaynardJutilaSpacingPartition.realGramQuadratic_le_card_mul_sum_colorFibers
#print axioms GuthMaynardJutilaSpacingPartition.colorFiber_longSeparated
#print axioms GuthMaynardJutilaSpacingPartition.powerSpacingColorFiber_TPowerSeparated
#print axioms GuthMaynardJutilaSpacingPartition.jutilaSecondMoment_le_powerSpacingColor_sum
