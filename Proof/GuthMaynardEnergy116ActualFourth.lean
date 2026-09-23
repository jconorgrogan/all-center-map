import GuthMaynardEnergy116ClassMean
import GuthMaynardEnergy116Decomposition
import GuthMaynardEnergy116Endpoint
import GuthMaynardEnergy116ShiftedMean
import GuthMaynardEnergy116ClassBudgets

open scoped BigOperators Real
open CGLProofDAG GuthMaynardLemma116 GuthMaynardRatioKernelIdentity
open GuthMaynardHeathBrownInterface GuthMaynardLemma118
open GuthMaynardS3LiteralLemma83Energy
open GuthMaynardEnergy116Decomposition GuthMaynardEnergy116Endpoint
open GuthMaynardEnergy116ShiftedMean GuthMaynardEnergy116ClassBudgets
open GuthMaynardEnergy116GroupedMoment GuthMaynardEnergy116ClassMean
open GuthMaynardEnergy114WeightedAverage GuthMaynardHeathBrownMajorant

noncomputable section
set_option maxHeartbeats 1600000
namespace GuthMaynardEnergy116ActualFourth

private theorem dyadic_class_shape_le_source
    (W : Finset ℝ) (B M : ℕ) {X : ℝ}
    (hB : 0 < B) (hX : 0 ≤ X) :
    (B : ℝ)^2 * heathBrownShape X M
        (floorDifferenceDyadicRealClass W B) ≤
      (W.card : ℝ)^4 * (M : ℝ) +
        (sourceApproximateAdditiveEnergy W : ℝ) * (M : ℝ)^2 +
        Real.rpow (sourceApproximateAdditiveEnergy W : ℝ) (3/4 : ℝ) *
          (W.card : ℝ) * Real.rpow X (1/2 : ℝ) * (M : ℝ) := by
  let U : ℕ := (dyadicMultiplicityClass (floorDifferenceBins W)
    (floorDifferenceMultiplicity W) B).card
  by_cases hU : U = 0
  · have hcard : (floorDifferenceDyadicRealClass W B).card = 0 := by
      rw [card_floorDifferenceDyadicRealClass]
      simpa [U] using hU
    unfold heathBrownShape
    rw [hcard]
    have hR : 0 ≤ (W.card : ℝ)^4 * (M : ℝ) +
        (sourceApproximateAdditiveEnergy W : ℝ) * (M : ℝ)^2 +
        Real.rpow (sourceApproximateAdditiveEnergy W : ℝ) (3/4 : ℝ) *
          (W.card : ℝ) * Real.rpow X (1/2 : ℝ) * (M : ℝ) := by
      have hE : 0 ≤ (sourceApproximateAdditiveEnergy W : ℝ) := by positivity
      have hcard0 : 0 ≤ (W.card : ℝ) := Nat.cast_nonneg _
      have hM0 : 0 ≤ (M : ℝ) := Nat.cast_nonneg _
      have hX0 : 0 ≤ Real.rpow X (1/2 : ℝ) := Real.rpow_nonneg hX _
      have hEpow : 0 ≤ Real.rpow (sourceApproximateAdditiveEnergy W : ℝ) (3/4 : ℝ) :=
        Real.rpow_nonneg hE _
      positivity
    simpa using hR
  · have hUpos : 0 < (U : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hU
    have hcard : (floorDifferenceDyadicRealClass W B).card = U := by
      dsimp [U]
      exact card_floorDifferenceDyadicRealClass W B
    unfold heathBrownShape
    rw [hcard]
    have hbud := floorDifference_source_class_budgets W B
    have hcount : (B : ℝ) * (U : ℝ) ≤ (W.card : ℝ)^2 := by
      exact_mod_cast hbud.1
    have henergy : (B : ℝ)^2 * (U : ℝ) ≤
        (sourceApproximateAdditiveEnergy W : ℝ) := by
      exact_mod_cast hbud.2
    exact dyadic_class_heathBrown_shape_le_energy_shape
      (by exact_mod_cast hB) hUpos
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hX hcount henergy

/-- Explicit source-facing finite Lemma 11.6 weld. The logarithmic class
count and endpoint correction are kept visible. -/
theorem discrete_fourth_moment {eta : ℝ} (heta : 0 < eta) :
    ∃ C T0 : ℝ, 0 < C ∧ 2 ≤ T0 ∧
      ∀ (M : ℕ) (W : Finset ℝ) (T : ℝ),
        1 ≤ M → 1 ≤ T → T0 ≤ 2*T+1 →
        OneSeparated W → ContainedInIntervalOfLength W T →
        ratioKernelMoment 4 M W ≤
          C * Real.rpow (2*T+1) eta *
            ((Nat.log2 W.card + 1 : ℕ) : ℝ)^2 *
            ((M : ℝ) * (W.card : ℝ)^4 +
              (M : ℝ)^2 * (sourceApproximateAdditiveEnergy W : ℝ) +
              Real.rpow (sourceApproximateAdditiveEnergy W : ℝ) (3/4 : ℝ) *
                (W.card : ℝ) * Real.rpow (2*T+1) (1/2 : ℝ) * M) := by
  obtain ⟨Cl, hCl, hclass⟩ :=
    groupedDifferenceField116_Ioc_local_fibre_capstone
  obtain ⟨Cw, Tw, hCw, hTw, hweighted⟩ := weighted_difference_bound heta
  let C : ℝ := 4 * Cl * Cw + 3
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, max 2 (Tw+1), hC, ?_, ?_⟩
  · exact le_max_left _ _
  intro M W T hM hT hTX hsep hcontained
  let X : ℝ := 2*T+1
  let K : ℝ := ((Nat.log2 W.card + 1 : ℕ) : ℝ)
  have hX : 0 ≤ X := by dsimp [X]; linarith
  have hMreal : 0 ≤ (M : ℝ) := Nat.cast_nonneg _
  have hUsep (B : ℕ) : OneSeparated (floorDifferenceDyadicRealClass W B) :=
    floorDifferenceDyadicRealClass_oneSeparated W B
  have hTwX : Tw ≤ X := by
    have hm := le_max_right (2 : ℝ) (Tw + 1)
    dsimp [X] at hTX ⊢
    linarith
  have hUcontained (B : ℕ) :
      ContainedInIntervalOfLength (floorDifferenceDyadicRealClass W B) X := by
    simpa [X] using floorDifferenceDyadicRealClass_contained hcontained B
  have hweighted (B : ℕ) :
      (∑ u ∈ floorDifferenceDyadicRealClass W B,
        ∑ v ∈ floorDifferenceDyadicRealClass W B,
          dirichletWeightedSquareMean M (fun _ => (1 : ℂ)) (u-v)) ≤
        Cw * Real.rpow X eta *
          heathBrownShape X M (floorDifferenceDyadicRealClass W B) := by
    have hb : ∀ n ∈ Finset.Ioc M (2 * M), ‖(1 : ℂ)‖ ≤ 1 := by
      intro n hn
      simp
    exact hweighted X M (fun _ => (1 : ℂ))
      (floorDifferenceDyadicRealClass W B)
      hTwX hM hb (hUsep B) (hUcontained B)
  have hdecomp :
      (∑ n ∈ Finset.Ioc M (2*M), ∑ m ∈ Finset.Ioc M (2*M),
        ‖ratioDirichletKernel W ((n : ℝ)/(m : ℝ))‖^4) ≤
      ((activeDyadicExponents116 W).card : ℝ) *
        ∑ n ∈ Finset.Ioc M (2*M), ∑ m ∈ Finset.Ioc M (2*M),
          ∑ j ∈ activeDyadicExponents116 W,
            ‖groupedDifferenceField W j ((n : ℝ)/(m : ℝ))‖^2 := by
    calc
      _ ≤ ∑ n ∈ Finset.Ioc M (2*M), ∑ m ∈ Finset.Ioc M (2*M),
          ((activeDyadicExponents116 W).card : ℝ) *
            ∑ j ∈ activeDyadicExponents116 W,
              ‖groupedDifferenceField W j ((n : ℝ)/(m : ℝ))‖^2 := by
        apply Finset.sum_le_sum
        intro n hn
        apply Finset.sum_le_sum
        intro m hm
        exact ratioKernel_fourth_le_active_grouped W ((n : ℝ)/(m : ℝ))
      _ = _ := by simp only [Finset.mul_sum]
  have hK : (activeDyadicExponents116 W).card ≤ Nat.log2 W.card + 1 :=
    active_exponent_card_le_log_card W hsep
  have hclasssum :
      (∑ n ∈ Finset.Ioc M (2*M), ∑ m ∈ Finset.Ioc M (2*M),
        ‖ratioDirichletKernel W ((n : ℝ)/(m : ℝ))‖^4) ≤
      K * ∑ j ∈ activeDyadicExponents116 W,
        ∑ n ∈ Finset.Ioc M (2*M), ∑ m ∈ Finset.Ioc M (2*M),
          ‖groupedDifferenceField W j ((n : ℝ)/(m : ℝ))‖^2 := by
    calc
      _ ≤ ((activeDyadicExponents116 W).card : ℝ) *
          ∑ n ∈ Finset.Ioc M (2*M), ∑ m ∈ Finset.Ioc M (2*M),
            ∑ j ∈ activeDyadicExponents116 W,
              ‖groupedDifferenceField W j ((n : ℝ)/(m : ℝ))‖^2 := hdecomp
      _ ≤ K * ∑ j ∈ activeDyadicExponents116 W,
          ∑ n ∈ Finset.Ioc M (2*M), ∑ m ∈ Finset.Ioc M (2*M),
            ‖groupedDifferenceField W j ((n : ℝ)/(m : ℝ))‖^2 := by
        have hrew :
            (∑ n ∈ Finset.Ioc M (2*M), ∑ m ∈ Finset.Ioc M (2*M),
              ∑ j ∈ activeDyadicExponents116 W,
                ‖groupedDifferenceField W j ((n : ℝ)/(m : ℝ))‖^2) =
              ∑ j ∈ activeDyadicExponents116 W,
                ∑ n ∈ Finset.Ioc M (2*M), ∑ m ∈ Finset.Ioc M (2*M),
                  ‖groupedDifferenceField W j ((n : ℝ)/(m : ℝ))‖^2 := by
          calc
            _ = ∑ n ∈ Finset.Ioc M (2*M), ∑ j ∈ activeDyadicExponents116 W,
                  ∑ m ∈ Finset.Ioc M (2*M),
                    ‖groupedDifferenceField W j ((n : ℝ)/(m : ℝ))‖^2 := by
              apply Finset.sum_congr rfl
              intro n hn
              rw [Finset.sum_comm]
            _ = _ := by rw [Finset.sum_comm]
        rw [hrew]
        gcongr
        dsimp [K]
        exact_mod_cast hK
  have hclassbound :
      ∑ j ∈ activeDyadicExponents116 W,
        ∑ n ∈ Finset.Ioc M (2*M), ∑ m ∈ Finset.Ioc M (2*M),
          ‖groupedDifferenceField W j ((n : ℝ)/(m : ℝ))‖^2 ≤
      K * (4 * Cl * Cw * Real.rpow X eta *
        ((W.card : ℝ)^4 * (M : ℝ) +
          (M : ℝ)^2 * (sourceApproximateAdditiveEnergy W : ℝ) +
          Real.rpow (sourceApproximateAdditiveEnergy W : ℝ) (3/4 : ℝ) *
            (W.card : ℝ) * Real.rpow X (1/2 : ℝ) * M)) := by
    have hper : ∀ j ∈ activeDyadicExponents116 W,
        (∑ n ∈ Finset.Ioc M (2*M), ∑ m ∈ Finset.Ioc M (2*M),
          ‖groupedDifferenceField W j ((n : ℝ)/(m : ℝ))‖^2) ≤
      4 * Cl * Cw * Real.rpow X eta *
        ((W.card : ℝ)^4 * (M : ℝ) +
          (M : ℝ)^2 * (sourceApproximateAdditiveEnergy W : ℝ) +
          Real.rpow (sourceApproximateAdditiveEnergy W : ℝ) (3/4 : ℝ) *
            (W.card : ℝ) * Real.rpow X (1/2 : ℝ) * M) := by
      intro j hj
      have hc := hclass M W j hM
      have hw := hweighted (2^j)
      have hs := dyadic_class_shape_le_source W (2^j) M (by positivity) hX
      calc
        _ ≤ 4 * Cl * ((2 ^ j : ℕ) : ℝ)^2 *
            (∑ u ∈ floorDifferenceDyadicRealClass W (2^j),
              ∑ v ∈ floorDifferenceDyadicRealClass W (2^j),
                dirichletWeightedSquareMean M (fun _ => (1 : ℂ)) (u-v)) := hc
        _ ≤ 4 * Cl * ((2 ^ j : ℕ) : ℝ)^2 *
            (Cw * Real.rpow X eta *
              heathBrownShape X M (floorDifferenceDyadicRealClass W (2^j))) := by
          gcongr
        _ ≤ 4 * Cl * Cw * Real.rpow X eta *
            ((W.card : ℝ)^4 * (M : ℝ) +
              (M : ℝ)^2 * (sourceApproximateAdditiveEnergy W : ℝ) +
              Real.rpow (sourceApproximateAdditiveEnergy W : ℝ) (3/4 : ℝ) *
                (W.card : ℝ) * Real.rpow X (1/2 : ℝ) * M) := by
          have hXeta : 0 ≤ Real.rpow X eta := Real.rpow_nonneg hX _
          have hfac : 0 ≤ 4 * Cl * Cw * Real.rpow X eta := by
            have h4 : (0 : ℝ) ≤ 4 := by norm_num
            have hCw0 : 0 ≤ Cw := le_of_lt hCw
            exact mul_nonneg (mul_nonneg (mul_nonneg h4 hCl) hCw0) hXeta
          nlinarith [mul_le_mul_of_nonneg_left hs hfac]
    calc
      _ ≤ ∑ j ∈ activeDyadicExponents116 W,
          (4 * Cl * Cw * Real.rpow X eta *
            ((W.card : ℝ)^4 * (M : ℝ) +
              (M : ℝ)^2 * (sourceApproximateAdditiveEnergy W : ℝ) +
              Real.rpow (sourceApproximateAdditiveEnergy W : ℝ) (3/4 : ℝ) *
                (W.card : ℝ) * Real.rpow X (1/2 : ℝ) * M)) := by
        apply Finset.sum_le_sum
        intro j hj
        exact hper j hj
      _ = (activeDyadicExponents116 W).card *
          (4 * Cl * Cw * Real.rpow X eta *
            ((W.card : ℝ)^4 * (M : ℝ) +
              (M : ℝ)^2 * (sourceApproximateAdditiveEnergy W : ℝ) +
              Real.rpow (sourceApproximateAdditiveEnergy W : ℝ) (3/4 : ℝ) *
                (W.card : ℝ) * Real.rpow X (1/2 : ℝ) * M)) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ K * (4 * Cl * Cw * Real.rpow X eta *
            ((W.card : ℝ)^4 * (M : ℝ) +
              (M : ℝ)^2 * (sourceApproximateAdditiveEnergy W : ℝ) +
              Real.rpow (sourceApproximateAdditiveEnergy W : ℝ) (3/4 : ℝ) *
                (W.card : ℝ) * Real.rpow X (1/2 : ℝ) * M)) := by
        have hKcast : ((activeDyadicExponents116 W).card : ℝ) ≤ K := by
          dsimp [K]
          exact_mod_cast hK
        have hE : 0 ≤ (sourceApproximateAdditiveEnergy W : ℝ) := by positivity
        have hbase : 0 ≤ 4 * Cl * Cw * Real.rpow X eta *
            ((W.card : ℝ)^4 * (M : ℝ) +
              (M : ℝ)^2 * (sourceApproximateAdditiveEnergy W : ℝ) +
              Real.rpow (sourceApproximateAdditiveEnergy W : ℝ) (3/4 : ℝ) *
                (W.card : ℝ) * Real.rpow X (1/2 : ℝ) * M) := by
          have hcard0 : 0 ≤ (W.card : ℝ) := Nat.cast_nonneg _
          have hM0 : 0 ≤ (M : ℝ) := Nat.cast_nonneg _
          have hXeta : 0 ≤ Real.rpow X eta := Real.rpow_nonneg hX _
          have hXhalf : 0 ≤ Real.rpow X (1/2 : ℝ) := Real.rpow_nonneg hX _
          have hEpow : 0 ≤ Real.rpow (sourceApproximateAdditiveEnergy W : ℝ) (3/4 : ℝ) :=
            Real.rpow_nonneg hE _
          have hshape : 0 ≤
              (W.card : ℝ)^4 * (M : ℝ) +
                (M : ℝ)^2 * (sourceApproximateAdditiveEnergy W : ℝ) +
                Real.rpow (sourceApproximateAdditiveEnergy W : ℝ) (3/4 : ℝ) *
                  (W.card : ℝ) * Real.rpow X (1/2 : ℝ) * M := by
            positivity
          have h4 : (0 : ℝ) ≤ 4 := by norm_num
          have hCw0 : 0 ≤ Cw := le_of_lt hCw
          have hcoeff : 0 ≤ 4 * Cl * Cw :=
            mul_nonneg (mul_nonneg h4 hCl) hCw0
          exact mul_nonneg (mul_nonneg hcoeff hXeta) hshape
        exact mul_le_mul_of_nonneg_right hKcast hbase
  have hopen : openRatioMoment 4 M W ≤
      K^2 * 4 * Cl * Cw * Real.rpow X eta *
        ((W.card : ℝ)^4 * (M : ℝ) +
          (M : ℝ)^2 * (sourceApproximateAdditiveEnergy W : ℝ) +
          Real.rpow (sourceApproximateAdditiveEnergy W : ℝ) (3/4 : ℝ) *
            (W.card : ℝ) * Real.rpow X (1/2 : ℝ) * M) := by
    unfold openRatioMoment
    have hnon : 0 ≤ K := by positivity
    calc
      _ ≤ K * _ := hclasssum
      _ ≤ K * (K * (4 * Cl * Cw * Real.rpow X eta * _)) :=
        mul_le_mul_of_nonneg_left hclassbound hnon
      _ = _ := by ring
  have hclosed := closed_fourth_le_open_add_three M W hM
  have hR4 : 0 ≤ (W.card : ℝ)^4 := by positivity
  have hX1 : (1 : ℝ) ≤ X := by dsimp [X]; linarith
  have hXpow : 1 ≤ Real.rpow X eta := Real.one_le_rpow hX1 (le_of_lt heta)
  let S : ℝ :=
    (W.card : ℝ)^4 * (M : ℝ) +
      (M : ℝ)^2 * (sourceApproximateAdditiveEnergy W : ℝ) +
      Real.rpow (sourceApproximateAdditiveEnergy W : ℝ) (3/4 : ℝ) *
        (W.card : ℝ) * Real.rpow X (1/2 : ℝ) * M
  have hSnon : 0 ≤
      S := by
    have hE : 0 ≤ (sourceApproximateAdditiveEnergy W : ℝ) := by positivity
    dsimp [S]
    positivity
  have hend : 3 * (M : ℝ) * (W.card : ℝ)^4 ≤
      3 * Real.rpow X eta * K^2 * S := by
    by_cases hcard : W.card = 0
    · have hW0 : W = ∅ := Finset.card_eq_zero.mp hcard
      subst W
      have hright : 0 ≤ 3 * Real.rpow X eta * K^2 * S := by
        positivity
      simpa using hright
    · have hR1 : (1 : ℝ) ≤ (W.card : ℝ) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hcard)
      have hK1 : (1 : ℝ) ≤ K := by
        dsimp [K]
        have : 1 ≤ Nat.log2 W.card + 1 := Nat.succ_le_succ (Nat.zero_le _)
        exact_mod_cast this
      have hfac : 1 ≤ Real.rpow X eta * K^2 := by
        have hKsq : (1 : ℝ) ≤ K^2 := by nlinarith [sq_nonneg (K-1)]
        nlinarith [mul_le_mul hXpow hKsq (by positivity) (by positivity)]
      calc
        3 * (M : ℝ) * (W.card : ℝ)^4 = 3 * ((W.card : ℝ)^4 * M) := by ring
        _ ≤ 3 * S := by
          have hE : 0 ≤ (sourceApproximateAdditiveEnergy W : ℝ) := by positivity
          have hB : 0 ≤ (M : ℝ)^2 * (sourceApproximateAdditiveEnergy W : ℝ) :=
            mul_nonneg (sq_nonneg _) hE
          have hC : 0 ≤ Real.rpow (sourceApproximateAdditiveEnergy W : ℝ) (3/4 : ℝ) *
              (W.card : ℝ) * Real.rpow X (1/2 : ℝ) * M := by
            have hpow : 0 ≤ Real.rpow (sourceApproximateAdditiveEnergy W : ℝ) (3/4 : ℝ) :=
              Real.rpow_nonneg hE _
            exact mul_nonneg (mul_nonneg (mul_nonneg hpow (Nat.cast_nonneg _))
              (Real.rpow_nonneg hX _)) (Nat.cast_nonneg _)
          have hsum : (W.card : ℝ)^4 * (M : ℝ) ≤ S := by
            dsimp [S]
            calc
              (W.card : ℝ)^4 * (M : ℝ) ≤
                  (W.card : ℝ)^4 * (M : ℝ) + (M : ℝ)^2 *
                    (sourceApproximateAdditiveEnergy W : ℝ) :=
                le_add_of_nonneg_right hB
              _ ≤ ((W.card : ℝ)^4 * (M : ℝ) + (M : ℝ)^2 *
                    (sourceApproximateAdditiveEnergy W : ℝ)) +
                    Real.rpow (sourceApproximateAdditiveEnergy W : ℝ) (3/4 : ℝ) *
                      (W.card : ℝ) * Real.rpow X (1/2 : ℝ) * M :=
                le_add_of_nonneg_right hC
          exact mul_le_mul_of_nonneg_left hsum (by norm_num)
        _ ≤ 3 * Real.rpow X eta * K^2 * S := by
          have hmul : S ≤ (Real.rpow X eta * K^2) * S :=
            by simpa using (mul_le_mul_of_nonneg_right hfac hSnon)
          have hmul3 : 3 * S ≤ 3 * ((Real.rpow X eta * K^2) * S) :=
            mul_le_mul_of_nonneg_left hmul (by norm_num)
          convert hmul3 using 1 <;> ring
  have hmain :
      openRatioMoment 4 M W + 3*(M : ℝ)*(W.card : ℝ)^4 ≤
        C * Real.rpow X eta * K^2 * S := by
    calc
      _ ≤ K^2 * 4 * Cl * Cw * Real.rpow X eta * S +
          3 * Real.rpow X eta * K^2 * S := by
        exact add_le_add (by nlinarith [hopen]) hend
      _ = _ := by dsimp [C]; ring
  calc
    ratioKernelMoment 4 M W ≤ openRatioMoment 4 M W + 3*(M : ℝ)*(W.card : ℝ)^4 := hclosed
    _ ≤ _ := by simpa [S] using hmain
    _ = _ := by dsimp [X, K]; ring

end GuthMaynardEnergy116ActualFourth

#print axioms GuthMaynardEnergy116ActualFourth.discrete_fourth_moment
