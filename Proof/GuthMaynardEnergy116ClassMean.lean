import GuthMaynardEnergy116GroupedMoment
import GuthMaynardLemma116ClassAlgebra
import GuthMaynardEnergy114LocalL2
import GuthMaynardEnergy114WeightedAverage
import GuthMaynardEnergy114DirichletKernel

open scoped BigOperators Real
open CGLProofDAG
open GuthMaynardLemma116
open GuthMaynardHeathBrownMajorant
open GuthMaynardEnergy114WeightedAverage

noncomputable section
set_option maxHeartbeats 1600000
namespace GuthMaynardEnergy116ClassMean

open GuthMaynardEnergy116GroupedMoment

private theorem sum_map_weight_le_card_mul_sum_image
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (f : α → β) (U : Finset β) (H : β → ℝ) (K : ℝ)
    (hmap : ∀ x ∈ S, f x ∈ U)
    (hcard : ∀ y ∈ U, ((S.filter fun x => f x = y).card : ℝ) ≤ K)
    (hH : ∀ y, 0 ≤ H y) :
    ∑ x ∈ S, H (f x) ≤ K * ∑ y ∈ U, H y := by
  have hfiber := Finset.sum_fiberwise_of_maps_to' hmap H
  calc
    ∑ x ∈ S, H (f x) =
        ∑ y ∈ U, ∑ x ∈ S with f x = y, H y := hfiber.symm
    _ = ∑ y ∈ U, ((S.filter fun x => f x = y).card : ℝ) * H y := by
      apply Finset.sum_congr rfl
      intro y hy
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ y ∈ U, K * H y := by
      apply Finset.sum_le_sum
      intro y hy
      exact mul_le_mul_of_nonneg_right (hcard y hy) (hH y)
    _ = K * ∑ y ∈ U, H y := by rw [Finset.mul_sum]

private theorem orderedDifferenceKernel116_sq_le_weighted
    : ∃ Cl : ℝ, 0 ≤ Cl ∧
      ∀ (M : ℕ), 1 ≤ M → ∀ (delta shift : ℝ),
        |delta - shift| ≤ 1 →
          ‖orderedDifferenceKernel116 M delta‖ ^ 2 ≤
            Cl * dirichletWeightedSquareMean M (fun _ => (1 : ℂ)) shift := by
  obtain ⟨C0, hC0, hlocal⟩ :=
    GuthMaynardEnergy114LocalL2.weightedPointMassFourierKernel_local_L2
      (ι := ℕ)
  refine ⟨C0, hC0, ?_⟩
  intro M hM delta shift hshift
  have hh := hlocal (Finset.Ioc M (2 * M))
    GuthMaynardEnergy114DirichletKernel.dirichletFrequency
    (fun _ => (1 : ℂ))
    (-(Real.log (M : ℝ) / (2 * Real.pi)) - 1) delta shift
    (GuthMaynardEnergy114DirichletKernel.dirichlet_frequency_interval hM)
    hshift
  rw [orderedDifferenceKernel116_eq_dirichletPolynomial]
  simpa only [GuthMaynardEnergy114DirichletKernel.weighted_kernel_eq_dirichlet,
      GuthMaynardEnergy114WeightedAverage.dirichletWeightedSquareMean,
      GuthMaynardEnergy114WeightedAverage.energy114Weight] using hh

theorem groupedDifferenceField116_Ioc_local_fibre_capstone :
    ∃ Cl : ℝ, 0 ≤ Cl ∧
      ∀ (M : ℕ) (W : Finset ℝ) (j : ℕ), 1 ≤ M →
        (∑ n ∈ Finset.Ioc M (2 * M),
          ∑ m ∈ Finset.Ioc M (2 * M),
            ‖groupedDifferenceField116 W j ((n : ℝ) / (m : ℝ))‖ ^ 2) ≤
          4 * Cl * ((2 ^ j : ℕ) : ℝ) ^ 2 *
            ∑ u ∈ floorDifferenceDyadicRealClass W (2 ^ j),
              ∑ v ∈ floorDifferenceDyadicRealClass W (2 ^ j),
                dirichletWeightedSquareMean M (fun _ => (1 : ℂ)) (u - v) := by
  obtain ⟨Cl, hCl, hkernel⟩ := orderedDifferenceKernel116_sq_le_weighted
  refine ⟨Cl, hCl, ?_⟩
  intro M W j hM
  let B : ℕ := 2 ^ j
  let C : Finset (ℝ × ℝ) := activePairClass116 W j
  let U : Finset ℝ := floorDifferenceDyadicRealClass W B
  let H : ℝ → ℝ :=
    dirichletWeightedSquareMean M (fun _ => (1 : ℂ))
  have hH : ∀ t, 0 ≤ H t := by
    intro t
    exact GuthMaynardEnergy114WeightedAverage.dirichletWeightedSquareMean_nonneg
      M (fun _ => (1 : ℂ)) t
  have hCmap : ∀ p ∈ C,
      ((floorDifference p : ℤ) : ℝ) ∈ U := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hmult : floorDifferenceMultiplicity W (floorDifference p) ≠ 0 := by
      unfold floorDifferenceMultiplicity
      apply Nat.ne_of_gt
      apply Finset.card_pos.mpr
      exact ⟨p, Finset.mem_filter.mpr ⟨hp'.1, rfl⟩⟩
    have hbin : floorDifference p ∈ floorDifferenceBins W := by
      exact Finset.mem_image.mpr ⟨p, hp'.1, rfl⟩
    have hclass := mem_dyadicMultiplicityClass_two_pow_log2
      (I := floorDifferenceBins W)
      (r := floorDifferenceMultiplicity W)
      (u := floorDifference p) hbin hmult
    have hlog := hp'.2
    have hclass' : floorDifference p ∈
        dyadicMultiplicityClass (floorDifferenceBins W)
          (floorDifferenceMultiplicity W) B := by
      simpa [B, hlog] using hclass
    exact Finset.mem_image.mpr ⟨floorDifference p, hclass', rfl⟩
  have hfiber : ∀ y ∈ U,
      ((C.filter fun p => ((floorDifference p : ℤ) : ℝ) = y).card : ℝ) ≤
        2 * (B : ℝ) := by
    intro y hy
    obtain ⟨u, hu, huy⟩ := Finset.mem_image.mp hy
    have hlt : floorDifferenceMultiplicity W u < 2 * B :=
      (Finset.mem_filter.mp hu).2.2
    have hsub : C.filter (fun p => ((floorDifference p : ℤ) : ℝ) = y) ⊆
        (W.product W).filter (fun p => floorDifference p = u) := by
      intro p hp
      have hpc := Finset.mem_filter.mp hp
      have hpu : floorDifference p = u := by
        exact_mod_cast (huy ▸ hpc.2)
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hpc.1).1, hpu⟩
    have hcard := Finset.card_le_card hsub
    have hlt' : ((W.product W).filter (fun p => floorDifference p = u)).card ≤
        2 * B := by
      simpa [floorDifferenceMultiplicity] using (Nat.le_of_lt hlt)
    have hnat : ((C.filter fun p => ((floorDifference p : ℤ) : ℝ) = y).card) ≤
        2 * B := hcard.trans hlt'
    exact_mod_cast hnat
  have hlocal_pair : ∀ p ∈ C, ∀ q ∈ C,
      ‖orderedDifferenceKernel116 M ((p.1 - p.2) - (q.1 - q.2))‖ ^ 2 ≤
        Cl * H (((floorDifference p : ℤ) : ℝ) -
          ((floorDifference q : ℤ) : ℝ)) := by
    intro p hp q hq
    have hp0 : 0 ≤ (p.1 - p.2) - ((floorDifference p : ℤ) : ℝ) := by
      exact sub_nonneg.mpr (Int.floor_le _)
    have hp1 : (p.1 - p.2) - ((floorDifference p : ℤ) : ℝ) < 1 := by
      have hh := Int.lt_floor_add_one (p.1 - p.2)
      change p.1 - p.2 < ((floorDifference p : ℤ) : ℝ) + 1 at hh
      linarith
    have hq0 : 0 ≤ (q.1 - q.2) - ((floorDifference q : ℤ) : ℝ) := by
      exact sub_nonneg.mpr (Int.floor_le _)
    have hq1 : (q.1 - q.2) - ((floorDifference q : ℤ) : ℝ) < 1 := by
      have hh := Int.lt_floor_add_one (q.1 - q.2)
      change q.1 - q.2 < ((floorDifference q : ℤ) : ℝ) + 1 at hh
      linarith
    have hres : |((p.1 - p.2) - (q.1 - q.2)) -
        (((floorDifference p : ℤ) : ℝ) - ((floorDifference q : ℤ) : ℝ))| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith
    exact hkernel M hM _ _ hres
  have hqbound (p : ℝ × ℝ) (hp : p ∈ C) :
      ∑ q ∈ C, H (((floorDifference p : ℤ) : ℝ) -
          ((floorDifference q : ℤ) : ℝ)) ≤
        2 * (B : ℝ) * ∑ v ∈ U,
          H (((floorDifference p : ℤ) : ℝ) - v) := by
    exact sum_map_weight_le_card_mul_sum_image C
      (fun q : ℝ × ℝ => ((floorDifference q : ℤ) : ℝ)) U
      (fun v => H (((floorDifference p : ℤ) : ℝ) - v))
      (2 * (B : ℝ)) hCmap hfiber (fun v => hH _)
  have hFnonneg : ∀ y : ℝ, 0 ≤ ∑ v ∈ U, H (y - v) := by
    intro y
    exact Finset.sum_nonneg (fun v hv => hH _)
  have hpbound :
      ∑ p ∈ C, ∑ q ∈ C,
        H (((floorDifference p : ℤ) : ℝ) -
          ((floorDifference q : ℤ) : ℝ)) ≤
        (2 * (B : ℝ)) ^ 2 *
          ∑ u ∈ U, ∑ v ∈ U, H (u - v) := by
    calc
      ∑ p ∈ C, ∑ q ∈ C,
          H (((floorDifference p : ℤ) : ℝ) -
            ((floorDifference q : ℤ) : ℝ)) ≤
          ∑ p ∈ C, (2 * (B : ℝ)) *
            ∑ v ∈ U, H (((floorDifference p : ℤ) : ℝ) - v) := by
        apply Finset.sum_le_sum
        intro p hp
        exact hqbound p hp
      _ = (2 * (B : ℝ)) *
          ∑ p ∈ C, ∑ v ∈ U,
            H (((floorDifference p : ℤ) : ℝ) - v) := by
        simp only [Finset.mul_sum]
      _ ≤ (2 * (B : ℝ)) *
          ((2 * (B : ℝ)) * ∑ u ∈ U, ∑ v ∈ U, H (u - v)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact sum_map_weight_le_card_mul_sum_image C
          (fun p : ℝ × ℝ => ((floorDifference p : ℤ) : ℝ)) U
          (fun u => ∑ v ∈ U, H (u - v))
          (2 * (B : ℝ)) hCmap hfiber hFnonneg
      _ = (2 * (B : ℝ)) ^ 2 *
          ∑ u ∈ U, ∑ v ∈ U, H (u - v) := by ring
  rw [groupedDifferenceField116_norm_square_Ioc_eq_differenceKernel M W j hM]
  calc
    ∑ p ∈ C, ∑ q ∈ C,
        ‖orderedDifferenceKernel116 M ((p.1 - p.2) - (q.1 - q.2))‖ ^ 2 ≤
        ∑ p ∈ C, ∑ q ∈ C,
          Cl * H (((floorDifference p : ℤ) : ℝ) -
            ((floorDifference q : ℤ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro q hq
      exact hlocal_pair p hp q hq
    _ = Cl * ∑ p ∈ C, ∑ q ∈ C,
          H (((floorDifference p : ℤ) : ℝ) -
            ((floorDifference q : ℤ) : ℝ)) := by
      simp only [Finset.mul_sum]
    _ ≤ Cl * ((2 * (B : ℝ)) ^ 2 *
          ∑ u ∈ U, ∑ v ∈ U, H (u - v)) :=
      mul_le_mul_of_nonneg_left hpbound hCl
    _ = 4 * Cl * ((2 ^ j : ℕ) : ℝ) ^ 2 *
          ∑ u ∈ floorDifferenceDyadicRealClass W (2 ^ j),
            ∑ v ∈ floorDifferenceDyadicRealClass W (2 ^ j),
              dirichletWeightedSquareMean M (fun _ => (1 : ℂ)) (u - v) := by
      dsimp [B, U, H]
      push_cast
      ring

end GuthMaynardEnergy116ClassMean

#print axioms GuthMaynardEnergy116ClassMean.groupedDifferenceField116_Ioc_local_fibre_capstone
