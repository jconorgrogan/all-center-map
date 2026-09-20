import Mathlib
import GuthMaynardEnergy114KernelEnvelope

open scoped BigOperators
noncomputable section
namespace GuthMaynardEnergy118Moments
open GuthMaynardEnergy114KernelEnvelope
open GuthMaynardJIteration
open scoped FourierTransform SchwartzMap

/-- Finite shell summation: once every floor shell has multiplicity at most
`2E`, any nonnegative shell weight whose finite subsums are bounded by `K`
has total mass at most `2 E K`.  This isolates the analytic summation from the
additive-energy shell count. -/
theorem finite_shell_weight_le
    {α : Type*} (Q : Finset α) (κ : α → ℤ) (w : ℤ → ℝ)
    {E K : ℝ} (hE : 0 ≤ E) (hK : 0 ≤ K)
    (hfiber : ∀ m : ℤ,
      ((Q.filter (fun q => κ q = m)).card : ℝ) ≤ 2 * E)
    (hw : ∀ m : ℤ, 0 ≤ w m)
    (hseries : ∀ S : Finset ℤ, (∑ m ∈ S, w m) ≤ K) :
    (∑ q ∈ Q, w (κ q)) ≤ 2 * E * K := by
  classical
  let S : Finset ℤ := Q.image κ
  have hmaps : ∀ q ∈ Q, κ q ∈ S := by
    intro q hq
    exact Finset.mem_image.mpr ⟨q, hq, rfl⟩
  have hfiberSum := Finset.sum_fiberwise_of_maps_to hmaps
    (fun q => w (κ q))
  have hfiber_eq :
      (∑ q ∈ Q, w (κ q)) =
        ∑ m ∈ S, ∑ q ∈ Q.filter (fun q => κ q = m), w (κ q) := by
    simpa [S] using hfiberSum.symm
  rw [hfiber_eq]
  have hsum :
      (∑ m ∈ S, ∑ q ∈ Q.filter (fun q => κ q = m), w (κ q)) ≤
        ∑ m ∈ S, (2 * E) * w m := by
    apply Finset.sum_le_sum
    intro m hm
    have hconst :
      (∑ q ∈ Q.filter (fun q => κ q = m), w (κ q)) =
          ((Q.filter (fun q => κ q = m)).card : ℝ) * w m := by
      have hq : ∀ q ∈ Q.filter (fun q => κ q = m), w (κ q) = w m := by
        intro q hq
        rw [Finset.mem_filter.mp hq |>.2]
      rw [Finset.sum_congr rfl hq]
      simp [nsmul_eq_mul]
    rw [hconst]
    exact mul_le_mul_of_nonneg_right (hfiber m) (hw m)
  calc
    (∑ m ∈ S, ∑ q ∈ Q.filter (fun q => κ q = m), w (κ q)) ≤
        ∑ m ∈ S, (2 * E) * w m := hsum
    _ = (2 * E) * ∑ m ∈ S, w m := by
      rw [Finset.mul_sum]
    _ ≤ (2 * E) * K := by
      exact mul_le_mul_of_nonneg_left (hseries S) (by positivity)
    _ = 2 * E * K := by ring

/-- The inverse-square shell weight has a finite-subsum bound.  The proof uses
the integer inverse-square summability theorem and a single zero shell. -/
theorem finite_inverse_square_shell_weight_bound :
    ∃ K : ℝ, 0 < K ∧
      ∀ S : Finset ℤ,
        (∑ m ∈ S, 1 / (1 + ((m : ℝ) / (2 * Real.pi)) ^ 2)) ≤ K := by
  let w : ℤ → ℝ := fun m => 1 / (1 + ((m : ℝ) / (2 * Real.pi)) ^ 2)
  let g : ℤ → ℝ := fun m =>
    (2 * Real.pi) ^ 2 * (1 / (m : ℝ) ^ 2)
  let e : ℤ → ℝ := fun m => if m = 0 then 1 else 0
  have hg0 : Summable (fun m : ℤ => 1 / (m : ℝ) ^ 2) := by
    exact (Real.summable_one_div_int_pow (p := 2)).mpr (by norm_num)
  have hg : Summable g := by
    exact hg0.mul_left ((2 * Real.pi) ^ 2)
  have he : Summable e := by
    apply summable_of_hasFiniteSupport
    rw [Function.HasFiniteSupport]
    exact (Set.finite_singleton (0 : ℤ)).subset (by
      intro m hm
      change e m ≠ 0 at hm
      change m = 0
      by_contra hne
      apply hm
      simp [e, hne])
  have hge : Summable (fun m : ℤ => g m + e m) := hg.add he
  let K : ℝ := 1 + (∑' m : ℤ, (g m + e m))
  have hKpos : 0 < K := by
    have hnonneg : ∀ m : ℤ, 0 ≤ g m + e m := by
      intro m; positivity
    have htsum : 0 ≤ ∑' m : ℤ, (g m + e m) := tsum_nonneg hnonneg
    dsimp [K]
    linarith
  refine ⟨K, hKpos, ?_⟩
  intro S
  have hle : ∀ m : ℤ, w m ≤ g m + e m := by
    intro m
    by_cases hm : m = 0
    · subst hm
      simp [w, g, e]
    · have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm
      have hm2 : 0 < (m : ℝ) ^ 2 := sq_pos_of_ne_zero hm0
      have hp : 0 < 2 * Real.pi := by positivity
      have hden : 0 < 1 + ((m : ℝ) / (2 * Real.pi)) ^ 2 := by positivity
      have hmain : w m ≤ g m := by
        dsimp [w, g]
        have hform : (2 * Real.pi) ^ 2 * (1 / (m : ℝ) ^ 2) =
            (2 * Real.pi) ^ 2 / (m : ℝ) ^ 2 := by ring
        rw [hform]
        apply (div_le_div_iff₀ hden hm2).2
        field_simp [hm0, ne_of_gt hp]
        nlinarith [sq_nonneg (m : ℝ)]
      simpa [e, hm] using hmain
  have hsum : (∑ m ∈ S, w m) ≤ ∑ m ∈ S, (g m + e m) := by
    apply Finset.sum_le_sum
    intro m hm
    exact hle m
  have hts := hge.sum_le_tsum S (fun m hm => by positivity)
  calc
    (∑ m ∈ S, w m) ≤ ∑ m ∈ S, (g m + e m) := hsum
    _ ≤ ∑' m : ℤ, (g m + e m) := hts
    _ ≤ K := by dsimp [K]; linarith

/-- The central bump Fourier envelope is bounded by the inverse-square weight
of the integer floor shell. -/
theorem exists_sourceBump_fourier_shell_weight :
    ∃ Cphi : ℝ, 0 < Cphi ∧
      ∀ (x : ℝ) (m : ℤ),
        (m : ℝ) ≤ x → x < (m : ℝ) + 1 →
        ‖( 𝓕 (sourceBumpSchwartz 1 zero_lt_one))
            (-x / (2 * Real.pi))‖ ≤
          Cphi / (1 + ((m : ℝ) / (2 * Real.pi)) ^ 2) := by
  obtain ⟨Cphi, hCphi_pos, hCphi⟩ :=
    sourceBump_fourier_local_quadratic_envelope
  refine ⟨Cphi, hCphi_pos, ?_⟩
  intro x m hmx0 hmx1
  have hpi : 0 < 2 * Real.pi := by positivity
  have hpi_one : 1 ≤ 2 * Real.pi := by
    have hpi3 := Real.pi_gt_three
    nlinarith
  have hshift : |(x - (m : ℝ)) / (2 * Real.pi)| ≤ 1 := by
    have hnonneg : 0 ≤ x - (m : ℝ) := by linarith
    rw [abs_of_nonneg (div_nonneg hnonneg hpi.le)]
    apply (div_le_iff₀ hpi).2
    nlinarith
  have hh := hCphi (-x / (2 * Real.pi))
    ((x - (m : ℝ)) / (2 * Real.pi)) hshift
  convert hh using 1 <;> ring

end GuthMaynardEnergy118Moments

#print axioms GuthMaynardEnergy118Moments.finite_shell_weight_le
#print axioms GuthMaynardEnergy118Moments.finite_inverse_square_shell_weight_bound
#print axioms GuthMaynardEnergy118Moments.exists_sourceBump_fourier_shell_weight
