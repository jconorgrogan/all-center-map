import FiniteWeightedSchur
import FullStripA5Family
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Finite harmonic row grouping

A uniform multiplicity bound in every translated closed unit window implies a
logarithmic row bound for the kernel `(1 + |γ-γ'|)⁻¹`.  This is the exact
finite Schur input in equation (2.8).
-/

namespace MAPHarmonicRowGrouping

open scoped BigOperators

noncomputable section

variable {ι : Type*} [DecidableEq ι]

private def shell (gamma : ι → ℝ) (i : ι) (n : ℕ) (S : Finset ι) : Finset ι :=
  S.filter fun j => (n : ℝ) ≤ |gamma j - gamma i| ∧
    |gamma j - gamma i| < (n : ℝ) + 1

private def unitWindow (gamma : ι → ℝ) (a : ℝ) (S : Finset ι) : Finset ι :=
  S.filter fun j => a ≤ gamma j ∧ gamma j ≤ a + 1

private theorem shell_subset_two_windows
    (S : Finset ι) (gamma : ι → ℝ) (i : ι) (n : ℕ) :
    shell gamma i n S ⊆
      unitWindow gamma (gamma i + n) S ∪
        unitWindow gamma (gamma i - n - 1) S := by
  intro j hj
  rw [shell, Finset.mem_filter] at hj
  rw [Finset.mem_union, unitWindow, Finset.mem_filter,
    unitWindow, Finset.mem_filter]
  by_cases hsign : gamma i ≤ gamma j
  · left
    rw [abs_of_nonneg (sub_nonneg.mpr hsign)] at hj
    exact ⟨hj.1, by constructor <;> linarith [hj.2.1, hj.2.2]⟩
  · right
    have hsign' : gamma j - gamma i ≤ 0 := by linarith
    rw [abs_of_nonpos hsign'] at hj
    exact ⟨hj.1, by constructor <;> linarith [hj.2.1, hj.2.2]⟩

private theorem shell_mass_le_two_mul
    (S : Finset ι) (m gamma : ι → ℝ) (i : ι) (n : ℕ) (M : ℝ)
    (hm : ∀ j ∈ S, 0 ≤ m j)
    (hlocal : ∀ a : ℝ, ∑ j ∈ unitWindow gamma a S, m j ≤ M) :
    ∑ j ∈ shell gamma i n S, m j ≤ 2 * M := by
  let P := unitWindow gamma (gamma i + n) S
  let N := unitWindow gamma (gamma i - n - 1) S
  have hsub : shell gamma i n S ⊆ P ∪ N :=
    shell_subset_two_windows S gamma i n
  have hfirst : (∑ j ∈ shell gamma i n S, m j) ≤ ∑ j ∈ P ∪ N, m j :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun j hj _ => hm j ((Finset.mem_union.mp hj).elim
        (fun h => (Finset.mem_filter.mp h).1)
        (fun h => (Finset.mem_filter.mp h).1)))
  have hinter : 0 ≤ ∑ j ∈ P ∩ N, m j := by
    apply Finset.sum_nonneg
    intro j hj
    exact hm j (Finset.mem_filter.mp (Finset.mem_inter.mp hj).1).1
  have hunion : (∑ j ∈ P ∪ N, m j) ≤
      (∑ j ∈ P, m j) + ∑ j ∈ N, m j := by
    have hident := Finset.sum_union_inter (s₁ := P) (s₂ := N) (f := m)
    linarith
  calc
    (∑ j ∈ shell gamma i n S, m j) ≤ ∑ j ∈ P ∪ N, m j := hfirst
    _ ≤ (∑ j ∈ P, m j) + ∑ j ∈ N, m j := hunion
    _ ≤ M + M := add_le_add (hlocal _) (hlocal _)
    _ = 2 * M := by ring

private theorem gap_le_two_mul_height_external
    (S : Finset ι) (gamma : ι → ℝ) {T : ℝ}
    (hheight : ∀ j ∈ S, |gamma j| ≤ T)
    {i j : ι} (hicenter : |gamma i| ≤ T) (hj : j ∈ S) :
    |gamma j - gamma i| ≤ 2 * T := by
  calc
    |gamma j - gamma i| ≤ |gamma j| + |gamma i| := abs_sub _ _
    _ ≤ T + T := add_le_add (hheight j hj) hicenter
    _ = 2 * T := by ring

/-- A unit-window mass bound implies the exact finite logarithmic row bound.
The height cutoff appears only through the finite harmonic number. -/
theorem finite_reciprocal_row_le_harmonic_external
    (S : Finset ι) (m gamma : ι → ℝ) {T M : ℝ}
    (hT : 0 ≤ T) (hM : 0 ≤ M)
    (hm : ∀ j ∈ S, 0 ≤ m j)
    (hheight : ∀ j ∈ S, |gamma j| ≤ T)
    (hlocal : ∀ a : ℝ, ∑ j ∈ unitWindow gamma a S, m j ≤ M)
    (i : ι) (hicenter : |gamma i| ≤ T) :
    (∑ j ∈ S, m j / (1 + |gamma j - gamma i|)) ≤
      2 * M * (harmonic (⌊2 * T⌋₊ + 1) : ℝ) := by
  let N : ℕ := ⌊2 * T⌋₊
  have hpoint :
      (∑ j ∈ S, m j / (1 + |gamma j - gamma i|)) ≤
        ∑ n ∈ Finset.range (N + 1),
          ∑ j ∈ shell gamma i n S, m j / (1 + (n : ℝ)) := by
    rw [show (∑ n ∈ Finset.range (N + 1),
          ∑ j ∈ shell gamma i n S, m j / (1 + (n : ℝ))) =
        ∑ j ∈ S, ∑ n ∈ Finset.range (N + 1),
          if (n : ℝ) ≤ |gamma j - gamma i| ∧
              |gamma j - gamma i| < (n : ℝ) + 1
          then m j / (1 + (n : ℝ)) else 0 by
      simp_rw [shell, Finset.sum_filter]
      rw [Finset.sum_comm]]
    apply Finset.sum_le_sum
    intro j hj
    let d : ℝ := |gamma j - gamma i|
    let n : ℕ := ⌊d⌋₊
    have hd0 : 0 ≤ d := abs_nonneg _
    have hdT : d ≤ 2 * T :=
      gap_le_two_mul_height_external S gamma hheight hicenter hj
    have hnN : n ≤ N := by
      exact Nat.floor_le_floor hdT
    have hnmem : n ∈ Finset.range (N + 1) := by
      rw [Finset.mem_range]
      omega
    have hnle : (n : ℝ) ≤ d := Nat.floor_le hd0
    have hdlt : d < (n : ℝ) + 1 := Nat.lt_floor_add_one d
    have htermNonneg : ∀ k ∈ Finset.range (N + 1),
        0 ≤ if (k : ℝ) ≤ |gamma j - gamma i| ∧
              |gamma j - gamma i| < (k : ℝ) + 1
          then m j / (1 + (k : ℝ)) else 0 := by
      intro k hk
      split_ifs
      · exact div_nonneg (hm j hj) (by positivity)
      · rfl
    have hsingle := Finset.single_le_sum htermNonneg hnmem
    have hden : 1 + (n : ℝ) ≤ 1 + d := by linarith
    have hfrac : m j / (1 + d) ≤ m j / (1 + (n : ℝ)) := by
      exact div_le_div_of_nonneg_left (hm j hj) (by positivity) hden
    calc
      m j / (1 + |gamma j - gamma i|) = m j / (1 + d) := rfl
      _ ≤ m j / (1 + (n : ℝ)) := hfrac
      _ = if (n : ℝ) ≤ |gamma j - gamma i| ∧
              |gamma j - gamma i| < (n : ℝ) + 1
          then m j / (1 + (n : ℝ)) else 0 := by
        simp [d, hnle, hdlt]
      _ ≤ ∑ k ∈ Finset.range (N + 1),
          if (k : ℝ) ≤ |gamma j - gamma i| ∧
              |gamma j - gamma i| < (k : ℝ) + 1
          then m j / (1 + (k : ℝ)) else 0 := hsingle
  calc
    (∑ j ∈ S, m j / (1 + |gamma j - gamma i|)) ≤
        ∑ n ∈ Finset.range (N + 1),
          ∑ j ∈ shell gamma i n S, m j / (1 + (n : ℝ)) := hpoint
    _ = ∑ n ∈ Finset.range (N + 1),
        (∑ j ∈ shell gamma i n S, m j) / (1 + (n : ℝ)) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.sum_div]
    _ ≤ ∑ n ∈ Finset.range (N + 1), (2 * M) / (1 + (n : ℝ)) := by
      apply Finset.sum_le_sum
      intro n hn
      exact div_le_div_of_nonneg_right
        (shell_mass_le_two_mul S m gamma i n M hm hlocal) (by positivity)
    _ = 2 * M * (harmonic (N + 1) : ℝ) := by
      calc
        (∑ n ∈ Finset.range (N + 1), 2 * M / (1 + (n : ℝ))) =
            ∑ n ∈ Finset.range (N + 1),
              2 * M * ((n + 1 : ℕ) : ℝ)⁻¹ := by
          apply Finset.sum_congr rfl
          intro n hn
          push_cast
          rw [div_eq_mul_inv]
          congr 1
          ring
        _ = 2 * M * ∑ n ∈ Finset.range (N + 1),
              ((n + 1 : ℕ) : ℝ)⁻¹ := by rw [Finset.mul_sum]
        _ = 2 * M * (harmonic (N + 1) : ℝ) := by
          congr 1
          simp [harmonic]
    _ = 2 * M * (harmonic (⌊2 * T⌋₊ + 1) : ℝ) := rfl

/-- The original row-centered version is the special case where the center
belongs to the finite set. -/
theorem finite_reciprocal_row_le_harmonic
    (S : Finset ι) (m gamma : ι → ℝ) {T M : ℝ}
    (hT : 0 ≤ T) (hM : 0 ≤ M)
    (hm : ∀ j ∈ S, 0 ≤ m j)
    (hheight : ∀ j ∈ S, |gamma j| ≤ T)
    (hlocal : ∀ a : ℝ, ∑ j ∈ unitWindow gamma a S, m j ≤ M)
    (i : ι) (hi : i ∈ S) :
    (∑ j ∈ S, m j / (1 + |gamma j - gamma i|)) ≤
      2 * M * (harmonic (⌊2 * T⌋₊ + 1) : ℝ) :=
  finite_reciprocal_row_le_harmonic_external S m gamma hT hM hm
    hheight hlocal i (hheight i hi)

/-- A closed interval of length one contains at most two points of a
one-separated real set.  The possible pair is exactly the two endpoints. -/
private theorem unitWindow_card_le_two_of_oneSeparated
    (S : Finset ι) (gamma : ι → ℝ)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      1 ≤ |gamma i - gamma j|)
    (a : ℝ) :
    (unitWindow gamma a S).card ≤ 2 := by
  classical
  let f : ι → Bool := fun i => decide (gamma i = a + 1)
  calc
    (unitWindow gamma a S).card ≤
        (Finset.univ : Finset Bool).card := by
      apply Finset.card_le_card_of_injOn f
      · intro i hi
        simp
      · intro x hx y hy hxy
        have hxmem : x ∈ unitWindow gamma a S := hx
        have hymem : y ∈ unitWindow gamma a S := hy
        have hxdata := Finset.mem_filter.mp hxmem
        have hydata := Finset.mem_filter.mp hymem
        by_cases hxe : gamma x = a + 1
        · have hye : gamma y = a + 1 := by
            simpa [f, hxe] using hxy
          by_contra hne
          have hgap := hsep x hxdata.1 y hydata.1 hne
          rw [hxe, hye, sub_self, abs_zero] at hgap
          linarith
        · have hye : gamma y ≠ a + 1 := by
            intro hye
            simpa [f, hxe, hye] using hxy
          by_contra hne
          have hgap := hsep x hxdata.1 y hydata.1 hne
          have hxlt : gamma x < a + 1 :=
            lt_of_le_of_ne hxdata.2.2 hxe
          have hylt : gamma y < a + 1 :=
            lt_of_le_of_ne hydata.2.2 hye
          have habs : |gamma x - gamma y| < 1 := by
            rw [abs_lt]
            constructor <;> linarith [hxdata.2.1, hydata.2.1]
          linarith
    _ = 2 := by decide

/-- Same-character one-spacing gives the logarithmic Perron-kernel packing
bound at an arbitrary ordinate `u` in the doubled height interval.  This is
the finite shell estimate used in the Holder step after BHP (3.36). -/
theorem oneSeparated_perronKernel_sum_le_harmonic
    (W : Finset ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hsep : ∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t - u|)
    (hheight : ∀ t ∈ W, |t| ≤ T)
    {u : ℝ} (hu : |u| ≤ 2 * T) :
    (∑ t ∈ W, 1 / (1 + |t - u|)) ≤
      4 * (harmonic (⌊4 * T⌋₊ + 1) : ℝ) := by
  have hrow := finite_reciprocal_row_le_harmonic_external
    (S := W) (m := fun _ : ℝ => (1 : ℝ)) (gamma := id)
    (T := 2 * T) (M := 2) (by linarith) (by norm_num)
    (by intro j hj; norm_num)
    (by
      intro j hj
      dsimp only [id]
      linarith [hheight j hj])
    (by
      intro a
      have hcard := unitWindow_card_le_two_of_oneSeparated W id
        (by simpa using hsep) a
      simpa using hcard)
    u (by simpa using hu)
  simp only [id_eq] at hrow
  rw [show 2 * (2 * T) = 4 * T by ring] at hrow
  convert hrow using 1 <;> ring

#print axioms finite_reciprocal_row_le_harmonic
#print axioms finite_reciprocal_row_le_harmonic_external
#print axioms oneSeparated_perronKernel_sum_le_harmonic

end
end MAPHarmonicRowGrouping
