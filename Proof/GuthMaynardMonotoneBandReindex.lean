import GuthMaynardGMPointwiseKernel

/-!
# Finite monotone band and shifted-range reindexing

The filtered natural interval cut out by an antitone function is contiguous.
This is the exact finite bridge used when a literal GM off-band sum is grouped
by a monotone phase variable; no contiguity is assumed as an extra premise.
-/

namespace GuthMaynardMonotoneBandReindex

open scoped BigOperators

noncomputable section

def monotoneBand (N : ℕ) (lo hi : ℝ) (f : ℕ → ℝ) : Finset ℕ :=
  (Finset.Ioc N (2 * N)).filter (fun n => lo < f n ∧ f n < hi)

theorem monotoneBand_eq_Icc
    (N : ℕ) (lo hi : ℝ) (f : ℕ → ℝ)
    (hanti : AntitoneOn f (Set.Ioc N (2 * N)))
    (hs : (monotoneBand N lo hi f).Nonempty) :
    monotoneBand N lo hi f =
      Finset.Icc ((monotoneBand N lo hi f).min' hs)
        ((monotoneBand N lo hi f).max' hs) := by
  let s := monotoneBand N lo hi f
  let a := s.min' hs
  let b := s.max' hs
  have ha : a ∈ s := s.min'_mem hs
  have hb : b ∈ s := s.max'_mem hs
  have hab : a ≤ b := s.le_max' a ha
  have hbase_a : a ∈ Finset.Ioc N (2 * N) := by
    exact (Finset.mem_filter.mp ha).1
  have hbase_b : b ∈ Finset.Ioc N (2 * N) := by
    exact (Finset.mem_filter.mp hb).1
  have hset_a : a ∈ Set.Ioc N (2 * N) := by
    simpa only [Set.mem_Ioc, Finset.mem_Ioc] using hbase_a
  have hset_b : b ∈ Set.Ioc N (2 * N) := by
    simpa only [Set.mem_Ioc, Finset.mem_Ioc] using hbase_b
  have hband_a : lo < f a ∧ f a < hi :=
    (Finset.mem_filter.mp ha).2
  have hband_b : lo < f b ∧ f b < hi :=
    (Finset.mem_filter.mp hb).2
  have hsub : s ⊆ Finset.Icc a b := by
    intro n hn
    exact Finset.mem_Icc.mpr ⟨s.min'_le n hn, s.le_max' n hn⟩
  have hsup : Finset.Icc a b ⊆ s := by
    intro n hn
    have hnbase : n ∈ Finset.Ioc N (2 * N) := by
      have hNa : N < a := (Finset.mem_Ioc.mp hbase_a).1
      have hb2 : b ≤ 2 * N := (Finset.mem_Ioc.mp hbase_b).2
      exact Finset.mem_Ioc.mpr ⟨lt_of_lt_of_le hNa (Finset.mem_Icc.mp hn).1,
        le_trans (Finset.mem_Icc.mp hn).2 hb2⟩
    have hset_n : n ∈ Set.Ioc N (2 * N) := by
      simpa only [Set.mem_Ioc, Finset.mem_Ioc] using hnbase
    have hna : a ≤ n := (Finset.mem_Icc.mp hn).1
    have hnb : n ≤ b := (Finset.mem_Icc.mp hn).2
    have hfa : f n ≤ f a := hanti hset_a hset_n hna
    have hfb : f b ≤ f n := hanti hset_n hset_b hnb
    apply Finset.mem_filter.mpr
    constructor
    · exact hnbase
    · constructor <;> linarith
  exact Finset.Subset.antisymm hsub hsup

theorem sum_Icc_eq_shifted_range
    (a b : ℕ) (hab : a ≤ b) (z : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc a b, z n) =
      ∑ k ∈ Finset.range (b + 1 - a), z (a + k) := by
  symm
  apply Finset.sum_bij (fun k _ => a + k)
  · intro k hk
    simp only [Finset.mem_range] at hk
    simp only [Finset.mem_Icc]
    omega
  · intro k hk l hl hkl
    omega
  · intro n hn
    simp only [Finset.mem_Icc] at hn
    refine ⟨n - a, ?_, ?_⟩
    · simp only [Finset.mem_range]
      omega
    · omega
  · intro k hk
    rfl

theorem monotoneBand_sum_eq_shifted_range
    (N : ℕ) (lo hi : ℝ) (f : ℕ → ℝ)
    (hanti : AntitoneOn f (Set.Ioc N (2 * N)))
    (hs : (monotoneBand N lo hi f).Nonempty) (z : ℕ → ℂ) :
    (∑ n ∈ monotoneBand N lo hi f, z n) =
      ∑ k ∈ Finset.range
          ((monotoneBand N lo hi f).max' hs + 1 -
            (monotoneBand N lo hi f).min' hs),
        z ((monotoneBand N lo hi f).min' hs + k) := by
  let s := monotoneBand N lo hi f
  let a := s.min' hs
  let b := s.max' hs
  have hab : a ≤ b := s.le_max' a (s.min'_mem hs)
  calc
    (∑ n ∈ monotoneBand N lo hi f, z n) =
        ∑ n ∈ Finset.Icc a b, z n := by
          rw [monotoneBand_eq_Icc N lo hi f hanti hs]
    _ = ∑ k ∈ Finset.range (b + 1 - a), z (a + k) :=
      sum_Icc_eq_shifted_range a b hab z
    _ = ∑ k ∈ Finset.range
          ((monotoneBand N lo hi f).max' hs + 1 -
            (monotoneBand N lo hi f).min' hs),
        z ((monotoneBand N lo hi f).min' hs + k) := by rfl

end
end GuthMaynardMonotoneBandReindex

#print axioms GuthMaynardMonotoneBandReindex.monotoneBand_eq_Icc
#print axioms GuthMaynardMonotoneBandReindex.sum_Icc_eq_shifted_range
#print axioms GuthMaynardMonotoneBandReindex.monotoneBand_sum_eq_shifted_range
