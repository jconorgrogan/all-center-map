import GuthMaynardGMOffBandPartition
import GuthMaynardGMSourceOffbandKusmin
import GuthMaynardMonotoneBandReindex

/-!
# Literal per-band off-resonant bound

The off-band shell is filtered directly by the literal increment margins.
Monotonicity makes the nonempty finite shell contiguous, after which the
source Kusmin bound applies to the exact shifted range.  Empty shells are
handled separately.
-/

namespace GuthMaynardGMOffBandPerBand

open scoped BigOperators
open GuthMaynardSectionFourTrace
open GuthMaynardGMPointwiseHighTPartition
open GuthMaynardGMOffBandPartition
open GuthMaynardGMSourceOffbandKusmin
open GuthMaynardGMSourceKusminActual
open GuthMaynardMonotoneBandReindex

noncomputable section

theorem norm_sum_gmOffBand_sourcePhase
    {N : ℕ} {t δ : ℝ} {ell : ℤ}
    (hN : 1 ≤ N) (ht : 0 < t) (hδ : 0 < δ) :
    ‖∑ n ∈ gmOffBand N t δ ell, sourcePhase n t‖ ≤
      3 * Real.pi / δ := by
  classical
  let f : ℕ → ℝ := fun n => gmIncrement t n
  let lo : ℝ := 2 * Real.pi * (ell : ℝ) + δ
  let hi : ℝ := 2 * Real.pi * ((ell + 1 : ℤ) : ℝ) - δ
  have hdef : monotoneBand N lo hi f = gmOffBand N t δ ell := by
    ext n
    simp [monotoneBand, gmOffBand, f, lo, hi]
  have hanti : AntitoneOn f (Set.Ioc N (2 * N)) := by
    have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
    have hshift : Antitone (fun k : ℕ => gmIncrement t (N + k)) :=
      gmIncrement_shift_antitone ht hNpos
    intro a ha b hb hab
    have haN : N ≤ a := (Set.mem_Ioc.mp ha).1.le
    have hbN : N ≤ b := (Set.mem_Ioc.mp hb).1.le
    have ha' : N + (a - N) = a := by omega
    have hb' : N + (b - N) = b := by omega
    have hab' : a - N ≤ b - N := by omega
    simpa [ha', hb'] using hshift hab'
  by_cases hs : (gmOffBand N t δ ell).Nonempty
  · have hs' : (monotoneBand N lo hi f).Nonempty := by
      rw [hdef]
      exact hs
    let s := monotoneBand N lo hi f
    let a := s.min' hs'
    let b := s.max' hs'
    have ha : a ∈ s := s.min'_mem hs'
    have hb : b ∈ s := s.max'_mem hs'
    have hab : a ≤ b := s.le_max' a ha
    have hsum := monotoneBand_sum_eq_shifted_range N lo hi f hanti hs' 
      (fun n => sourcePhase n t)
    have hbase : 0 < a := by
      have hmem := (Finset.mem_filter.mp ha).1
      have : N < a := (Finset.mem_Ioc.mp hmem).1
      omega
    have hmargin_lo : ∀ n ≤ b - a,
        δ ≤ gmIncrement t (a + n) - 2 * Real.pi * (ell : ℝ) := by
      intro n hn
      have hmemIcc : a + n ∈ Finset.Icc a b := by
        simp only [Finset.mem_Icc]
        omega
      have hmems : a + n ∈ s := by
        change a + n ∈ monotoneBand N lo hi f
        rw [monotoneBand_eq_Icc N lo hi f hanti hs']
        exact hmemIcc
      have hp := (Finset.mem_filter.mp hmems).2.1
      dsimp [f, lo] at hp ⊢
      linarith
    have hmargin_hi : ∀ n ≤ b - a,
        gmIncrement t (a + n) - 2 * Real.pi * (ell : ℝ) ≤
          2 * Real.pi - δ := by
      intro n hn
      have hmemIcc : a + n ∈ Finset.Icc a b := by
        simp only [Finset.mem_Icc]
        omega
      have hmems : a + n ∈ s := by
        change a + n ∈ monotoneBand N lo hi f
        rw [monotoneBand_eq_Icc N lo hi f hanti hs']
        exact hmemIcc
      have hp := (Finset.mem_filter.mp hmems).2.2
      dsimp [f, hi] at hp ⊢
      push_cast at hp
      linarith
    have hrange : b + 1 - a = (b - a) + 1 := by omega
    have hnorm := norm_sum_sourcePhase_shift_offband_of_pos
      a (b - a) t ell hbase ht hδ hmargin_lo hmargin_hi
    have hsum' :
        (∑ n ∈ gmOffBand N t δ ell, sourcePhase n t) =
          ∑ n ∈ Finset.range (b - a + 1), sourcePhase (a + n) t := by
      rw [← hdef]
      simpa [s, a, b, hrange] using hsum
    rw [hsum']
    exact hnorm
  · have hempty : gmOffBand N t δ ell = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hs
    rw [hempty]
    simp
    positivity

end
end GuthMaynardGMOffBandPerBand

#print axioms GuthMaynardGMOffBandPerBand.norm_sum_gmOffBand_sourcePhase
