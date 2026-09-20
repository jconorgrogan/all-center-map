import MRTCorollary25Abel

/-!
# Real-endpoint clipping for MRT Corollary 2.5
-/

namespace MAPMRTCorollary25EndpointClip

open scoped BigOperators
open MAPMRTCorollary25 MAPMRTCorollary25PerronCore
open MixedMeanFrontend

noncomputable section

/-- A natural interval sum is exactly the difference of two raw prefixes. -/
theorem sum_Icc_eq_rawPrefix_sub
    (M : ℕ) (f : ℕ → ℂ) (t : ℝ) {A B : ℕ}
    (hA : 1 ≤ A) (hAB : A ≤ B) (hBM : B ≤ M) :
    (∑ n ∈ Finset.Icc A B, f n * mellinPhase n t) =
      rawPrefixOn (Finset.Icc 1 M) B f t -
        rawPrefixOn (Finset.Icc 1 M) (A - 1) f t := by
  have hAM : A - 1 ≤ M := (Nat.sub_le A 1).trans (hAB.trans hBM)
  have hleft :
      (Finset.Icc 1 M).filter (fun n => n ≤ B) = Finset.Icc 1 B := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  have hright :
      (Finset.Icc 1 M).filter (fun n => n ≤ A - 1) =
        Finset.Icc 1 (A - 1) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  have hunion :
      Finset.Icc 1 (A - 1) ∪ Finset.Icc A B = Finset.Icc 1 B := by
    ext n
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  have hdisj : Disjoint (Finset.Icc 1 (A - 1)) (Finset.Icc A B) := by
    rw [Finset.disjoint_left]
    intro n hn1 hn2
    simp only [Finset.mem_Icc] at hn1 hn2
    omega
  have hsumUnion := Finset.sum_union hdisj
    (f := fun n => f n * mellinPhase n t)
  rw [hunion] at hsumUnion
  unfold rawPrefixOn
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  rw [hleft, hright]
  rw [hsumUnion]
  ring

/-- The active set cut out by two real inequalities inside a natural prefix
is either empty or a complete natural interval. -/
theorem intervalCutoff_prefix_norm_le_two
    (M N : ℕ) (hNM : N ≤ M) (f : ℕ → ℂ) (t X1 X2 P : ℝ)
    (hP : 0 ≤ P)
    (hraw : ∀ K : ℕ, K ≤ M →
      ‖rawPrefixOn (Finset.Icc 1 M) K f t‖ ≤ P) :
    ‖∑ n ∈ Finset.Icc 1 M,
        if n ≤ N then intervalCutoff X1 X2 f n * mellinPhase n t else 0‖ ≤
      2 * P := by
  let Q : Finset ℕ := (Finset.Icc 1 M).filter (fun n =>
    n ≤ N ∧ X1 ≤ (n : ℝ) ∧ (n : ℝ) ≤ X2)
  by_cases hQ : Q.Nonempty
  · let A := Q.min' hQ
    let B := Q.max' hQ
    have hAmem : A ∈ Q := Q.min'_mem hQ
    have hBmem : B ∈ Q := Q.max'_mem hQ
    have hAle : ∀ n ∈ Q, A ≤ n := fun n hn => Q.min'_le n hn
    have hleB : ∀ n ∈ Q, n ≤ B := fun n hn => Q.le_max' n hn
    have hAdata : A ∈ Finset.Icc 1 M ∧
        A ≤ N ∧ X1 ≤ (A : ℝ) ∧ (A : ℝ) ≤ X2 := by
      simpa only [Q, Finset.mem_filter] using hAmem
    have hBdata : B ∈ Finset.Icc 1 M ∧
        B ≤ N ∧ X1 ≤ (B : ℝ) ∧ (B : ℝ) ≤ X2 := by
      simpa only [Q, Finset.mem_filter] using hBmem
    have hAB : A ≤ B := hAle B hBmem
    have hAI := Finset.mem_Icc.mp hAdata.1
    have hBI := Finset.mem_Icc.mp hBdata.1
    have hQeq : Q = Finset.Icc A B := by
      ext n
      constructor
      · intro hn
        exact Finset.mem_Icc.mpr ⟨hAle n hn, hleB n hn⟩
      · intro hn
        have hnAB := Finset.mem_Icc.mp hn
        have hnReal : (A : ℝ) ≤ n ∧ (n : ℝ) ≤ B := by exact_mod_cast hnAB
        apply Finset.mem_filter.mpr
        constructor
        · exact Finset.mem_Icc.mpr ⟨hAI.1.trans hnAB.1,
            hnAB.2.trans hBI.2⟩
        · exact ⟨hnAB.2.trans hBdata.2.1,
            hAdata.2.2.1.trans hnReal.1,
            hnReal.2.trans hBdata.2.2.2⟩
    have hsum :
        (∑ n ∈ Finset.Icc 1 M,
          if n ≤ N then intervalCutoff X1 X2 f n * mellinPhase n t else 0) =
          ∑ n ∈ Q, f n * mellinPhase n t := by
      unfold Q
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n hn
      unfold intervalCutoff
      by_cases h1 : n ≤ N <;>
        by_cases h2 : X1 ≤ (n : ℝ) ∧ (n : ℝ) ≤ X2 <;>
        simp [h1, h2]
    rw [hsum, hQeq]
    rw [sum_Icc_eq_rawPrefix_sub M f t hAI.1 hAB hBI.2]
    calc
      ‖rawPrefixOn (Finset.Icc 1 M) B f t -
          rawPrefixOn (Finset.Icc 1 M) (A - 1) f t‖ ≤
        ‖rawPrefixOn (Finset.Icc 1 M) B f t‖ +
          ‖rawPrefixOn (Finset.Icc 1 M) (A - 1) f t‖ := norm_sub_le _ _
      _ ≤ P + P := add_le_add (hraw B hBI.2)
        (hraw (A - 1) ((Nat.sub_le A 1).trans hAI.2))
      _ = 2 * P := by ring
  · have hQempty : Q = ∅ := Finset.not_nonempty_iff_eq_empty.mp hQ
    have hsum :
        (∑ n ∈ Finset.Icc 1 M,
          if n ≤ N then intervalCutoff X1 X2 f n * mellinPhase n t else 0) = 0 := by
      have heq :
          (∑ n ∈ Finset.Icc 1 M,
            if n ≤ N then intervalCutoff X1 X2 f n * mellinPhase n t else 0) =
            ∑ n ∈ Q, f n * mellinPhase n t := by
        unfold Q
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro n hn
        unfold intervalCutoff
        by_cases h1 : n ≤ N <;>
          by_cases h2 : X1 ≤ (n : ℝ) ∧ (n : ℝ) ≤ X2 <;>
          simp [h1, h2]
      rw [heq, hQempty, Finset.sum_empty]
    rw [hsum, norm_zero]
    linarith

end
end MAPMRTCorollary25EndpointClip

#print axioms MAPMRTCorollary25EndpointClip.sum_Icc_eq_rawPrefix_sub
#print axioms MAPMRTCorollary25EndpointClip.intervalCutoff_prefix_norm_le_two
