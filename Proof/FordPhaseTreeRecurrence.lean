import FordPhaseCorrelation
import FordDiscreteGoodShiftBound
import FordDifferenceTreeBound

open scoped BigOperators
noncomputable section
namespace FordPhaseTreeRecurrence
open FordPhaseDifferencing FordDiscreteCorrelationDiagonal FordDiscretePairCount

/-- The exact remaining interval after all shifts, with natural truncation. -/
def phaseSum (H : ℕ) (f : ℝ → ℝ) (x : ℝ) (hs : List ℕ) : ℂ :=
  ∑ n ∈ Finset.range (H - hs.sum),
    phaseDiff (hs.map (fun h : ℕ => (h : ℝ))) f (x + (n : ℝ))

def phaseSize (N H : ℕ) (f : ℝ → ℝ) (x : ℝ) (hs : List ℕ) : ℝ :=
  ‖phaseSum H f x hs‖ / N

theorem phaseSize_nonneg (N H : ℕ) (f : ℝ → ℝ) (x : ℝ) (hs : List ℕ) :
    0 ≤ phaseSize N H f x hs := by unfold phaseSize; positivity

theorem correlation_eq_child (H h : ℕ) (f : ℝ → ℝ) (x : ℝ) (hs : List ℕ) :
    correlation (H - hs.sum) h
      (fun n => phaseDiff (hs.map (fun k : ℕ => (k : ℝ))) f (x + (n : ℝ))) =
      phaseSum H f x (h :: hs) := by
  rw [FordPhaseCorrelation.correlation_phaseDiff_eq]
  simp only [phaseSum, List.sum_cons, List.map_cons, Nat.sub_sub]
  rw [Nat.add_comm h hs.sum]

/-- Actual finite differencing supplies the tree recurrence, retaining its bad-shift count. -/
theorem phaseSize_sq_le {N H Q : ℕ} (hH : H ≤ N) (hQ : 1 ≤ Q) (hQN : Q ≤ N)
    (f : ℝ → ℝ) (x : ℝ) (hs : List ℕ)
    (G : Finset ℕ) (hG : G ⊆ positiveRange Q) {T : ℝ} (hT : 0 ≤ T)
    (hchild : ∀ h ∈ G, phaseSize N H f x (h :: hs) ≤ T) :
    phaseSize N H f x hs ^ 2 ≤
      2 / (Q : ℝ) + 4 * ((positiveRange Q \ G).card : ℝ) / Q + 4 * T := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hc : ∀ h ∈ G, ‖correlation (H - hs.sum) h
      (fun n => phaseDiff (hs.map (fun k : ℕ => (k : ℝ))) f (x + (n : ℝ)))‖ ≤
        (N : ℝ) * T := by
    intro h hh
    rw [correlation_eq_child]
    have ht := (div_le_iff₀ hn).mp (hchild h hh)
    simpa [mul_comm] using ht
  have hv := FordDiscreteGoodShiftBound.normalized_norm_sum_sq_le_good_bad
    ((Nat.sub_le H hs.sum).trans hH) hQ hQN
    (fun n => phaseDiff (hs.map (fun k : ℕ => (k : ℝ))) f (x + (n : ℝ)))
    (fun n _ => (phaseDiff_norm _ _ _).le) G hG ((N : ℝ) * T)
    (mul_nonneg hn.le hT) hc
  have he : 4 * ((N : ℝ) * T) / N = 4 * T := by field_simp
  rw [he] at hv
  simpa only [phaseSize, phaseSum, div_pow] using hv

/-- Iteration for actual phase sums. Only terminal good-shift sums remain as input. -/
theorem phaseSize_iterated_le {N H Q r : ℕ} (hH : H ≤ N) (hQ : 1 ≤ Q) (hQN : Q ≤ N)
    (f : ℝ → ℝ) (x : ℝ) (G : Finset ℕ) (hGsub : G ⊆ positiveRange Q)
    (hG : G.Nonempty) {a B : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hB : 0 ≤ B)
    (herror : 2 / (Q : ℝ) + 4 * ((positiveRange Q \ G).card : ℝ) / Q ≤ a)
    (hleaf : ∀ hs : List ℕ, (∀ g ∈ hs, g ∈ G) → hs.length = r →
      phaseSize N H f x hs ≤ B) :
    phaseSize N H f x [] ^ (2 ^ r) ≤ 16 ^ (2 ^ r) * (a + B) := by
  apply FordDifferenceTreeBound.tree_bound ha0 ha1 hB G hG (phaseSize N H f x)
    (phaseSize_nonneg N H f x)
  · intro hs _ _
    have ht : 0 ≤ G.sup' hG (fun g => phaseSize N H f x (g :: hs)) := by
      obtain ⟨g, hg⟩ := hG
      exact (phaseSize_nonneg N H f x (g :: hs)).trans
        (Finset.le_sup' (fun g => phaseSize N H f x (g :: hs)) hg)
    have hv := phaseSize_sq_le hH hQ hQN f x hs G hGsub ht
      (fun g hg => Finset.le_sup' (fun g => phaseSize N H f x (g :: hs)) hg)
    linarith
  · exact hleaf

end FordPhaseTreeRecurrence
#print axioms FordPhaseTreeRecurrence.correlation_eq_child
#print axioms FordPhaseTreeRecurrence.phaseSize_sq_le
#print axioms FordPhaseTreeRecurrence.phaseSize_iterated_le
