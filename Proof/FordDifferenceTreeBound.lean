import FordIteratedDifferenceScalar

noncomputable section
namespace FordDifferenceTreeBound

open FordIteratedDifferenceScalar

/-- A finite branching tree version of the scalar differencing recurrence.
The finite supremum is kept literal, and the conclusion is only the
conditional powered bound supplied by the recurrence and its leaf bound. -/
theorem tree_bound
    {r : ℕ} {a B : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hB : 0 ≤ B)
    (G : Finset ℕ) (hG : G.Nonempty) (F : List ℕ → ℝ)
    (hF0 : ∀ hs, 0 ≤ F hs)
    (hstep : ∀ hs, (∀ g ∈ hs, g ∈ G) → hs.length < r →
      F hs ^ 2 ≤ a + 4 * G.sup' hG (fun g => F (g :: hs)))
    (hleaf : ∀ hs, (∀ g ∈ hs, g ∈ G) → hs.length = r → F hs ≤ B) :
    F [] ^ (2 ^ r) ≤ 16 ^ (2 ^ r) * (a + B) := by
  have hbound : ∀ (d : ℕ) (hs : List ℕ),
      (∀ g ∈ hs, g ∈ G) → hs.length + d = r →
        F hs ^ (2 ^ d) ≤ 16 ^ (2 ^ d) * (a + B) := by
    intro d
    induction d with
    | zero =>
        intro hs hvalid hlen
        have hleaf := hleaf hs hvalid (by simpa using hlen)
        simp only [pow_zero, pow_one]
        nlinarith [hF0 hs, hB, ha0]
    | succ d ih =>
        intro hs hvalid hlen
        let M : ℝ := G.sup' hG (fun g => F (g :: hs))
        have hlenlt : hs.length < r := by omega
        have hM0 : 0 ≤ M := by
          obtain ⟨g, hg⟩ := hG
          have hle := Finset.le_sup'
            (fun g : ℕ => F (g :: hs)) hg
          dsimp [M] at hle ⊢
          exact (hF0 (g :: hs)).trans hle
        let m : ℕ := 2 ^ d
        have hm : 1 ≤ m := by
          dsimp [m]
          exact Nat.one_le_pow d 2 (by omega)
        have hMpow : M ^ m ≤ 16 ^ m * (a + B) := by
          obtain ⟨g, hg, hgeq⟩ := Finset.exists_mem_eq_sup'
            hG (fun g : ℕ => F (g :: hs))
          dsimp [M]
          rw [hgeq]
          exact ih (g :: hs) (by
            intro q hq
            simp only [List.mem_cons] at hq
            rcases hq with rfl | hq
            · exact hg
            · exact hvalid q hq) (by simp; omega)
        have hpow := pow_le_pow_left₀ (sq_nonneg (F hs))
          (hstep hs hvalid hlenlt) m
        have hscalar := FordDifferencePowerStep.power_step hm ha0 ha1 hM0
        have hc := FordDifferencePowerStep.coefficient_step hm
        have hk : (1 : ℝ) ≤ 16 ^ m := one_le_pow₀ (by norm_num)
        have hz : 0 ≤ a + B := add_nonneg ha0 hB
        have haK : a ≤ 16 ^ m * (a + B) := by
          have hh := mul_le_mul_of_nonneg_right hk hz
          nlinarith [hB]
        have hexp : 2 ^ (d + 1) = 2 * m := by
          dsimp [m]
          omega
        calc
          F hs ^ (2 ^ (d + 1)) = (F hs ^ 2) ^ m := by
            rw [hexp, pow_mul]
          _ ≤ (a + 4 * M) ^ m := hpow
          _ ≤ 5 ^ m * (a + M ^ m) := hscalar
          _ ≤ 5 ^ m * (2 * (16 ^ m * (a + B))) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            nlinarith [hMpow, haK]
          _ = (2 * 5 ^ m) * 16 ^ m * (a + B) := by ring
          _ ≤ 16 ^ m * 16 ^ m * (a + B) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hc (by positivity)) hz
          _ = 16 ^ (2 ^ (d + 1)) * (a + B) := by
            rw [← pow_add, hexp, two_mul]
  exact hbound r [] (by simp) (by simp)

end FordDifferenceTreeBound

#print axioms FordDifferenceTreeBound.tree_bound
