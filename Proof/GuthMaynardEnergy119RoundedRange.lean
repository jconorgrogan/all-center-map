import CGLProofDAG

open scoped BigOperators

namespace GuthMaynardEnergy119RoundedRange

noncomputable section

/-- A rounded positive quotient block covers every positive integer in the
literal open-left interval `N < d*a ≤ 2N`.  The upper bound uses only
`N/d ≥ 1/2`, which follows from `d ≤ 2N`; it does not replace the interval by
an unproved surrogate equality. -/
theorem ceil_dyadic_range_cover
    {N d : ℕ} (hN : 1 ≤ N) (hd : 1 ≤ d) (hd2 : d ≤ 2 * N) :
    let M : ℕ := Nat.ceil ((N : ℝ) / (d : ℝ))
    1 ≤ M ∧
      (M : ℝ) ≤ 2 * (N : ℝ) / (d : ℝ) ∧
      ∀ a : ℕ, 0 < a → N < d * a → d * a ≤ 2 * N →
        a ∈ Finset.Icc M (2 * M) := by
  dsimp
  let x : ℝ := (N : ℝ) / (d : ℝ)
  let M : ℕ := Nat.ceil x
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (Nat.zero_lt_of_lt hd)
  have hx0 : 0 < x := by
    dsimp [x]
    positivity
  have hdx : (1 / 2 : ℝ) ≤ x := by
    dsimp [x]
    have hd2R : (d : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hd2
    apply (le_div_iff₀ hd0).2
    nlinarith
  have hMpos : 1 ≤ M := by
    have hceilpos : 0 < Nat.ceil x := (Nat.ceil_pos).2 hx0
    exact hceilpos
  have hMupper : (M : ℝ) ≤ 2 * (N : ℝ) / (d : ℝ) := by
    by_cases hx1 : 1 ≤ x
    · have hceillt : (M : ℝ) < x + 1 := by
        dsimp [M]
        exact Nat.ceil_lt_add_one hx0.le
      have hxx : x + 1 ≤ 2 * x := by linarith
      have hupper : (M : ℝ) ≤ 2 * x := le_of_lt (hceillt.trans_le hxx)
      calc
        (M : ℝ) ≤ 2 * x := hupper
        _ = 2 * (N : ℝ) / (d : ℝ) := by dsimp [x]; ring
    · have hx1' : x ≤ 1 := le_of_not_ge hx1
      have hMeq : M = 1 := by
        dsimp [M]
        apply (Nat.ceil_eq_iff (n := 1) (by norm_num)).2
        constructor
        · norm_num
          exact hx0
        · norm_num
          exact hx1'
      rw [hMeq]
      have hxupperR : (1 : ℝ) ≤ 2 * x := by nlinarith [hdx]
      have hxupper : ((1 : ℕ) : ℝ) ≤ 2 * x := by simpa using hxupperR
      calc
        ((1 : ℕ) : ℝ) ≤ 2 * x := hxupper
        _ = 2 * (N : ℝ) / (d : ℝ) := by dsimp [x]; ring
  refine ⟨hMpos, hMupper, ?_⟩
  intro a ha hlow hupp
  have hxa : x ≤ (a : ℝ) := by
    dsimp [x]
    apply (div_le_iff₀ hd0).2
    have hcast : (N : ℝ) < (d * a : ℕ) := by exact_mod_cast hlow
    exact le_of_lt (by simpa [Nat.cast_mul, mul_comm] using hcast)
  have hMle : M ≤ a := by
    apply (Nat.ceil_le).2
    simpa [M] using hxa
  have hax : (a : ℝ) ≤ 2 * x := by
    have hcast : (d : ℝ) * (a : ℝ) ≤ 2 * (N : ℝ) := by
      have hnat : (d * a : ℕ) ≤ (2 * N : ℕ) := hupp
      exact_mod_cast hnat
    have hdiv : (a : ℝ) ≤ 2 * (N : ℝ) / (d : ℝ) :=
      (le_div_iff₀ hd0).2 (by simpa [mul_comm] using hcast)
    calc
      (a : ℝ) ≤ 2 * (N : ℝ) / (d : ℝ) := hdiv
      _ = 2 * x := by dsimp [x]; ring

  have hAle : a ≤ 2 * M := by
    have hMx : x ≤ (M : ℝ) := by
      dsimp [M]
      exact Nat.le_ceil x
    have hreal : (a : ℝ) ≤ (2 * M : ℕ) := by
      have : (a : ℝ) ≤ 2 * (M : ℝ) := hax.trans (mul_le_mul_of_nonneg_left hMx (by norm_num))
      simpa using this
    exact_mod_cast hreal
  exact Finset.mem_Icc.mpr ⟨hMle, hAle⟩

end
end GuthMaynardEnergy119RoundedRange

#print axioms GuthMaynardEnergy119RoundedRange.ceil_dyadic_range_cover
