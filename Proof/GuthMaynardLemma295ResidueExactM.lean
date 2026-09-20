import GuthMaynardLemma295FiniteContour

/-!
# Pole-residue decay at the corrected Lemma 29.5 scale

The chapter hypothesis bounds `N` polynomially in `T`.  At the exact range
used by (29.40), `N <= T^(1+epsilon)`, arbitrary Mellin decay at
`|g| >= T^delta` makes the displaced zeta-pole residue `O_A(T^-A)`.
-/

namespace GuthMaynardLemma295ResidueExactM

open scoped FourierTransform SchwartzMap
open GuthMaynardJutilaReflection2941
open GuthMaynardLemma295CutoffAnalytic
open GuthMaynardLemma295FiniteContour

noncomputable section

def residueDecayOrder (delta epsilon A : ℝ) : ℕ :=
  Nat.ceil ((A + 1 + epsilon) / delta)

theorem residueDecayOrder_exponent_le
    {delta epsilon A : ℝ} (hdelta : 0 < delta) :
    1 + epsilon - delta * (residueDecayOrder delta epsilon A : ℝ) ≤ -A := by
  have hceil : (A + 1 + epsilon) / delta ≤
      (residueDecayOrder delta epsilon A : ℝ) := by
    exact Nat.le_ceil _
  have hmul : A + 1 + epsilon ≤
      delta * (residueDecayOrder delta epsilon A : ℝ) := by
    apply (div_le_iff₀ hdelta).mp at hceil
    simpa [mul_comm] using hceil
  linarith

/-- Exact power comparison underlying the residue estimate. -/
theorem N_div_gapPow_le_time
    {T N g delta epsilon A : ℝ}
    (hT : 1 ≤ T) (hN0 : 0 ≤ N)
    (hNcap : N ≤ Real.rpow T (1 + epsilon))
    (hgap : Real.rpow T delta ≤ |g|)
    (hdelta : 0 < delta) :
    N / |g| ^ residueDecayOrder delta epsilon A ≤
      Real.rpow T (-A) := by
  let k := residueDecayOrder delta epsilon A
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hTdelta : 0 < Real.rpow T delta := Real.rpow_pos_of_pos hTpos _
  have hgapPos : 0 < |g| := hTdelta.trans_le hgap
  have hkpow : Real.rpow T (delta * (k : ℝ)) ≤ |g| ^ k := by
    calc
      Real.rpow T (delta * (k : ℝ)) =
          (Real.rpow T delta) ^ k :=
        Real.rpow_mul_natCast hTpos.le delta k
      _ ≤ |g| ^ k :=
        pow_le_pow_left₀ (Real.rpow_nonneg hTpos.le _) hgap k
  have hdenPos : 0 < Real.rpow T (delta * (k : ℝ)) :=
    Real.rpow_pos_of_pos hTpos _
  have hpowPos : 0 < |g| ^ k := pow_pos hgapPos _
  have hnum : N ≤ Real.rpow T (1 + epsilon) := hNcap
  have hexp : 1 + epsilon - delta * (k : ℝ) ≤ -A := by
    dsimp [k]
    exact residueDecayOrder_exponent_le
      (delta := delta) (epsilon := epsilon) (A := A) hdelta
  calc
    N / |g| ^ k ≤ Real.rpow T (1 + epsilon) /
        Real.rpow T (delta * (k : ℝ)) := by
      exact div_le_div₀ (Real.rpow_nonneg hTpos.le _) hnum hdenPos hkpow
    _ = Real.rpow T (1 + epsilon - delta * (k : ℝ)) := by
      exact (Real.rpow_sub hTpos _ _).symm
    _ ≤ Real.rpow T (-A) :=
      Real.rpow_le_rpow_of_exponent_le hT hexp

/-- The literal zeta-pole residue is power-saving uniformly on the corrected
`N ≤ T^(1+epsilon)` range.  The constant is explicit in the fixed Mellin
seminorm and in `delta,epsilon,A`. -/
theorem exists_norm_lemma295PoleResidue_le_exactM
    {delta epsilon A : ℝ} (hdelta : 0 < delta) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {T N g : ℝ},
        1 ≤ T → 0 < N →
        N ≤ sourceReflectionNumerator29_40 T epsilon →
        Real.rpow T delta ≤ |g| →
        ‖lemma295PoleResidue N g‖ ≤ C * Real.rpow T (-A) := by
  let k := residueDecayOrder delta epsilon A
  let S : ℝ :=
    SchwartzMap.seminorm ℂ k 0
      (𝓕 (GuthMaynardMellinRapidDecay.mellinLogLiftSchwartz sourceHZero
        (GuthMaynardMellinRapidDecay.mellinLogLift_hasCompactSupport
          (by norm_num : (0 : ℝ) < 1 / 2)
          (by norm_num : (0 : ℝ) < 5 / 2) sourceHZero_support)
        (GuthMaynardMellinRapidDecay.mellinLogLift_contDiff
          sourceHZero_contDiff)) : 𝓢(ℝ, ℂ))
  let C : ℝ := max 1 (S * (2 * Real.pi) ^ k)
  refine ⟨C, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro T N g hT hN hNcap hgap
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hgapPos : 0 < |g| :=
    (Real.rpow_pos_of_pos hTpos delta).trans_le hgap
  have hg : g ≠ 0 := by simpa [abs_pos] using hgapPos
  have hres := norm_lemma295PoleResidue_le
    (N := N) (g := g) (k := k) hN hg
  have hden : |g / (2 * Real.pi)| ^ k =
      |g| ^ k / (2 * Real.pi) ^ k := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi), div_pow]
  have hscalar :
      N * (S / |g / (2 * Real.pi)| ^ k) =
        (S * (2 * Real.pi) ^ k) * (N / |g| ^ k) := by
    rw [hden]
    field_simp [hgapPos.ne', Real.pi_ne_zero]
    <;> ring
  have htime := N_div_gapPow_le_time
    (T := T) (N := N) (g := g) (delta := delta)
    (epsilon := epsilon) (A := A) hT hN.le
    (by simpa [sourceReflectionNumerator29_40] using hNcap) hgap hdelta
  have hcoeff0 : 0 ≤ S * (2 * Real.pi) ^ k := by
    dsimp [S]
    positivity
  calc
    ‖lemma295PoleResidue N g‖ ≤
        N * (S / |g / (2 * Real.pi)| ^ k) := by
      simpa [S, k] using hres
    _ = (S * (2 * Real.pi) ^ k) * (N / |g| ^ k) := hscalar
    _ ≤ C * Real.rpow T (-A) := by
      exact mul_le_mul (le_max_right _ _) htime
        (div_nonneg hN.le (pow_nonneg (abs_nonneg _) _))
        (zero_le_one.trans (le_max_left _ _))

end
end GuthMaynardLemma295ResidueExactM

#print axioms GuthMaynardLemma295ResidueExactM.residueDecayOrder_exponent_le
#print axioms GuthMaynardLemma295ResidueExactM.N_div_gapPow_le_time
#print axioms GuthMaynardLemma295ResidueExactM.exists_norm_lemma295PoleResidue_le_exactM
