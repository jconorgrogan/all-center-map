import GuthMaynardLemma2910ConcreteAssembly
import GuthMaynardLemma2910RegimeGeometry

/-!
# Uniform bound at the Lemma 29.10 bootstrap target

This packages the three legal possibilities for `P = 4M^2`: unconditional
high range, direct feedback inside the exact-M AFE range, and the finite
reflected-prefix collar.  In particular the AFE is never invoked above its
source cap.
-/

namespace GuthMaynardLemma2910BootstrapTarget

open CGLProofDAG
open GuthMaynardJutilaReflection2941
open GuthMaynardJutilaLemma29NineKTwo
open GuthMaynardHeathBrownMajorant
open GuthMaynardLengthComparison
open GuthMaynardJutilaTransference
open GuthMaynardLemma2910ConcreteAssembly
open GuthMaynardLemma2910HighRangeFromAFE
open GuthMaynardLemma2910RegimeGeometry

noncomputable section

def bootstrapDirectRaw (C₁ C₂ Cp T P L eta B : ℝ) (G : Finset ℝ) : ℝ :=
  2 * (C₁ * (G.card : ℝ) * P + C₁ * Real.rpow T (-B)) +
    (C₁ * C₂ * (Real.log L) ^ (5 : ℕ)) ^ 2 *
      (Cp * (1 + Real.log P) ^ 3 * (G.card : ℝ) ^ 2 *
        Real.rpow (4 * L ^ 2) eta)

def bootstrapFiniteRaw (C T P M₀ B : ℝ) (G : Finset ℝ) : ℝ :=
  C * (G.card : ℝ) * P +
    C * (G.card : ℝ)^2 * ((Nat.ceil M₀ + 1 : ℕ) : ℝ)^2 +
    C * Real.rpow T (-B)

def bootstrapHighRaw (T P : ℝ) (G : Finset ℝ) : ℝ :=
  (252 + 252 * Classical.choose
    MontgomeryVaughanFiniteReduction.finiteLogHilbertInequality_via_integerHilbert) *
    (G.card : ℝ) * P

/-- The exact three-case bound at the bootstrap target.  The target `P` is
real, matching the printed proof. -/
theorem bootstrap_target_uniform_raw_of_exactAFE
    (hAFE : Lemma295ApproximateFunctionalEquationExactM)
    {delta epsilon B eta : ℝ}
    (hdelta : 0 < delta) (hepsilon : 0 < epsilon)
    (hB : 0 < B) (heta : 0 < eta) :
    ∃ C₁ C₂ Cp Cf T₀ M₀ : ℝ,
      0 < C₁ ∧ 0 < C₂ ∧ 0 < Cp ∧ 0 < Cf ∧ 2 ≤ T₀ ∧ 2 ≤ M₀ ∧
      ∀ (T N : ℝ) (G : Finset ℝ),
        T₀ ≤ T → 1 ≤ N → N < T →
        TPowerSeparated G T delta → InOpenClosedZeroT G T →
        let A := sourceReflectionNumerator29_40 T epsilon
        let M := reflectedLength29_40 T epsilon N
        let P := 4 * M ^ 2
        kTwoPrimeLower M N < 1 →
        (T ≤ P ∧ jutilaSecondMoment P G ≤ bootstrapHighRaw T P G) ∨
        (P < T ∧ M₀ ≤ A/P ∧ jutilaSecondMoment P G ≤
          bootstrapDirectRaw C₁ C₂ Cp T P (A/P) eta B G) ∨
        (P < T ∧ A/P < M₀ ∧ jutilaSecondMoment P G ≤
          bootstrapFiniteRaw Cf T P M₀ B G) := by
  obtain ⟨C₁, C₂, Cp, Td, M₀, hC₁, hC₂, hCp, hTd, hM₀, hdirect⟩ :=
    lemma2910_direct_oneScale_of_exactAFE hAFE hdelta hepsilon hB heta
  obtain ⟨Cf, Tf, hCf, hTf, hfinite⟩ :=
    jutilaSecondMoment_le_finitePrefixCollar_of_exactM
      hAFE hdelta hepsilon hB
  let T₀ := max Td Tf
  refine ⟨C₁, C₂, Cp, Cf, T₀, M₀, hC₁, hC₂, hCp, hCf,
    ?_, hM₀, ?_⟩
  · exact hTd.trans (le_max_left _ _)
  intro T N G hT hN hNT hsep hheight
  dsimp only
  let A := sourceReflectionNumerator29_40 T epsilon
  let M := reflectedLength29_40 T epsilon N
  let P := 4 * M ^ 2
  intro hfail
  have hTtwo : 2 ≤ T := hTd.trans ((le_max_left Td Tf).trans hT)
  have hTone : 1 ≤ T := by linarith
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hgeo := direct_or_bootstrap_target hTone hepsilon.le hNpos
  dsimp only at hgeo
  rcases hgeo with hdir | ⟨hNP, hhigh | ⟨hPT, hPA, htargetDirect⟩⟩
  · exact False.elim ((not_le_of_gt hfail) hdir)
  · have hPone : 1 ≤ P := hN.trans hNP.le
    have hh := jutilaSecondMoment_real_highRange_le
      hTone hdelta.le hPone hhigh hsep hheight
    exact Or.inl ⟨hhigh, hh⟩
  · have hPone : 1 ≤ P := hN.trans hNP.le
    have hTdirect : Td ≤ T := (le_max_left Td Tf).trans hT
    have hTfinite : Tf ≤ T := (le_max_right Td Tf).trans hT
    by_cases hL : M₀ ≤ A / P
    · have hd := hdirect T P G hTdirect hPone hPA hsep hheight hL htargetDirect
      exact Or.inr (Or.inl ⟨hPT, hL, hd⟩)
    · have hf := hfinite T P G hTfinite hPone hPA hsep hheight
      have hrefEq : reflectedLength29_40 T epsilon P = A / P := by
        rfl
      rw [hrefEq] at hf
      have hcardNat : (natRealIoc 0 (A / P)).card ≤ Nat.ceil M₀ + 1 :=
        card_natRealIoc_zero_le_ceil_add_one (le_of_not_ge hL)
      have hcard : ((natRealIoc 0 (A / P)).card : ℝ) ≤
          ((Nat.ceil M₀ + 1 : ℕ) : ℝ) := by exact_mod_cast hcardNat
      have hcard0 : 0 ≤ ((natRealIoc 0 (A / P)).card : ℝ) := by positivity
      have hsq := pow_le_pow_left₀ hcard0 hcard 2
      have hmid : Cf * (G.card : ℝ)^2 *
          ((natRealIoc 0 (A / P)).card : ℝ)^2 ≤
          Cf * (G.card : ℝ)^2 * ((Nat.ceil M₀ + 1 : ℕ) : ℝ)^2 := by
        exact mul_le_mul_of_nonneg_left hsq
          (mul_nonneg hCf.le (sq_nonneg _))
      have hf' : jutilaSecondMoment P G ≤
          bootstrapFiniteRaw Cf T P M₀ B G := by
        unfold bootstrapFiniteRaw
        exact hf.trans (by linarith)
      exact Or.inr (Or.inr ⟨hPT, lt_of_not_ge hL, hf'⟩)

end
end GuthMaynardLemma2910BootstrapTarget

#print axioms GuthMaynardLemma2910BootstrapTarget.bootstrap_target_uniform_raw_of_exactAFE
