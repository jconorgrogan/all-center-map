import JutilaPseudocharacterHarmonicLower

/-!
# Terminal lower-bound weld in Jutila Lemma 6

After Mellin inversion, Jutila's positive main term is
`exp(-1/X) * sum' 1/r`.  This module combines the uniform
squarefree-coprime harmonic lower bound with a unit error estimate.
The remaining Lemma-6 work is therefore the exact Mellin identity and its
unit error bound, not the asymptotic Lemma 5 or the final reverse triangle
inequality.
-/

namespace MAPJutilaLemma6LowerWeld

open MAPJutilaPseudocharacterHarmonicLower

noncomputable section

def lemmaSixMain (X : ℝ) (q R : ℕ) : ℝ :=
  Real.exp (-(1 / X)) * jutilaPrimedHarmonic q R

theorem lemmaSixMain_nonneg (X : ℝ) (q R : ℕ) :
    0 ≤ lemmaSixMain X q R := by
  unfold lemmaSixMain jutilaPrimedHarmonic
  positivity

/-- Exact detector lower bound after a unit Mellin/tail error.  The size
condition is eventual in the source parameters and is the only threshold
needed after replacing Jutila's Lemma-5 asymptotic by the uniform `1/4`
harmonic lower bound. -/
theorem norm_detector_ge_of_eq_main_add_error
    {X : ℝ} {q R : ℕ} (hq : 0 < q) (hR : 1 ≤ R) (hX : 2 ≤ X)
    {g error : ℂ}
    (hidentity : g = (lemmaSixMain X q R : ℂ) + error)
    (herror : ‖error‖ ≤ 1)
    (hsize : 2 ≤ (1 / 8 : ℝ) *
      ((Nat.totient q : ℝ) / (q : ℝ)) * Real.log (R : ℝ)) :
    (1 / 16 : ℝ) * ((Nat.totient q : ℝ) / (q : ℝ)) *
        Real.log (R : ℝ) ≤ ‖g‖ := by
  have hXpos : 0 < X := by linarith
  have hinv : 1 / X ≤ 1 / 2 := by
    apply (div_le_iff₀ hXpos).2
    nlinarith
  have hhalfExp : (1 / 2 : ℝ) ≤ Real.exp (-(1 / 2 : ℝ)) := by
    nlinarith [Real.add_one_le_exp (-(1 / 2 : ℝ))]
  have hexpMono : Real.exp (-(1 / 2 : ℝ)) ≤ Real.exp (-(1 / X)) := by
    exact Real.exp_le_exp.mpr (by linarith)
  have hexpHalf : (1 / 2 : ℝ) ≤ Real.exp (-(1 / X)) :=
    hhalfExp.trans hexpMono
  have hlog0 : 0 ≤ Real.log (R : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast hR
  have hratio0 : 0 ≤ (Nat.totient q : ℝ) / (q : ℝ) := by positivity
  have hlowerCore0 : 0 ≤
      (1 / 4 : ℝ) * ((Nat.totient q : ℝ) / (q : ℝ)) *
        Real.log (R : ℝ) := by positivity
  let lower : ℝ :=
    (1 / 8 : ℝ) * ((Nat.totient q : ℝ) / (q : ℝ)) *
      Real.log (R : ℝ)
  have hmainLower : lower ≤ lemmaSixMain X q R := by
    have hharmonic := quarter_totientRatio_log_le_jutilaPrimedHarmonic
      (q := q) (R := R) hq
    unfold lower lemmaSixMain
    calc
      (1 / 8 : ℝ) * ((Nat.totient q : ℝ) / (q : ℝ)) *
          Real.log (R : ℝ) =
        (1 / 2 : ℝ) *
          ((1 / 4 : ℝ) * ((Nat.totient q : ℝ) / (q : ℝ)) *
            Real.log (R : ℝ)) := by ring
      _ ≤ Real.exp (-(1 / X)) * jutilaPrimedHarmonic q R :=
        mul_le_mul hexpHalf hharmonic hlowerCore0 (Real.exp_pos _).le
  have hmain0 : 0 ≤ lemmaSixMain X q R := lemmaSixMain_nonneg X q R
  have hmainNorm : ‖(lemmaSixMain X q R : ℂ)‖ = lemmaSixMain X q R := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hmain0]
  have hreverse : lemmaSixMain X q R ≤ ‖g‖ + ‖error‖ := by
    calc
      lemmaSixMain X q R = ‖(lemmaSixMain X q R : ℂ)‖ := hmainNorm.symm
      _ = ‖g - error‖ := by rw [hidentity]; ring_nf
      _ ≤ ‖g‖ + ‖error‖ := norm_sub_le _ _
  have hlowerNorm : lower - 1 ≤ ‖g‖ := by linarith
  have hhalf : lower / 2 ≤ lower - 1 := by
    dsimp [lower] at hsize ⊢
    linarith
  have htarget :
      (1 / 16 : ℝ) * ((Nat.totient q : ℝ) / (q : ℝ)) *
          Real.log (R : ℝ) =
        lower / 2 := by
    dsimp [lower]
    ring
  rw [htarget]
  exact hhalf.trans hlowerNorm

end

end MAPJutilaLemma6LowerWeld

#print axioms MAPJutilaLemma6LowerWeld.norm_detector_ge_of_eq_main_add_error
