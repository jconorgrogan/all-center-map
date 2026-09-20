import GuthMaynardGMHalaszConcreteAbsorption
import GuthMaynardLiteralShellTimeSubdivision
import GuthMaynardGMGlobalHighScalar
import GuthMaynardGMClassicalSmallN

namespace GuthMaynardGMGlobalHighActual
open scoped BigOperators
open CGLProofDAG
open GuthMaynardGMHalaszConcreteAbsorption GuthMaynardLiteralShellTimeSubdivision
open GuthMaynardGMGlobalHighScalar GuthMaynardGMClassicalSmallN
noncomputable section

def highConstant : ℝ := 19200 * (19200 : ℝ) ^ 2

theorem global_high_largeN {T V : ℝ} {N : ℕ}
    (hN : 1 ≤ N) (hNlarge : (19200 : ℝ) ^ 10 ≤ N)
    (hT : 1 ≤ T) (hV : 0 < V) (hhigh : Real.rpow (N : ℝ) (4 / 5 : ℝ) ≤ V)
    (b : ℕ → ℂ) (W : Finset ℝ) (hb : ∀ n, ‖b n‖ ≤ 1)
    (hsep : OneSeparated W) (hheight : ∀ t ∈ W, 0 ≤ t ∧ t ≤ T)
    (hlarge : ∀ t ∈ W, V ≤ ‖dirichletPolynomial b N t‖) :
    (W.card : ℝ) ≤ highConstant * Real.log (2 * T) *
      ((N : ℝ) ^ 2 / V ^ 2 + T * (N : ℝ) ^ 4 / V ^ 6) := by
  have hNR : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hNR1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  let S : ℝ := V ^ 4 / ((19200 : ℝ) ^ 2 * (N : ℝ) ^ 2)
  let L : ℝ := min T S
  have hSge : (N : ℝ) ≤ S := by
    have hh := sourceScale_ge_N hN (by norm_num at hNlarge ⊢; exact hNlarge) hV hhigh
    convert hh using 1 <;> dsimp [S] <;> field_simp <;> ring
  have hL1 : 1 ≤ L := le_min hT (hNR1.trans hSge)
  have hLp : 0 < L := by linarith
  have hLshape : L ≤ ((64 * (300 : ℝ))⁻¹) ^ 2 * V ^ 4 / (N : ℝ) ^ 2 := by
    have hh : L ≤ S := min_le_right _ _
    convert hh using 1 <;> dsimp [S] <;> field_simp <;> ring
  have hlogL : 0 ≤ Real.log (2 * L) := Real.log_nonneg (by linarith)
  have hK : 0 ≤ 9600 * (N : ℝ) ^ 2 * Real.log (2 * L) / V ^ 2 := by positivity
  have hlocal : ∀ (a : ℕ → ℂ) (U : Finset ℝ),
      (∀ n, ‖a n‖ ≤ 1) → OneSeparated U →
      (∀ u ∈ U, 0 ≤ u ∧ u ≤ L) →
      (∀ u ∈ U, V ≤ ‖gmShellPolynomial a N u‖) →
      (U.card : ℝ) ≤ 9600 * (N : ℝ) ^ 2 * Real.log (2 * L) / V ^ 2 := by
    intro a U ha hUsep hUheight hUlarge
    apply gmHalaszLocalHighValues300 hN (by norm_num at hNlarge ⊢; exact hNlarge)
      hV hhigh hL1 hLshape U hUsep hUheight a (fun n _ => ha n)
    exact hUlarge
  have hW := card_le_time_ratio_plus_one_of_literal_local_bound b N W hLp
    (by linarith) hheight hb hsep
    (fun t ht => by simpa [gmShellPolynomial_eq_dirichletPolynomial] using hlarge t ht)
    hK hlocal
  have hout := global_high_scalar hNR hV hT (by norm_num : (1 : ℝ) ≤ 19200) hW
  exact hout


/-- Unconditional classical high-value branch with the exact GM target. -/
theorem guthMaynard_high_range :
    ∀ eta : ℝ, 0 < eta → ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (T V : ℝ) (N : ℕ) (b : ℕ → ℂ) (W : Finset ℝ),
        T₀ ≤ T → 1 ≤ N → 0 < V →
        Real.rpow (N : ℝ) (4 / 5 : ℝ) ≤ V →
        (∀ n, ‖b n‖ ≤ 1) → OneSeparated W →
        (∀ t ∈ W, 0 ≤ t ∧ t ≤ T) →
        (∀ t ∈ W, V ≤ ‖dirichletPolynomial b N t‖) →
        (W.card : ℝ) ≤ C * Real.rpow T eta *
          ((N : ℝ) ^ 2 / V ^ 2 + Real.rpow (N : ℝ) (18 / 5 : ℝ) / V ^ 4 +
            T * Real.rpow (N : ℝ) (12 / 5 : ℝ) / V ^ 4) := by
  intro eta heta
  let Cs : ℝ := 2 * ((19200 : ℝ) ^ 10) ^ 2
  let Cb : ℝ := highConstant * (Real.log 2 + 1 / eta)
  let C : ℝ := max Cs Cb
  have hCs : 0 < Cs := by dsimp [Cs]; positivity
  have hC : 0 < C := lt_of_lt_of_le hCs (le_max_left _ _)
  refine ⟨C, 2, hC, by norm_num, ?_⟩
  intro T V N b W hT hN hV hhigh hb hsep hheight hlarge
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 ≤ T := by linarith
  have hNR : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  let G : ℝ := (N : ℝ) ^ 2 / V ^ 2 + Real.rpow (N : ℝ) (18 / 5 : ℝ) / V ^ 4 +
      T * Real.rpow (N : ℝ) (12 / 5 : ℝ) / V ^ 4
  have hG : 0 ≤ G := by
    dsimp [G]
    have h1 := Real.rpow_nonneg hNR.le (18 / 5 : ℝ)
    have h2 := Real.rpow_nonneg hNR.le (12 / 5 : ℝ)
    positivity
  have hTp : 1 ≤ Real.rpow T eta := Real.one_le_rpow hT1 heta.le
  change (W.card : ℝ) ≤ C * Real.rpow T eta * G
  by_cases hs : (N : ℝ) ≤ (19200 : ℝ) ^ 10
  · have hsmall := smallN_largeValue_cardinality_rpow
      (N₀ := (19200 : ℕ) ^ 10) (by norm_num) hN
      (by norm_num at hs ⊢; exact hs) hT1 hV hb hsep hheight hlarge
    have hmain : (W.card : ℝ) ≤ Cs * G := by
      have hterm : T * Real.rpow (N : ℝ) (12 / 5 : ℝ) / V ^ 4 ≤ G := by
        change T * Real.rpow (N : ℝ) (12 / 5 : ℝ) / V ^ 4 ≤
          (N : ℝ) ^ 2 / V ^ 2 + Real.rpow (N : ℝ) (18 / 5 : ℝ) / V ^ 4 +
            T * Real.rpow (N : ℝ) (12 / 5 : ℝ) / V ^ 4
        have h1 : 0 ≤ (N : ℝ) ^ 2 / V ^ 2 := by positivity
        have h2 : 0 ≤ Real.rpow (N : ℝ) (18 / 5 : ℝ) / V ^ 4 :=
          div_nonneg (Real.rpow_nonneg hNR.le _) (pow_nonneg hV.le _)
        linarith
      have hh := mul_le_mul_of_nonneg_left hterm hCs.le
      have hsmall' : (W.card : ℝ) ≤ Cs * (T * Real.rpow (N : ℝ) (12 / 5 : ℝ) / V ^ 4) := by
        convert hsmall using 1 <;> dsimp [Cs] <;> norm_num <;> ring
      exact hsmall'.trans hh
    have hcoeff : Cs ≤ C * Real.rpow T eta := by
      have hh := mul_le_mul_of_nonneg_left hTp hC.le
      have hsc : Cs ≤ C := le_max_left _ _
      linarith
    exact hmain.trans (mul_le_mul_of_nonneg_right hcoeff hG)
  · have hraw := global_high_largeN hN (le_of_not_ge hs) hT1 hV hhigh b W hb hsep hheight hlarge
    have hterm := high_classical_terms_le_gm hNR hV hT0 hhigh
    have hlog : 0 ≤ Real.log (2 * T) := Real.log_nonneg (by linarith)
    have hHC : 0 ≤ highConstant := by norm_num [highConstant]
    have hmain : (W.card : ℝ) ≤ highConstant * Real.log (2 * T) * G :=
      hraw.trans (mul_le_mul_of_nonneg_left hterm (mul_nonneg hHC hlog))
    have hcoeff : highConstant * Real.log (2 * T) ≤ Cb * Real.rpow T eta := by
      have hh := mul_le_mul_of_nonneg_left (log_two_mul_le_rpow hT1 heta) hHC
      change highConstant * Real.log (2 * T) ≤
        (highConstant * (Real.log 2 + 1 / eta)) * Real.rpow T eta
      simpa only [mul_assoc] using hh
    have hcoeffC : Cb * Real.rpow T eta ≤ C * Real.rpow T eta :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)
    exact hmain.trans (mul_le_mul_of_nonneg_right (hcoeff.trans hcoeffC) hG)

end
end GuthMaynardGMGlobalHighActual
#print axioms GuthMaynardGMGlobalHighActual.global_high_largeN
#print axioms GuthMaynardGMGlobalHighActual.guthMaynard_high_range
