import RecenteredSampling
import BudgetedFixedCharacterPoweredLargeValueBridge

/-!
# Budgeted powered-bridge connector analysis

This staging file checks the exact interfaces needed to assemble the corrected
budgeted fixed-character bridge.  It introduces no source proposition and no
unproved declaration.  The first result is the discrete-mean-value analogue of
`CGLProofDAG.guthMaynard_powered_block_transfer`.
-/

namespace BudgetedConnectorAnalysis

open scoped BigOperators
open CGLProofDAG FixedCharacterPoweredBridge AppendixTypeIPower

noncomputable section

/-- Normalizing a selected powered block by a positive coefficient majorant
commutes with the now-inhabited discrete Dirichlet mean-value theorem. -/
theorem discreteMeanValue_powered_block_transfer
    (hMV : DiscreteDirichletMeanValue) (η : ℝ) (hη : 0 < η) :
    ∃ K T₀ : ℝ, 0 < K ∧ 2 ≤ T₀ ∧
      ∀ (T V C : ℝ) (baseN k blockN : ℕ) (a : ℕ → ℂ) (W : Finset ℝ),
        T₀ ≤ T → 1 ≤ blockN → 0 < V → 0 < C →
        (∀ n ∈ Finset.Ioc baseN (2 * baseN), ‖a n‖ ≤ 1) →
        (∀ m ∈ Finset.Ioc blockN (2 * blockN),
          (orderedDivisorCount k m : ℝ) ≤ C) →
        OneSeparated W →
        (∀ t ∈ W, 0 ≤ t ∧ t ≤ T) →
        (∀ t ∈ W, V ≤
          ‖dirichletPolynomial
            (fun m => (dyadicCoefficient baseN a ^ k) m) blockN t‖) →
        (W.card : ℝ) ≤
          K * Real.rpow T η *
            (((blockN : ℝ) ^ 2 + T * blockN) / (V / C) ^ 2) := by
  obtain ⟨K, T₀, hK, hT₀, hbound⟩ := hMV η hη
  refine ⟨K, T₀, hK, hT₀, ?_⟩
  intro T V C baseN k blockN a W hT hblock hV hC ha hdiv hsep hheight hlarge
  apply hbound T (V / C) blockN
    (normalizedPoweredBlock baseN k blockN a C) W hT hblock
    (div_pos hV hC)
    (norm_normalizedPoweredBlock_le_one ha hC hdiv) hsep hheight
  intro t ht
  rw [dirichletPolynomial_normalizedPoweredBlock baseN k blockN a C t,
    norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hC]
  exact (div_le_div_iff_of_pos_right hC).2 (hlarge t ht)

/-- The common-block threshold after dividing the powered coefficients by a
positive uniform divisor majorant.  This records the exact `k * D` loss and
feeds either published large-value interface without a normalization gap. -/
theorem normalized_selected_powered_block_threshold
    {V D : ℝ} {N k blockN : ℕ} {b : ℕ → ℂ} {S : Finset ℝ}
    (hk : 0 < k) (hD : 0 < D)
    (hblock : ∀ t ∈ S,
      V ^ k ≤ (k : ℝ) *
        ‖dirichletPolynomial
          (fun m => (dyadicCoefficient N b ^ k) m) blockN t‖) :
    ∀ t ∈ S,
      V ^ k / ((k : ℝ) * D) ≤
        ‖dirichletPolynomial
          (normalizedPoweredBlock N k blockN b D) blockN t‖ := by
  intro t ht
  rw [dirichletPolynomial_normalizedPoweredBlock N k blockN b D t,
    norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hD]
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  rw [div_le_div_iff₀ (mul_pos hkreal hD) hD]
  have h := hblock t ht
  nlinarith

/-!
The public bridge permits the original length to have the logarithmic collar
`N ≤ T^(1/2) (log T)^2`.  Consequently `log_T N ≤ 1/2` is not a legal premise
for the existing bounded-power selector.  Capping the logarithmic length at
`1/2` preserves a lower comparison and records the collar on the upper side.
-/

/-- Exact capped logarithmic-length adapter needed before the existing
bounded-power selector can be invoked. -/
theorem capped_logb_length_collar
    {κ T : ℝ} {N : ℕ}
    (hκhalf : κ ≤ 1 / 2)
    (hT : Real.exp 1 ≤ T)
    (hNlow : Real.rpow T κ ≤ (N : ℝ))
    (hNhigh : (N : ℝ) ≤
      Real.rpow T (1 / 2) * (Real.log T) ^ 2) :
    κ ≤ min (Real.logb T N) (1 / 2) ∧
      min (Real.logb T N) (1 / 2) ≤ 1 / 2 ∧
      Real.rpow T (min (Real.logb T N) (1 / 2)) ≤ (N : ℝ) ∧
      (N : ℝ) ≤
        Real.rpow T (min (Real.logb T N) (1 / 2)) *
          (Real.log T) ^ 2 := by
  have hTone : 1 < T := (Real.exp_one_gt_d9.trans_le hT).trans' (by norm_num)
  have hTpos : 0 < T := zero_lt_one.trans hTone
  have hNpos : (0 : ℝ) < N :=
    (Real.rpow_pos_of_pos hTpos κ).trans_le hNlow
  have hκlogb : κ ≤ Real.logb T N :=
    (Real.le_logb_iff_rpow_le hTone hNpos).2 hNlow
  have hlogone : 1 ≤ Real.log T := by
    calc
      1 = Real.log (Real.exp 1) := by rw [Real.log_exp]
      _ ≤ Real.log T := Real.log_le_log (Real.exp_pos 1) hT
  have hlogsq : 1 ≤ (Real.log T) ^ 2 := by nlinarith
  have hTN : Real.rpow T (Real.logb T (N : ℝ)) = (N : ℝ) := by
    simpa only [Real.rpow_def] using
      (Real.rpow_logb hTpos hTone.ne' hNpos)
  refine ⟨le_min hκlogb hκhalf, min_le_right _ _, ?_, ?_⟩
  · by_cases hlogb : Real.logb T N ≤ 1 / 2
    · rw [min_eq_left hlogb, hTN]
    · have hhalf : (1 / 2 : ℝ) ≤ Real.logb T N := le_of_not_ge hlogb
      rw [min_eq_right hhalf,
        ← hTN]
      exact Real.rpow_le_rpow_of_exponent_le hTone.le hhalf
  · by_cases hlogb : Real.logb T N ≤ 1 / 2
    · rw [min_eq_left hlogb, hTN]
      exact le_mul_of_one_le_right hNpos.le hlogsq
    · rw [min_eq_right (le_of_not_ge hlogb)]
      exact hNhigh

/-- Every positive power eventually strictly absorbs the squared logarithmic
collar. -/
theorem eventually_log_sq_lt_rpow {a : ℝ} (ha : 0 < a) :
    ∃ T₀ : ℝ, Real.exp 1 ≤ T₀ ∧
      ∀ T : ℝ, T₀ ≤ T → (Real.log T) ^ 2 < Real.rpow T a := by
  have hevent := (isLittleO_log_rpow_rpow_atTop 2 ha).bound
    (show (0 : ℝ) < 1 / 2 by norm_num)
  rw [Filter.eventually_atTop] at hevent
  obtain ⟨A, hA⟩ := hevent
  refine ⟨max A (Real.exp 1), le_max_right _ _, ?_⟩
  intro T hT
  have hAT : A ≤ T := (le_max_left _ _).trans hT
  have hET : Real.exp 1 ≤ T := (le_max_right _ _).trans hT
  have hraw := hA T hAT
  have hlog0 : 0 ≤ Real.log T := by
    calc
      0 ≤ 1 := by norm_num
      _ ≤ Real.log T := by
        calc
          1 = Real.log (Real.exp 1) := by rw [Real.log_exp]
          _ ≤ Real.log T := Real.log_le_log (Real.exp_pos 1) hET
  have hT0 : 0 ≤ T := (Real.exp_pos 1).le.trans hET
  have hle : (Real.log T) ^ 2 ≤
      (1 / 2 : ℝ) * Real.rpow T a := by
    change ‖Real.rpow (Real.log T) 2‖ ≤
      (1 / 2 : ℝ) * ‖Real.rpow T a‖ at hraw
    have hlogpow : Real.rpow (Real.log T) 2 = (Real.log T) ^ 2 := by
      simpa only [Real.rpow_def] using Real.rpow_natCast (Real.log T) 2
    have hnormpow : ‖Real.rpow T a‖ = Real.rpow T a :=
      Real.norm_of_nonneg (Real.rpow_nonneg hT0 a)
    rw [hlogpow, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
      hnormpow] at hraw
    exact hraw
  have hpowpos : 0 < Real.rpow T a :=
    Real.rpow_pos_of_pos ((Real.exp_pos 1).trans_le hET) a
  nlinarith

/-- For `κ > 1/2` the public lower and upper length constraints are eventually
incompatible, so that part of the bridge is vacuous. -/
theorem no_admissible_length_above_half
    {κ : ℝ} (hκ : 1 / 2 < κ) :
    ∃ T₀ : ℝ, Real.exp 1 ≤ T₀ ∧
      ∀ (T : ℝ) (N : ℕ), T₀ ≤ T →
        Real.rpow T κ ≤ (N : ℝ) →
        (N : ℝ) ≤ Real.rpow T (1 / 2) * (Real.log T) ^ 2 → False := by
  have ha : 0 < κ - 1 / 2 := sub_pos.mpr hκ
  obtain ⟨T₀, hT₀, hlog⟩ := eventually_log_sq_lt_rpow ha
  refine ⟨T₀, hT₀, ?_⟩
  intro T N hT hlow hupp
  have hTone : 1 < T :=
    (Real.exp_one_gt_d9.trans_le (hT₀.trans hT)).trans' (by norm_num)
  have hTpos : 0 < T := zero_lt_one.trans hTone
  have hcollar := hlog T hT
  have hcombine :
      Real.rpow T (1 / 2) * Real.rpow T (κ - 1 / 2) =
        Real.rpow T κ := by
    change (T ^ (1 / 2 : ℝ)) * (T ^ (κ - 1 / 2)) = T ^ κ
    rw [← Real.rpow_add hTpos]
    congr 1
    ring
  have hupper : (N : ℝ) < Real.rpow T κ := by
    calc
      (N : ℝ) ≤ Real.rpow T (1 / 2) * (Real.log T) ^ 2 := hupp
      _ < Real.rpow T (1 / 2) * Real.rpow T (κ - 1 / 2) :=
        mul_lt_mul_of_pos_left hcollar
          (Real.rpow_pos_of_pos hTpos _)
      _ = Real.rpow T κ := hcombine
  exact (not_lt_of_ge hlow) hupper

/-- All public quantifiers, the logarithmic collar, the bounded-power choice,
and the common-block pigeonhole reduce the desired bridge to the single
selected-block Type-I/II estimate encoded in the function-valued premise.  The
premise is deliberately at the selected-block level rather than equivalent to
the public bridge. -/
theorem budgetedBridge_of_selectedPoweredBlockAssembly
    (hAssembly :
      ∀ (_hGM : GuthMaynardTheorem11) (_hMV : DiscreteDirichletMeanValue)
          (κ η : ℝ), 0 < κ → κ ≤ 1 / 2 → 0 < η →
        ∃ C T₀ : ℝ, 0 < C ∧ Real.exp 1 ≤ T₀ ∧
          ∀ (T σ : ℝ) (N k : ℕ) (b : ℕ → ℂ)
              (W S : Finset ℝ) (i : Fin k),
            T₀ ≤ T → 7 / 10 ≤ σ → σ ≤ 4 / 5 →
            Real.rpow T κ ≤ (N : ℝ) →
            (N : ℝ) ≤ Real.rpow T (1 / 2) * (Real.log T) ^ 2 →
            1 ≤ k → k ≤ powerCap κ →
            poweredLengthLower σ ≤
              (k : ℝ) * min (Real.logb T N) (1 / 2) →
            (k : ℝ) * min (Real.logb T N) (1 / 2) ≤
              poweredLengthUpper σ →
            (∀ n, ‖b n‖ ≤ 1) →
            OneSeparated W →
            (∀ t ∈ W, 0 ≤ t ∧ t ≤ T) →
            S ⊆ W → W.card ≤ k * S.card →
            (∀ t ∈ S,
              (Real.rpow N σ * Real.rpow T (-inputLoss κ η)) ^ k ≤
                (k : ℝ) *
                  ‖dirichletPolynomial
                    (fun m => (dyadicCoefficient N b ^ k) m)
                    (N ^ k * 2 ^ (i : ℕ)) t‖) →
            (W.card : ℝ) ≤ C * Real.rpow T (gmExponent σ + η))
    (hGM : GuthMaynardTheorem11) :
    BudgetedFixedCharacterPoweredLargeValueBridge := by
  intro κ η hκ hη
  by_cases hκhalf : κ ≤ 1 / 2
  · obtain ⟨C, T₀, hC, hT₀, hselected⟩ :=
      hAssembly hGM RecenteredSampling.discreteDirichletMeanValue
        κ η hκ hκhalf hη
    refine ⟨C, T₀, hC, ?_, ?_⟩
    · exact (show (2 : ℝ) ≤ Real.exp 1 by
        linarith [Real.exp_one_gt_d9]).trans hT₀
    · intro T σ N b W hT hσlow hσhigh hNlow hNhigh hb hsep hheight hlarge
      have hET : Real.exp 1 ≤ T := hT₀.trans hT
      obtain ⟨hκlam, hlamHalf, -, -⟩ :=
        capped_logb_length_collar hκhalf hET hNlow hNhigh
      obtain ⟨k, hk, hkcap, hmuLow, hmuHigh⟩ :=
        exists_power_bounded_by_powerCap
          hσlow hσhigh hκ hκlam hlamHalf
      let V : ℝ := Real.rpow N σ * Real.rpow T (-inputLoss κ η)
      have hTpos : 0 < T := (Real.exp_pos 1).trans_le hET
      have hNpos : (0 : ℝ) < N :=
        (Real.rpow_pos_of_pos hTpos κ).trans_le hNlow
      have hVpos : 0 < V := by
        dsimp [V]
        exact mul_pos (Real.rpow_pos_of_pos hNpos σ)
          (Real.rpow_pos_of_pos hTpos _)
      obtain ⟨i, S, hSW, hcard, hblock⟩ :=
        exists_common_powered_dirichlet_block
          (N := N) (k := k) (a := b) (W := W) (V := V)
          (Nat.zero_lt_of_lt hk) hVpos.le (by simpa [V] using hlarge)
      exact hselected T σ N k b W S i hT hσlow hσhigh
        hNlow hNhigh hk hkcap hmuLow hmuHigh hb hsep hheight
        hSW hcard (by simpa [V] using hblock)
  · have hκlarge : 1 / 2 < κ := lt_of_not_ge hκhalf
    obtain ⟨T₀, hT₀, hnone⟩ := no_admissible_length_above_half hκlarge
    refine ⟨1, max 2 T₀, by norm_num, le_max_left _ _, ?_⟩
    intro T σ N b W hT _ _ hNlow hNhigh _ _ _ _
    exact (hnone T N ((le_max_right _ _).trans hT) hNlow hNhigh).elim

end
end BudgetedConnectorAnalysis

#print axioms BudgetedConnectorAnalysis.discreteMeanValue_powered_block_transfer
#print axioms BudgetedConnectorAnalysis.normalized_selected_powered_block_threshold
#print axioms BudgetedConnectorAnalysis.capped_logb_length_collar
#print axioms BudgetedConnectorAnalysis.eventually_log_sq_lt_rpow
#print axioms BudgetedConnectorAnalysis.no_admissible_length_above_half
#print axioms BudgetedConnectorAnalysis.budgetedBridge_of_selectedPoweredBlockAssembly
