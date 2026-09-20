import FordWeightedGrowthBlock
import FordWeightedLongBlock
import FordOffsetDyadicPartition

open scoped BigOperators ComplexConjugate
noncomputable section
namespace FordFiniteGrowthBound

open FordAllLambdaOffsetBound FordOffsetLogTransfer

def commonEnvelope (R t eta : ℝ) : ℝ :=
  R + Real.exp (1000 * eta * (Real.log t) ^ ((4 : ℝ) / 5)) +
    272 * Real.exp (eta * Real.sqrt (eta / savingCoeff) * Real.log t) +
    12 * Real.pi

lemma norm_actual_block_le_rpow
    {N H : ℕ} {t u eta : ℝ} (hN : 1 ≤ N) (hH : H ≤ N)
    (hu : 0 ≤ u) (heta : 0 ≤ eta) (heta1 : eta ≤ 1) :
    ‖∑ n ∈ Finset.range H,
        (((N + n : ℕ) : ℝ) + u : ℂ) ^
          (-(((1 - eta : ℝ) : ℂ) + Complex.I * (t : ℂ)))‖ ≤
      (N : ℝ) ^ eta := by
  have hσ : 0 ≤ 1 - eta := by linarith
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hterm : ∀ n : ℕ,
      ‖(((N + n : ℕ) : ℝ) + u : ℂ) ^
          (-(((1 - eta : ℝ) : ℂ) + Complex.I * (t : ℂ)))‖ ≤
        (((N + n : ℕ) : ℝ) + u) ^ (-(1 - eta)) := by
    intro n
    have hpos : 0 < ((N + n : ℕ) : ℝ) + u := by
      have hn : 0 ≤ (n : ℝ) := by positivity
      push_cast
      linarith
    have hcpow :
        (((N + n : ℕ) : ℝ) + u : ℂ) ^
            (-(((1 - eta : ℝ) : ℂ) + Complex.I * (t : ℂ))) =
          (((N + n : ℕ) : ℝ) + u) ^ (-(1 - eta)) •
            FordHurwitz.phase u t (N + n) := by
      simpa [FordWeightedOffsetBlock.phase_eq_offsetPhase] using
        (FordHurwitz.cpow_neg_real_add_imag_eq_weight_phase
          (u := u) (σ := 1 - eta) (t := t) (n := N + n) hpos)
    rw [hcpow]
    rw [norm_smul, FordHurwitz.norm_phase, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    simp
  have hbase : ∀ n : ℕ, (N : ℝ) ≤ ((N + n : ℕ) : ℝ) + u := by
    intro n
    have hn : 0 ≤ (n : ℝ) := by positivity
    push_cast
    linarith
  have hterm' : ∀ n : ℕ,
      (((N + n : ℕ) : ℝ) + u) ^ (-(1 - eta)) ≤ (N : ℝ) ^ (-(1 - eta)) := by
    intro n
    exact Real.rpow_le_rpow_of_nonpos hNpos (hbase n)
      (neg_nonpos.mpr hσ)
  have hsum :
      ‖∑ n ∈ Finset.range H,
        (((N + n : ℕ) : ℝ) + u : ℂ) ^
          (-(((1 - eta : ℝ) : ℂ) + Complex.I * (t : ℂ)))‖ ≤
      ∑ n ∈ Finset.range H, (N : ℝ) ^ (-(1 - eta)) := by
    calc
      _ ≤ ∑ n ∈ Finset.range H,
          ‖(((N + n : ℕ) : ℝ) + u : ℂ) ^
            (-(((1 - eta : ℝ) : ℂ) + Complex.I * (t : ℂ)))‖ :=
        norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.range H, (N : ℝ) ^ (-(1 - eta)) := by
        apply Finset.sum_le_sum
        intro n hn
        exact (hterm n).trans (hterm' n)
  have hpow :
      (N : ℝ) * (N : ℝ) ^ (-(1 - eta)) = (N : ℝ) ^ eta := by
    calc
      (N : ℝ) * (N : ℝ) ^ (-(1 - eta)) =
          (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-(1 - eta)) := by
            rw [Real.rpow_one]
      _ = (N : ℝ) ^ ((1 : ℝ) + (-(1 - eta))) :=
        (Real.rpow_add hNpos _ _).symm
      _ = (N : ℝ) ^ eta := by ring_nf
  calc
    _ ≤ ∑ n ∈ Finset.range H, (N : ℝ) ^ (-(1 - eta)) := hsum
    _ = (H : ℝ) * (N : ℝ) ^ (-(1 - eta)) := by simp
    _ ≤ (N : ℝ) * (N : ℝ) ^ (-(1 - eta)) := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hH)
        (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    _ = (N : ℝ) ^ eta := hpow

theorem exists_uniform_common_block_bound :
    ∃ R : ℝ, 2 ≤ R ∧ ∀ (N H : ℕ) (t u eta : ℝ),
      1 ≤ N → H ≤ N → 2 ≤ t → 0 ≤ u → u ≤ 1 →
      0 ≤ eta → eta ≤ (1 : ℝ) / 2 → (N : ℝ) ≤ t ^ 2 →
      ‖∑ n ∈ Finset.range H,
          (((N + n : ℕ) : ℝ) + u : ℂ) ^
            (-(((1 - eta : ℝ) : ℂ) + Complex.I * (t : ℂ)))‖ ≤
        commonEnvelope R t eta := by
  obtain ⟨N0, hgrowth⟩ := FordWeightedGrowthBlock.norm_weighted_growth_block
  let R : ℝ := max N0 2
  have hR2 : 2 ≤ R := by dsimp [R]; exact le_max_right _ _
  have hRN0 : N0 ≤ R := by dsimp [R]; exact le_max_left _ _
  refine ⟨R, hR2, ?_⟩
  intro N H t u eta hN hH ht hu hu1 heta hetaHalf hNt2
  have hRnonneg : 0 ≤ R := by linarith
  have hCnonneg : 0 ≤ commonEnvelope R t eta := by
    dsimp [commonEnvelope]
    positivity
  by_cases hNR : (N : ℝ) < R
  · have htriv := norm_actual_block_le_rpow
      (N := N) (H := H) (t := t) (u := u) (eta := eta)
      hN hH hu heta (by linarith)
    have hNleR : (N : ℝ) ≤ R := le_of_lt hNR
    have hNpow_le : (N : ℝ) ^ eta ≤ R := by
      have hNone : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      have hNpow : (N : ℝ) ^ eta ≤ (N : ℝ) := by
        calc
          (N : ℝ) ^ eta ≤ (N : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hNone (by linarith)
          _ = (N : ℝ) := Real.rpow_one _
      exact hNpow.trans hNleR
    exact htriv.trans (hNpow_le.trans (by
      dsimp [commonEnvelope]
      nlinarith [Real.exp_pos (1000 * eta * (Real.log t) ^ ((4 : ℝ) / 5)),
        Real.exp_pos (eta * Real.sqrt (eta / savingCoeff) * Real.log t),
        Real.pi_pos]))
  · have hRN : R ≤ (N : ℝ) := le_of_not_gt hNR
    have hN2 : 2 ≤ N := by
      have : (2 : ℝ) ≤ (N : ℝ) := hR2.trans hRN
      exact_mod_cast this
    by_cases hsmalllog : Real.log (N : ℝ) <
        1000 * (Real.log t) ^ ((4 : ℝ) / 5)
    · have htriv := norm_actual_block_le_rpow
        (N := N) (H := H) (t := t) (u := u) (eta := eta)
        hN hH hu heta (by linarith)
      have hlogN_nonneg : 0 ≤ Real.log (N : ℝ) := by
        exact Real.log_nonneg (by exact_mod_cast hN)
      have hpowexp : (N : ℝ) ^ eta ≤
          Real.exp (1000 * eta * (Real.log t) ^ ((4 : ℝ) / 5)) := by
        rw [Real.rpow_def_of_pos (by positivity)]
        apply Real.exp_le_exp.mpr
        have hm := mul_le_mul_of_nonneg_left (le_of_lt hsmalllog) heta
        nlinarith [hm]
      exact htriv.trans (hpowexp.trans (by
        dsimp [commonEnvelope]
        nlinarith [Real.exp_pos (eta * Real.sqrt (eta / savingCoeff) * Real.log t),
          Real.pi_pos]))
    · have hthreshold : 1000 * (Real.log t) ^ ((4 : ℝ) / 5) ≤
          Real.log (N : ℝ) := le_of_not_gt hsmalllog
      by_cases htN : t ≤ (N : ℝ)
      · have hlong := FordWeightedLongBlock.norm_weighted_long_block
          hN2 hH (by linarith) htN hu hu1 heta (by linarith)
        have hratio : (N : ℝ) ^ eta / t ≤ 1 := by
          have hNpow_sq : (N : ℝ) ^ eta ≤ (t ^ 2) ^ eta :=
            Real.rpow_le_rpow (by positivity) hNt2 heta
          have hsq : (t ^ 2) ^ eta = t ^ (2 * eta) := by
            have hpow := Real.rpow_mul (le_of_lt (by linarith : 0 < t))
              (2 : ℝ) eta
            norm_num [Real.rpow_natCast] at hpow ⊢
            exact hpow.symm
          have hNpow : (N : ℝ) ^ eta ≤ t := by
            calc
              _ ≤ t ^ (2 * eta) := hsq ▸ hNpow_sq
              _ ≤ t ^ (1 : ℝ) := by
                exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
              _ = t := Real.rpow_one t
          exact (div_le_iff₀ (by linarith)).2 (by simpa using hNpow)
        have hlong' : ‖∑ n ∈ Finset.range H,
            (((N + n : ℕ) : ℝ) + u : ℂ) ^
              (-(((1 - eta : ℝ) : ℂ) + Complex.I * (t : ℂ)))‖ ≤
            12 * Real.pi := by
          calc
            _ ≤ 12 * Real.pi * (N : ℝ) ^ eta / t := hlong
            _ = 12 * Real.pi * ((N : ℝ) ^ eta / t) := by ring
            _ ≤ 12 * Real.pi := by
              simpa only [mul_one] using
                (mul_le_mul_of_nonneg_left hratio
                  (by positivity : 0 ≤ 12 * Real.pi))
        have hE1 : 0 ≤ Real.exp (1000 * eta * (Real.log t) ^ ((4 : ℝ) / 5)) :=
          (Real.exp_pos _).le
        have hE2 : 0 ≤ 272 * Real.exp
            (eta * Real.sqrt (eta / savingCoeff) * Real.log t) := by positivity
        have hPi : 0 ≤ 12 * Real.pi := by positivity
        exact hlong'.trans (by
          dsimp [commonEnvelope]
          linarith [hRnonneg, hE1, hE2])
      · have htN' : (N : ℝ) ≤ t := le_of_not_ge htN
        have hratio : 1 ≤ Real.log t / Real.log (N : ℝ) := by
          have hlogNpos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN2)
          rw [le_div_iff₀ hlogNpos]
          simpa using (Real.log_le_log (by positivity) htN')
        have hgrowth' := hgrowth N H t u eta
          (hRN0.trans hRN) hH (by linarith) hu hu1 heta (by linarith)
          hratio hthreshold
        have hE1 : 0 ≤ Real.exp (1000 * eta * (Real.log t) ^ ((4 : ℝ) / 5)) :=
          (Real.exp_pos _).le
        have hPi : 0 ≤ 12 * Real.pi := by positivity
        exact hgrowth'.trans (by
          dsimp [commonEnvelope]
          nlinarith [hRnonneg, hE1, hPi])

theorem finite_sum_le_common_envelope :
    ∃ R : ℝ, 2 ≤ R ∧ ∀ (M r : ℕ) (t u eta : ℝ),
      1 ≤ M → M ≤ 2 ^ r → M ≤ t ^ 2 → 2 ≤ t →
      0 ≤ u → u ≤ 1 → 0 ≤ eta → eta ≤ (1 : ℝ) / 2 →
      ‖∑ n ∈ Finset.range (M - 1),
          (((n + 1 : ℕ) : ℝ) + u : ℂ) ^
            (-(((1 - eta : ℝ) : ℂ) + Complex.I * (t : ℂ)))‖ ≤
        (r : ℝ) * commonEnvelope R t eta := by
  obtain ⟨R, hR2, hblock⟩ := exists_uniform_common_block_bound
  refine ⟨R, hR2, ?_⟩
  intro M r t u eta hM hMr hMt ht hu hu1 heta hetaHalf
  let z : ℕ → ℂ := fun n ↦
    (((n : ℝ) + u : ℂ) ^
      (-(((1 - eta : ℝ) : ℂ) + Complex.I * (t : ℂ))))
  have hCnonneg : 0 ≤ commonEnvelope R t eta := by
    dsimp [commonEnvelope]
    positivity
  calc
    _ ≤ ∑ j ∈ Finset.range r, commonEnvelope R t eta := by
      apply FordOffsetDyadicPartition.norm_sum_range_sub_one_le_sum_block_bounds
        z hM hMr (fun _ ↦ commonEnvelope R t eta)
      intro j hj
      let N : ℕ := 2 ^ j
      by_cases hNM : M ≤ N
      · rw [FordOffsetDyadicPartition.offsetDyadicBlock]
        have hMN2 : M ≤ 2 * (2 ^ j) := by omega
        have hmin : min M (2 * (2 ^ j)) = M := min_eq_left hMN2
        rw [hmin]
        have hempty : M - 2 ^ j = 0 := by omega
        simpa [hempty] using hCnonneg
      · have hNM' : N < M := Nat.lt_of_not_ge hNM
        have hN : 1 ≤ N := by
          dsimp [N]
          have hp : 0 < 2 ^ j := by positivity
          omega
        have hH : min M (2 * N) - N ≤ N :=
          FordOffsetDyadicPartition.offsetDyadicBlock_length_le z M j
        have hNreal : (N : ℝ) ≤ t ^ 2 := by
          have hNMcast : (N : ℝ) < (M : ℝ) := by exact_mod_cast hNM'
          exact hNMcast.le.trans hMt
        have hb := hblock N (min M (2 * N) - N) t u eta
          hN hH ht hu hu1 heta hetaHalf hNreal
        simpa [FordOffsetDyadicPartition.offsetDyadicBlock, N, z] using hb
    _ = (r : ℝ) * commonEnvelope R t eta := by simp

end FordFiniteGrowthBound

#print axioms FordFiniteGrowthBound.norm_actual_block_le_rpow
#print axioms FordFiniteGrowthBound.exists_uniform_common_block_bound
#print axioms FordFiniteGrowthBound.finite_sum_le_common_envelope
