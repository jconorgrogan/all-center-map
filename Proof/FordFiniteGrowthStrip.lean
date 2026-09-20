import FordFiniteGrowthBound
import FordHurwitzFirstLeaf

open scoped BigOperators ComplexConjugate
noncomputable section

namespace FordFiniteGrowthStrip

open FordFiniteGrowthBound

private lemma cpow_strip_term
    {n : ℕ} {u sigma eta t : ℝ}
    (hu : 0 ≤ u) (heta : 0 ≤ eta) (hsigma : 1 - eta ≤ sigma) :
    (((n + 1 : ℕ) : ℝ) + u : ℂ) ^
        (-((sigma : ℂ) + Complex.I * (t : ℂ))) =
      ((((n + 1 : ℕ) : ℝ) + u) ^ (-(sigma - (1 - eta)))) •
        ((((n + 1 : ℕ) : ℝ) + u : ℂ) ^
          (-(((1 - eta : ℝ) : ℂ) + Complex.I * (t : ℂ)))) := by
  have hpos : 0 < ((n + 1 : ℕ) : ℝ) + u := by positivity
  have hsig0 := FordHurwitz.cpow_neg_real_add_imag_eq_weight_phase
    (u := u) (σ := sigma) (t := t) (n := n + 1) hpos
  have hsig1 := FordHurwitz.cpow_neg_real_add_imag_eq_weight_phase
    (u := u) (σ := 1 - eta) (t := t) (n := n + 1) hpos
  have hsig0' : (((n + 1 : ℕ) : ℝ) + u : ℂ) ^
        (-((sigma : ℂ) + Complex.I * (t : ℂ))) =
      ((((n + 1 : ℕ) : ℝ) + u) ^ (-sigma)) •
        FordHurwitz.phase u t (n + 1) := by
    simpa [Nat.cast_add, Nat.cast_one, Complex.ofReal_add] using hsig0
  have hsig1' : (((n + 1 : ℕ) : ℝ) + u : ℂ) ^
        (-(((1 - eta : ℝ) : ℂ) + Complex.I * (t : ℂ))) =
      ((((n + 1 : ℕ) : ℝ) + u) ^ (-(1 - eta))) •
        FordHurwitz.phase u t (n + 1) := by
    simpa [Nat.cast_add, Nat.cast_one, Complex.ofReal_add] using hsig1
  rw [hsig0', hsig1']
  simp only [smul_smul]
  rw [← Real.rpow_add hpos]
  congr 2
  ring

theorem finite_sum_le_common_envelope_strip :
    ∃ R : ℝ, 2 ≤ R ∧ ∀ (M r : ℕ) (t u eta sigma : ℝ),
      1 ≤ M → M ≤ 2 ^ r → M ≤ t ^ 2 → 2 ≤ t →
      0 ≤ u → u ≤ 1 → 0 ≤ eta → eta ≤ (1 : ℝ) / 2 →
      1 - eta ≤ sigma →
      ‖∑ n ∈ Finset.range (M - 1),
          (((n + 1 : ℕ) : ℝ) + u : ℂ) ^
            (-((sigma : ℂ) + Complex.I * (t : ℂ)))‖ ≤
        (r : ℝ) * commonEnvelope R t eta := by
  obtain ⟨R, hR, hbase⟩ := FordFiniteGrowthBound.finite_sum_le_common_envelope
  refine ⟨R, hR, ?_⟩
  intro M r t u eta sigma hM hMr hMt ht hu hu1 heta hetaHalf hsigma
  let sigma0 : ℝ := 1 - eta
  let d : ℝ := sigma - sigma0
  let B : ℝ := (r : ℝ) * commonEnvelope R t eta
  have hd : 0 ≤ d := by dsimp [d, sigma0]; linarith
  have hB : 0 ≤ B := by
    dsimp [B, commonEnvelope]
    positivity
  let w : ℕ → ℝ := fun n => (((n + 1 : ℕ) : ℝ) + u) ^ (-d)
  let z : ℕ → ℂ := fun n =>
    (((n + 1 : ℕ) : ℝ) + u : ℂ) ^
      (-(((sigma0 : ℝ) : ℂ) + Complex.I * (t : ℂ)))
  have hw0 : ∀ n, 0 ≤ w n := by
    intro n
    dsimp [w]
    positivity
  have hw : Antitone w := by
    intro i j hij
    dsimp [w]
    apply Real.rpow_le_rpow_of_nonpos
    · positivity
    · have hnat : i + 1 ≤ j + 1 := by omega
      have hreal : ((i + 1 : ℕ) : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by
        exact_mod_cast hnat
      linarith
    · linarith
  have hprefix : ∀ q, q ≤ M - 1 →
      ‖∑ i ∈ Finset.range q, z i‖ ≤ B := by
    intro q hq
    have hqM : q + 1 ≤ M := by omega
    have hq1 : 1 ≤ q + 1 := by omega
    have hqpow : q + 1 ≤ 2 ^ r := hqM.trans hMr
    have hqt2 : ((q + 1 : ℕ) : ℝ) ≤ t ^ 2 := by
      have hqcast : ((q + 1 : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast hqM
      exact hqcast.trans hMt
    have hb := hbase (q + 1) r t u eta hq1 hqpow hqt2 ht hu hu1 heta hetaHalf
    simpa [z, sigma0] using hb
  have hcore := FordHurwitz.norm_weighted_range_le_first
    (r := M - 1) (M := B) hB hw0 hw hprefix
  have hweighted :
      (∑ n ∈ Finset.range (M - 1),
        (((n + 1 : ℕ) : ℝ) + u : ℂ) ^
          (-((sigma : ℂ) + Complex.I * (t : ℂ)))) =
      ∑ n ∈ Finset.range (M - 1), w n • z n := by
    apply Finset.sum_congr rfl
    intro n hn
    exact cpow_strip_term hu heta hsigma
  have hw_le_one : w 0 ≤ 1 := by
    dsimp [w]
    have hbase : (1 : ℝ) ≤ (1 : ℝ) + u := by linarith
    have hpow := Real.rpow_le_rpow_of_nonpos (show (0 : ℝ) < 1 by norm_num)
      hbase (neg_nonpos.mpr hd)
    simpa using hpow
  rw [hweighted]
  calc
    ‖∑ n ∈ Finset.range (M - 1), w n • z n‖ ≤ w 0 * B := hcore
    _ ≤ B := by
      exact (mul_le_of_le_one_left hB hw_le_one)

end FordFiniteGrowthStrip

#print axioms FordFiniteGrowthStrip.finite_sum_le_common_envelope_strip
