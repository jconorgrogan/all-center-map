import FordWRiemann

open scoped BigOperators
noncomputable section
namespace FordUniformEnvelope
open FordWEnvelopeScalar

def envelopeSum (K : ℕ) (lam : ℝ) : ℝ :=
  ∑ i ∈ Finset.range K, lam * envelope (((i + 1 : ℕ) : ℝ) / lam)

def rawSaving (K : ℕ) (lam : ℝ) : ℝ :=
  mu2 * (K : ℝ) * (K + 1) / 2 - envelopeSum K lam -
    eps * (mu1 + mu2) * (K : ℝ) ^ 2

/-- Literal finite envelope sum for a variable scale above b*K. -/
theorem envelope_sum_le (K : ℕ) {lam : ℝ} (hpos : 0 < lam)
    (hlow : b * (K : ℝ) ≤ lam) :
    envelopeSum K lam ≤ lam ^ 2 * envelopeIntegral + (K : ℝ) / 2 := by
  have hx0 : 0 ≤ (K : ℝ) / lam := by positivity
  have hx1 : (K : ℝ) / lam ≤ 2500 / 1623 := by
    apply (div_le_iff₀ hpos).mpr
    norm_num [b] at hlow ⊢
    nlinarith
  have hint := FordWRiemann.envelope_partial_integral_le hx0 hx1
  have hr := FordWRiemann.right_sum_le envelope_lipschitz_one K (h := 1 / lam) (by positivity)
  simp only [mul_one_div] at hr
  have hbound : (1 / lam) *
      (∑ i ∈ Finset.range K, envelope (((i + 1 : ℕ) : ℝ) / lam)) ≤
      envelopeIntegral + (K : ℝ) * (1 / lam) ^ 2 / 2 := by linarith
  unfold envelopeSum
  calc
    _ = lam * (∑ i ∈ Finset.range K,
        envelope (((i + 1 : ℕ) : ℝ) / lam)) := by rw [Finset.mul_sum]
    _ = lam ^ 2 * ((1 / lam) *
        (∑ i ∈ Finset.range K, envelope (((i + 1 : ℕ) : ℝ) / lam))) := by field_simp
    _ ≤ lam ^ 2 * (envelopeIntegral + (K : ℝ) * (1 / lam) ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left hbound (sq_nonneg _)
    _ = lam ^ 2 * envelopeIntegral + (K : ℝ) / 2 := by field_simp

private theorem slab_quadratic_pos {k : ℝ} (hk : 2000 ≤ k) :
    0 < (17460190897 / 4720396875000 : ℝ) * k ^ 2 -
      (29060066449573 / 49031706420000 : ℝ) * k -
      (529631531821 / 3978922975983 : ℝ) := by
  have hA : (0 : ℝ) < 17460190897 / 4720396875000 := by norm_num
  have hbase : (0 : ℝ) < (17460190897 / 4720396875000 : ℝ) * 2000 ^ 2 -
      (29060066449573 / 49031706420000 : ℝ) * 2000 -
      (529631531821 / 3978922975983 : ℝ) := by norm_num
  have hderiv : (0 : ℝ) < 2 * (17460190897 / 4720396875000 : ℝ) * 2000 -
      (29060066449573 / 49031706420000 : ℝ) := by norm_num
  nlinarith [sq_nonneg (k - 2000)]

/-- Uniform scalar saving throughout the entire closed scale slab. -/
theorem raw_saving_ge_target {K : ℕ} {lam : ℝ} (hK : 2000 ≤ K)
    (hlow : b * (K : ℝ) ≤ lam) (hupp : lam ≤ b * (K : ℝ) + 1) :
    (K : ℝ) ^ 2 / 50 ≤ rawSaving K lam := by
  have hb : 0 < b := by norm_num [b]
  have hk0 : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hpos : 0 < lam := (mul_pos hb hk0).trans_le hlow
  have hs := envelope_sum_le K hpos hlow
  have hsq : lam ^ 2 ≤ (b * (K : ℝ) + 1) ^ 2 := pow_le_pow_left₀ hpos.le hupp 2
  have hI : 0 ≤ envelopeIntegral := by norm_num [envelopeIntegral]
  have hmul : lam ^ 2 * envelopeIntegral ≤ (b * (K : ℝ) + 1) ^ 2 * envelopeIntegral :=
    mul_le_mul_of_nonneg_right hsq hI
  have hsum : envelopeSum K lam ≤ (b * (K : ℝ) + 1) ^ 2 * envelopeIntegral + (K : ℝ) / 2 :=
    hs.trans (add_le_add hmul le_rfl)
  have hquad := slab_quadratic_pos (k := (K : ℝ)) (by exact_mod_cast hK)
  unfold rawSaving
  norm_num [mu1, mu2, b, eps, envelopeIntegral] at hsum ⊢
  nlinarith

/-- A floor choice covers every sufficiently large real scale by a valid slab. -/
theorem floor_degree_slab {lam : ℝ} (hlam : 2000 * b ≤ lam) :
    let K := ⌊lam / b⌋₊
    2000 ≤ K ∧ b * (K : ℝ) ≤ lam ∧ lam ≤ b * (K : ℝ) + 1 := by
  have hb : 0 < b := by norm_num [b]
  have hb1 : b ≤ 1 := by norm_num [b]
  have hratio : (2000 : ℝ) ≤ lam / b := (le_div_iff₀ hb).mpr (by nlinarith)
  have hratio0 : 0 ≤ lam / b := by linarith
  have hK : 2000 ≤ ⌊lam / b⌋₊ := (Nat.le_floor_iff hratio0).mpr (by simpa using hratio)
  have hfl := Nat.floor_le hratio0
  have hfu := Nat.lt_floor_add_one (lam / b)
  have hlo : b * (⌊lam / b⌋₊ : ℝ) ≤ lam := by
    have h := (le_div_iff₀ hb).mp hfl
    nlinarith
  have hup : lam ≤ b * (⌊lam / b⌋₊ : ℝ) + 1 := by
    have h := (div_lt_iff₀ hb).mp hfu
    nlinarith
  exact ⟨hK, hlo, hup⟩

theorem raw_saving_floor_degree {lam : ℝ} (hlam : 2000 * b ≤ lam) :
    ((⌊lam / b⌋₊ : ℕ) : ℝ) ^ 2 / 50 ≤ rawSaving ⌊lam / b⌋₊ lam := by
  obtain ⟨hK, hlo, hup⟩ := floor_degree_slab hlam
  exact raw_saving_ge_target hK hlo hup

end FordUniformEnvelope
#print axioms FordUniformEnvelope.envelope_sum_le
#print axioms FordUniformEnvelope.raw_saving_ge_target
#print axioms FordUniformEnvelope.floor_degree_slab
#print axioms FordUniformEnvelope.raw_saving_floor_degree
