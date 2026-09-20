import FordWEnvelopeScalar
noncomputable section
namespace FordScaleFloor
/-- Ordinary floor has uniform factor-two comparability above one. -/
theorem floor_comparable {x : ℝ} (hx : 1 ≤ x) :
    1 ≤ Nat.floor x ∧ (Nat.floor x : ℝ) ≤ x ∧ x / 2 ≤ (Nat.floor x : ℝ) := by
  have hone : 1 ≤ Nat.floor x := (Nat.one_le_floor_iff x).mpr hx
  have honeR : (1 : ℝ) ≤ Nat.floor x := by exact_mod_cast hone
  have hlt := Nat.lt_floor_add_one x
  exact ⟨hone, Nat.floor_le (by linarith), by linarith⟩

/-- The concrete natural scale used by the source envelope. -/
def scale (N : ℕ) (mu : ℝ) : ℕ := Nat.floor ((N : ℝ) ^ mu)

theorem scale_comparable {N : ℕ} {mu : ℝ} (hN : 1 ≤ N) (hmu : 0 ≤ mu) :
    1 ≤ scale N mu ∧ (scale N mu : ℝ) ≤ (N : ℝ) ^ mu ∧
      (N : ℝ) ^ mu / 2 ≤ (scale N mu : ℝ) := by
  apply floor_comparable
  exact Real.one_le_rpow (by exact_mod_cast hN) hmu

theorem scale_le_base {N : ℕ} {mu : ℝ} (hN : 1 ≤ N)
    (hmu : 0 ≤ mu) (hmu1 : mu ≤ 1) : scale N mu ≤ N := by
  have hc := (scale_comparable hN hmu).2.1
  have hp : (N : ℝ) ^ mu ≤ (N : ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) hmu1
  exact_mod_cast hc.trans hp

theorem ford_scales {N : ℕ} (hN : 1 ≤ N) :
    1 ≤ scale N FordWEnvelopeScalar.mu1 ∧
    1 ≤ scale N FordWEnvelopeScalar.mu2 ∧
    (N : ℝ) ^ FordWEnvelopeScalar.mu1 / 2 ≤ scale N FordWEnvelopeScalar.mu1 ∧
    (scale N FordWEnvelopeScalar.mu2 : ℝ) ≤ (N : ℝ) ^ FordWEnvelopeScalar.mu2 ∧
    scale N FordWEnvelopeScalar.mu1 ≤ N ∧
    scale N FordWEnvelopeScalar.mu2 ≤ N := by
  have h1 := scale_comparable (mu := FordWEnvelopeScalar.mu1) hN (by norm_num)
  have h2 := scale_comparable (mu := FordWEnvelopeScalar.mu2) hN (by norm_num)
  exact ⟨h1.1, h2.1, h1.2.2, h2.2.1,
    scale_le_base hN (by norm_num) (by norm_num),
    scale_le_base hN (by norm_num) (by norm_num)⟩
end FordScaleFloor
#print axioms FordScaleFloor.ford_scales
