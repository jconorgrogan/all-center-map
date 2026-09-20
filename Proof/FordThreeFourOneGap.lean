import FordFinitePoleReal

noncomputable section
namespace FordThreeFourOneGap

/-- A literal three-four gap forces a one-percent lower bound for `ε`. -/
theorem delta_div_100_le_epsilon
    {δ ε R : ℝ}
    (hδ : 0 < δ) (hε : 0 ≤ ε) (hR : δ * R ≤ (1 : ℝ) / 2)
    (hgap : 4 / (δ + ε) ≤ 3 / δ + R) :
    δ / 100 ≤ ε := by
  have hsum : 0 < δ + ε := by linarith
  by_contra hnot
  have hεlt : ε < δ / 100 := lt_of_not_ge hnot
  have hcross := (div_le_iff₀ hsum).mp hgap
  have hcross' : 4 * δ ≤ (3 + δ * R) * (δ + ε) := by
    calc
      4 * δ = δ * 4 := by ring
      _ ≤ δ * ((3 / δ + R) * (δ + ε)) :=
        mul_le_mul_of_nonneg_left hcross hδ.le
      _ = (3 + δ * R) * (δ + ε) := by
        field_simp
  nlinarith [mul_pos hδ hsum]

end FordThreeFourOneGap

#print axioms FordThreeFourOneGap.delta_div_100_le_epsilon
