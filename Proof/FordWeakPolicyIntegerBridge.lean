import Mathlib
import FordWeakEndpointPolynomial

namespace MAPFordWeakPolicy

noncomputable section
set_option maxHeartbeats 900000

def fordPhi1 (k Delta A : ℝ) : ℝ :=
  1 / (2 * (k - A)) +
    (k ^ 2 + k + (k - A) ^ 2 - (k - A) + 2 * (k - 1) - 2 * Delta) /
      (4 * k * (k - A) ^ 2)

def fordDeltaNext (k Delta A : ℝ) : ℝ :=
  Delta * (1 - fordPhi1 k Delta A) - k +
    fordPhi1 k Delta A * (k ^ 2 + k + (k - A) ^ 2 - (k - A)) / 2 +
    k * fordPhi1 k Delta A

theorem ford_j2_normalized_identity
    {k Delta A : ℝ} (hk0 : 0 < k) (hR0 : 0 < k - A) :
    (Delta - fordDeltaNext k Delta A) / k =
      1 -
        (1 - (A / k) + (A / k) ^ 2 / 2 - Delta / k ^ 2 +
            (1 / k) * ((A / k) / 2 + 1)) *
          (1 - (A / k) +
              (1 - (A / k) + (A / k) ^ 2 / 2 - Delta / k ^ 2 +
                (1 / k) * ((A / k) / 2 + 1)) - (1 / k) ^ 2) /
            (2 * (1 - A / k) ^ 2) := by
  dsimp [fordDeltaNext, fordPhi1]
  field_simp [ne_of_gt hk0, ne_of_gt hR0]
  ring

theorem policy_ceiling_bounds
    {k Delta : ℝ} (hk : 200 ≤ k) (hk0 : 0 < k)
    (hD0 : k ^ 2 / 100 ≤ Delta)
    (hD1 : Delta ≤ (k ^ 2 - k) / 2) :
    let x : ℝ := Delta / k ^ 2
    let A : ℝ := max 1 (Nat.ceil (Delta / k - 1) : ℝ)
    let R : ℝ := k - A
    1 ≤ A ∧ A ≤ k / 2 ∧ 4 ≤ R ∧ R < k ∧
      x - 1 / k ≤ A / k ∧ A / k ≤ x := by
  dsimp
  let y : ℝ := Delta / k - 1
  have hy1 : 1 ≤ y := by
    dsimp [y]
    have hk100 : 2 ≤ k / 100 := by nlinarith
    have : k / 100 ≤ Delta / k := by
      apply (le_div_iff₀ hk0).2
      nlinarith
    nlinarith
  have hy0 : 0 ≤ y := le_trans (by norm_num) hy1
  have hypos : 0 < y := lt_of_lt_of_le (by norm_num) hy1
  have hceil_lo : y ≤ (Nat.ceil y : ℝ) := Nat.le_ceil y
  have hceil_hi : (Nat.ceil y : ℝ) < y + 1 := Nat.ceil_lt_add_one hy0
  have hAeq : max 1 (Nat.ceil y : ℝ) = (Nat.ceil y : ℝ) := by
    rw [max_eq_right]
    exact_mod_cast (Nat.one_le_ceil_iff.mpr hypos)
  have hAlo : 1 ≤ (Nat.ceil y : ℝ) := by
    exact_mod_cast (Nat.one_le_ceil_iff.mpr hypos)
  have hAhi : (Nat.ceil y : ℝ) < Delta / k := by
    dsimp [y] at hceil_hi
    linarith
  have hDkhi : Delta / k ≤ (k - 1) / 2 := by
    apply (div_le_iff₀ hk0).2
    nlinarith
  have hA_half : (Nat.ceil y : ℝ) ≤ k / 2 := by
    have := le_of_lt hAhi
    nlinarith
  have hRlo : 4 ≤ k - (Nat.ceil y : ℝ) := by nlinarith
  have hRhi : k - (Nat.ceil y : ℝ) < k := by nlinarith
  have hxlo : Delta / k ^ 2 - 1 / k ≤ (Nat.ceil y : ℝ) / k := by
    have h := hceil_lo
    dsimp [y] at h
    have heq : Delta / k ^ 2 - 1 / k = (Delta / k - 1) / k := by
      field_simp
    rw [heq]
    exact (div_le_div_iff_of_pos_right hk0).2 h
  have hxhi : (Nat.ceil y : ℝ) / k ≤ Delta / k ^ 2 := by
    have h := le_of_lt hAhi
    have heq : Delta / k ^ 2 = (Delta / k) / k := by
      field_simp
    rw [heq]
    exact (div_le_div_iff_of_pos_right hk0).2 h
  rw [hAeq]
  exact ⟨hAlo, hA_half, hRlo, hRhi, hxlo, hxhi⟩

theorem policy_high_contraction
    {k Delta : ℝ} (hk : 200 ≤ k) (hk0 : 0 < k)
    (hD0 : k ^ 2 / 10 ≤ Delta)
    (hD1 : Delta ≤ (k ^ 2 - k) / 2) :
    let A : ℝ := max 1 (Nat.ceil (Delta / k - 1) : ℝ)
    (7 : ℝ) * (Delta / k ^ 2) / 5 ≤
      (Delta - fordDeltaNext k Delta A) / k := by
  dsimp
  let A : ℝ := max 1 (Nat.ceil (Delta / k - 1) : ℝ)
  have hp := policy_ceiling_bounds hk hk0 (by nlinarith [hD0]) hD1
  rcases hp with ⟨hA1, hAhalf, hR4, hRk, hxl, hxu⟩
  let x : ℝ := Delta / k ^ 2
  let t : ℝ := 1 / k
  let v : ℝ := Delta / k - A
  have hx0 : (1 / 10 : ℝ) ≤ x := by
    dsimp [x]
    apply (le_div_iff₀ (sq_pos_of_pos hk0)).2
    nlinarith [hD0]
  have hx1 : x ≤ (1 / 2 : ℝ) := by
    dsimp [x]
    apply (div_le_iff₀ (sq_pos_of_pos hk0)).2
    nlinarith
  have ht0 : 0 ≤ t := by
    dsimp [t]
    exact (one_div_pos.mpr hk0).le
  have ht1 : t ≤ (1 / 200 : ℝ) := by
    dsimp [t]
    apply (div_le_iff₀ hk0).2
    nlinarith
  have hAupper : A ≤ Delta / k := by
    have h := hxu
    change A / k ≤ Delta / k ^ 2 at h
    have hh := (div_le_iff₀ hk0).1 h
    calc
      A ≤ (Delta / k ^ 2) * k := hh
      _ = Delta / k := by field_simp
  have hAlower : Delta / k - 1 ≤ A := by
    have h := hxl
    change Delta / k ^ 2 - 1 / k ≤ A / k at h
    have h' : (Delta / k - 1) / k ≤ A / k := by
      convert h using 1 <;> field_simp <;> ring
    have hh := (div_le_iff₀ hk0).1 h'
    calc
      Delta / k - 1 ≤ (A / k) * k := hh
      _ = A := by field_simp
  have hv0 : 0 ≤ v := by dsimp [v]; linarith [hAupper]
  have hv1 : v ≤ 1 := by
    dsimp [v]
    linarith [hAlower]
  have hF := MAPFordWeakEndpoint.first_full_contraction hx0 hx1 ht0 ht1 hv0 hv1
  have hz : x - v * t = A / k := by
    dsimp [x, v, t]
    field_simp [ne_of_gt hk0]
    ring
  have hID := ford_j2_normalized_identity (k := k) (Delta := Delta) (A := A)
      hk0 (by linarith [hR4])
  calc
    (7 : ℝ) * (Delta / k ^ 2) / 5 = (7 : ℝ) * x / 5 := by rfl
    _ ≤ 1 -
        (1 - (x - v * t) + (x - v * t) ^ 2 / 2 - x +
            t * ((x - v * t) / 2 + 1)) *
          (1 - (x - v * t) +
              (1 - (x - v * t) + (x - v * t) ^ 2 / 2 - x +
                t * ((x - v * t) / 2 + 1)) - t ^ 2) /
            (2 * (1 - (x - v * t)) ^ 2) := hF
    _ = (Delta - fordDeltaNext k Delta A) / k := by
      rw [hz]
      dsimp [x, t]
      rw [← hID]

theorem policy_low_contraction
    {k Delta : ℝ} (hk : 200 ≤ k) (hk0 : 0 < k)
    (hD0 : k ^ 2 / 100 ≤ Delta)
    (hD1 : Delta ≤ k ^ 2 / 10) :
    let A : ℝ := max 1 (Nat.ceil (Delta / k - 1) : ℝ)
    (3 : ℝ) * (Delta / k ^ 2) / 2 - 1 / 125 ≤
      (Delta - fordDeltaNext k Delta A) / k := by
  dsimp
  let A : ℝ := max 1 (Nat.ceil (Delta / k - 1) : ℝ)
  have hp := policy_ceiling_bounds hk hk0 hD0 (by nlinarith [hD1, hk0])
  rcases hp with ⟨hA1, hAhalf, hR4, hRk, hxl, hxu⟩
  let x : ℝ := Delta / k ^ 2
  let t : ℝ := 1 / k
  let v : ℝ := Delta / k - A
  have hx0 : (1 / 100 : ℝ) ≤ x := by
    dsimp [x]
    apply (le_div_iff₀ (sq_pos_of_pos hk0)).2
    nlinarith [hD0]
  have hx1 : x ≤ (1 / 10 : ℝ) := by
    dsimp [x]
    apply (div_le_iff₀ (sq_pos_of_pos hk0)).2
    nlinarith [hD1]
  have ht0 : 0 ≤ t := by
    dsimp [t]
    exact (one_div_pos.mpr hk0).le
  have ht1 : t ≤ (1 / 200 : ℝ) := by
    dsimp [t]
    apply (div_le_iff₀ hk0).2
    nlinarith
  have hAupper : A ≤ Delta / k := by
    have h := hxu
    change A / k ≤ Delta / k ^ 2 at h
    have hh := (div_le_iff₀ hk0).1 h
    calc
      A ≤ (Delta / k ^ 2) * k := hh
      _ = Delta / k := by field_simp
  have hAlower : Delta / k - 1 ≤ A := by
    have h := hxl
    change Delta / k ^ 2 - 1 / k ≤ A / k at h
    have h' : (Delta / k - 1) / k ≤ A / k := by
      convert h using 1 <;> field_simp <;> ring
    have hh := (div_le_iff₀ hk0).1 h'
    calc
      Delta / k - 1 ≤ (A / k) * k := hh
      _ = A := by field_simp
  have hv0 : 0 ≤ v := by dsimp [v]; linarith [hAupper]
  have hv1 : v ≤ 1 := by dsimp [v]; linarith [hAlower]
  have hF := MAPFordWeakEndpoint.second_full_contraction hx0 hx1 ht0 ht1 hv0 hv1
  have hz : x - v * t = A / k := by
    dsimp [x, v, t]
    field_simp [ne_of_gt hk0]
    ring
  have hID := ford_j2_normalized_identity (k := k) (Delta := Delta) (A := A)
      hk0 (by linarith [hR4])
  calc
    (3 : ℝ) * (Delta / k ^ 2) / 2 - 1 / 125 = (3 : ℝ) * x / 2 - 1 / 125 := by rfl
    _ ≤ 1 -
        (1 - (x - v * t) + (x - v * t) ^ 2 / 2 - x +
            t * ((x - v * t) / 2 + 1)) *
          (1 - (x - v * t) +
              (1 - (x - v * t) + (x - v * t) ^ 2 / 2 - x +
                t * ((x - v * t) / 2 + 1)) - t ^ 2) /
            (2 * (1 - (x - v * t)) ^ 2) := hF
    _ = (Delta - fordDeltaNext k Delta A) / k := by
      rw [hz]
      dsimp [x, t]
      rw [← hID]

/- The ceiling policy is expressed over `ℝ`; this avoids an irrelevant cast
   choice for `r`, while retaining the literal natural ceiling in `A`. -/
theorem policy_j2_admissibility
    {k Delta A : ℝ} (hk : 200 ≤ k) (hk0 : 0 < k)
    (hD0 : k ^ 2 / 100 ≤ Delta)
    (hD1 : Delta ≤ (k ^ 2 - k) / 2)
    (hA0 : 0 ≤ A) (hAupper : A ≤ Delta / k) :
    2 * (k - 1) ≤ 2 * Delta - A * (A + 1) := by
  have hd0 : k / 100 ≤ Delta / k := by
    apply (le_div_iff₀ hk0).2
    nlinarith
  have hd1 : Delta / k ≤ (k - 1) / 2 := by
    apply (div_le_iff₀ hk0).2
    nlinarith
  have hprod : 0 ≤ (Delta / k - k / 100) * ((k - 1) / 2 - Delta / k) :=
    mul_nonneg (sub_nonneg.mpr hd0) (sub_nonneg.mpr hd1)
  have hAprod : A * (A + 1) ≤ (Delta / k) * (Delta / k + 1) := by
    have h1 : A + 1 ≤ Delta / k + 1 := by linarith
    have hDk0 : 0 ≤ Delta / k := hA0.trans hAupper
    calc
      A * (A + 1) ≤ (Delta / k) * (A + 1) :=
        mul_le_mul_of_nonneg_right hAupper (by positivity)
      _ ≤ (Delta / k) * (Delta / k + 1) :=
        mul_le_mul_of_nonneg_left h1 hDk0
  have hendpoint0 : 2 * k * (k / 100) - (k / 100) ^ 2 - k / 100 ≥
      2 * (k - 1) := by nlinarith
  have hendpoint1 : 2 * k * ((k - 1) / 2) - ((k - 1) / 2) ^ 2 -
      (k - 1) / 2 ≥ 2 * (k - 1) := by nlinarith
  have hconc : 2 * k * (Delta / k) - (Delta / k) ^ 2 - Delta / k ≥
      2 * (k - 1) := by
    have hfactor : 0 ≤ (Delta / k - k / 100) *
        (2 * k - Delta / k - k / 100 - 1) := by
      apply mul_nonneg (sub_nonneg.mpr hd0)
      nlinarith [hd1]
    nlinarith [hfactor, hendpoint0]
  calc
    2 * (k - 1) ≤ 2 * k * (Delta / k) - (Delta / k) ^ 2 - Delta / k := hconc
    _ ≤ 2 * Delta - A * (A + 1) := by
      have hkne : k ≠ 0 := ne_of_gt hk0
      rw [show 2 * k * (Delta / k) = 2 * Delta by field_simp]
      nlinarith [hAprod]

theorem policy_ceiling_j2_admissible
    {k Delta : ℝ} (hk : 200 ≤ k) (hk0 : 0 < k)
    (hD0 : k ^ 2 / 100 ≤ Delta)
    (hD1 : Delta ≤ (k ^ 2 - k) / 2) :
    let A : ℝ := max 1 (Nat.ceil (Delta / k - 1) : ℝ)
    2 * (k - 1) ≤ 2 * Delta - A * (A + 1) := by
  dsimp
  let A : ℝ := max 1 (Nat.ceil (Delta / k - 1) : ℝ)
  have hp := policy_ceiling_bounds hk hk0 hD0 hD1
  rcases hp with ⟨hA1, hAhalf, hR4, hRk, hxl, hxu⟩
  have hAupper : A ≤ Delta / k := by
    have h := hxu
    change A / k ≤ Delta / k ^ 2 at h
    have hh := (div_le_iff₀ hk0).1 h
    calc
      A ≤ (Delta / k ^ 2) * k := hh
      _ = Delta / k := by field_simp
  exact policy_j2_admissibility hk hk0 hD0 hD1 (by linarith [hA1]) hAupper

end
end MAPFordWeakPolicy

#print axioms MAPFordWeakPolicy.policy_ceiling_bounds
#print axioms MAPFordWeakPolicy.policy_j2_admissibility
#print axioms MAPFordWeakPolicy.policy_ceiling_j2_admissible
#print axioms MAPFordWeakPolicy.ford_j2_normalized_identity
#print axioms MAPFordWeakPolicy.policy_high_contraction
#print axioms MAPFordWeakPolicy.policy_low_contraction
