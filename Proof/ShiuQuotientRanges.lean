import MAPShiuSpecialization

/-!
# Exact floor-sensitive range checks for the MAP Shiu specialization

These lemmas discharge the two strict cube hypotheses in
`DyadicTauSquareShiuTarget` for the determinant quotient window.  Integer
division is retained literally throughout.
-/

namespace ShiuAnalyticLayer

open MAPShiuSpecialization

/-- The quotient upper endpoint differs from twice the quotient lower
endpoint by at most one. -/
theorem quotient_window_bounds (N D : ℕ) (hD : 0 < D) :
    let t := N / D
    let x := (2 * N) / D
    2 * t ≤ x ∧ x ≤ 2 * t + 1 := by
  dsimp
  constructor
  · exact Nat.mul_div_le_mul_div_assoc 2 N D
  · have hr : N % D < D := Nat.mod_lt N hD
    have hx :
        (2 * N) / D =
          2 * (N / D) + (2 * (N % D)) / D := by
      conv_lhs =>
        rw [← Nat.div_add_mod N D]
      rw [mul_add]
      conv_lhs =>
        rw [show 2 * (D * (N / D)) = D * (2 * (N / D)) by ring]
      rw [Nat.mul_add_div hD]
    rw [hx]
    have : (2 * (N % D)) / D < 2 := by
      rw [Nat.div_lt_iff_lt_mul hD]
      omega
    omega

/-- Under the paper's scale and short-variable bounds, a sufficiently large
quotient endpoint satisfies every range hypothesis of the fixed
`α = β = 1/3` Shiu target. -/
theorem quotient_shiu_ranges
    (A M N d b D : ℕ)
    (hA : 0 < A) (hd : 0 < d) (hb : 0 < b) (hD : 0 < D)
    (hscale : M ^ 2 ≤ A * N)
    (hshort : d * b ≤ 2 * M)
    (hDb : D ∣ b)
    (hxlarge : 2 * (8 * A) ^ 3 + 2 ≤ (2 * N) / D) :
    let x := quotientUpper N D
    let y := quotientLength N D
    let q := b / D
    0 < q ∧ y ≤ x ∧ x < y ^ 3 ∧ q ^ 3 < y ^ 2 := by
  dsimp [quotientUpper, quotientLength]
  let t := N / D
  let x := (2 * N) / D
  let y := x - t
  let q := b / D
  have hbounds := quotient_window_bounds N D hD
  dsimp only at hbounds
  have htbig : (8 * A) ^ 3 < t := by
    dsimp [t]
    omega
  have htpos : 0 < t := lt_trans (by positivity) htbig
  have hyge : t ≤ y := by
    dsimp [y, x]
    exact Nat.le_sub_of_add_le (by simpa [two_mul] using hbounds.1)
  have hyx : y ≤ x := Nat.sub_le _ _
  have hxlt : x < y ^ 3 := by
    have h8A : 8 ≤ 8 * A := by nlinarith
    have h512 : 512 ≤ (8 * A) ^ 3 := by
      calc
        512 = 8 ^ 3 := by norm_num
        _ ≤ (8 * A) ^ 3 := Nat.pow_le_pow_left h8A 3
    have ht2 : 2 ≤ t := by omega
    have hxt : x ≤ 2 * t + 1 := hbounds.2
    have hfour : 4 ≤ t ^ 2 := by
      calc
        4 = 2 ^ 2 := by norm_num
        _ ≤ t ^ 2 := Nat.pow_le_pow_left ht2 2
    have hpoly : 2 * t + 1 < t ^ 3 := by
      have : 4 * t ≤ t ^ 3 := by
        calc
          4 * t ≤ t ^ 2 * t := Nat.mul_le_mul_right t hfour
          _ = t ^ 3 := by ring
      omega
    exact hxt.trans_lt (hpoly.trans_le (Nat.pow_le_pow_left hyge 3))
  have hbM : b ≤ 2 * M := by
    have hbd : b ≤ d * b := by nlinarith
    exact hbd.trans hshort
  have hb2 : b ^ 2 ≤ 4 * A * N := by
    have hb_sq : b ^ 2 ≤ (2 * M) ^ 2 := Nat.pow_le_pow_left hbM 2
    nlinarith [hscale]
  have hDq : D * q = b := by
    dsimp [q]
    exact Nat.mul_div_cancel' hDb
  have hNlt : N < D * (t + 1) := by
    dsimp [t]
    exact Nat.lt_mul_div_succ N hD
  have hq2 : q ^ 2 < 8 * A * t := by
    have hprod : q ^ 2 * D ^ 2 ≤ 4 * A * N := by
      calc
        q ^ 2 * D ^ 2 = b ^ 2 := by
          rw [pow_two, pow_two, ← hDq]
          ring
        _ ≤ 4 * A * N := hb2
    have hprod' : q ^ 2 * D ^ 2 < 4 * A * (D * (t + 1)) := by
      exact hprod.trans_lt <| by
        have := (Nat.mul_lt_mul_left (by positivity : 0 < 4 * A)).2 hNlt
        simpa [mul_assoc] using this
    have hcancel : q ^ 2 * D < 4 * A * (t + 1) := by
      have : D * (q ^ 2 * D) < D * (4 * A * (t + 1)) := by
        simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hprod'
      exact (Nat.mul_lt_mul_left hD).mp this
    calc
      q ^ 2 ≤ q ^ 2 * D := by nlinarith
      _ < 4 * A * (t + 1) := hcancel
      _ ≤ 8 * A * t := by nlinarith
  have hqpos : 0 < q := by
    dsimp [q]
    exact Nat.div_pos (Nat.le_of_dvd hb hDb) hD
  have hqcube : q ^ 3 < t ^ 2 := by
    have hpow6 : q ^ 6 < t ^ 4 := by
      calc
        q ^ 6 = (q ^ 2) ^ 3 := by ring
        _ < (8 * A * t) ^ 3 := Nat.pow_lt_pow_left hq2 (by decide)
        _ = (8 * A) ^ 3 * t ^ 3 := by ring
        _ < t * t ^ 3 :=
          (Nat.mul_lt_mul_right (by positivity : 0 < t ^ 3)).2 htbig
        _ = t ^ 4 := by ring
    have hsquares : (q ^ 3) ^ 2 < (t ^ 2) ^ 2 := by
      simpa [← pow_mul] using hpow6
    exact (Nat.pow_lt_pow_iff_left (by decide)).mp hsquares
  refine ⟨hqpos, hyx, hxlt, ?_⟩
  exact hqcube.trans_le (Nat.pow_le_pow_left hyge 2)

/-! ## Cast-free cube hypotheses imply Shiu's real ranges -/

/-- The target's natural cube condition is exactly strong enough for
`x^(1/3) < y` over the reals. -/
theorem cube_lt_implies_real_cuberoot_lt {x y : ℕ} (hxy : x < y ^ 3) :
    (x : ℝ) ^ ((3 : ℝ)⁻¹) < (y : ℝ) := by
  have hcast : (x : ℝ) < (y : ℝ) ^ 3 := by exact_mod_cast hxy
  have hroot := Real.rpow_lt_rpow (Nat.cast_nonneg x) hcast
    (inv_pos.mpr (by norm_num : (0 : ℝ) < 3))
  simpa using hroot.trans_eq
    (Real.pow_rpow_inv_natCast (Nat.cast_nonneg y) (by decide : (3 : ℕ) ≠ 0))

/-- The target's modulus cube condition is exactly strong enough for
`q < y^(2/3)` over the reals. -/
theorem cube_lt_square_implies_real_two_thirds {q y : ℕ}
    (hqy : q ^ 3 < y ^ 2) :
    (q : ℝ) < (y : ℝ) ^ ((2 : ℝ) * (3 : ℝ)⁻¹) := by
  have hcast : (q : ℝ) ^ 3 < (y : ℝ) ^ 2 := by exact_mod_cast hqy
  have hroot := Real.rpow_lt_rpow (by positivity : (0 : ℝ) ≤ (q : ℝ) ^ 3)
    hcast (inv_pos.mpr (by norm_num : (0 : ℝ) < 3))
  calc
    (q : ℝ) = ((q : ℝ) ^ 3) ^ ((3 : ℝ)⁻¹) := by
      symm
      exact Real.pow_rpow_inv_natCast (Nat.cast_nonneg q) (by decide)
    _ < ((y : ℝ) ^ 2) ^ ((3 : ℝ)⁻¹) := hroot
    _ = (y : ℝ) ^ ((2 : ℝ) * (3 : ℝ)⁻¹) := by
      rw [Real.rpow_mul (Nat.cast_nonneg y)]
      norm_num [Real.rpow_natCast]

/-- Complete real range package obtained from the exact quotient geometry.
This is the form accepted by Shiu's published `α = β = 1/3` hypotheses. -/
theorem quotient_real_shiu_ranges
    (A M N d b D : ℕ)
    (hA : 0 < A) (hd : 0 < d) (hb : 0 < b) (hD : 0 < D)
    (hscale : M ^ 2 ≤ A * N)
    (hshort : d * b ≤ 2 * M)
    (hDb : D ∣ b)
    (hxlarge : 2 * (8 * A) ^ 3 + 2 ≤ quotientUpper N D) :
    let x := quotientUpper N D
    let y := quotientLength N D
    let q := b / D
    0 < q ∧ y ≤ x ∧
      (x : ℝ) ^ ((3 : ℝ)⁻¹) < (y : ℝ) ∧
      (q : ℝ) < (y : ℝ) ^ ((2 : ℝ) * (3 : ℝ)⁻¹) := by
  dsimp only
  obtain ⟨hq, hyx, hxy, hqy⟩ := quotient_shiu_ranges
    A M N d b D hA hd hb hD hscale hshort hDb hxlarge
  exact ⟨hq, hyx, cube_lt_implies_real_cuberoot_lt hxy,
    cube_lt_square_implies_real_two_thirds hqy⟩

end ShiuAnalyticLayer
