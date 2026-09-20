import FordBoundaryWeightedHolder

open scoped BigOperators

namespace FordCollisionThreeHolder

noncomputable section

def fordThreeAvg {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  (Finset.univ : Finset α).expect f

def fordThreeMoment {α : Type*} [Fintype α]
    (w a b : α → ℝ) (k : ℕ) : ℝ :=
  fordThreeAvg (fun x => w x * a x * b x ^ (2 * k - 2))

def fordThreeA {α : Type*} [Fintype α]
    (w a : α → ℝ) (k : ℕ) : ℝ :=
  fordThreeAvg (fun x => w x * a x ^ (2 * k))

def fordThreeE {α : Type*} [Fintype α]
    (w b : α → ℝ) (k : ℕ) : ℝ :=
  fordThreeAvg (fun x => w x * b x ^ (2 * k))

def fordThreeB {α : Type*} [Fintype α]
    (w : α → ℝ) : ℝ := fordThreeAvg w

private theorem three_integrand_nonneg
    {α : Type*} [Fintype α]
    (w a b : α → ℝ) (k : ℕ)
    (hw : ∀ x, 0 ≤ w x) (ha : ∀ x, 0 ≤ a x) (hb : ∀ x, 0 ≤ b x) (x : α) :
    0 ≤ w x * a x * b x ^ (2 * k - 2) := by
  exact mul_nonneg (mul_nonneg (hw x) (ha x)) (pow_nonneg (hb x) _)

private theorem moment_zero_of_A_zero
    {α : Type*} [Fintype α] [Nonempty α]
    (w a b : α → ℝ) (k : ℕ) (hk : 2 ≤ k)
    (hw : ∀ x, 0 ≤ w x) (ha : ∀ x, 0 ≤ a x) (hb : ∀ x, 0 ≤ b x)
    (hA : fordThreeA w a k = 0) : fordThreeMoment w a b k = 0 := by
  have hterm : ∀ x : α, w x * a x ^ (2 * k) = 0 := by
    intro x
    have hz := (Finset.expect_eq_zero_iff_of_nonneg
      (s := (Finset.univ : Finset α))
      (fun i _ => mul_nonneg (hw i) (pow_nonneg (ha i) _))).mp (by
        simpa [fordThreeA, fordThreeAvg] using hA)
    exact hz x (Finset.mem_univ x)
  apply Finset.expect_eq_zero
  intro x hx
  rcases mul_eq_zero.mp (hterm x) with hwx | hax
  · simp [hwx]
  · have hapos : 2 * k ≠ 0 := by omega
    have hax0 : a x = 0 := (pow_eq_zero_iff hapos).mp hax
    simp [hax0]

private theorem moment_zero_of_E_zero
    {α : Type*} [Fintype α] [Nonempty α]
    (w a b : α → ℝ) (k : ℕ) (hk : 2 ≤ k)
    (hw : ∀ x, 0 ≤ w x) (ha : ∀ x, 0 ≤ a x) (hb : ∀ x, 0 ≤ b x)
    (hE : fordThreeE w b k = 0) : fordThreeMoment w a b k = 0 := by
  have hterm : ∀ x : α, w x * b x ^ (2 * k) = 0 := by
    intro x
    have hz := (Finset.expect_eq_zero_iff_of_nonneg
      (s := (Finset.univ : Finset α))
      (fun i _ => mul_nonneg (hw i) (pow_nonneg (hb i) _))).mp (by
        simpa [fordThreeE, fordThreeAvg] using hE)
    exact hz x (Finset.mem_univ x)
  apply Finset.expect_eq_zero
  intro x hx
  rcases mul_eq_zero.mp (hterm x) with hwx | hbx
  · simp [hwx]
  · have hbpos : 2 * k - 2 ≠ 0 := by omega
    have hbx0 : b x = 0 := (pow_eq_zero_iff (by omega : 2 * k ≠ 0)).mp hbx
    rw [hbx0, zero_pow hbpos]
    simp

private theorem moment_zero_of_B_zero
    {α : Type*} [Fintype α] [Nonempty α]
    (w a b : α → ℝ) (k : ℕ)
    (hw : ∀ x, 0 ≤ w x) (ha : ∀ x, 0 ≤ a x) (hb : ∀ x, 0 ≤ b x)
    (hB : fordThreeB w = 0) : fordThreeMoment w a b k = 0 := by
  have hterm : ∀ x : α, w x = 0 := by
    intro x
    have hz := (Finset.expect_eq_zero_iff_of_nonneg
      (s := (Finset.univ : Finset α)) (fun i _ => hw i)).mp (by
        simpa [fordThreeB, fordThreeAvg] using hB)
    exact hz x (Finset.mem_univ x)
  apply Finset.expect_eq_zero
  intro x hx
  simp [hterm x]

theorem fordThreeMoment_le_geometric
    {α : Type*} [Fintype α] [Nonempty α]
    (w a b : α → ℝ) (k : ℕ) (hk : 2 ≤ k)
    (hw : ∀ x, 0 ≤ w x) (ha : ∀ x, 0 ≤ a x) (hb : ∀ x, 0 ≤ b x)
    (hA : 0 < fordThreeA w a k)
    (hE : 0 < fordThreeE w b k)
    (hB : 0 < fordThreeB w) :
    fordThreeMoment w a b k ≤
      fordThreeA w a k ^ (1 / (2 * k : ℝ)) *
        fordThreeE w b k ^ ((k - 1 : ℝ) / k) *
          fordThreeB w ^ (1 / (2 * k : ℝ)) := by
  let A : ℝ := fordThreeA w a k
  let E : ℝ := fordThreeE w b k
  let B : ℝ := fordThreeB w
  let lam : ℝ := 1 / (2 * k : ℝ)
  let mu : ℝ := (k - 1 : ℝ) / k
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := lt_of_lt_of_le (by norm_num) hkR
  have hlam : 0 ≤ lam := by dsimp [lam]; positivity
  have hmu : 0 ≤ mu := by
    dsimp [mu]
    have hk1 : (1 : ℝ) ≤ k := by linarith
    positivity
  have hsum : lam + mu + lam = 1 := by
    dsimp [lam, mu]
    field_simp
    ring
  have hdenA : 0 < A := hA
  have hdenE : 0 < E := hE
  have hdenB : 0 < B := hB
  have hpoint (x : α) :
      (w x * a x * b x ^ (2 * k - 2)) /
          (A ^ lam * E ^ mu * B ^ lam) ≤
        lam * ((w x * a x ^ (2 * k)) / A) +
          mu * ((w x * b x ^ (2 * k)) / E) +
            lam * (w x / B) := by
    have hU : 0 ≤ (w x * a x ^ (2 * k)) / A := by
      exact div_nonneg (mul_nonneg (hw x) (pow_nonneg (ha x) _)) hdenA.le
    have hV : 0 ≤ (w x * b x ^ (2 * k)) / E := by
      exact div_nonneg (mul_nonneg (hw x) (pow_nonneg (hb x) _)) hdenE.le
    have hW : 0 ≤ w x / B := div_nonneg (hw x) hdenB.le
    have hamgm := Real.geom_mean_le_arith_mean3_weighted
      hlam hmu hlam hU hV hW hsum
    have hpowA : (A ^ lam) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hdenA _)
    have hpowE : (E ^ mu) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hdenE _)
    have hpowB : (B ^ lam) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hdenB _)
    have hmulA : ((w x * a x ^ (2 * k)) / A) ^ lam =
        (w x) ^ lam * (a x) ^ (2 * k * lam) / A ^ lam := by
      rw [Real.div_rpow
        (mul_nonneg (hw x) (pow_nonneg (ha x) _)) (le_of_lt hdenA)]
      rw [Real.mul_rpow (hw x) (pow_nonneg (ha x) _)]
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul (ha x)]
      have hexp : (↑(2 * k) : ℝ) * lam = 2 * (k : ℝ) * lam := by
        norm_num [Nat.cast_mul]
      rw [hexp]
    have hmulE : ((w x * b x ^ (2 * k)) / E) ^ mu =
        (w x) ^ mu * (b x) ^ (2 * k * mu) / E ^ mu := by
      rw [Real.div_rpow
        (mul_nonneg (hw x) (pow_nonneg (hb x) _)) (le_of_lt hdenE)]
      rw [Real.mul_rpow (hw x) (pow_nonneg (hb x) _)]
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul (hb x)]
      have hexp : (↑(2 * k) : ℝ) * mu = 2 * (k : ℝ) * mu := by
        norm_num [Nat.cast_mul]
      rw [hexp]
    have hmulB : (w x / B) ^ lam = (w x) ^ lam / B ^ lam := by
      rw [Real.div_rpow (hw x) (le_of_lt hdenB)]
    have hla : 2 * (k : ℝ) * lam = 1 := by
      dsimp [lam]
      field_simp
    have hmu_exp : 2 * (k : ℝ) * mu = 2 * (k - 1 : ℝ) := by
      dsimp [mu]
      field_simp
    have hprod :
        ((w x * a x ^ (2 * k)) / A) ^ lam *
            ((w x * b x ^ (2 * k)) / E) ^ mu *
              (w x / B) ^ lam =
          (w x * a x * b x ^ (2 * k - 2)) /
            (A ^ lam * E ^ mu * B ^ lam) := by
      rw [hmulA, hmulE, hmulB, hla, hmu_exp]
      rw [Real.rpow_one]
      have hcast : 2 * ((k : ℝ) - 1) = ((2 * k - 2 : ℕ) : ℝ) := by
        rw [Nat.cast_sub (by omega)]
        norm_num
        ring
      rw [hcast, Real.rpow_natCast]
      have hwmul : (w x) ^ lam * (w x) ^ mu * (w x) ^ lam = w x := by
        rw [← Real.rpow_add' (hw x) (by linarith [hsum]),
          ← Real.rpow_add' (hw x) (by linarith [hsum])]
        rw [hsum]
        exact Real.rpow_one _
      calc
        _ = (w x ^ lam * w x ^ mu * w x ^ lam) *
              (a x * b x ^ (2 * k - 2)) /
              (A ^ lam * E ^ mu * B ^ lam) := by
          field_simp
          
        _ = (w x * a x * b x ^ (2 * k - 2)) /
              (A ^ lam * E ^ mu * B ^ lam) := by
          rw [hwmul]
          ring
    rw [hprod] at hamgm
    exact hamgm
  have hexpect := Finset.expect_le_expect (s := (Finset.univ : Finset α))
    (fun x _ => hpoint x)
  have hleft :
      Finset.expect (Finset.univ : Finset α)
          (fun x => (w x * a x * b x ^ (2 * k - 2)) /
            (A ^ lam * E ^ mu * B ^ lam)) =
        fordThreeMoment w a b k /
          (A ^ lam * E ^ mu * B ^ lam) := by
    rw [fordThreeMoment, fordThreeAvg, ← Finset.expect_div]
  have hright :
      Finset.expect (Finset.univ : Finset α)
          (fun x => lam * ((w x * a x ^ (2 * k)) / A) +
            mu * ((w x * b x ^ (2 * k)) / E) + lam * (w x / B)) = 1 := by
    have hscale (c : ℝ) (f : α → ℝ) :
        Finset.expect (Finset.univ : Finset α) (fun x => c * f x) =
          c * Finset.expect (Finset.univ : Finset α) f := by
      calc
        _ = Finset.expect (Finset.univ : Finset α) (fun x => f x * c) := by
          apply Finset.expect_congr rfl
          intro x hx
          ring
        _ = Finset.expect (Finset.univ : Finset α) f * c := by
          simpa using (Finset.expect_mul (Finset.univ : Finset α) f c).symm
        _ = c * Finset.expect (Finset.univ : Finset α) f := by ring
    rw [Finset.expect_add_distrib, Finset.expect_add_distrib]
    rw [hscale lam, hscale mu, hscale lam]
    have hAexp : Finset.expect (Finset.univ : Finset α)
        (fun x => (w x * a x ^ (2 * k)) / A) = fordThreeA w a k / A := by
      rw [fordThreeA, fordThreeAvg, Finset.expect_div]
    have hEexp : Finset.expect (Finset.univ : Finset α)
        (fun x => (w x * b x ^ (2 * k)) / E) = fordThreeE w b k / E := by
      rw [fordThreeE, fordThreeAvg, Finset.expect_div]
    have hBexp : Finset.expect (Finset.univ : Finset α)
        (fun x => w x / B) = fordThreeB w / B := by
      rw [fordThreeB, fordThreeAvg, Finset.expect_div]
    rw [hAexp, hEexp, hBexp]
    dsimp [A, E, B]
    field_simp
    dsimp [lam, mu]
    field_simp
    ring
  rw [hleft, hright] at hexpect
  have hdenpos : 0 < A ^ lam * E ^ mu * B ^ lam := by positivity
  have hmain : fordThreeMoment w a b k ≤ A ^ lam * E ^ mu * B ^ lam := by
    have hh := (div_le_iff₀ hdenpos).mp (by simpa using hexpect)
    simpa only [one_mul] using hh
  simpa [A, E, B, lam, mu, Nat.cast_sub (by omega)] using hmain

theorem fordThreeMoment_le_geometric_of_nonneg
    {α : Type*} [Fintype α] [Nonempty α]
    (w a b : α → ℝ) (k : ℕ) (hk : 2 ≤ k)
    (hw : ∀ x, 0 ≤ w x) (ha : ∀ x, 0 ≤ a x) (hb : ∀ x, 0 ≤ b x) :
    fordThreeMoment w a b k ≤
      fordThreeA w a k ^ (1 / (2 * k : ℝ)) *
        fordThreeE w b k ^ ((k - 1 : ℝ) / k) *
          fordThreeB w ^ (1 / (2 * k : ℝ)) := by
  have hA_nonneg : 0 ≤ fordThreeA w a k := by
    exact Finset.expect_nonneg (fun x _ =>
      mul_nonneg (hw x) (pow_nonneg (ha x) _))
  have hE_nonneg : 0 ≤ fordThreeE w b k := by
    exact Finset.expect_nonneg (fun x _ =>
      mul_nonneg (hw x) (pow_nonneg (hb x) _))
  have hB_nonneg : 0 ≤ fordThreeB w := by
    exact Finset.expect_nonneg (fun x _ => hw x)
  by_cases hAz : fordThreeA w a k = 0
  · rw [moment_zero_of_A_zero w a b k hk hw ha hb hAz]
    positivity
  by_cases hEz : fordThreeE w b k = 0
  · rw [moment_zero_of_E_zero w a b k hk hw ha hb hEz]
    positivity
  by_cases hBz : fordThreeB w = 0
  · rw [moment_zero_of_B_zero w a b k hw ha hb hBz]
    positivity
  exact fordThreeMoment_le_geometric w a b k hk hw ha hb
    (lt_of_le_of_ne hA_nonneg (Ne.symm hAz))
    (lt_of_le_of_ne hE_nonneg (Ne.symm hEz))
    (lt_of_le_of_ne hB_nonneg (Ne.symm hBz))

theorem scalar_three_factor_power
    {k : ℕ} (hk : 2 ≤ k) {P A E B : ℝ}
    (hP : 0 ≤ P) (hA : 0 ≤ A) (hE : 0 ≤ E) (hB : 0 ≤ B)
    (hholder : P ≤
      A ^ (1 / (2 * k : ℝ)) * E ^ ((k - 1 : ℝ) / k) *
        B ^ (1 / (2 * k : ℝ))) :
    P ^ (2 * k) ≤ A * E ^ (2 * k - 2) * B := by
  have hkR : (0 : ℝ) ≤ 2 * k := by positivity
  have hpow := Real.rpow_le_rpow hP hholder hkR
  have hcast : P ^ (2 * k : ℝ) = P ^ (2 * k) := by
    calc
      P ^ (2 * k : ℝ) = P ^ ((2 * k : ℕ) : ℝ) := by
        congr 2
        norm_num [Nat.cast_mul]
      _ = P ^ (2 * k) := Real.rpow_natCast _ _
  have hAexp : ((1 / (2 * k : ℝ)) * (2 * k : ℝ)) = 1 := by
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    field_simp
  have hEexp : (((k - 1 : ℝ) / k) * (2 * k : ℝ)) = 2 * (k - 1 : ℝ) := by
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    field_simp
  have hright :
      (A ^ (1 / (2 * k : ℝ)) * E ^ ((k - 1 : ℝ) / k) *
        B ^ (1 / (2 * k : ℝ))) ^ (2 * k : ℝ) =
        A * E ^ (2 * k - 2) * B := by
    rw [Real.mul_rpow (mul_nonneg (Real.rpow_nonneg hA _) 
          (Real.rpow_nonneg hE _)) (Real.rpow_nonneg hB _)]
    rw [Real.mul_rpow (Real.rpow_nonneg hA _) (Real.rpow_nonneg hE _)]
    rw [← Real.rpow_mul hA, ← Real.rpow_mul hE, ← Real.rpow_mul hB]
    rw [hAexp, hEexp, Real.rpow_one]
    have hcastE : 2 * (k - 1 : ℝ) = ((2 * k - 2 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]
      norm_num
      ring_nf
    rw [hcastE, Real.rpow_natCast]
    simp only [Real.rpow_one]
  rw [hcast, hright] at hpow
  exact hpow

end
end FordCollisionThreeHolder

#print axioms FordCollisionThreeHolder.fordThreeMoment_le_geometric
#print axioms FordCollisionThreeHolder.fordThreeMoment_le_geometric_of_nonneg
#print axioms FordCollisionThreeHolder.scalar_three_factor_power
