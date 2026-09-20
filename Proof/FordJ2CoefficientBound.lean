import FordJ2GeometricAlgebra

noncomputable section
set_option autoImplicit false
namespace FordJ2CoefficientBound

open FordJ2GeometricAlgebra

/-- The literal one-step coefficient for a natural widened prime bound `B`. -/
def stepCoefficient (s k r B : ℕ) : ℝ :=
  4 * (k : ℝ) ^ 3 * (B : ℝ) ^ (countExponent s k r 0) * (2 : ℝ) ^ k *
    max ((k : ℝ) ^ k)
      (2 * Real.sqrt (4 * (k : ℝ) ^ 3 * (B : ℝ) ^ (countExponent s k r 1)))

/-- The terminal specialization `B = 2^(k^3)`. -/
def terminalCstep (s k r : ℕ) : ℝ :=
  stepCoefficient s k r (2 ^ (k ^ 3))

private lemma nat_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        n + 1 ≤ 2 ^ n + 1 := Nat.succ_le_succ ih
        _ ≤ 2 ^ n + 2 ^ n := by have h1 : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by norm_num); omega
        _ = 2 ^ (n + 1) := by rw [pow_succ]; ring

private lemma countExponent_one_le_bound
    {s k r : ℕ} (hs : s ≤ 1003 * k ^ 2) (hr : 2 ≤ r) (hrk : r ≤ k)
    (hk : 2000 ≤ k) :
    countExponent s k r 1 ≤ 2008 * k ^ 2 := by
  have h2s : 2 * s ≤ 2006 * k ^ 2 := by
    calc
      2 * s ≤ 2 * (1003 * k ^ 2) := Nat.mul_le_mul_left 2 hs
      _ = 2006 * k ^ 2 := by ring
  have hprod : (r - 1) * (r - 2) ≤ k ^ 2 := by
    have h1 : r - 1 ≤ k := by omega
    have h2 : r - 2 ≤ k := by omega
    have hp := Nat.mul_le_mul h1 h2
    simpa [pow_two] using hp
  have htri : (r - 1) * (r - 2) / 2 ≤ k ^ 2 :=
    (Nat.div_le_self _ _).trans hprod
  have hk2 : k ≤ k ^ 2 := by
    have : 1 ≤ k := by omega
    simpa [pow_two] using (Nat.mul_le_mul_left k this)
  have htri' : (r - 1) * (r - 1 - 1) / 2 ≤ k ^ 2 := by
    simpa [Nat.sub_sub] using htri
  have hsub1 : 2 * s - 1 ≤ 2 * s := by omega
  have hsubk : k - 1 ≤ k := by omega
  have h2k : r + (k - 1) ≤ k ^ 2 := by
    have hrk2 : r + (k - 1) ≤ k + k := by omega
    have hkk : k + k ≤ k * k := by
      have htwo : 2 ≤ k := by omega
      have hh := Nat.mul_le_mul_left k htwo
      simpa [mul_two] using hh
    simpa [pow_two] using hrk2.trans hkk
  simp only [countExponent]
  omega

private lemma exponent_bounds
    {s k r : ℕ} (hk : 2000 ≤ k) (hs : s ≤ 1003 * k ^ 2)
    (hr : 2 ≤ r) (hrk : r ≤ k) :
    countExponent s k r 0 ≤ 2008 * k ^ 2 ∧
    countExponent s k r 1 ≤ 2008 * k ^ 2 := by
  have hk1 : 1 ≤ k := by omega
  have h2s : 2 * s ≤ 2006 * k ^ 2 := by
    calc
      2 * s ≤ 2 * (1003 * k ^ 2) := Nat.mul_le_mul_left 2 hs
      _ = 2006 * k ^ 2 := by ring
  have hprod : r * (r - 1) ≤ k ^ 2 := by
    have h1 : r - 1 ≤ k := by omega
    have hp := Nat.mul_le_mul hrk h1
    simpa [pow_two] using hp
  have htri : r * (r - 1) / 2 ≤ k ^ 2 :=
    (Nat.div_le_self _ _).trans hprod
  have hk2 : k ≤ k ^ 2 := by
    have : 1 ≤ k := by omega
    simpa [pow_two] using (Nat.mul_le_mul_left k this)
  have hE0 : countExponent s k r 0 ≤ 2008 * k ^ 2 := by
    simp only [countExponent, Nat.sub_zero, Nat.mul_zero, Nat.add_zero]
    omega
  have hE1 : countExponent s k r 1 ≤ 2008 * k ^ 2 :=
    countExponent_one_le_bound hs hr hrk hk
  exact ⟨hE0, hE1⟩

/-- The actual coefficient is positive and has a deliberately conservative
`2^(8192*k^5)` envelope for the stated finite parameter range. -/
theorem terminalCstep_pos_and_bound
    {s k r : ℕ} (hk : 2000 ≤ k) (hs : s ≤ 1003 * k ^ 2)
    (hr : 2 ≤ r) (hrk : r ≤ k) :
    0 < terminalCstep s k r ∧
      terminalCstep s k r ≤ (2 : ℝ) ^ (8192 * k ^ 5) := by
  let B : ℕ := 2 ^ (k ^ 3)
  let E0 : ℕ := countExponent s k r 0
  let E1 : ℕ := countExponent s k r 1
  have hk1 : 1 ≤ k := by omega
  have hE := exponent_bounds hk hs hr hrk
  have hE0 : E0 ≤ 2008 * k ^ 2 := hE.1
  have hE1 : E1 ≤ 2008 * k ^ 2 := hE.2
  have hB1 : 1 ≤ B := by
    dsimp [B]
    exact Nat.one_le_pow _ _ (by norm_num)
  have hB0 : 0 < B := by omega
  have hBreal : (0 : ℝ) < B := by exact_mod_cast hB0
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hk_le_k5 : k ≤ k ^ 5 := by
    have hk4 : 1 ≤ k ^ 4 := Nat.one_le_pow _ _ (by omega)
    calc
      k ≤ k * k ^ 4 := by simpa using (Nat.mul_le_mul_left k hk4)
      _ = k ^ 5 := by ring
  have hk5two : 2 ≤ k ^ 5 := by omega
  have hk2_le_k5 : k ^ 2 ≤ k ^ 5 := by
    have hk3 : 1 ≤ k ^ 3 := Nat.one_le_pow _ _ (by omega)
    calc
      k ^ 2 ≤ k ^ 2 * k ^ 3 := by
        simpa using (Nat.mul_le_mul_left (k ^ 2) hk3)
      _ = k ^ 5 := by ring
  have hpowB0 : (B : ℝ) ^ E0 ≤ (2 : ℝ) ^ (2008 * k ^ 5) := by
    have hEprod : k ^ 3 * E0 ≤ 2008 * k ^ 5 := by
      calc
        k ^ 3 * E0 ≤ k ^ 3 * (2008 * k ^ 2) := Nat.mul_le_mul_left _ hE0
        _ = 2008 * k ^ 5 := by ring
    have hEq : (B : ℝ) ^ E0 = (2 : ℝ) ^ (k ^ 3 * E0) := by
      dsimp [B]
      push_cast
      rw [← pow_mul]
    rw [hEq]
    exact pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) hEprod
  have hpowB1 : (B : ℝ) ^ E1 ≤ (2 : ℝ) ^ (2008 * k ^ 5) := by
    have hEprod : k ^ 3 * E1 ≤ 2008 * k ^ 5 := by
      calc
        k ^ 3 * E1 ≤ k ^ 3 * (2008 * k ^ 2) := Nat.mul_le_mul_left _ hE1
        _ = 2008 * k ^ 5 := by ring
    have hEq : (B : ℝ) ^ E1 = (2 : ℝ) ^ (k ^ 3 * E1) := by
      dsimp [B]
      push_cast
      rw [← pow_mul]
    rw [hEq]
    exact pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) hEprod
  have hk5 : 1 ≤ k ^ 5 := Nat.one_le_pow _ _ (by omega)
  have hk5three : 3 ≤ k ^ 5 := by omega
  have hpoly : 4 * (k : ℝ) ^ 3 ≤ (2 : ℝ) ^ (2 * k ^ 5) := by
    have h4 : (4 : ℝ) ≤ (2 : ℝ) ^ (k ^ 5) := by
      calc
        (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
        _ ≤ (2 : ℝ) ^ (k ^ 5) :=
          pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) hk5two
    have hkn : k ^ 3 ≤ 2 ^ (k ^ 3) := nat_le_two_pow _
    have hkr : (k : ℝ) ^ 3 ≤ (2 : ℝ) ^ (k ^ 5) := by
      calc
        (k : ℝ) ^ 3 ≤ (2 : ℝ) ^ (k ^ 3) := by exact_mod_cast hkn
        _ ≤ (2 : ℝ) ^ (k ^ 5) := by
          apply pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num)
          have : k ^ 3 ≤ k ^ 5 := by
            calc
              k ^ 3 ≤ k ^ 3 * k ^ 2 := by
                simpa using (Nat.mul_le_mul_left (k ^ 3)
                  (show 1 ≤ k ^ 2 by exact Nat.one_le_pow _ _ (by omega)))
              _ = k ^ 5 := by ring
          exact this
    calc
      4 * (k : ℝ) ^ 3 ≤ (2 : ℝ) ^ (k ^ 5) * (2 : ℝ) ^ (k ^ 5) :=
        mul_le_mul h4 hkr (by positivity) (by positivity)
      _ = (2 : ℝ) ^ (2 * k ^ 5) := by rw [← pow_add]; congr 1 <;> ring
  have hpolyD : 8 * (k : ℝ) ^ 3 ≤ (2 : ℝ) ^ (2 * k ^ 5) := by
    have h8 : (8 : ℝ) ≤ (2 : ℝ) ^ (k ^ 5) := by
      calc
        (8 : ℝ) = (2 : ℝ) ^ 3 := by norm_num
        _ ≤ (2 : ℝ) ^ (k ^ 5) :=
          pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) hk5three
    have hkn : k ^ 3 ≤ 2 ^ (k ^ 3) := nat_le_two_pow _
    have hkr : (k : ℝ) ^ 3 ≤ (2 : ℝ) ^ (k ^ 5) := by
      calc
        (k : ℝ) ^ 3 ≤ (2 : ℝ) ^ (k ^ 3) := by exact_mod_cast hkn
        _ ≤ (2 : ℝ) ^ (k ^ 5) := by
          apply pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num)
          have : k ^ 3 ≤ k ^ 5 := by
            calc
              k ^ 3 ≤ k ^ 3 * k ^ 2 := by
                simpa using (Nat.mul_le_mul_left (k ^ 3)
                  (show 1 ≤ k ^ 2 by exact Nat.one_le_pow _ _ (by omega)))
              _ = k ^ 5 := by ring
          exact this
    calc
      8 * (k : ℝ) ^ 3 ≤ (2 : ℝ) ^ (k ^ 5) * (2 : ℝ) ^ (k ^ 5) :=
        mul_le_mul h8 hkr (by positivity) (by positivity)
      _ = (2 : ℝ) ^ (2 * k ^ 5) := by rw [← pow_add]; congr 1 <;> ring
  have hD1 : (1 : ℝ) ≤ 4 * (k : ℝ) ^ 3 * (B : ℝ) ^ E1 := by
    have hpow1 : (1 : ℝ) ≤ (B : ℝ) ^ E1 := one_le_pow₀ (by exact_mod_cast hB1)
    have hfactor : (1 : ℝ) ≤ 4 * (k : ℝ) ^ 3 := by
      have hkR1 : (1 : ℝ) ≤ k := by exact_mod_cast hk1
      have hkpow : (1 : ℝ) ≤ (k : ℝ) ^ 3 := one_le_pow₀ hkR1
      nlinarith
    have hh := mul_le_mul hfactor hpow1 (by positivity) (by positivity)
    simpa using hh
  have hDsqrt : Real.sqrt (4 * (k : ℝ) ^ 3 * (B : ℝ) ^ E1) ≤
      4 * (k : ℝ) ^ 3 * (B : ℝ) ^ E1 := by
    have hD0 : 0 ≤ 4 * (k : ℝ) ^ 3 * (B : ℝ) ^ E1 := by positivity
    have hsquare := Real.sq_sqrt hD0
    nlinarith [Real.sqrt_nonneg (4 * (k : ℝ) ^ 3 * (B : ℝ) ^ E1)]
  have hmax : max ((k : ℝ) ^ k)
      (2 * Real.sqrt (4 * (k : ℝ) ^ 3 * (B : ℝ) ^ E1)) ≤
      (2 : ℝ) ^ (2010 * k ^ 5) := by
    apply max_le
    · have hkpow : (k : ℝ) ^ k ≤ (2 : ℝ) ^ (k ^ 5) := by
        have hk2 : (k : ℝ) ≤ (2 : ℝ) ^ k := by exact_mod_cast (nat_le_two_pow k)
        have hh := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ k) hk2 k
        rw [← pow_mul] at hh
        exact hh.trans (pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) (by
          have : k * k ≤ k ^ 5 := by
            calc
              k * k = k ^ 2 := by ring
              _ ≤ k ^ 5 := by
                have hk3 : 1 ≤ k ^ 3 := Nat.one_le_pow _ _ (by omega)
                calc
                  k ^ 2 ≤ k ^ 2 * k ^ 3 := by
                    simpa using (Nat.mul_le_mul_left (k ^ 2) hk3)
                  _ = k ^ 5 := by ring
          exact this))
      exact hkpow.trans (pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) (by omega))
    · calc
        2 * Real.sqrt (4 * (k : ℝ) ^ 3 * (B : ℝ) ^ E1) ≤
            2 * (4 * (k : ℝ) ^ 3 * (B : ℝ) ^ E1) := by
              exact mul_le_mul_of_nonneg_left hDsqrt (by norm_num)
        _ = 8 * (k : ℝ) ^ 3 * (B : ℝ) ^ E1 := by ring
        _ ≤ (2 : ℝ) ^ (2 * k ^ 5) * (2 : ℝ) ^ (2008 * k ^ 5) := by
              exact mul_le_mul hpolyD hpowB1 (by positivity) (by positivity)
        _ = (2 : ℝ) ^ (2010 * k ^ 5) := by rw [← pow_add]; congr 1 <;> ring
  have hpos : 0 < terminalCstep s k r := by
    have hpow0 : 0 < (B : ℝ) ^ E0 := by positivity
    have hkpow : 0 < (k : ℝ) ^ k := by positivity
    have hmx : 0 < max ((k : ℝ) ^ k)
        (2 * Real.sqrt (4 * (k : ℝ) ^ 3 * (B : ℝ) ^ E1)) :=
      lt_of_lt_of_le hkpow (le_max_left _ _)
    dsimp [terminalCstep, stepCoefficient]
    exact mul_pos (mul_pos (mul_pos (mul_pos (by positivity) (by positivity)) hpow0)
      (by positivity)) hmx
  refine ⟨hpos, ?_⟩
  dsimp [terminalCstep, stepCoefficient]
  calc
    4 * (k : ℝ) ^ 3 * (B : ℝ) ^ E0 * (2 : ℝ) ^ k *
        max ((k : ℝ) ^ k) (2 * Real.sqrt (4 * (k : ℝ) ^ 3 * (B : ℝ) ^ E1)) ≤
      (2 : ℝ) ^ (2 * k ^ 5) * (2 : ℝ) ^ (2008 * k ^ 5) *
        (2 : ℝ) ^ (k ^ 5) * (2 : ℝ) ^ (2010 * k ^ 5) := by
      have hpowk : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (k ^ 5) := by
        exact pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) hk_le_k5
      have hAB :
          4 * (k : ℝ) ^ 3 * (B : ℝ) ^ E0 ≤
            (2 : ℝ) ^ (2 * k ^ 5) * (2 : ℝ) ^ (2008 * k ^ 5) := by
        exact mul_le_mul hpoly hpowB0 (by positivity) (by positivity)
      have hABC :
          4 * (k : ℝ) ^ 3 * (B : ℝ) ^ E0 * (2 : ℝ) ^ k ≤
            (2 : ℝ) ^ (2 * k ^ 5) * (2 : ℝ) ^ (2008 * k ^ 5) *
              (2 : ℝ) ^ (k ^ 5) := by
        calc
          _ ≤ ((2 : ℝ) ^ (2 * k ^ 5) * (2 : ℝ) ^ (2008 * k ^ 5)) *
              (2 : ℝ) ^ k := mul_le_mul_of_nonneg_right hAB (by positivity)
          _ ≤ ((2 : ℝ) ^ (2 * k ^ 5) * (2 : ℝ) ^ (2008 * k ^ 5)) *
              (2 : ℝ) ^ (k ^ 5) := mul_le_mul_of_nonneg_left hpowk (by positivity)
          _ = _ := by ring
      calc
        _ = (4 * (k : ℝ) ^ 3 * (B : ℝ) ^ E0 * (2 : ℝ) ^ k) *
            max ((k : ℝ) ^ k) (2 * Real.sqrt (4 * (k : ℝ) ^ 3 * (B : ℝ) ^ E1)) := by ring
        _ ≤ ((2 : ℝ) ^ (2 * k ^ 5) * (2 : ℝ) ^ (2008 * k ^ 5) *
            (2 : ℝ) ^ (k ^ 5)) *
              max ((k : ℝ) ^ k) (2 * Real.sqrt (4 * (k : ℝ) ^ 3 * (B : ℝ) ^ E1)) :=
          mul_le_mul_of_nonneg_right hABC (by positivity)
        _ ≤ ((2 : ℝ) ^ (2 * k ^ 5) * (2 : ℝ) ^ (2008 * k ^ 5) *
            (2 : ℝ) ^ (k ^ 5)) *
              (2 : ℝ) ^ (2010 * k ^ 5) :=
          mul_le_mul_of_nonneg_left hmax (by positivity)
    _ = (2 : ℝ) ^ (4021 * k ^ 5) := by rw [← pow_add, ← pow_add, ← pow_add]; congr 1 <;> ring
    _ ≤ (2 : ℝ) ^ (8192 * k ^ 5) := by
      apply pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num)
      omega

end FordJ2CoefficientBound
#print axioms FordJ2CoefficientBound.terminalCstep_pos_and_bound
