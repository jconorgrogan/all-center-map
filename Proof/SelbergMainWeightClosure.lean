import ShiuSieveSlice
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.SelbergSieve

/-!
# Explicit finite Selberg weights for the Shiu slice

This module supplies the Λ² algebra missing from Mathlib's current
`NumberTheory.SelbergSieve`: the finite level set, its Selberg denominator,
the Möbius-inverted weights, and the lcm-kernel diagonalization needed by
`ShiuSieveSlice.selbergMainQuadratic`.
-/

noncomputable section

namespace ShiuSelbergMainWeight

open ShiuSieveSlice
open scoped BigOperators ArithmeticFunction.Moebius

/-- Divisors of the squarefree sieve product which lie at Selberg level `z`. -/
def levelDivisors (P z : ℕ) : Finset ℕ :=
  P.divisors.filter fun r => r ≤ z

/-- The dimension-one Selberg denominator
`G(P,z) = sum_{r|P,r≤z} μ(r)^2/φ(r)`. -/
def selbergDenominator (P z : ℕ) : ℝ :=
  ∑ r ∈ levelDivisors P z,
    (ArithmeticFunction.moebius r : ℝ) ^ 2 / (Nat.totient r : ℝ)

theorem one_mem_levelDivisors {P z : ℕ} (hP : 0 < P) (hz : 1 ≤ z) :
    1 ∈ levelDivisors P z := by
  simp [levelDivisors, Nat.mem_divisors, hP.ne', hz]

theorem levelDivisor_pos {P z r : ℕ} (hr : r ∈ levelDivisors P z) :
    0 < r := by
  have hrP : r ∣ P := (Nat.mem_divisors.mp (Finset.mem_filter.mp hr).1).1
  have hP : P ≠ 0 := (Nat.mem_divisors.mp (Finset.mem_filter.mp hr).1).2
  exact Nat.pos_of_dvd_of_pos hrP (Nat.pos_of_ne_zero hP)

theorem levelDivisor_le {P z r : ℕ} (hr : r ∈ levelDivisors P z) :
    r ≤ z := (Finset.mem_filter.mp hr).2

theorem selbergDenominator_summand_nonneg (r : ℕ) :
    0 ≤ (ArithmeticFunction.moebius r : ℝ) ^ 2 /
      (Nat.totient r : ℝ) := by positivity

/-- The `r=1` term makes the finite Selberg denominator at least one. -/
theorem one_le_selbergDenominator
    {P z : ℕ} (hP : 0 < P) (hz : 1 ≤ z) :
    1 ≤ selbergDenominator P z := by
  unfold selbergDenominator
  calc
    (1 : ℝ) = (ArithmeticFunction.moebius 1 : ℝ) ^ 2 /
        (Nat.totient 1 : ℝ) := by simp
    _ ≤ ∑ r ∈ levelDivisors P z,
        (ArithmeticFunction.moebius r : ℝ) ^ 2 /
          (Nat.totient r : ℝ) := by
      exact Finset.single_le_sum
        (fun r _ => selbergDenominator_summand_nonneg r)
        (one_mem_levelDivisors hP hz)

theorem selbergDenominator_pos
    {P z : ℕ} (hP : 0 < P) (hz : 1 ≤ z) :
    0 < selbergDenominator P z :=
  lt_of_lt_of_le (by norm_num) (one_le_selbergDenominator hP hz)

/-- The diagonal coordinates of the optimal finite Selberg vector. -/
def selbergY (P z r : ℕ) : ℝ :=
  if r ∈ levelDivisors P z then
    (ArithmeticFunction.moebius r : ℝ) /
      ((Nat.totient r : ℝ) * selbergDenominator P z)
  else 0

/-- Möbius inversion of the optimal diagonal vector.  This is a literal
level-`z` sequence on all naturals, not an existential placeholder. -/
def optimalSelbergWeight (P z d : ℕ) : ℝ :=
  (d : ℝ) * ∑ r ∈ levelDivisors P z,
    if d ∣ r then
      (ArithmeticFunction.moebius (r / d) : ℝ) * selbergY P z r
    else 0

/-- The explicit weights vanish above level `z`. -/
theorem optimalSelbergWeight_eq_zero_of_lt
    {P z d : ℕ} (hd : z < d) :
    optimalSelbergWeight P z d = 0 := by
  unfold optimalSelbergWeight
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro r hr
  have hrz : r ≤ z := levelDivisor_le hr
  have hnot : ¬d ∣ r := by
    intro hdr
    have hrpos := levelDivisor_pos hr
    exact (not_le_of_gt hd) ((Nat.le_of_dvd hrpos hdr).trans hrz)
  simp [hnot]

/-- The Möbius-inverted vector has the required normalization `λ₁ = 1`. -/
theorem optimalSelbergWeight_one
    {P z : ℕ} (hP : 0 < P) (hz : 1 ≤ z) :
    optimalSelbergWeight P z 1 = 1 := by
  have hG : selbergDenominator P z ≠ 0 :=
    (selbergDenominator_pos hP hz).ne'
  unfold optimalSelbergWeight
  simp only [Nat.cast_one, one_mul, one_dvd, if_true, Nat.div_one]
  calc
    (∑ r ∈ levelDivisors P z,
        (ArithmeticFunction.moebius r : ℝ) * selbergY P z r) =
      ∑ r ∈ levelDivisors P z,
        ((ArithmeticFunction.moebius r : ℝ) ^ 2 /
          (Nat.totient r : ℝ)) / selbergDenominator P z := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [selbergY, if_pos hr]
      ring
    _ = selbergDenominator P z / selbergDenominator P z := by
      rw [← Finset.sum_div]
      rfl
    _ = 1 := div_self hG

/-! ## The lcm kernel and diagonalization -/

/-- Summing Euler's totient over the common divisors of two divisors of `P`
recovers their gcd. -/
theorem sum_totient_common_divisors_eq_gcd
    {P d e : ℕ} (hP : 0 < P) (hd : d ∣ P) (he : e ∣ P) :
    (∑ r ∈ P.divisors,
        if r ∣ d ∧ r ∣ e then (Nat.totient r : ℝ) else 0) =
      (d.gcd e : ℝ) := by
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd hP
  have hepos : 0 < e := Nat.pos_of_dvd_of_pos he hP
  have hgpos : 0 < d.gcd e := Nat.gcd_pos_of_pos_left e hdpos
  rw [← Finset.sum_filter]
  have hset :
      P.divisors.filter (fun r => r ∣ d ∧ r ∣ e) = (d.gcd e).divisors := by
    ext r
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hrP, _⟩, hrd, hre⟩
      exact ⟨Nat.dvd_gcd hrd hre, hgpos.ne'⟩
    · rintro ⟨hrg, _⟩
      have hrd : r ∣ d := dvd_trans hrg (Nat.gcd_dvd_left d e)
      have hre : r ∣ e := dvd_trans hrg (Nat.gcd_dvd_right d e)
      exact ⟨⟨dvd_trans hrd hd, hP.ne'⟩, hrd, hre⟩
  rw [hset]
  exact_mod_cast Nat.sum_totient (d.gcd e)

/-- The reciprocal-lcm kernel is the totient Gram kernel on divisors of a
positive ambient product. -/
theorem inv_lcm_eq_sum_totient_kernel
    {P d e : ℕ} (hP : 0 < P) (hd : d ∣ P) (he : e ∣ P) :
    ((d.lcm e : ℕ) : ℝ)⁻¹ =
      ∑ r ∈ P.divisors,
        if r ∣ d ∧ r ∣ e then
          (Nat.totient r : ℝ) / ((d : ℝ) * (e : ℝ))
        else 0 := by
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd hP
  have hepos : 0 < e := Nat.pos_of_dvd_of_pos he hP
  have hlpos : 0 < d.lcm e := Nat.lcm_pos hdpos hepos
  calc
    ((d.lcm e : ℕ) : ℝ)⁻¹ =
        (d.gcd e : ℝ) / ((d : ℝ) * (e : ℝ)) := by
      rw [inv_eq_one_div]
      field_simp
      exact_mod_cast (by
        simpa [mul_comm] using Nat.gcd_mul_lcm d e)
    _ = (∑ r ∈ P.divisors,
          if r ∣ d ∧ r ∣ e then (Nat.totient r : ℝ) else 0) /
        ((d : ℝ) * (e : ℝ)) := by
      rw [sum_totient_common_divisors_eq_gcd hP hd he]
    _ = ∑ r ∈ P.divisors,
        if r ∣ d ∧ r ∣ e then
          (Nat.totient r : ℝ) / ((d : ℝ) * (e : ℝ))
        else 0 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro r hr
      split <;> simp_all

/-- The upper-divisor transform which diagonalizes the reciprocal-lcm
quadratic form. -/
def selbergTransform (weights : ℕ → ℝ) (P r : ℕ) : ℝ :=
  ∑ d ∈ P.divisors, if r ∣ d then weights d / (d : ℝ) else 0

/-- Exact finite Gram diagonalization of the quadratic form used by the MAP
Shiu slice. -/
theorem selbergMainQuadratic_eq_diagonal
    (weights : ℕ → ℝ) {P : ℕ} (hP : 0 < P) :
    selbergMainQuadratic weights P =
      ∑ r ∈ P.divisors,
        (Nat.totient r : ℝ) * selbergTransform weights P r ^ 2 := by
  let D := P.divisors
  let F := fun d e r : ℕ =>
    if r ∣ d ∧ r ∣ e then
      (Nat.totient r : ℝ) *
        (weights d / (d : ℝ)) * (weights e / (e : ℝ))
    else 0
  have hkernel (d : ℕ) (hd : d ∈ D) (e : ℕ) (he : e ∈ D) :
      weights d * weights e / (d.lcm e : ℝ) =
        ∑ r ∈ D, F d e r := by
    have hdP : d ∣ P := (Nat.mem_divisors.mp hd).1
    have heP : e ∣ P := (Nat.mem_divisors.mp he).1
    rw [div_eq_mul_inv, inv_lcm_eq_sum_totient_kernel hP hdP heP,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    dsimp [F]
    by_cases hrd : r ∣ d <;> by_cases hre : r ∣ e <;>
      simp [hrd, hre] <;> ring
  unfold selbergMainQuadratic
  change (∑ d ∈ D, ∑ e ∈ D,
      weights d * weights e / (d.lcm e : ℝ)) = _
  calc
    (∑ d ∈ D, ∑ e ∈ D,
        weights d * weights e / (d.lcm e : ℝ)) =
      ∑ d ∈ D, ∑ e ∈ D, ∑ r ∈ D, F d e r := by
        apply Finset.sum_congr rfl
        intro d hd
        apply Finset.sum_congr rfl
        intro e he
        exact hkernel d hd e he
    _ = ∑ d ∈ D, ∑ r ∈ D, ∑ e ∈ D, F d e r := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.sum_comm]
    _ = ∑ r ∈ D, ∑ d ∈ D, ∑ e ∈ D, F d e r := by
      rw [Finset.sum_comm]
    _ = ∑ r ∈ D,
        (Nat.totient r : ℝ) * selbergTransform weights P r ^ 2 := by
      apply Finset.sum_congr rfl
      intro r hr
      unfold selbergTransform
      change (∑ d ∈ D, ∑ e ∈ D, F d e r) = _
      calc
        (∑ d ∈ D, ∑ e ∈ D, F d e r) =
          ∑ d ∈ D, ∑ e ∈ D,
            (Nat.totient r : ℝ) *
              (if r ∣ d then weights d / (d : ℝ) else 0) *
                (if r ∣ e then weights e / (e : ℝ) else 0) := by
            apply Finset.sum_congr rfl
            intro d hd
            apply Finset.sum_congr rfl
            intro e he
            dsimp [F]
            by_cases hrd : r ∣ d <;> by_cases hre : r ∣ e <;>
              simp [hrd, hre]
        _ = (Nat.totient r : ℝ) *
            (∑ d ∈ D, if r ∣ d then weights d / (d : ℝ) else 0) *
              (∑ e ∈ D, if r ∣ e then weights e / (e : ℝ) else 0) := by
            calc
              (∑ d ∈ D, ∑ e ∈ D,
                  (Nat.totient r : ℝ) *
                    (if r ∣ d then weights d / (d : ℝ) else 0) *
                      (if r ∣ e then weights e / (e : ℝ) else 0)) =
                ∑ d ∈ D,
                  ((Nat.totient r : ℝ) *
                    (if r ∣ d then weights d / (d : ℝ) else 0)) *
                    (∑ e ∈ D,
                      if r ∣ e then weights e / (e : ℝ) else 0) := by
                    apply Finset.sum_congr rfl
                    intro d hd
                    rw [Finset.mul_sum]
              _ = (∑ d ∈ D,
                    (Nat.totient r : ℝ) *
                      (if r ∣ d then weights d / (d : ℝ) else 0)) *
                    (∑ e ∈ D,
                      if r ∣ e then weights e / (e : ℝ) else 0) := by
                    rw [Finset.sum_mul]
              _ = _ := by
                apply congrArg (fun x : ℝ => x *
                  (∑ e ∈ D,
                    if r ∣ e then weights e / (e : ℝ) else 0))
                rw [Finset.mul_sum]
        _ = (Nat.totient r : ℝ) *
            (∑ d ∈ D, if r ∣ d then weights d / (d : ℝ) else 0) ^ 2 := by
          rw [pow_two]
          ring

/-! ## Upper-divisor Möbius inversion -/

/-- The divisor sum of the real-cast Möbius function is the Kronecker delta
at one. -/
theorem sum_moebius_divisors_real (n : ℕ) :
    (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ)) =
      if n = 1 then 1 else 0 := by
  have h := DFunLike.congr_fun
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ)) n
  rw [ArithmeticFunction.coe_mul_zeta_apply] at h
  simpa [ArithmeticFunction.one_apply] using h

/-- Möbius cancellation on the finite interval of divisors between `r` and
`s`. -/
theorem sum_moebius_quotient_between
    {r s : ℕ} (hr : 0 < r) (hrs : r ∣ s) (hs : 0 < s) :
    (∑ d ∈ s.divisors,
        if r ∣ d then (ArithmeticFunction.moebius (s / d) : ℝ) else 0) =
      if r = s then 1 else 0 := by
  rw [← Finset.sum_filter]
  let t := s / r
  have ht : 0 < t := Nat.div_pos (Nat.le_of_dvd hs hrs) hr
  calc
    (∑ d ∈ s.divisors.filter (fun d => r ∣ d),
        (ArithmeticFunction.moebius (s / d) : ℝ)) =
      ∑ q ∈ t.divisors,
        (ArithmeticFunction.moebius (t / q) : ℝ) := by
      apply Finset.sum_bij'
        (fun d _ => d / r) (fun q _ => r * q)
      · intro d hd
        have hdata := Finset.mem_filter.mp hd
        have hds : d ∣ s := (Nat.mem_divisors.mp hdata.1).1
        have hdr : r ∣ d := hdata.2
        apply Nat.mem_divisors.mpr
        constructor
        · apply (Nat.dvd_div_iff_mul_dvd hrs).2
          simpa [Nat.mul_div_cancel' hdr] using hds
        · exact ht.ne'
      · intro q hq
        have hqt : q ∣ t := (Nat.mem_divisors.mp hq).1
        have hrq_s : r * q ∣ s := by
          simpa [t] using (Nat.dvd_div_iff_mul_dvd hrs).1 hqt
        apply Finset.mem_filter.mpr
        exact ⟨Nat.mem_divisors.mpr ⟨hrq_s, hs.ne'⟩,
          dvd_mul_right r q⟩
      · intro d hd
        exact Nat.mul_div_cancel' (Finset.mem_filter.mp hd).2
      · intro q hq
        exact Nat.mul_div_cancel_left q hr
      · intro d hd
        have hdr : r ∣ d := (Finset.mem_filter.mp hd).2
        rw [Nat.div_div_eq_div_mul, Nat.mul_div_cancel' hdr]
    _ = ∑ q ∈ t.divisors,
        (ArithmeticFunction.moebius q : ℝ) := by
      exact Nat.sum_div_divisors t
        (fun q => (ArithmeticFunction.moebius q : ℝ))
    _ = if t = 1 then 1 else 0 := sum_moebius_divisors_real t
    _ = if r = s then 1 else 0 := by
      have htiff : t = 1 ↔ r = s := by
        dsimp [t]
        constructor
        · intro h
          have hmul := Nat.mul_div_cancel' hrs
          rw [h, mul_one] at hmul
          exact hmul
        · rintro rfl
          exact Nat.div_self hs
      simp only [htiff]

/-- Ambient-divisor version of `sum_moebius_quotient_between`. -/
theorem sum_moebius_quotient_between_ambient
    {P r s : ℕ} (hP : 0 < P) (hr : 0 < r) (hsP : s ∣ P)
    (hrs : r ∣ s) :
    (∑ d ∈ P.divisors,
        if r ∣ d ∧ d ∣ s then
          (ArithmeticFunction.moebius (s / d) : ℝ)
        else 0) = if r = s then 1 else 0 := by
  have hs : 0 < s := Nat.pos_of_dvd_of_pos hsP hP
  rw [← Finset.sum_filter]
  have hset :
      P.divisors.filter (fun d => r ∣ d ∧ d ∣ s) =
        s.divisors.filter (fun d => r ∣ d) := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hdP, _⟩, hrd, hds⟩
      exact ⟨⟨hds, hs.ne'⟩, hrd⟩
    · rintro ⟨⟨hds, _⟩, hrd⟩
      exact ⟨⟨dvd_trans hds hsP, hP.ne'⟩, hrd, hds⟩
  rw [hset, Finset.sum_filter]
  exact sum_moebius_quotient_between hr hrs hs

/-- The upper-divisor transform of the explicit Möbius-inverted weights is
exactly the chosen diagonal vector. -/
theorem selbergTransform_optimalSelbergWeight
    {P z r : ℕ} (hP : 0 < P) (hrP : r ∈ P.divisors) :
    selbergTransform (optimalSelbergWeight P z) P r = selbergY P z r := by
  let D := P.divisors
  let L := levelDivisors P z
  have hrpos : 0 < r := Nat.pos_of_mem_divisors hrP
  have hrdivP : r ∣ P := (Nat.mem_divisors.mp hrP).1
  unfold selbergTransform
  change (∑ d ∈ D,
      if r ∣ d then optimalSelbergWeight P z d / (d : ℝ) else 0) = _
  calc
    (∑ d ∈ D,
        if r ∣ d then optimalSelbergWeight P z d / (d : ℝ) else 0) =
      ∑ d ∈ D, ∑ s ∈ L,
        if r ∣ d ∧ d ∣ s then
          (ArithmeticFunction.moebius (s / d) : ℝ) * selbergY P z s
        else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
      by_cases hrd : r ∣ d
      · rw [if_pos hrd]
        unfold optimalSelbergWeight
        change ((d : ℝ) *
            (∑ s ∈ L, if d ∣ s then
              (ArithmeticFunction.moebius (s / d) : ℝ) * selbergY P z s
            else 0)) / (d : ℝ) = _
        rw [mul_div_cancel_left₀ _ (by exact_mod_cast hdpos.ne')]
        apply Finset.sum_congr rfl
        intro s hs
        by_cases hds : d ∣ s <;> simp [hrd, hds]
      · rw [if_neg hrd]
        symm
        apply Finset.sum_eq_zero
        intro s hs
        simp [hrd]
    _ = ∑ s ∈ L, ∑ d ∈ D,
        if r ∣ d ∧ d ∣ s then
          (ArithmeticFunction.moebius (s / d) : ℝ) * selbergY P z s
        else 0 := by rw [Finset.sum_comm]
    _ = ∑ s ∈ L, selbergY P z s *
        (∑ d ∈ D, if r ∣ d ∧ d ∣ s then
          (ArithmeticFunction.moebius (s / d) : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hcond : r ∣ d ∧ d ∣ s <;> simp [hcond]
      ring
    _ = ∑ s ∈ L, selbergY P z s * (if r = s then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro s hs
      have hsP : s ∣ P :=
        (Nat.mem_divisors.mp (Finset.mem_filter.mp hs).1).1
      by_cases hrs : r ∣ s
      · rw [sum_moebius_quotient_between_ambient hP hrpos hsP hrs]
      · have hrsne : r ≠ s := by
          intro h
          subst s
          exact hrs (dvd_refl r)
        rw [if_neg hrsne]
        have hzero :
            (∑ d ∈ D, if r ∣ d ∧ d ∣ s then
              (ArithmeticFunction.moebius (s / d) : ℝ) else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro d hd
          by_cases hcond : r ∣ d ∧ d ∣ s
          · exact (hrs (dvd_trans hcond.1 hcond.2)).elim
          · simp [hcond]
        rw [hzero, mul_zero]
    _ = selbergY P z r := by
      by_cases hrL : r ∈ L
      · rw [Finset.sum_eq_single r]
        · simp
        · intro s hs hsr
          simp [Ne.symm hsr]
        · exact fun h => (h hrL).elim
      · rw [selbergY, if_neg hrL]
        apply Finset.sum_eq_zero
        intro s hs
        have hrsne : r ≠ s := by
          intro h
          subst s
          exact hrL hs
        simp [hrsne]

/-! ## Exact value of the finite Selberg quadratic form -/

/-- The explicit Möbius-inverted vector attains exactly the reciprocal of
the finite Selberg denominator.  This is the algebraic core of the Selberg
upper-bound sieve; no asymptotic estimate is used here. -/
theorem selbergMainQuadratic_optimalSelbergWeight
    {P z : ℕ} (hP : 0 < P) (hz : 1 ≤ z) :
    selbergMainQuadratic (optimalSelbergWeight P z) P =
      1 / selbergDenominator P z := by
  have hG : selbergDenominator P z ≠ 0 :=
    (selbergDenominator_pos hP hz).ne'
  rw [selbergMainQuadratic_eq_diagonal _ hP]
  calc
    (∑ r ∈ P.divisors,
        (Nat.totient r : ℝ) *
          selbergTransform (optimalSelbergWeight P z) P r ^ 2) =
      ∑ r ∈ P.divisors,
        (Nat.totient r : ℝ) * selbergY P z r ^ 2 := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [selbergTransform_optimalSelbergWeight hP hr]
    _ = ∑ r ∈ levelDivisors P z,
        (Nat.totient r : ℝ) * selbergY P z r ^ 2 := by
      symm
      apply Finset.sum_subset
      · intro r hr
        exact (Finset.mem_filter.mp hr).1
      · intro r hrP hrL
        rw [selbergY, if_neg hrL]
        simp
    _ = ∑ r ∈ levelDivisors P z,
        ((ArithmeticFunction.moebius r : ℝ) ^ 2 /
          (Nat.totient r : ℝ)) /
            selbergDenominator P z ^ 2 := by
      apply Finset.sum_congr rfl
      intro r hr
      have hrpos : 0 < r := levelDivisor_pos hr
      have hphiNat : Nat.totient r ≠ 0 :=
        (Nat.ne_of_gt ((Nat.totient_pos).2 hrpos))
      have hphi : (Nat.totient r : ℝ) ≠ 0 := by
        exact_mod_cast hphiNat
      rw [selbergY, if_pos hr]
      field_simp
    _ = selbergDenominator P z / selbergDenominator P z ^ 2 := by
      rw [← Finset.sum_div]
      rfl
    _ = 1 / selbergDenominator P z := by
      field_simp

/-! ## Specialization to the literal prime product -/

/-- The literal product used by the Shiu frontend is squarefree. -/
theorem sievingProduct_squarefree (z modulus : ℕ) :
    Squarefree (sievingProduct z modulus) := by
  unfold sievingProduct
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    change IsRelPrime p q
    rw [← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes
      (Finset.mem_filter.mp hp).2.1
      (Finset.mem_filter.mp hq).2.1).2 hpq
  · intro p hp
    exact (Finset.mem_filter.mp hp).2.1.prime.squarefree

/-- On nested divisors of a squarefree product, the two Möbius signs in the
inverted Selberg coefficient collapse to the sign of the lower divisor. -/
theorem moebius_quotient_mul_moebius_of_squarefree
    {P d r : ℕ} (hPsq : Squarefree P) (hrP : r ∣ P) (hdr : d ∣ r) :
    (ArithmeticFunction.moebius (r / d) : ℝ) *
        (ArithmeticFunction.moebius r : ℝ) =
      (ArithmeticFunction.moebius d : ℝ) := by
  have hPne : P ≠ 0 := hPsq.ne_zero
  have hrpos : 0 < r := Nat.pos_of_dvd_of_pos hrP (Nat.pos_of_ne_zero hPne)
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdr hrpos
  have hrsq : Squarefree r := Squarefree.squarefree_of_dvd hrP hPsq
  have hqsq : Squarefree (r / d) :=
    Squarefree.squarefree_of_dvd (Nat.div_dvd_of_dvd hdr) hrsq
  have hcop : (r / d).Coprime d := by
    have h := Nat.coprime_div_gcd_of_squarefree hrsq hdpos.ne'
    rw [Nat.gcd_eq_right_iff_dvd.mpr hdr] at h
    exact h
  have hmu : ArithmeticFunction.moebius r =
      ArithmeticFunction.moebius d * ArithmeticFunction.moebius (r / d) := by
    have h := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
      hcop.symm
    rwa [Nat.mul_div_cancel' hdr] at h
  have hmusq : (ArithmeticFunction.moebius (r / d) : ℝ) ^ 2 = 1 := by
    exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hqsq
  rw [hmu]
  push_cast
  calc
    (ArithmeticFunction.moebius (r / d) : ℝ) *
        ((ArithmeticFunction.moebius d : ℝ) *
          (ArithmeticFunction.moebius (r / d) : ℝ)) =
      (ArithmeticFunction.moebius d : ℝ) *
        (ArithmeticFunction.moebius (r / d) ^ 2 : ℝ) := by ring
    _ = (ArithmeticFunction.moebius d : ℝ) := by rw [hmusq, mul_one]

/-- For a positive squarefree integer, the reciprocal-totient divisor mass
is exactly `d / phi(d)`. -/
theorem sum_inv_totient_divisors_of_squarefree
    {d : ℕ} (hdpos : 0 < d) (hdsq : Squarefree d) :
    (∑ t ∈ d.divisors, 1 / (Nat.totient t : ℝ)) =
      (d : ℝ) / (Nat.totient d : ℝ) := by
  have hphiDnat : Nat.totient d ≠ 0 :=
    Nat.ne_of_gt ((Nat.totient_pos).2 hdpos)
  have hphiD : (Nat.totient d : ℝ) ≠ 0 := by
    exact_mod_cast hphiDnat
  calc
    (∑ t ∈ d.divisors, 1 / (Nat.totient t : ℝ)) =
      ∑ t ∈ d.divisors,
        (Nat.totient (d / t) : ℝ) / (Nat.totient d : ℝ) := by
      apply Finset.sum_congr rfl
      intro t ht
      have htd : t ∣ d := (Nat.mem_divisors.mp ht).1
      have htpos : 0 < t := Nat.pos_of_dvd_of_pos htd hdpos
      have hcop : t.Coprime (d / t) := by
        have h := Nat.coprime_div_gcd_of_squarefree hdsq htpos.ne'
        rw [Nat.gcd_eq_right_iff_dvd.mpr htd] at h
        exact h.symm
      have hphi := Nat.totient_mul hcop
      rw [Nat.mul_div_cancel' htd] at hphi
      have hphiTnat : Nat.totient t ≠ 0 :=
        Nat.ne_of_gt ((Nat.totient_pos).2 htpos)
      have hphiT : (Nat.totient t : ℝ) ≠ 0 := by
        exact_mod_cast hphiTnat
      have hqpos : 0 < d / t :=
        Nat.div_pos (Nat.le_of_dvd hdpos htd) htpos
      have hphiQnat : Nat.totient (d / t) ≠ 0 :=
        Nat.ne_of_gt ((Nat.totient_pos).2 hqpos)
      have hphiQ : (Nat.totient (d / t) : ℝ) ≠ 0 := by
        exact_mod_cast hphiQnat
      rw [hphi]
      push_cast
      field_simp
    _ = (∑ t ∈ d.divisors, (Nat.totient (d / t) : ℝ)) /
        (Nat.totient d : ℝ) := by
      rw [Finset.sum_div]
    _ = (∑ t ∈ d.divisors, (Nat.totient t : ℝ)) /
        (Nat.totient d : ℝ) := by
      rw [Nat.sum_div_divisors d (fun t => (Nat.totient t : ℝ))]
    _ = (d : ℝ) / (Nat.totient d : ℝ) := by
      congr 1
      exact_mod_cast Nat.sum_totient d

/-- Cofactors which occur after restricting the Selberg level set to
multiples of `d`. -/
def cofactorDivisors (P z d : ℕ) : Finset ℕ :=
  (P / d).divisors.filter fun s => d * s ≤ z

/-- Reciprocal-totient mass of the admissible cofactors. -/
def cofactorMass (P z d : ℕ) : ℝ :=
  ∑ s ∈ cofactorDivisors P z d, 1 / (Nat.totient s : ℝ)

/-- Reindexing the multiples of `d` in the level set by their unique
cofactor. -/
theorem sum_level_multiples_eq_sum_cofactorDivisors
    {P z d : ℕ} (hP : 0 < P) (hdP : d ∣ P) (f : ℕ → ℝ) :
    (∑ r ∈ levelDivisors P z, if d ∣ r then f (r / d) else 0) =
      ∑ s ∈ cofactorDivisors P z d, f s := by
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdP hP
  rw [← Finset.sum_filter]
  apply Finset.sum_bij'
      (fun r _ => r / d) (fun s _ => d * s)
  · intro r hr
    have hdata := Finset.mem_filter.mp hr
    have hrL := hdata.1
    have hdr := hdata.2
    have hrP : r ∣ P :=
      (Nat.mem_divisors.mp (Finset.mem_filter.mp hrL).1).1
    apply Finset.mem_filter.mpr
    constructor
    · apply Nat.mem_divisors.mpr
      constructor
      · apply (Nat.dvd_div_iff_mul_dvd hdP).2
        simpa [Nat.mul_div_cancel' hdr] using hrP
      · exact (Nat.div_pos (Nat.le_of_dvd hP hdP) hdpos).ne'
    · simpa [Nat.mul_div_cancel' hdr] using levelDivisor_le hrL
  · intro s hs
    have hdata := Finset.mem_filter.mp hs
    have hsdiv : s ∣ P / d := (Nat.mem_divisors.mp hdata.1).1
    have hdsP : d * s ∣ P := (Nat.dvd_div_iff_mul_dvd hdP).1 hsdiv
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_filter.mpr
      exact ⟨Nat.mem_divisors.mpr ⟨hdsP, hP.ne'⟩, hdata.2⟩
    · exact dvd_mul_right d s
  · intro r hr
    exact Nat.mul_div_cancel' (Finset.mem_filter.mp hr).2
  · intro s hs
    exact Nat.mul_div_cancel_left s hdpos
  · intro r hr
    rfl

/-- Closed form of each optimal coefficient on a squarefree ambient
product. -/
theorem optimalSelbergWeight_eq_cofactorMass
    {P z d : ℕ} (hP : 0 < P) (hPsq : Squarefree P)
    (hz : 1 ≤ z) (hdP : d ∣ P) :
    optimalSelbergWeight P z d =
      (ArithmeticFunction.moebius d : ℝ) *
        ((d : ℝ) / (Nat.totient d : ℝ)) *
          cofactorMass P z d / selbergDenominator P z := by
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdP hP
  have hphiDnat : Nat.totient d ≠ 0 :=
    Nat.ne_of_gt ((Nat.totient_pos).2 hdpos)
  have hphiD : (Nat.totient d : ℝ) ≠ 0 := by
    exact_mod_cast hphiDnat
  have hG : selbergDenominator P z ≠ 0 :=
    (selbergDenominator_pos hP hz).ne'
  unfold optimalSelbergWeight
  calc
    (d : ℝ) *
        (∑ r ∈ levelDivisors P z,
          if d ∣ r then
            (ArithmeticFunction.moebius (r / d) : ℝ) * selbergY P z r
          else 0) =
      (d : ℝ) *
        (∑ r ∈ levelDivisors P z,
          if d ∣ r then
            (ArithmeticFunction.moebius d : ℝ) /
              ((Nat.totient d : ℝ) * (Nat.totient (r / d) : ℝ) *
                selbergDenominator P z)
          else 0) := by
      congr 1
      apply Finset.sum_congr rfl
      intro r hr
      by_cases hdr : d ∣ r
      · rw [if_pos hdr, if_pos hdr, selbergY, if_pos hr]
        have hrP : r ∣ P :=
          (Nat.mem_divisors.mp (Finset.mem_filter.mp hr).1).1
        have hrsq : Squarefree r := Squarefree.squarefree_of_dvd hrP hPsq
        have hcop : d.Coprime (r / d) := by
          have h := Nat.coprime_div_gcd_of_squarefree hrsq hdpos.ne'
          rw [Nat.gcd_eq_right_iff_dvd.mpr hdr] at h
          exact h.symm
        have hphi := Nat.totient_mul hcop
        rw [Nat.mul_div_cancel' hdr] at hphi
        rw [← mul_div_assoc,
          moebius_quotient_mul_moebius_of_squarefree hPsq hrP hdr,
          hphi]
        push_cast
        rfl
      · simp [hdr]
    _ = (d : ℝ) *
        (∑ s ∈ cofactorDivisors P z d,
          (ArithmeticFunction.moebius d : ℝ) /
            ((Nat.totient d : ℝ) * (Nat.totient s : ℝ) *
              selbergDenominator P z)) := by
      congr 1
      exact sum_level_multiples_eq_sum_cofactorDivisors hP hdP
        (fun s => (ArithmeticFunction.moebius d : ℝ) /
          ((Nat.totient d : ℝ) * (Nat.totient s : ℝ) *
            selbergDenominator P z))
    _ = (ArithmeticFunction.moebius d : ℝ) *
        ((d : ℝ) / (Nat.totient d : ℝ)) *
          cofactorMass P z d / selbergDenominator P z := by
      unfold cofactorMass
      have hfactor :
          (∑ s ∈ cofactorDivisors P z d,
            (ArithmeticFunction.moebius d : ℝ) /
              ((Nat.totient d : ℝ) * (Nat.totient s : ℝ) *
                selbergDenominator P z)) =
            ((ArithmeticFunction.moebius d : ℝ) /
              ((Nat.totient d : ℝ) * selbergDenominator P z)) *
              (∑ s ∈ cofactorDivisors P z d,
                1 / (Nat.totient s : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s hs
        field_simp
      rw [hfactor]
      field_simp

/-- Every admissible cofactor is coprime to the fixed divisor in a
squarefree ambient product. -/
theorem coprime_cofactor_of_squarefree
    {P z d s : ℕ} (hPsq : Squarefree P) (hdP : d ∣ P)
    (hs : s ∈ cofactorDivisors P z d) : d.Coprime s := by
  have hsdiv : s ∣ P / d :=
    (Nat.mem_divisors.mp (Finset.mem_filter.mp hs).1).1
  have hdsP : d * s ∣ P := (Nat.dvd_div_iff_mul_dvd hdP).1 hsdiv
  exact Nat.coprime_of_squarefree_mul
    (Squarefree.squarefree_of_dvd hdsP hPsq)

/-- Multiplication is injective on the cofactor/divisor rectangle because
the two coordinates live on coprime prime supports. -/
theorem cofactor_pairProduct_injOn
    {P z d : ℕ} (hP : 0 < P) (hPsq : Squarefree P) (hdP : d ∣ P) :
    Set.InjOn (fun x : ℕ × ℕ => x.2 * x.1)
      ↑((cofactorDivisors P z d).product d.divisors) := by
  intro a ha b hb hab
  rcases a with ⟨s₁, t₁⟩
  rcases b with ⟨s₂, t₂⟩
  change (s₁, t₁) ∈ (cofactorDivisors P z d).product d.divisors at ha
  change (s₂, t₂) ∈ (cofactorDivisors P z d).product d.divisors at hb
  change t₁ * s₁ = t₂ * s₂ at hab
  have ha' := Finset.mem_product.mp ha
  have hb' := Finset.mem_product.mp hb
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdP hP
  have ht₁d : t₁ ∣ d := (Nat.mem_divisors.mp ha'.2).1
  have ht₂d : t₂ ∣ d := (Nat.mem_divisors.mp hb'.2).1
  have hs₁cop : s₁.Coprime d :=
    (coprime_cofactor_of_squarefree hPsq hdP ha'.1).symm
  have hs₂cop : s₂.Coprime d :=
    (coprime_cofactor_of_squarefree hPsq hdP hb'.1).symm
  have ht : t₁ = t₂ := by
    have hg := congrArg (fun n : ℕ => n.gcd d) hab
    have hg₁ : (t₁ * s₁).gcd d = t₁ := by
      rw [mul_comm, hs₁cop.gcd_mul_left_cancel,
        Nat.gcd_eq_left_iff_dvd.mpr ht₁d]
    have hg₂ : (t₂ * s₂).gcd d = t₂ := by
      rw [mul_comm, hs₂cop.gcd_mul_left_cancel,
        Nat.gcd_eq_left_iff_dvd.mpr ht₂d]
    dsimp at hg
    rwa [hg₁, hg₂] at hg
  subst t₂
  have htpos : 0 < t₁ := Nat.pos_of_dvd_of_pos ht₁d hdpos
  have hs : s₁ = s₂ := Nat.eq_of_mul_eq_mul_left htpos hab
  subst s₂
  rfl

/-- Every product in the cofactor/divisor rectangle remains in the original
Selberg level set. -/
theorem cofactor_pairProduct_mem_level
    {P z d : ℕ} (hP : 0 < P) (hdP : d ∣ P)
    {x : ℕ × ℕ}
    (hx : x ∈ (cofactorDivisors P z d).product d.divisors) :
    x.2 * x.1 ∈ levelDivisors P z := by
  rcases x with ⟨s, t⟩
  have hs := (Finset.mem_product.mp hx).1
  have ht := (Finset.mem_product.mp hx).2
  have hsc := Finset.mem_filter.mp hs
  have hsdiv : s ∣ P / d := (Nat.mem_divisors.mp hsc.1).1
  have htd : t ∣ d := (Nat.mem_divisors.mp ht).1
  have hdsP : d * s ∣ P := (Nat.dvd_div_iff_mul_dvd hdP).1 hsdiv
  have htsP : t * s ∣ P :=
    dvd_trans (Nat.mul_dvd_mul_right htd s) hdsP
  apply Finset.mem_filter.mpr
  constructor
  · exact Nat.mem_divisors.mpr ⟨htsP, hP.ne'⟩
  · exact (Nat.mul_le_mul_right s (Nat.le_of_dvd
      (Nat.pos_of_dvd_of_pos hdP hP) htd)).trans hsc.2

/-- The complete divisor rectangle attached to `d` embeds in the Selberg
denominator.  This is the finite domination which makes every optimal
coefficient bounded by one. -/
theorem scaled_cofactorMass_le_selbergDenominator
    {P z d : ℕ} (hP : 0 < P) (hPsq : Squarefree P)
    (hdP : d ∣ P) :
    ((d : ℝ) / (Nat.totient d : ℝ)) * cofactorMass P z d ≤
      selbergDenominator P z := by
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdP hP
  have hdsq : Squarefree d := Squarefree.squarefree_of_dvd hdP hPsq
  let S := (cofactorDivisors P z d).product d.divisors
  let prod := fun x : ℕ × ℕ => x.2 * x.1
  have hinj : Set.InjOn prod ↑S := by
    exact cofactor_pairProduct_injOn hP hPsq hdP
  have himage : S.image prod ⊆ levelDivisors P z := by
    intro n hn
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hn
    exact cofactor_pairProduct_mem_level hP hdP hx
  calc
    ((d : ℝ) / (Nat.totient d : ℝ)) * cofactorMass P z d =
      (∑ t ∈ d.divisors, 1 / (Nat.totient t : ℝ)) *
        (∑ s ∈ cofactorDivisors P z d,
          1 / (Nat.totient s : ℝ)) := by
      rw [sum_inv_totient_divisors_of_squarefree hdpos hdsq]
      rfl
    _ = ∑ x ∈ S,
        1 / ((Nat.totient x.2 : ℝ) * (Nat.totient x.1 : ℝ)) := by
      dsimp [S]
      rw [Finset.sum_product_right]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      field_simp
    _ = ∑ n ∈ S.image prod,
        (ArithmeticFunction.moebius n : ℝ) ^ 2 /
          (Nat.totient n : ℝ) := by
      symm
      rw [Finset.sum_image hinj]
      apply Finset.sum_congr rfl
      intro x hx
      rcases x with ⟨s, t⟩
      have hmem := Finset.mem_product.mp hx
      have hnL : t * s ∈ levelDivisors P z :=
        cofactor_pairProduct_mem_level hP hdP hx
      have hnP : t * s ∣ P :=
        (Nat.mem_divisors.mp (Finset.mem_filter.mp hnL).1).1
      have hnsq : Squarefree (t * s) :=
        Squarefree.squarefree_of_dvd hnP hPsq
      have hmusq : (ArithmeticFunction.moebius (t * s) : ℝ) ^ 2 = 1 := by
        exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hnsq
      have htd : t ∣ d := (Nat.mem_divisors.mp hmem.2).1
      have hds : d.Coprime s :=
        coprime_cofactor_of_squarefree hPsq hdP hmem.1
      have hts : t.Coprime s :=
        Nat.Coprime.of_dvd htd (dvd_refl s) hds
      have hphi := Nat.totient_mul hts
      dsimp [prod]
      rw [hmusq, hphi]
      push_cast
      rfl
    _ ≤ ∑ n ∈ levelDivisors P z,
        (ArithmeticFunction.moebius n : ℝ) ^ 2 /
          (Nat.totient n : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg himage
      intro n hn hnimage
      positivity
    _ = selbergDenominator P z := rfl

theorem cofactorMass_nonneg (P z d : ℕ) : 0 ≤ cofactorMass P z d := by
  unfold cofactorMass
  positivity

/-- The literal optimal weights are bounded by one on a squarefree ambient
product. -/
theorem abs_optimalSelbergWeight_le_one
    {P z d : ℕ} (hP : 0 < P) (hPsq : Squarefree P) (hz : 1 ≤ z) :
    |optimalSelbergWeight P z d| ≤ 1 := by
  by_cases hdP : d ∣ P
  · have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdP hP
    have hdsq : Squarefree d := Squarefree.squarefree_of_dvd hdP hPsq
    have hmuabsInt : |ArithmeticFunction.moebius d| = 1 :=
      ArithmeticFunction.abs_moebius_eq_one_of_squarefree hdsq
    have hmuabs : |(ArithmeticFunction.moebius d : ℝ)| = 1 := by
      exact_mod_cast hmuabsInt
    have hphiNat : 0 < Nat.totient d := (Nat.totient_pos).2 hdpos
    have hphi : (0 : ℝ) < Nat.totient d := by exact_mod_cast hphiNat
    have hGpos : 0 < selbergDenominator P z :=
      selbergDenominator_pos hP hz
    have hscale : 0 ≤
        ((d : ℝ) / (Nat.totient d : ℝ)) * cofactorMass P z d := by
      exact mul_nonneg (div_nonneg (by positivity) hphi.le)
        (cofactorMass_nonneg P z d)
    rw [optimalSelbergWeight_eq_cofactorMass hP hPsq hz hdP]
    rw [abs_div, abs_mul, abs_mul, hmuabs, one_mul,
      abs_of_nonneg (div_nonneg (by positivity) hphi.le),
      abs_of_nonneg (cofactorMass_nonneg P z d), abs_of_pos hGpos]
    exact (div_le_one hGpos).2
      (scaled_cofactorMass_le_selbergDenominator hP hPsq hdP)
  · have hzero : optimalSelbergWeight P z d = 0 := by
      unfold optimalSelbergWeight
      apply mul_eq_zero_of_right
      apply Finset.sum_eq_zero
      intro r hr
      have hrP : r ∣ P :=
        (Nat.mem_divisors.mp (Finset.mem_filter.mp hr).1).1
      have hdr : ¬d ∣ r := by
        intro hdr
        exact hdP (dvd_trans hdr hrP)
      simp [hdr]
    rw [hzero, abs_zero]
    norm_num

/-- Once the standard denominator lower bound is supplied, the explicit
weights give the desired main quadratic estimate with the exact reciprocal
constant.  This theorem isolates the analytic input from all Lambda-square
algebra. -/
theorem selbergMainQuadratic_optimal_le_of_denominator_lower
    {c : ℝ} (hc : 0 < c) {z modulus : ℕ}
    (hmodulus : 0 < modulus) (hz : 2 ≤ z)
    (hdenominator :
      c * (Nat.totient modulus : ℝ) / (modulus : ℝ) *
          Real.log (z : ℝ) ≤
        selbergDenominator (sievingProduct z modulus) z) :
    selbergMainQuadratic
        (optimalSelbergWeight (sievingProduct z modulus) z)
        (sievingProduct z modulus) ≤
      (1 / c) * (modulus : ℝ) /
        ((Nat.totient modulus : ℝ) * Real.log (z : ℝ)) := by
  have hP : 0 < sievingProduct z modulus :=
    sievingProduct_pos z modulus
  have hz1 : 1 ≤ z := by omega
  have hGpos : 0 < selbergDenominator (sievingProduct z modulus) z :=
    selbergDenominator_pos hP hz1
  have hphiNat : 0 < Nat.totient modulus :=
    (Nat.totient_pos).2 hmodulus
  have hphi : (0 : ℝ) < Nat.totient modulus := by
    exact_mod_cast hphiNat
  have hzreal : (1 : ℝ) < z := by exact_mod_cast (show 1 < z by omega)
  have hlog : 0 < Real.log (z : ℝ) := Real.log_pos hzreal
  rw [selbergMainQuadratic_optimalSelbergWeight hP hz1]
  rw [div_le_iff₀ hGpos]
  calc
    (1 : ℝ) =
        ((1 / c) * (modulus : ℝ) /
          ((Nat.totient modulus : ℝ) * Real.log (z : ℝ))) *
        (c * (Nat.totient modulus : ℝ) / (modulus : ℝ) *
          Real.log (z : ℝ)) := by
      field_simp
    _ ≤ ((1 / c) * (modulus : ℝ) /
          ((Nat.totient modulus : ℝ) * Real.log (z : ℝ))) *
        selbergDenominator (sievingProduct z modulus) z := by
      apply mul_le_mul_of_nonneg_left hdenominator
      positivity

/-- The exact public MAP frontend follows from the sole remaining analytic
inequality for the explicit finite denominator.  All weights, normalization,
support, coefficient control, and Lambda-square algebra are discharged here. -/
theorem selbergMainWeightBound_of_uniform_denominator_lower
    {c : ℝ} (hc : 0 < c)
    (hdenominator : ∀ z modulus : ℕ, 0 < modulus → 2 ≤ z →
      c * (Nat.totient modulus : ℝ) / (modulus : ℝ) *
          Real.log (z : ℝ) ≤
        selbergDenominator (sievingProduct z modulus) z) :
    SelbergMainWeightBound := by
  refine ⟨1 / c, by positivity, ?_⟩
  intro z modulus hmodulus hz
  let P := sievingProduct z modulus
  let weights := optimalSelbergWeight P z
  have hP : 0 < P := sievingProduct_pos z modulus
  have hPsq : Squarefree P := sievingProduct_squarefree z modulus
  have hz1 : 1 ≤ z := by omega
  refine ⟨weights, ?_, ?_, ?_, ?_⟩
  · exact optimalSelbergWeight_one hP hz1
  · intro d hd
    exact optimalSelbergWeight_eq_zero_of_lt hd
  · intro d hd
    exact abs_optimalSelbergWeight_le_one hP hPsq hz1
  · exact selbergMainQuadratic_optimal_le_of_denominator_lower hc
      hmodulus hz (hdenominator z modulus hmodulus hz)

/-! ## Reduction of the remaining analytic denominator estimate -/

/-- Positive squarefree integers up to `z` which are coprime to the
progression modulus. -/
def squarefreeCoprimeLevel (z modulus : ℕ) : Finset ℕ :=
  (Finset.range (z + 1)).filter fun r =>
    0 < r ∧ Squarefree r ∧ r.Coprime modulus

/-- Every squarefree integer in the coprime level divides the literal sieve
product. -/
theorem squarefree_coprime_mem_level
    {z modulus r : ℕ} (hrpos : 0 < r) (hrsq : Squarefree r)
    (hrcop : r.Coprime modulus) (hrz : r ≤ z) :
    r ∈ levelDivisors (sievingProduct z modulus) z := by
  have hsubset : r.primeFactors ⊆ sievingPrimes z modulus := by
    intro p hp
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpr : p ∣ r := Nat.dvd_of_mem_primeFactors hp
    have hple : p ≤ z := (Nat.le_of_dvd hrpos hpr).trans hrz
    have hpcop : p.Coprime modulus :=
      Nat.Coprime.of_dvd hpr (dvd_refl modulus) hrcop
    have hpnot : ¬p ∣ modulus := hpprime.coprime_iff_not_dvd.mp hpcop
    simp [sievingPrimes, hpprime, hpnot, hple]
  have hrdiv : r ∣ sievingProduct z modulus := by
    rw [← Nat.prod_primeFactors_of_squarefree hrsq]
    exact Finset.prod_dvd_prod_of_subset r.primeFactors
      (sievingPrimes z modulus) id hsubset
  apply Finset.mem_filter.mpr
  exact ⟨Nat.mem_divisors.mpr
    ⟨hrdiv, (sievingProduct_pos z modulus).ne'⟩, hrz⟩

theorem squarefreeCoprimeLevel_subset_levelDivisors (z modulus : ℕ) :
    squarefreeCoprimeLevel z modulus ⊆
      levelDivisors (sievingProduct z modulus) z := by
  intro r hr
  have hdata := (Finset.mem_filter.mp hr).2
  have hrz : r ≤ z := by
    have := Finset.mem_range.mp (Finset.mem_filter.mp hr).1
    omega
  exact squarefree_coprime_mem_level hdata.1 hdata.2.1 hdata.2.2 hrz

/-- The Selberg denominator dominates the squarefree-coprime harmonic mass.
Thus its final lower bound is a classical one-variable harmonic-density
estimate, with no sieve-weight algebra left. -/
theorem squarefreeCoprimeHarmonic_le_selbergDenominator
    (z modulus : ℕ) :
    (∑ r ∈ squarefreeCoprimeLevel z modulus, 1 / (r : ℝ)) ≤
      selbergDenominator (sievingProduct z modulus) z := by
  calc
    (∑ r ∈ squarefreeCoprimeLevel z modulus, 1 / (r : ℝ)) ≤
      ∑ r ∈ squarefreeCoprimeLevel z modulus,
        (ArithmeticFunction.moebius r : ℝ) ^ 2 /
          (Nat.totient r : ℝ) := by
      apply Finset.sum_le_sum
      intro r hr
      have hdata := (Finset.mem_filter.mp hr).2
      have hrpos := hdata.1
      have hmusq : (ArithmeticFunction.moebius r : ℝ) ^ 2 = 1 := by
        exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree
          hdata.2.1
      rw [hmusq]
      have hphiNat : 0 < Nat.totient r := (Nat.totient_pos).2 hrpos
      have hphi : (0 : ℝ) < Nat.totient r := by exact_mod_cast hphiNat
      apply one_div_le_one_div_of_le hphi
      exact_mod_cast Nat.totient_le r
    _ ≤ ∑ r ∈ levelDivisors (sievingProduct z modulus) z,
        (ArithmeticFunction.moebius r : ℝ) ^ 2 /
          (Nat.totient r : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (squarefreeCoprimeLevel_subset_levelDivisors z modulus)
      intro r hr hrsmall
      positivity
    _ = selbergDenominator (sievingProduct z modulus) z := rfl

/-- A squarefree-coprime harmonic lower bound is now sufficient, verbatim,
to close the public Shiu Lemma 2 Selberg-weight endpoint. -/
theorem selbergMainWeightBound_of_squarefreeCoprimeHarmonic_lower
    {c : ℝ} (hc : 0 < c)
    (hharmonic : ∀ z modulus : ℕ, 0 < modulus → 2 ≤ z →
      c * (Nat.totient modulus : ℝ) / (modulus : ℝ) *
          Real.log (z : ℝ) ≤
        ∑ r ∈ squarefreeCoprimeLevel z modulus, 1 / (r : ℝ)) :
    SelbergMainWeightBound := by
  apply selbergMainWeightBound_of_uniform_denominator_lower hc
  intro z modulus hmodulus hz
  exact (hharmonic z modulus hmodulus hz).trans
    (squarefreeCoprimeHarmonic_le_selbergDenominator z modulus)

end ShiuSelbergMainWeight

#print axioms ShiuSelbergMainWeight.one_le_selbergDenominator
#print axioms ShiuSelbergMainWeight.optimalSelbergWeight_eq_zero_of_lt
#print axioms ShiuSelbergMainWeight.optimalSelbergWeight_one
#print axioms ShiuSelbergMainWeight.inv_lcm_eq_sum_totient_kernel
#print axioms ShiuSelbergMainWeight.selbergMainQuadratic_eq_diagonal
#print axioms ShiuSelbergMainWeight.sum_moebius_quotient_between
#print axioms ShiuSelbergMainWeight.selbergTransform_optimalSelbergWeight
#print axioms ShiuSelbergMainWeight.selbergMainQuadratic_optimalSelbergWeight
#print axioms ShiuSelbergMainWeight.sievingProduct_squarefree
#print axioms ShiuSelbergMainWeight.selbergMainQuadratic_optimal_le_of_denominator_lower
#print axioms ShiuSelbergMainWeight.abs_optimalSelbergWeight_le_one
#print axioms ShiuSelbergMainWeight.selbergMainWeightBound_of_uniform_denominator_lower
#print axioms ShiuSelbergMainWeight.squarefreeCoprimeHarmonic_le_selbergDenominator
#print axioms ShiuSelbergMainWeight.selbergMainWeightBound_of_squarefreeCoprimeHarmonic_lower
