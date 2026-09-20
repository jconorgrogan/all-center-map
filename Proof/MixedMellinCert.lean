import Mathlib

/-!
# Algebraic certification for the mixed-Mellin argument

This file deliberately proves only exact arithmetic statements.  It does not
postulate Shiu's theorem, the Fourier majorant, or the final analytic estimate.
-/

namespace MixedMellinCert

open ArithmeticFunction
open scoped ArithmeticFunction.zeta

/-- Algebraic extraction of the common factor in the determinant. -/
theorem determinant_factorization (d a b n₁ n₂ : ℤ) :
    (d * a) * n₁ - (d * b) * n₂ = d * (a * n₁ - b * n₂) := by
  ring

/-- Natural-number form of the nonnegative determinant parametrization:
`a*n₁ = ell + b*n₂` implies the original determinant is exactly `d*ell`. -/
theorem determinant_reconstruction {d a b n₁ n₂ ell : ℕ}
    (hdet : a * n₁ = ell + b * n₂) :
    (d * a) * n₁ = d * ell + (d * b) * n₂ := by
  calc
    (d * a) * n₁ = d * (a * n₁) := by ac_rfl
    _ = d * (ell + b * n₂) := by rw [hdet]
    _ = d * ell + (d * b) * n₂ := by ring

/-- The left residue in `a*n₁ = ell + b*n₂` has exactly the same content
modulo `b` as `ell`. -/
theorem left_residue_content {a b n₁ n₂ ell : ℕ} (hab : a.Coprime b)
    (hdet : a * n₁ = ell + b * n₂) : n₁.gcd b = ell.gcd b := by
  calc
    n₁.gcd b = b.gcd n₁ := Nat.gcd_comm _ _
    _ = b.gcd (a * n₁) := (hab.gcd_mul_left_cancel_right n₁).symm
    _ = b.gcd (ell + b * n₂) := by rw [hdet]
    _ = b.gcd ell := Nat.gcd_add_mul_left_right b ell n₂
    _ = ell.gcd b := Nat.gcd_comm _ _

/-- The right residue in `a*n₁ = ell + b*n₂` also has exactly the expected
content.  The proof explicitly cancels the coprime factor `b`. -/
theorem right_residue_content {a b n₁ n₂ ell : ℕ} (hab : a.Coprime b)
    (hdet : a * n₁ = ell + b * n₂) : n₂.gcd a = ell.gcd a := by
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd
    · have hbn : n₂.gcd a ∣ b * n₂ :=
        dvd_mul_of_dvd_right (Nat.gcd_dvd_left n₂ a) b
      have han : n₂.gcd a ∣ a * n₁ :=
        dvd_mul_of_dvd_left (Nat.gcd_dvd_right n₂ a) n₁
      have hsum : n₂.gcd a ∣ ell + b * n₂ := by simpa [hdet] using han
      exact (Nat.dvd_add_iff_left hbn).mpr hsum
    · exact Nat.gcd_dvd_right n₂ a
  · apply Nat.dvd_gcd
    · have hga : ell.gcd a ∣ a := Nat.gcd_dvd_right ell a
      have hgel : ell.gcd a ∣ ell := Nat.gcd_dvd_left ell a
      have han : ell.gcd a ∣ a * n₁ := dvd_mul_of_dvd_left hga n₁
      have hsum : ell.gcd a ∣ ell + b * n₂ := by simpa [hdet] using han
      have hbn : ell.gcd a ∣ b * n₂ :=
        (Nat.dvd_add_iff_right hgel).mpr hsum
      exact (Nat.Coprime.of_dvd_left hga hab).dvd_of_dvd_mul_left hbn
    · exact Nat.gcd_dvd_right ell a

/-- Dividing a residue and its modulus by their exact content produces a
primitive residue class. -/
theorem reduced_left_residue_coprime {a b n₁ n₂ ell : ℕ} (hab : a.Coprime b)
    (hb : 0 < b) (hdet : a * n₁ = ell + b * n₂) :
    (n₁ / ell.gcd b).Coprime (b / ell.gcd b) := by
  rw [← left_residue_content hab hdet]
  exact Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_right n₁ hb)

/-- The symmetric primitive-residue statement. -/
theorem reduced_right_residue_coprime {a b n₁ n₂ ell : ℕ} (hab : a.Coprime b)
    (ha : 0 < a) (hdet : a * n₁ = ell + b * n₂) :
    (n₂ / ell.gcd a).Coprime (a / ell.gcd a) := by
  rw [← right_residue_content hab hdet]
  exact Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_right n₂ ha)

/-- Exact parametrization of the zero determinant sector. -/
theorem zero_determinant_parametrization {a b n₁ n₂ : ℕ} (hab : a.Coprime b)
    (hb : 0 < b) (hdet : a * n₁ = b * n₂) :
    ∃ r : ℕ, n₁ = b * r ∧ n₂ = a * r := by
  have hb_n₁ : b ∣ n₁ := by
    apply hab.symm.dvd_of_dvd_mul_left
    rw [hdet]
    exact Nat.dvd_mul_right b n₂
  obtain ⟨r, hr⟩ := hb_n₁
  refine ⟨r, hr, ?_⟩
  apply Nat.eq_of_mul_eq_mul_left hb
  calc
    b * n₂ = a * n₁ := hdet.symm
    _ = a * (b * r) := by rw [hr]
    _ = b * (a * r) := by ac_rfl

/-- The parametrization really gives zero determinant. -/
theorem zero_determinant_of_parametrization (a b r : ℕ) :
    a * (b * r) = b * (a * r) := by
  ac_rfl

/-- Exact finite Dirichlet-polynomial square expansion.  This certifies the
algebraic Fubini step before any Fourier-support or integral estimate enters. -/
theorem finite_square_expansion {ι : Type*} (s : Finset ι) (c : ι → ℂ) :
    (∑ i ∈ s, c i) * star (∑ j ∈ s, c j) =
      ∑ i ∈ s, ∑ j ∈ s, c i * star (c j) := by
  rw [star_sum]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]

/-- If `a` and `b` are coprime, the two residue contents multiply to the
content against `a*b`.  This is the exact identity used for
`d₁*d₂ = gcd(ell,a*b)`. -/
theorem gcd_mul_gcd_of_coprime {ell a b : ℕ} (hab : a.Coprime b) :
    ell.gcd a * ell.gcd b = ell.gcd (a * b) := by
  let x := ell.gcd (a * b)
  have hxdiv : x ∣ a * b := Nat.gcd_dvd_right ell (a * b)
  have hx : x.gcd a * x.gcd b = x :=
    (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hab).2 hxdiv
  simpa [x, Nat.gcd_assoc, Nat.gcd_eq_right_iff_dvd,
    Nat.dvd_mul_right, Nat.dvd_mul_left] using hx

/-- Divisors of `gcd(ell,q)` are exactly the divisors of `q` which divide
`ell`. -/
theorem divisors_gcd_eq_filter {ell q : ℕ} (hq : q ≠ 0) :
    (ell.gcd q).divisors = {v ∈ q.divisors | v ∣ ell} := by
  rw [← Nat.divisors_filter_dvd_of_dvd hq (Nat.gcd_dvd_right ell q)]
  ext v
  simp only [Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hvq, _⟩, hvg⟩
    exact ⟨⟨hvq, hq⟩, hvg.trans (Nat.gcd_dvd_left ell q)⟩
  · rintro ⟨⟨hvq, _⟩, hvell⟩
    exact ⟨⟨hvq, hq⟩, Nat.dvd_gcd hvell hvq⟩

/-- Exact positive-determinant divisor-sum identity.  It has no additive
`+1`: if `L = 0`, both sides vanish. -/
theorem sum_gcd_divisorSum_eq_floor_sum (f : ℕ → ℕ) (L q : ℕ) (hq : q ≠ 0) :
    (∑ e ∈ Finset.range L, ∑ v ∈ ((e + 1).gcd q).divisors, f v) =
      ∑ v ∈ q.divisors, (L / v) * f v := by
  calc
    (∑ e ∈ Finset.range L, ∑ v ∈ ((e + 1).gcd q).divisors, f v) =
        ∑ e ∈ Finset.range L, ∑ v ∈ q.divisors,
          if v ∣ e + 1 then f v else 0 := by
            apply Finset.sum_congr rfl
            intro e he
            rw [divisors_gcd_eq_filter hq]
            rw [Finset.sum_filter]
    _ = ∑ v ∈ q.divisors, ∑ e ∈ Finset.range L,
          if v ∣ e + 1 then f v else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ v ∈ q.divisors, (L / v) * f v := by
            apply Finset.sum_congr rfl
            intro v hv
            rw [← Finset.sum_filter]
            simp [Nat.card_multiples, mul_comm]

/-- The `r`-fold divisor function, defined as an exact Dirichlet-convolution
power of zeta. -/
def tauAF (r : ℕ) : ArithmeticFunction ℕ :=
  (ζ : ArithmeticFunction ℕ) ^ r

/-- Exact divisor recurrence `tau_(r+1)(n) = sum_{d|n} tau_r(d)`. -/
theorem tauAF_succ_apply (r n : ℕ) :
    tauAF (r + 1) n = ∑ d ∈ n.divisors, tauAF r d := by
  unfold tauAF
  rw [pow_succ']
  exact ArithmeticFunction.zeta_mul_apply

/-- The exact positive-determinant identity in the notation of the paper.
There is no additive `+1`, including at `L = 0`. -/
theorem tau_gcd_sum_exact (r L q : ℕ) (hq : q ≠ 0) :
    (∑ e ∈ Finset.range L, tauAF (r + 1) ((e + 1).gcd q)) =
      ∑ v ∈ q.divisors, (L / v) * tauAF r v := by
  simpa only [tauAF_succ_apply] using
    sum_gcd_divisorSum_eq_floor_sum (tauAF r) L q hq

/-- Combining positive and negative nonzero determinants gives exactly twice
the positive sum.  This is the formal counterpart of the factor `2` in (5). -/
theorem signed_tau_gcd_sum_exact (r L q : ℕ) (hq : q ≠ 0) :
    2 * (∑ e ∈ Finset.range L, tauAF (r + 1) ((e + 1).gcd q)) =
      2 * ∑ v ∈ q.divisors, (L / v) * tauAF r v := by
  rw [tau_gcd_sum_exact r L q hq]

/-- A coarse consequence that still preserves the absence of an additive
constant in the determinant length. -/
theorem tau_gcd_sum_le_length_mul (r L q : ℕ) (hq : q ≠ 0) :
    (∑ e ∈ Finset.range L, tauAF (r + 1) ((e + 1).gcd q)) ≤
      L * ∑ v ∈ q.divisors, tauAF r v := by
  rw [tau_gcd_sum_exact r L q hq, Finset.mul_sum]
  exact Finset.sum_le_sum fun v hv ↦
    Nat.mul_le_mul_right (tauAF r v) (Nat.div_le_self L v)

/-- Exact affine exponent checks used in the rapid-transfer parameter budget. -/
theorem log_parameter_budget (A loss : ℝ) (hA : 0 ≤ A) (hloss : 0 ≤ loss) :
    let B := 4 * (A + loss + 20)
    let C := B + A + loss + 20
    let D := A + 2 * B + 20
    (-B / 2 + loss ≤ -A - 20) ∧
      B - C + loss = -A - 20 ∧
      2 * B - D = -A - 20 := by
  dsimp
  constructor
  · linarith
  constructor <;> ring

/-- Exact power-exponent checks for `theta = 2/15 + epsilon` and
`eta = epsilon/100`. -/
theorem aperture_exponent_budget (epsilon : ℝ) (heps : 0 < epsilon)
    (hepsUpper : epsilon ≤ 1 / 100) :
    let theta := 2 / 15 + epsilon
    let eta := epsilon / 100
    theta - 2 * eta > 1 / 8 ∧
      theta - eta > 0 ∧
      1 - theta > 1 / 2 ∧
      2 * eta - (1 - theta) < 0 := by
  dsimp
  norm_num at hepsUpper ⊢
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

end MixedMellinCert
