import ShiuUniformContract
import MertensAnalyticLeaf
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.SmoothNumbers

/-!
# The Rankin and Euler-product core of Shiu's Lemma 4

Shiu (1980), Lemma 4, bounds an infinite harmonic tail of smooth numbers.
Section 5 of that paper only applies it to the finite subrange
`z^(1/2) <= n <= z`.  This file formalizes that finite subrange for the MAP
weight `tau_k(n)^2` and proves the complete Rankin-to-Euler-product reduction.

The source chooses

`delta = 1 - r * log r / (4 * log z)`.

Consequently the Rankin factor is *exactly*
`exp (-(1/8) * r * log r)`.  This sign and coefficient are retained below.
The only analytic comparison left after the main theorem in this file is the
finite prime-factor distortion estimate which changes `-1/8` to `-1/10`.
-/

namespace ShiuLemma4TauTail

set_option maxHeartbeats 250000

open ArithmeticFunction MixedMellinCert ShiuFoundation ShiuAnalyticLayer
open scoped ArithmeticFunction.zeta BigOperators

noncomputable section

/-- The finite smooth harmonic tail actually used in Shiu's Section 5.

`n ∈ smoothNumbers (y+1)` means that every prime factor of `n` is at most
`y`.  The lower cutoff is written over `ℝ` to preserve the literal
`z^(1/2)` in the source. -/
def tauSquareSmoothTail (k z y modulus : ℕ) : ℝ := by
  classical
  let source : Finset ℕ :=
    (Finset.Icc 1 z).filter (fun n : ℕ ↦
      (z : ℝ) ^ (1 / 2 : ℝ) ≤ (n : ℝ) ∧
        n ∈ Nat.smoothNumbers (y + 1) ∧ n.Coprime modulus)
  exact ∑ n ∈ source, (tauAF k n ^ 2 : ℝ) / (n : ℝ)

theorem tauSquareSmoothTail_eq_filterSum (k z y modulus : ℕ) :
    tauSquareSmoothTail k z y modulus =
      ∑ n ∈ (Finset.Icc 1 z).filter (fun n : ℕ ↦
          (z : ℝ) ^ (1 / 2 : ℝ) ≤ (n : ℝ) ∧
            n ∈ Nat.smoothNumbers (y + 1) ∧ n.Coprime modulus),
        (tauAF k n ^ 2 : ℝ) / (n : ℝ) := by
  rfl

/-- The Rankin-twisted multiplicative weight for the majorant `tau_R`. -/
def tauCoprimeRpowWeight (R modulus n : ℕ) (delta : ℝ) : ℝ :=
  if n.Coprime modulus then (tauAF R n : ℝ) * (n : ℝ) ^ (-delta) else 0

theorem tauCoprimeRpowWeight_nonneg
    (R modulus n : ℕ) (delta : ℝ) :
    0 ≤ tauCoprimeRpowWeight R modulus n delta := by
  unfold tauCoprimeRpowWeight
  split <;> positivity

theorem tauCoprimeRpowWeight_one
    (R modulus : ℕ) (delta : ℝ) :
    tauCoprimeRpowWeight R modulus 1 delta = 1 := by
  simp [tauCoprimeRpowWeight, (tauAF_isMultiplicative R).map_one]

theorem tauCoprimeRpowWeight_mul_of_coprime
    (R modulus : ℕ) (delta : ℝ) {m n : ℕ} (hmn : m.Coprime n) :
    tauCoprimeRpowWeight R modulus (m * n) delta =
      tauCoprimeRpowWeight R modulus m delta *
        tauCoprimeRpowWeight R modulus n delta := by
  unfold tauCoprimeRpowWeight
  by_cases hm : m.Coprime modulus <;>
    by_cases hn : n.Coprime modulus
  · have hprod : (m * n).Coprime modulus :=
      Nat.coprime_mul_iff_left.mpr ⟨hm, hn⟩
    rw [if_pos hprod, if_pos hm, if_pos hn]
    rw [(tauAF_isMultiplicative R).map_mul_of_coprime hmn]
    simp only [Nat.cast_mul]
    rw [Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
    push_cast
    ring
  · have hprod : ¬(m * n).Coprime modulus := by
      simpa [Nat.coprime_mul_iff_left, hm, hn]
    simp [hm, hn, hprod]
  · have hprod : ¬(m * n).Coprime modulus := by
      simpa [Nat.coprime_mul_iff_left, hm, hn]
    simp [hm, hn, hprod]
  · have hprod : ¬(m * n).Coprime modulus := by
      simpa [Nat.coprime_mul_iff_left, hm, hn]
    simp [hm, hn, hprod]

/-- For positive rank, the multichoose coefficient is in the standard
negative-binomial form. -/
theorem multichoose_eq_choose_add_pred
    (R e : ℕ) (hR : 1 ≤ R) :
    R.multichoose e = (e + (R - 1)).choose (R - 1) := by
  rw [Nat.multichoose_eq]
  have htop : R + e - 1 = e + (R - 1) := by omega
  rw [htop, Nat.choose_symm_add]

/-- Raising a natural prime power to a real exponent commutes with taking the
natural power outside. -/
theorem natCast_pow_rpow_neg (p e : ℕ) (delta : ℝ) :
    (((p ^ e : ℕ) : ℝ) ^ (-delta)) =
      ((p : ℝ) ^ (-delta)) ^ e := by
  rw [Nat.cast_pow, ← Real.rpow_natCast]
  calc
    (((p : ℝ) ^ (e : ℝ)) ^ (-delta)) =
        (p : ℝ) ^ ((e : ℝ) * (-delta)) :=
      (Real.rpow_mul (Nat.cast_nonneg p) (e : ℝ) (-delta)).symm
    _ = (p : ℝ) ^ ((-delta) * (e : ℝ)) := by ring_nf
    _ = ((p : ℝ) ^ (-delta)) ^ (e : ℝ) :=
      Real.rpow_mul (Nat.cast_nonneg p) (-delta) (e : ℝ)
    _ = ((p : ℝ) ^ (-delta)) ^ e := by rw [Real.rpow_natCast]

theorem pow_rpow_neg (x : ℝ) (e : ℕ) (delta : ℝ) (hx : 0 ≤ x) :
    (x ^ e) ^ (-delta) = (x ^ (-delta)) ^ e := by
  rw [← Real.rpow_natCast]
  calc
    (x ^ (e : ℝ)) ^ (-delta) = x ^ ((e : ℝ) * (-delta)) :=
      (Real.rpow_mul hx (e : ℝ) (-delta)).symm
    _ = x ^ ((-delta) * (e : ℝ)) := by ring_nf
    _ = (x ^ (-delta)) ^ (e : ℝ) :=
      Real.rpow_mul hx (-delta) (e : ℝ)
    _ = (x ^ (-delta)) ^ e := by rw [Real.rpow_natCast]

/-- Exact local Euler factor for `tau_R(n) n^{-delta}` with the primitive
modulus mask.  Positivity of `delta`, rather than `delta > 1`, suffices because
only one prime is involved. -/
theorem tsum_tauCoprimeRpowWeight_primePow
    (R modulus p : ℕ) (delta : ℝ) (hR : 1 ≤ R)
    (hp : p.Prime) (hdelta : 0 < delta) :
    (∑' e : ℕ, tauCoprimeRpowWeight R modulus (p ^ e) delta) =
      if p ∣ modulus then 1
      else 1 / (1 - (p : ℝ) ^ (-delta)) ^ R := by
  by_cases hpmod : p ∣ modulus
  · rw [if_pos hpmod]
    have hfun :
        (fun e : ℕ ↦ tauCoprimeRpowWeight R modulus (p ^ e) delta) =
          fun e : ℕ ↦ if e = 0 then 1 else 0 := by
      funext e
      cases e with
      | zero => simp [tauCoprimeRpowWeight,
          (tauAF_isMultiplicative R).map_one]
      | succ e =>
          have hnot : ¬(p ^ (e + 1)).Coprime modulus := by
            intro hcop
            have hpp : p.Coprime p :=
              Nat.Coprime.of_dvd (dvd_pow_self p (by omega)) hpmod hcop
            exact hp.ne_one (hpp.eq_one_of_dvd (dvd_refl p))
          simp [tauCoprimeRpowWeight, hnot]
    rw [hfun, (hasSum_ite_eq 0 (1 : ℝ)).tsum_eq]
  · rw [if_neg hpmod]
    have hpcop : p.Coprime modulus := hp.coprime_iff_not_dvd.mpr hpmod
    have hnorm : ‖(p : ℝ) ^ (-delta)‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
      exact Real.rpow_lt_one_of_one_lt_of_neg
        (by exact_mod_cast hp.one_lt) (by linarith)
    have hseries := tsum_choose_mul_geometric_of_norm_lt_one
      (𝕜 := ℝ) (R - 1) hnorm
    rw [show R - 1 + 1 = R by omega] at hseries
    rw [← hseries]
    apply tsum_congr
    intro e
    have hpowcop : (p ^ e).Coprime modulus := hpcop.pow_left e
    rw [tauCoprimeRpowWeight, if_pos hpowcop,
      tauAF_prime_pow_eq_multichoose R e p hp,
      multichoose_eq_choose_add_pred R e hR]
    norm_num [Nat.cast_pow]
    rw [pow_rpow_neg (p : ℝ) e delta (by positivity)]
    exact Or.inl rfl

/-- Summability of every local prime-power series. -/
theorem summable_norm_tauCoprimeRpowWeight_primePow
    (R modulus : ℕ) (delta : ℝ) (hR : 1 ≤ R) (hdelta : 0 < delta)
    {p : ℕ} (hp : p.Prime) :
    Summable (fun e : ℕ ↦
      ‖tauCoprimeRpowWeight R modulus (p ^ e) delta‖) := by
  by_cases hpmod : p ∣ modulus
  · have hfun :
        (fun e : ℕ ↦ ‖tauCoprimeRpowWeight R modulus (p ^ e) delta‖) =
          fun e : ℕ ↦ if e = 0 then 1 else 0 := by
      funext e
      cases e with
      | zero => simp [tauCoprimeRpowWeight,
          (tauAF_isMultiplicative R).map_one]
      | succ e =>
          have hnot : ¬(p ^ (e + 1)).Coprime modulus := by
            intro hcop
            have hpp : p.Coprime p :=
              Nat.Coprime.of_dvd (dvd_pow_self p (by omega)) hpmod hcop
            exact hp.ne_one (hpp.eq_one_of_dvd (dvd_refl p))
          simp [tauCoprimeRpowWeight, hnot]
    rw [hfun]
    exact (hasSum_ite_eq 0 (1 : ℝ)).summable
  · have hpcop : p.Coprime modulus := hp.coprime_iff_not_dvd.mpr hpmod
    have hnorm : ‖(p : ℝ) ^ (-delta)‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
      exact Real.rpow_lt_one_of_one_lt_of_neg
        (by exact_mod_cast hp.one_lt) (by linarith)
    have hs := summable_choose_mul_geometric_of_norm_lt_one
      (R := ℝ) (R - 1) hnorm
    have hfun :
        (fun e : ℕ ↦ ‖tauCoprimeRpowWeight R modulus (p ^ e) delta‖) =
          fun e : ℕ ↦
            ((e + (R - 1)).choose (R - 1) : ℝ) *
              ((p : ℝ) ^ (-delta)) ^ e := by
      funext e
      have hpowcop : (p ^ e).Coprime modulus := hpcop.pow_left e
      rw [Real.norm_eq_abs,
        abs_of_nonneg (tauCoprimeRpowWeight_nonneg ..),
        tauCoprimeRpowWeight, if_pos hpowcop,
        tauAF_prime_pow_eq_multichoose R e p hp,
        multichoose_eq_choose_add_pred R e hR]
      norm_num [Nat.cast_pow]
      rw [pow_rpow_neg (p : ℝ) e delta (by positivity)]
      exact Or.inl rfl
    rw [hfun]
    exact hs

/-- Exact smooth-number Euler product for the twisted `tau_R` weight. -/
theorem tsum_smooth_tauCoprimeRpowWeight_eq_eulerProduct
    (R modulus y : ℕ) (delta : ℝ) (hR : 1 ≤ R) (hdelta : 0 < delta) :
    (∑' n : (y + 1).smoothNumbers,
        tauCoprimeRpowWeight R modulus n delta) =
      ∏ p ∈ (y + 1).primesBelow,
        (if p ∣ modulus then 1
          else 1 / (1 - (p : ℝ) ^ (-delta)) ^ R) := by
  have hEuler :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
      (f := fun n ↦ tauCoprimeRpowWeight R modulus n delta)
      (tauCoprimeRpowWeight_one R modulus delta)
      (fun {_ _} hmn ↦
        tauCoprimeRpowWeight_mul_of_coprime R modulus delta hmn)
      (fun hp ↦ summable_norm_tauCoprimeRpowWeight_primePow
        R modulus delta hR hdelta hp)
      (y + 1)
  rw [hEuler.2.tsum_eq]
  apply Finset.prod_congr rfl
  intro p hpP
  exact tsum_tauCoprimeRpowWeight_primePow R modulus p delta hR
    (Nat.prime_of_mem_primesBelow hpP) hdelta

/-- The source's Rankin factor before choosing `delta`.  The literal square
weight is majorized by `tau_(k^2)` and the finite tail is injected into the
full smooth Euler product. -/
theorem tauSquareSmoothTail_le_rankinEulerProduct
    (k z y modulus : ℕ) (delta : ℝ)
    (hk : 1 ≤ k) (hz : 1 ≤ z) (hdelta0 : 0 < delta)
    (hdelta1 : delta ≤ 1) :
    tauSquareSmoothTail k z y modulus ≤
      (z : ℝ) ^ ((delta - 1) / 2) *
        ∏ p ∈ (y + 1).primesBelow,
          (if p ∣ modulus then 1
            else 1 / (1 - (p : ℝ) ^ (-delta)) ^ (k * k)) := by
  let R := k * k
  have hR : 1 ≤ R := by dsimp [R]; nlinarith
  let source : Finset ℕ :=
    (Finset.Icc 1 z).filter (fun n ↦
      (z : ℝ) ^ (1 / 2 : ℝ) ≤ (n : ℝ) ∧
        n ∈ Nat.smoothNumbers (y + 1) ∧ n.Coprime modulus)
  let embedFun : (↥source) → (y + 1).smoothNumbers := fun n ↦
    ⟨n.1, (Finset.mem_filter.mp n.2).2.2.1⟩
  let embed : (↥source) ↪ (y + 1).smoothNumbers :=
    ⟨embedFun, by
      intro a b h
      apply Subtype.ext
      exact congrArg (fun w : (y + 1).smoothNumbers ↦ (w : ℕ)) h⟩
  have hsmooth : Summable (fun n : (y + 1).smoothNumbers ↦
      tauCoprimeRpowWeight R modulus n delta) := by
    have hEuler :=
      EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
        (f := fun n ↦ tauCoprimeRpowWeight R modulus n delta)
        (tauCoprimeRpowWeight_one R modulus delta)
        (fun {_ _} hmn ↦
          tauCoprimeRpowWeight_mul_of_coprime R modulus delta hmn)
        (fun hp ↦ summable_norm_tauCoprimeRpowWeight_primePow
          R modulus delta hR hdelta0 hp)
        (y + 1)
    exact hEuler.1.of_norm
  have hpoint (n : ↥source) :
      (tauAF k n.1 ^ 2 : ℝ) / (n.1 : ℝ) ≤
        (z : ℝ) ^ ((delta - 1) / 2) *
          tauCoprimeRpowWeight R modulus (embedFun n) delta := by
    have hmem := (Finset.mem_filter.mp n.2).2
    have hnIcc := Finset.mem_Icc.mp (Finset.mem_filter.mp n.2).1
    have hnpos : (0 : ℝ) < n.1 := by exact_mod_cast hnIcc.1
    have hzpos : (0 : ℝ) < z := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hz)
    have hcop : n.1.Coprime modulus := hmem.2.2
    have hpow :
        (n.1 : ℝ) ^ (delta - 1) ≤
          ((z : ℝ) ^ (1 / 2 : ℝ)) ^ (delta - 1) :=
      Real.rpow_le_rpow_of_nonpos
        (Real.rpow_pos_of_pos hzpos _) hmem.1 (by linarith)
    have hzrewrite :
        ((z : ℝ) ^ (1 / 2 : ℝ)) ^ (delta - 1) =
          (z : ℝ) ^ ((delta - 1) / 2) := by
      calc
        ((z : ℝ) ^ (1 / 2 : ℝ)) ^ (delta - 1) =
            (z : ℝ) ^ ((1 / 2 : ℝ) * (delta - 1)) :=
          (Real.rpow_mul hzpos.le (1 / 2 : ℝ) (delta - 1)).symm
        _ = (z : ℝ) ^ ((delta - 1) / 2) := by congr 1 <;> ring
    rw [hzrewrite] at hpow
    rw [tauCoprimeRpowWeight, if_pos hcop]
    have htau : (tauAF k n.1 ^ 2 : ℝ) ≤ (tauAF R n.1 : ℝ) := by
      exact_mod_cast tauAF_square_le_tauAF_mul k n.1
    have hfactor :
        (n.1 : ℝ)⁻¹ =
          (n.1 : ℝ) ^ (-delta) * (n.1 : ℝ) ^ (delta - 1) := by
      calc
        (n.1 : ℝ)⁻¹ = (n.1 : ℝ) ^ (-1 : ℝ) :=
          (Real.rpow_neg_one (n.1 : ℝ)).symm
        _ = (n.1 : ℝ) ^ (-delta + (delta - 1)) := by
          congr 1 <;> ring
        _ = (n.1 : ℝ) ^ (-delta) * (n.1 : ℝ) ^ (delta - 1) :=
          Real.rpow_add hnpos (-delta) (delta - 1)
    rw [div_eq_mul_inv, hfactor]
    have hnonneg : 0 ≤ (n.1 : ℝ) ^ (-delta) := Real.rpow_nonneg hnpos.le _
    calc
      (tauAF k n.1 ^ 2 : ℝ) *
          ((n.1 : ℝ) ^ (-delta) * (n.1 : ℝ) ^ (delta - 1)) ≤
        (tauAF R n.1 : ℝ) *
          ((n.1 : ℝ) ^ (-delta) * (n.1 : ℝ) ^ (delta - 1)) := by
            gcongr
      _ = (n.1 : ℝ) ^ (delta - 1) *
          ((tauAF R n.1 : ℝ) * (n.1 : ℝ) ^ (-delta)) := by ring
      _ ≤ (z : ℝ) ^ ((delta - 1) / 2) *
          ((tauAF R n.1 : ℝ) * (n.1 : ℝ) ^ (-delta)) := by
            gcongr
  have hfinite : Summable (fun n : ↥source ↦
      (tauAF k n.1 ^ 2 : ℝ) / (n.1 : ℝ)) :=
    summable_of_finite_support (Set.toFinite _)
  have hsub :
      (∑' n : ↥source, (tauAF k n.1 ^ 2 : ℝ) / (n.1 : ℝ)) ≤
        ∑' m : (y + 1).smoothNumbers,
          (z : ℝ) ^ ((delta - 1) / 2) *
            tauCoprimeRpowWeight R modulus m delta := by
    apply Summable.tsum_le_tsum_of_inj embed embed.injective
    · intro m hm
      exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg z) _)
        (tauCoprimeRpowWeight_nonneg R modulus m delta)
    · exact hpoint
    · exact hfinite
    · exact hsmooth.mul_left _
  have hsumfactor :
      (∑' m : (y + 1).smoothNumbers,
          (z : ℝ) ^ ((delta - 1) / 2) *
            tauCoprimeRpowWeight R modulus m delta) =
        (z : ℝ) ^ ((delta - 1) / 2) *
          ∑' m : (y + 1).smoothNumbers,
            tauCoprimeRpowWeight R modulus m delta := by
    rw [tsum_mul_left]
  rw [hsumfactor,
    tsum_smooth_tauCoprimeRpowWeight_eq_eulerProduct
      R modulus y delta hR hdelta0] at hsub
  rw [tauSquareSmoothTail_eq_filterSum]
  change (∑ n ∈ source, (tauAF k n ^ 2 : ℝ) / (n : ℝ)) ≤ _
  rw [← Finset.sum_coe_sort]
  rw [← (hasSum_fintype (fun n : ↥source ↦
    (tauAF k n.1 ^ 2 : ℝ) / (n.1 : ℝ))).tsum_eq]
  simpa only [R] using hsub

/-- Shiu's source choice of the Rankin exponent. -/
def shiuDelta (z r : ℝ) : ℝ :=
  1 - r * Real.log r / (4 * Real.log z)

/-- The source range implies `3/4 <= delta <= 1`.  The upper endpoint
`r log r <= log z` is the non-asymptotic content of
`r <= log z / log log z` used on page 165. -/
theorem shiuDelta_mem_threeQuarter_one
    {z r : ℝ} (hz : 1 < z) (hr : 1 ≤ r)
    (hrange : r * Real.log r ≤ Real.log z) :
    (3 / 4 : ℝ) ≤ shiuDelta z r ∧ shiuDelta z r ≤ 1 := by
  have hlogz : 0 < Real.log z := Real.log_pos hz
  have hlogr : 0 ≤ Real.log r := Real.log_nonneg hr
  have hnum : 0 ≤ r * Real.log r := mul_nonneg (by positivity) hlogr
  constructor
  · unfold shiuDelta
    have hdiv : r * Real.log r / (4 * Real.log z) ≤ 1 / 4 := by
      apply (div_le_iff₀ (by positivity : 0 < 4 * Real.log z)).2
      nlinarith
    linarith
  · unfold shiuDelta
    have hdivnonneg : 0 ≤ r * Real.log r / (4 * Real.log z) := by
      positivity
    linarith

/-- The load-bearing exact calculation in Shiu's Lemma 4:
`z^((delta-1)/2) = exp (-(1/8) r log r)`. -/
theorem shiuDelta_rankinFactor_exact
    {z r : ℝ} (hz : 1 < z) :
    z ^ ((shiuDelta z r - 1) / 2) =
      Real.exp (-(1 / 8 : ℝ) * r * Real.log r) := by
  have hzpos : 0 < z := zero_lt_one.trans hz
  rw [Real.rpow_def_of_pos hzpos]
  apply congrArg Real.exp
  unfold shiuDelta
  have hlogz : Real.log z ≠ 0 := (Real.log_pos hz).ne'
  field_simp
  ring

/-- Fully certified finite specialization of the Rankin step in Shiu Lemma 4.
The negative `-(1/8) r log r` saving is exact.  No progression theorem or
unproved analytic estimate is assumed. -/
theorem tauSquareSmoothTail_le_shiuEulerProduct
    (k z y modulus : ℕ) (r : ℝ)
    (hk : 1 ≤ k) (hz : 3 ≤ z) (hr : 1 ≤ r)
    (hrange : r * Real.log r ≤ Real.log (z : ℝ)) :
    tauSquareSmoothTail k z y modulus ≤
      Real.exp (-(1 / 8 : ℝ) * r * Real.log r) *
        ∏ p ∈ (y + 1).primesBelow,
          (if p ∣ modulus then 1
            else 1 / (1 - (p : ℝ) ^ (-shiuDelta z r)) ^ (k * k)) := by
  have hz1 : (1 : ℝ) < z := by exact_mod_cast (show 1 < z by omega)
  have hdelta := shiuDelta_mem_threeQuarter_one hz1 hr hrange
  have hbase := tauSquareSmoothTail_le_rankinEulerProduct
    k z y modulus (shiuDelta z r) hk (by omega) (by linarith [hdelta.1]) hdelta.2
  rw [shiuDelta_rankinFactor_exact hz1] at hbase
  exact hbase

/-!
The first genuinely analytic residue is now isolated without restating the
tail theorem.  It is a finite Euler-product comparison.  For the source's
relation `y <= z^(1/r)`, Shiu proves it by expanding the prime factors at
`delta = shiuDelta z r`; the distortion costs at most
`exp(C_k + (1/40) r log r)`.  Combining that estimate with the theorem above
gives the published `-(1/10) r log r` exponent.
-/

/-- Exact finite prime-factor distortion proposition still needed to recover
the printed `-1/10` endpoint from the certified `-1/8` Rankin saving.
This is deliberately a proposition rather than an axiom or theorem. -/
def TauEulerDistortionTarget : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    ∃ C z0 : ℝ, 0 < C ∧ 1 < z0 ∧
      ∀ (z r : ℝ) (y modulus : ℕ),
        z0 ≤ z → 1 ≤ r → r * Real.log r ≤ Real.log z →
        (y : ℝ) ≤ z ^ r⁻¹ →
        (∏ p ∈ (y + 1).primesBelow,
            (if p ∣ modulus then 1
              else 1 / (1 - (p : ℝ) ^ (-shiuDelta z r)) ^ (k * k))) ≤
          C * Real.exp
            ((k * k : ℕ) *
                ∑ p ∈ (y + 1).primesBelow,
                  (if p ∣ modulus then 0 else (p : ℝ)⁻¹) +
              (1 / 40 : ℝ) * r * Real.log r)

end

end ShiuLemma4TauTail

#print axioms ShiuLemma4TauTail.tsum_tauCoprimeRpowWeight_primePow
#print axioms ShiuLemma4TauTail.tsum_smooth_tauCoprimeRpowWeight_eq_eulerProduct
#print axioms ShiuLemma4TauTail.tauSquareSmoothTail_le_rankinEulerProduct
#print axioms ShiuLemma4TauTail.shiuDelta_rankinFactor_exact
#print axioms ShiuLemma4TauTail.tauSquareSmoothTail_le_shiuEulerProduct
