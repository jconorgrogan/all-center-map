import ShiuUniformContract
import MertensAnalyticLeaf
import Mathlib.NumberTheory.EulerProduct.Basic

/-!
# Shiu's harmonic mean lemma for the MAP divisor-square weight

This is the specialization of Shiu (1980), Lemma 3, to
`f(n) = tau_k(n)^2`.  The source lemma is a harmonic mean:

`sum_{n <= x, (n,q)=1} f(n)/n << exp (sum_{p <= x, p \nmid q} f(p)/p)`.

No progression estimate is asserted here.  The proof uses only a finite Euler
product and the already certified pointwise majorant
`tau_k(n)^2 <= tau_{k^2}(n)`.
-/

namespace ShiuLemma3TauMean

open ArithmeticFunction MixedMellinCert ShiuFoundation ShiuAnalyticLayer ShiuUniformContract
open scoped ArithmeticFunction.zeta BigOperators

noncomputable section

/-- The literal harmonic coprime mean in Shiu's Lemma 3. -/
def tauSquareCoprimeHarmonicSum (k x modulus : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 x,
    if n.Coprime modulus then (tauAF k n ^ 2 : ℝ) / (n : ℝ) else 0

/-- The multiplicative harmonic weight for the majorizing divisor function. -/
def tauCoprimeHarmonicWeight (r modulus n : ℕ) : ℝ :=
  if n.Coprime modulus then (tauAF r n : ℝ) / (n : ℝ) else 0

theorem tauCoprimeHarmonicWeight_nonneg (r modulus n : ℕ) :
    0 ≤ tauCoprimeHarmonicWeight r modulus n := by
  unfold tauCoprimeHarmonicWeight
  split <;> positivity

theorem tauCoprimeHarmonicWeight_one (r modulus : ℕ) :
    tauCoprimeHarmonicWeight r modulus 1 = 1 := by
  simp [tauCoprimeHarmonicWeight, (tauAF_isMultiplicative r).map_one]

theorem tauCoprimeHarmonicWeight_mul_of_coprime
    (r modulus : ℕ) {m n : ℕ} (hmn : m.Coprime n) :
    tauCoprimeHarmonicWeight r modulus (m * n) =
      tauCoprimeHarmonicWeight r modulus m *
        tauCoprimeHarmonicWeight r modulus n := by
  unfold tauCoprimeHarmonicWeight
  by_cases hm : m.Coprime modulus <;>
    by_cases hn : n.Coprime modulus
  · have hprod : (m * n).Coprime modulus := Nat.coprime_mul_iff_left.mpr ⟨hm, hn⟩
    rw [if_pos hprod, if_pos hm, if_pos hn]
    rw [(tauAF_isMultiplicative r).map_mul_of_coprime hmn]
    simp only [Nat.cast_mul, div_eq_mul_inv, mul_inv]
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

/-- For positive `r`, multichoose has the form used by the standard generating
function `(1-t)^{-r}`. -/
theorem multichoose_eq_choose_add_pred (r e : ℕ) (hr : 1 ≤ r) :
    r.multichoose e = (e + (r - 1)).choose (r - 1) := by
  rw [Nat.multichoose_eq]
  have htop : r + e - 1 = e + (r - 1) := by omega
  rw [htop, Nat.choose_symm_add]

/-- Exact local Euler factor for `tau_r(n)/n`, with a primitive modulus mask. -/
theorem tsum_tauCoprimeHarmonicWeight_primePow
    (r modulus p : ℕ) (hr : 1 ≤ r) (hp : p.Prime) :
    (∑' e : ℕ, tauCoprimeHarmonicWeight r modulus (p ^ e)) =
      if p ∣ modulus then 1
      else 1 / (1 - (p : ℝ)⁻¹) ^ r := by
  by_cases hpmod : p ∣ modulus
  · rw [if_pos hpmod]
    have hfun : (fun e : ℕ => tauCoprimeHarmonicWeight r modulus (p ^ e)) =
        fun e : ℕ => if e = 0 then 1 else 0 := by
      funext e
      cases e with
      | zero => simp [tauCoprimeHarmonicWeight, (tauAF_isMultiplicative r).map_one]
      | succ e =>
          have hnot : ¬(p ^ (e + 1)).Coprime modulus := by
            intro hcop
            have hpp : p.Coprime p :=
              Nat.Coprime.of_dvd (dvd_pow_self p (by omega)) hpmod hcop
            exact hp.ne_one (hpp.eq_one_of_dvd (dvd_refl p))
          simp [tauCoprimeHarmonicWeight, hnot]
    rw [hfun, (hasSum_ite_eq 0 (1 : ℝ)).tsum_eq]
  · rw [if_neg hpmod]
    have hpcop : p.Coprime modulus := hp.coprime_iff_not_dvd.mpr hpmod
    have hnorm : ‖((p : ℝ)⁻¹)‖ < 1 := by
      rw [Real.norm_eq_abs, abs_inv, abs_of_nonneg (by positivity)]
      exact (inv_lt_one₀ (by exact_mod_cast hp.pos)).2 (by exact_mod_cast hp.one_lt)
    have hseries := tsum_choose_mul_geometric_of_norm_lt_one
      (𝕜 := ℝ) (r - 1) hnorm
    rw [show r - 1 + 1 = r by omega] at hseries
    rw [← hseries]
    apply tsum_congr
    intro e
    have hpowcop : (p ^ e).Coprime modulus := hpcop.pow_left e
    rw [tauCoprimeHarmonicWeight, if_pos hpowcop,
      tauAF_prime_pow_eq_multichoose r e p hp,
      multichoose_eq_choose_add_pred r e hr]
    norm_num [div_eq_mul_inv, Nat.cast_pow, inv_pow]

/-- The local series needed by the finite Euler-product theorem is summable. -/
theorem summable_norm_tauCoprimeHarmonicWeight_primePow
    (r modulus : ℕ) (hr : 1 ≤ r) {p : ℕ} (hp : p.Prime) :
    Summable (fun e : ℕ => ‖tauCoprimeHarmonicWeight r modulus (p ^ e)‖) := by
  by_cases hpmod : p ∣ modulus
  · have hfun : (fun e : ℕ => ‖tauCoprimeHarmonicWeight r modulus (p ^ e)‖) =
        fun e : ℕ => if e = 0 then 1 else 0 := by
      funext e
      cases e with
      | zero => simp [tauCoprimeHarmonicWeight, (tauAF_isMultiplicative r).map_one]
      | succ e =>
          have hnot : ¬(p ^ (e + 1)).Coprime modulus := by
            intro hcop
            have hpp : p.Coprime p :=
              Nat.Coprime.of_dvd (dvd_pow_self p (by omega)) hpmod hcop
            exact hp.ne_one (hpp.eq_one_of_dvd (dvd_refl p))
          simp [tauCoprimeHarmonicWeight, hnot]
    rw [hfun]
    exact (hasSum_ite_eq 0 (1 : ℝ)).summable
  · have hpcop : p.Coprime modulus := hp.coprime_iff_not_dvd.mpr hpmod
    have hnorm : ‖((p : ℝ)⁻¹)‖ < 1 := by
      rw [Real.norm_eq_abs, abs_inv, abs_of_nonneg (by positivity)]
      exact (inv_lt_one₀ (by exact_mod_cast hp.pos)).2 (by exact_mod_cast hp.one_lt)
    have hs := summable_choose_mul_geometric_of_norm_lt_one
      (R := ℝ) (r - 1) hnorm
    have hfun : (fun e : ℕ => ‖tauCoprimeHarmonicWeight r modulus (p ^ e)‖) =
        fun e : ℕ => ((e + (r - 1)).choose (r - 1) : ℝ) * ((p : ℝ)⁻¹) ^ e := by
      funext e
      have hpowcop : (p ^ e).Coprime modulus := hpcop.pow_left e
      rw [Real.norm_eq_abs, abs_of_nonneg (tauCoprimeHarmonicWeight_nonneg ..),
        tauCoprimeHarmonicWeight, if_pos hpowcop,
        tauAF_prime_pow_eq_multichoose r e p hp,
        multichoose_eq_choose_add_pred r e hr]
      norm_num [div_eq_mul_inv, Nat.cast_pow, inv_pow]
    rw [hfun]
    exact hs

/-- The literal square-weight harmonic sum is bounded by the full smooth-number
Euler product for `tau_{k^2}`. -/
theorem tauSquareCoprimeHarmonicSum_le_localEulerProduct
    (k x modulus : ℕ) (hk : 1 ≤ k) :
    tauSquareCoprimeHarmonicSum k x modulus ≤
      ∏ p ∈ (x + 1).primesBelow,
        (if p ∣ modulus then 1 else 1 / (1 - (p : ℝ)⁻¹) ^ (k * k)) := by
  let r := k * k
  have hr : 1 ≤ r := by dsimp [r]; nlinarith
  let f : ℕ → ℝ := tauCoprimeHarmonicWeight r modulus
  have hEuler :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
      (f := f)
      (tauCoprimeHarmonicWeight_one r modulus)
      (fun {_ _} hmn => tauCoprimeHarmonicWeight_mul_of_coprime r modulus hmn)
      (fun hp => summable_norm_tauCoprimeHarmonicWeight_primePow r modulus hr hp)
      (x + 1)
  have hprod :
      (∑' m : (x + 1).smoothNumbers, f m) =
        ∏ p ∈ (x + 1).primesBelow,
          (if p ∣ modulus then 1 else 1 / (1 - (p : ℝ)⁻¹) ^ r) := by
    rw [hEuler.2.tsum_eq]
    apply Finset.prod_congr rfl
    intro p hpP
    exact tsum_tauCoprimeHarmonicWeight_primePow r modulus p hr
      (Nat.prime_of_mem_primesBelow hpP)
  let source : Finset ℕ := Finset.Icc 1 x
  let embedFun : (↥source) → (x + 1).smoothNumbers := fun n =>
    ⟨n.1, by
      apply Nat.mem_smoothNumbers_of_lt
      · have : 1 ≤ n.1 := by simpa [source] using (Finset.mem_Icc.mp n.2).1
        exact Nat.lt_of_lt_of_le (by norm_num) this
      · have hnle := (Finset.mem_Icc.mp n.2).2
        omega⟩
  let embed : (↥source) ↪ (x + 1).smoothNumbers :=
    ⟨embedFun, by
      intro a b h
      apply Subtype.ext
      exact congrArg (fun z : (x + 1).smoothNumbers => z.1) h⟩
  have hsource : Summable (fun n : ↥source =>
      if n.1.Coprime modulus then (tauAF k n.1 ^ 2 : ℝ) / (n.1 : ℝ) else 0) :=
    summable_of_finite_support (Set.toFinite _)
  have hsmooth := hEuler.1.of_norm
  have hsub :
      (∑' n : ↥source,
        if n.1.Coprime modulus then (tauAF k n.1 ^ 2 : ℝ) / (n.1 : ℝ) else 0) ≤
      ∑' m : (x + 1).smoothNumbers, f m := by
    apply Summable.tsum_le_tsum_of_inj embed embed.injective
    · intro m hm
      exact tauCoprimeHarmonicWeight_nonneg r modulus m
    · intro n
      change (if n.1.Coprime modulus then (tauAF k n.1 ^ 2 : ℝ) / (n.1 : ℝ)
        else 0) ≤ tauCoprimeHarmonicWeight r modulus n.1
      by_cases hcop : n.1.Coprime modulus
      · rw [if_pos hcop, tauCoprimeHarmonicWeight, if_pos hcop]
        exact div_le_div_of_nonneg_right
          (by exact_mod_cast tauAF_square_le_tauAF_mul k n.1)
          (by positivity)
      · simp [hcop, tauCoprimeHarmonicWeight]
    · exact hsource
    · exact hsmooth
  rw [← hprod]
  exact (by
    rw [tauSquareCoprimeHarmonicSum, ← Finset.sum_coe_sort]
    change (∑ n : ↥source,
      if n.1.Coprime modulus then (tauAF k n.1 ^ 2 : ℝ) / (n.1 : ℝ) else 0) ≤ _
    rw [← (hasSum_fintype (fun n : ↥source =>
      if n.1.Coprime modulus then
        (tauAF k n.1 ^ 2 : ℝ) / (n.1 : ℝ) else 0)).tsum_eq]
    exact hsub)

/-- The coefficient-one prime sum after omitting primes dividing the modulus. -/
def omittedPrimeReciprocalSum (x modulus : ℕ) : ℝ :=
  ∑ p ∈ (x + 1).primesBelow,
    if p ∣ modulus then 0 else (p : ℝ)⁻¹

/-- For the literal square weight, Shiu's prime sum is exactly `k^2` times
the coefficient-one omitted prime sum. -/
theorem omittedPrimeSum_tauSquare_eq (k x modulus : ℕ) :
    omittedPrimeSum ((tauAF k).pmul (tauAF k)) x modulus =
      (k * k : ℕ) * omittedPrimeReciprocalSum x modulus := by
  classical
  unfold omittedPrimeSum omittedPrimeReciprocalSum Nat.primesBelow
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hpp : p.Prime := (Finset.mem_filter.mp hp).2
  by_cases hpmod : p ∣ modulus
  · simp [hpmod]
  · have hnat : tauAF k p * tauAF k p = k * k := by
      simpa [pow_two] using tauAF_square_at_prime k p hpp
    rw [if_neg hpmod, if_neg hpmod]
    simp only [ArithmeticFunction.pmul_apply, hnat, Nat.cast_mul]

/-- Elementary logarithmic majorization of one Mertens Euler factor. -/
theorem inv_one_sub_le_exp_add_sq
    (u : ℝ) (hu : u ≤ 1 / 2) :
    (1 - u)⁻¹ ≤ Real.exp (u + 2 * u ^ 2) := by
  have hden : 0 < 1 - u := by linarith
  have hinv : 0 < (1 - u)⁻¹ := inv_pos.mpr hden
  have hlog := Real.log_le_sub_one_of_pos hinv
  have hfrac : (1 - u)⁻¹ - 1 ≤ u + 2 * u ^ 2 := by
    field_simp
    nlinarith [sq_nonneg u]
  rw [← Real.exp_log hinv]
  exact Real.exp_le_exp.mpr (hlog.trans hfrac)

/-- The square-prime tail is bounded by the full `p`-series, uniformly in the
finite prime cutoff. -/
theorem primeInverseSquareSum_le_two (N : ℕ) :
    (∑ p ∈ N.primesBelow, (p : ℝ)⁻¹ ^ 2) ≤ 2 := by
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ (-(2 : ℝ))) := by
    simpa using Real.summable_nat_rpow.mpr (by norm_num : (-(2 : ℝ)) < -1)
  calc
    (∑ p ∈ N.primesBelow, (p : ℝ)⁻¹ ^ 2) =
        ∑ p ∈ N.primesBelow, (p : ℝ) ^ (-(2 : ℝ)) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hpp := Nat.prime_of_mem_primesBelow hp
      have hpR : (0 : ℝ) < p := by exact_mod_cast hpp.pos
      rw [show (-(2 : ℝ)) = -(2 : ℕ) by norm_num,
        Real.rpow_neg hpR.le, Real.rpow_natCast]
      simp [inv_pow]
    _ ≤ ∑' n : ℕ, (n : ℝ) ^ (-(2 : ℝ)) := by
      apply Summable.sum_le_tsum
      · intro n hn
        exact Real.rpow_nonneg (Nat.cast_nonneg n) _
      · exact hs
    _ ≤ 1 + ((2 : ℝ) - 1)⁻¹ := by
      simpa using MAPMertensAnalyticLeaf.pSeries_le_one_add_inv_sub_one
        (show (1 : ℝ) < 2 by norm_num)
    _ = 2 := by norm_num

/-- Finite Euler-product form of Shiu's Lemma 3.  The constant
`exp(4*k^2)` is explicit and uniform in both the cutoff and the modulus. -/
theorem localEulerProduct_le_exp_omittedPrimeSum
    (k x modulus : ℕ) (hk : 1 ≤ k) :
    (∏ p ∈ (x + 1).primesBelow,
        (if p ∣ modulus then 1 else
          1 / (1 - (p : ℝ)⁻¹) ^ (k * k))) ≤
      Real.exp (4 * (k * k : ℕ)) *
        Real.exp (omittedPrimeSum ((tauAF k).pmul (tauAF k)) x modulus) := by
  let r : ℕ := k * k
  let S : ℝ := omittedPrimeReciprocalSum x modulus
  let E : ℝ := ∑ p ∈ (x + 1).primesBelow,
    if p ∣ modulus then 0 else (p : ℝ)⁻¹ ^ 2
  have hfactor (p : ℕ) (hpp : p.Prime) :
      (if p ∣ modulus then 1 else 1 / (1 - (p : ℝ)⁻¹) ^ r) ≤
        Real.exp (if p ∣ modulus then 0 else
          (r : ℝ) * ((p : ℝ)⁻¹ + 2 * (p : ℝ)⁻¹ ^ 2)) := by
    by_cases hpmod : p ∣ modulus
    · simp [hpmod]
    · rw [if_neg hpmod, if_neg hpmod]
      have hpR : (0 : ℝ) < p := by exact_mod_cast hpp.pos
      have hu : (p : ℝ)⁻¹ ≤ 1 / 2 := by
        simpa [one_div] using
          (inv_le_inv₀ hpR (by norm_num : (0 : ℝ) < 2)).mpr
            (by exact_mod_cast hpp.two_le)
      have hbase := inv_one_sub_le_exp_add_sq (p : ℝ)⁻¹ hu
      calc
        1 / (1 - (p : ℝ)⁻¹) ^ r = ((1 - (p : ℝ)⁻¹)⁻¹) ^ r := by
          simp [one_div, inv_pow]
        _ ≤ (Real.exp ((p : ℝ)⁻¹ + 2 * (p : ℝ)⁻¹ ^ 2)) ^ r := by
          exact pow_le_pow_left₀ (inv_nonneg.mpr (by linarith)) hbase r
        _ = Real.exp ((r : ℝ) * ((p : ℝ)⁻¹ + 2 * (p : ℝ)⁻¹ ^ 2)) := by
          rw [← Real.exp_nat_mul]
  have hprod :
      (∏ p ∈ (x + 1).primesBelow,
          (if p ∣ modulus then 1 else 1 / (1 - (p : ℝ)⁻¹) ^ r)) ≤
        Real.exp ((r : ℝ) * (S + 2 * E)) := by
    calc
      (∏ p ∈ (x + 1).primesBelow,
          (if p ∣ modulus then 1 else 1 / (1 - (p : ℝ)⁻¹) ^ r)) ≤
          ∏ p ∈ (x + 1).primesBelow,
            Real.exp (if p ∣ modulus then 0 else
              (r : ℝ) * ((p : ℝ)⁻¹ + 2 * (p : ℝ)⁻¹ ^ 2)) := by
        apply Finset.prod_le_prod₀
        · intro p hp
          have hpp := Nat.prime_of_mem_primesBelow hp
          have hpR : (0 : ℝ) < p := by exact_mod_cast hpp.pos
          by_cases hpmod : p ∣ modulus
          · simp [hpmod]
          · simp only [hpmod, if_false]
            have hinv : 0 < (p : ℝ)⁻¹ := inv_pos.mpr hpR
            have hden : 0 ≤ 1 - (p : ℝ)⁻¹ := by
              have hu' : (p : ℝ)⁻¹ ≤ 1 := by
                exact (inv_le_one₀ hpR).2 (by exact_mod_cast hpp.one_lt.le)
              linarith
            exact div_nonneg (by norm_num) (pow_nonneg hden r)
        · intro p hp
          exact hfactor p (Nat.prime_of_mem_primesBelow hp)
      _ = Real.exp ((r : ℝ) * (S + 2 * E)) := by
        rw [← Real.exp_sum]
        congr 1
        unfold S E omittedPrimeReciprocalSum
        rw [mul_add, Finset.mul_sum]
        calc
          (∑ p ∈ (x + 1).primesBelow,
              if p ∣ modulus then 0 else
                (r : ℝ) * ((p : ℝ)⁻¹ + 2 * (p : ℝ)⁻¹ ^ 2)) =
              (∑ p ∈ (x + 1).primesBelow,
                (r : ℝ) * (if p ∣ modulus then 0 else (p : ℝ)⁻¹)) +
              ∑ p ∈ (x + 1).primesBelow,
                (r : ℝ) * (2 * (if p ∣ modulus then 0 else (p : ℝ)⁻¹ ^ 2)) := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro p hp
            by_cases hpmod : p ∣ modulus <;> simp [hpmod]
            ring
          _ = (∑ p ∈ (x + 1).primesBelow,
                (r : ℝ) * (if p ∣ modulus then 0 else (p : ℝ)⁻¹)) +
              (r : ℝ) * (2 * ∑ p ∈ (x + 1).primesBelow,
                if p ∣ modulus then 0 else (p : ℝ)⁻¹ ^ 2) := by
            congr 1
            rw [Finset.mul_sum, Finset.mul_sum]
  have hE : E ≤ 2 := by
    unfold E
    calc
      (∑ p ∈ (x + 1).primesBelow,
        if p ∣ modulus then 0 else (p : ℝ)⁻¹ ^ 2) ≤
          ∑ p ∈ (x + 1).primesBelow, (p : ℝ)⁻¹ ^ 2 := by
        apply Finset.sum_le_sum
        intro p hp
        by_cases hpmod : p ∣ modulus <;> simp [hpmod]
      _ ≤ 2 := primeInverseSquareSum_le_two (x + 1)
  have hS : 0 ≤ S := by
    unfold S omittedPrimeReciprocalSum
    positivity
  have hr0 : (0 : ℝ) ≤ r := by positivity
  calc
    (∏ p ∈ (x + 1).primesBelow,
        (if p ∣ modulus then 1 else
          1 / (1 - (p : ℝ)⁻¹) ^ (k * k))) ≤
        Real.exp ((r : ℝ) * (S + 2 * E)) := by simpa [r] using hprod
    _ ≤ Real.exp ((r : ℝ) * S + 4 * (r : ℝ)) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    _ = Real.exp (4 * (k * k : ℕ)) *
        Real.exp (omittedPrimeSum ((tauAF k).pmul (tauAF k)) x modulus) := by
      rw [← Real.exp_add, omittedPrimeSum_tauSquare_eq]
      congr 1
      dsimp [r, S]
      push_cast
      ring

/-- The exact MAP-specialized form of Shiu (1980), Lemma 3.  The harmonic
mean and modulus-uniformity match the primary source. -/
theorem tauSquare_coprime_harmonic_mean
    (k : ℕ) (hk : 1 ≤ k) :
    ∀ x modulus : ℕ,
      tauSquareCoprimeHarmonicSum k x modulus ≤
        Real.exp (4 * (k * k : ℕ)) *
          Real.exp (omittedPrimeSum ((tauAF k).pmul (tauAF k)) x modulus) := by
  intro x modulus
  exact (tauSquareCoprimeHarmonicSum_le_localEulerProduct k x modulus hk).trans
    (localEulerProduct_le_exp_omittedPrimeSum k x modulus hk)

/-- Mertens converts the exact prime exponential to the logarithmic power
used in the specialized Shiu proof.  The constant is explicit and independent
of `x` and `modulus`. -/
theorem tauSquare_coprime_harmonic_mean_le_logPow
    (k x modulus : ℕ) (hk : 1 ≤ k) (hx : 3 ≤ x) :
    tauSquareCoprimeHarmonicSum k x modulus ≤
      Real.exp ((k * k : ℕ) * (5 + 2 * Real.log 4)) *
        (Real.log (x : ℝ)) ^ (k * k) := by
  calc
    tauSquareCoprimeHarmonicSum k x modulus ≤
        Real.exp (4 * (k * k : ℕ)) *
          Real.exp (omittedPrimeSum ((tauAF k).pmul (tauAF k)) x modulus) :=
      tauSquare_coprime_harmonic_mean k hk x modulus
    _ ≤ Real.exp (4 * (k * k : ℕ)) *
        (Real.exp ((k ^ 2 : ℕ) * (1 + 2 * Real.log 4)) *
          (Real.log (x : ℝ)) ^ (k ^ 2)) := by
      gcongr
      exact exp_omittedPrimeSum_tauAFSquare_le_explicit k x modulus hx
    _ = Real.exp ((k * k : ℕ) * (5 + 2 * Real.log 4)) *
        (Real.log (x : ℝ)) ^ (k * k) := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 1
      · norm_num [pow_two]
        ring
      · norm_num [pow_two]

/-- The requested `log(2x)` surface, convenient when later expressions use a
single common logarithm. -/
theorem tauSquare_coprime_harmonic_mean_le_logTwoPow
    (k x modulus : ℕ) (hk : 1 ≤ k) (hx : 3 ≤ x) :
    tauSquareCoprimeHarmonicSum k x modulus ≤
      Real.exp ((k * k : ℕ) * (5 + 2 * Real.log 4)) *
        (Real.log (2 * x : ℕ)) ^ (k * k) := by
  refine (tauSquare_coprime_harmonic_mean_le_logPow k x modulus hk hx).trans ?_
  have hlog0 : 0 ≤ Real.log (x : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ x by omega))
  have hlog : Real.log (x : ℝ) ≤ Real.log (2 * x : ℕ) := by
    apply Real.log_le_log
    · exact_mod_cast (show 0 < x by omega)
    · exact_mod_cast (show x ≤ 2 * x by omega)
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hlog0 hlog (k * k)) (Real.exp_pos _).le

end

end ShiuLemma3TauMean
