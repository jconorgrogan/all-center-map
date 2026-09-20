import DeterminantCountWeld

/-!
# Unconditional foundation for the Shiu determinant-fiber input

The analytic theorem still missing from this file is recorded as the proposition
`DyadicTauSquareShiuTarget`; it is not postulated as an axiom.  Its interval is
written by its upper endpoint `x` and length `y`, so the reduced interval
`(N / d, (2 * N) / d]` is represented literally, without pretending that
integer division commutes with doubling.
-/

namespace ShiuFoundation

open ArithmeticFunction MixedMellinCert DeterminantCountWeld
open scoped ArithmeticFunction.zeta

/-- The sum of a nonnegative arithmetic weight in the primitive progression
`n = residue (mod modulus)` and the half-open interval `(x-y,x]`. -/
def progressionSum (f : ArithmeticFunction ℕ)
    (x y modulus residue : ℕ) : ℕ :=
  ∑ n ∈ Finset.Ioc (x - y) x,
    if n ≡ residue [MOD modulus] then f n else 0

/-- The exact Shiu input needed after Cauchy in either signed determinant
fiber.  For each fixed divisor order `k`, the constant and threshold are
uniform in the upper endpoint, interval length, modulus, and primitive
residue.  The strict cube inequalities encode Shiu's fixed choice
`alpha = beta = 1/3`: `modulus < y^(2/3)` and `x^(1/3) < y`.

The weight is the literal square of `tau_k`; the logarithmic exponent `k^2`
also absorbs the standard `q/phi(q)` loss.  This is slightly more direct than
replacing `tau_k^2` by `tau_R`. -/
def DyadicTauSquareShiuTarget : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    ∃ C x₀ : ℕ, 0 < C ∧ 2 ≤ x₀ ∧
      ∀ x y modulus residue : ℕ,
        x₀ ≤ x →
        0 < modulus →
        residue < modulus →
        residue.Coprime modulus →
        y ≤ x →
        x < y ^ 3 →
        modulus ^ 3 < y ^ 2 →
        modulus * progressionSum ((tauAF k).pmul (tauAF k))
            x y modulus residue ≤
          C * y * (Nat.log 2 (x + 2) + 1) ^ (k * k)

/-- Dirichlet-convolution powers of zeta are multiplicative. -/
theorem tauAF_isMultiplicative (r : ℕ) : (tauAF r).IsMultiplicative := by
  induction r with
  | zero => simpa [tauAF] using
      (ArithmeticFunction.isMultiplicative_one :
        (1 : ArithmeticFunction ℕ).IsMultiplicative)
  | succ r ih =>
      rw [tauAF, pow_succ']
      exact ArithmeticFunction.isMultiplicative_zeta.mul ih

/-- The divisor functions are nonnegative (their codomain is `ℕ`). -/
theorem tauAF_nonnegative (r n : ℕ) : 0 ≤ tauAF r n := Nat.zero_le _

/-- Exact prime-power local factor for `tau_r`. -/
theorem tauAF_prime_pow_eq_multichoose (r e p : ℕ) (hp : p.Prime) :
    tauAF r (p ^ e) = r.multichoose e := by
  induction r generalizing e with
  | zero =>
      cases e with
      | zero => simp [tauAF]
      | succ e =>
          have hpow : p ^ (e + 1) ≠ 1 :=
            (Nat.one_lt_pow (Nat.succ_ne_zero e) hp.one_lt).ne'
          simp [tauAF, ArithmeticFunction.one_apply, hpow, hp.ne_one,
            Nat.multichoose_zero_succ]
  | succ r ih =>
      rw [show r + 1 = Nat.succ r by omega, tauAF_succ_apply]
      rw [Nat.divisors_prime_pow hp, Finset.sum_map]
      simp only [Function.Embedding.coeFn_mk, ih]
      rw [Nat.sum_range_multichoose]
      simpa [Nat.multichoose_eq, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (Nat.choose_symm_add (a := e) (b := r)).symm

/-- Increasing the number of available symbols increases `multichoose`. -/
theorem multichoose_le_succ (r e : ℕ) :
    r.multichoose e ≤ (r + 1).multichoose e := by
  cases e with
  | zero => simp
  | succ e =>
      rw [Nat.multichoose_succ_succ]
      omega

/-- Local submultiplicativity of multichoose in the exponent. -/
theorem multichoose_add_le_mul (r a b : ℕ) :
    r.multichoose (a + b) ≤ r.multichoose a * r.multichoose b := by
  induction r generalizing a b with
  | zero =>
      cases a with
      | zero => simp
      | succ a =>
          cases b with
          | zero => simp
          | succ b =>
              rw [show (a + 1) + (b + 1) = (a + b + 1) + 1 by omega]
              simp [Nat.multichoose_zero_succ]
  | succ r ihr =>
      induction b with
      | zero => simp
      | succ b ihb =>
          change (r + 1).multichoose ((a + b) + 1) ≤
            (r + 1).multichoose a * (r + 1).multichoose (b + 1)
          nth_rewrite 1 [Nat.multichoose_succ_succ r (a + b)]
          calc
            r.multichoose (a + (b + 1)) + (r + 1).multichoose (a + b) ≤
                r.multichoose a * r.multichoose (b + 1) +
                  (r + 1).multichoose a * (r + 1).multichoose b :=
              Nat.add_le_add (ihr a (b + 1)) ihb
            _ ≤ (r + 1).multichoose a * r.multichoose (b + 1) +
                  (r + 1).multichoose a * (r + 1).multichoose b := by
              gcongr
              exact multichoose_le_succ r a
            _ = (r + 1).multichoose a * (r + 1).multichoose (b + 1) := by
              rw [Nat.multichoose_succ_succ r b, mul_add]

/-- The elementary exponential local-factor bound used in Shiu's growth
hypothesis: the number of multisets is at most the number of ordered words. -/
theorem multichoose_le_pow (r e : ℕ) : r.multichoose e ≤ r ^ e := by
  induction r generalizing e with
  | zero =>
      cases e <;> simp [Nat.multichoose_zero_succ]
  | succ r ihr =>
      induction e with
      | zero => simp
      | succ e ihe =>
          rw [Nat.multichoose_succ_succ, pow_succ]
          calc
            r.multichoose (e + 1) + (r + 1).multichoose e ≤
                r ^ (e + 1) + (r + 1) ^ e := Nat.add_le_add (ihr (e + 1)) ihe
            _ ≤ r * (r + 1) ^ e + (r + 1) ^ e := by
              gcongr
              calc
                r ^ (e + 1) = r ^ e * r := pow_succ r e
                _ ≤ (r + 1) ^ e * r :=
                  Nat.mul_le_mul_right r (Nat.pow_le_pow_left (Nat.le_succ r) e)
                _ = r * (r + 1) ^ e := by ac_rfl
            _ = (r + 1) ^ (e + 1) := by rw [pow_succ]; ring

/-- Prime-power growth for the literal square weight passed to Shiu. -/
theorem tauAF_square_prime_pow_le (k e p : ℕ) (hp : p.Prime) :
    tauAF k (p ^ e) ^ 2 ≤ (k * k) ^ e := by
  rw [tauAF_prime_pow_eq_multichoose k e p hp, mul_pow]
  simpa [pow_two] using Nat.mul_le_mul (multichoose_le_pow k e)
    (multichoose_le_pow k e)

/-- Multiplicativity of the squared divisor weight used by the target. -/
theorem tauAF_square_isMultiplicative (k : ℕ) :
    ((tauAF k).pmul (tauAF k)).IsMultiplicative :=
  (tauAF_isMultiplicative k).pmul (tauAF_isMultiplicative k)

/-- Exact Euler product for the generalized divisor function. -/
theorem tauAF_eq_factorization_prod (r n : ℕ) (hn : n ≠ 0) :
    tauAF r n = n.factorization.prod (fun _ e ↦ r.multichoose e) := by
  rw [(tauAF_isMultiplicative r).multiplicative_factorization (tauAF r) hn]
  apply Finsupp.prod_congr
  intro p hp
  exact tauAF_prime_pow_eq_multichoose r _ p
    (Nat.prime_of_mem_primeFactors (by simpa using hp))

/-- A product of local multichoose factors is submultiplicative under
addition of exponent vectors. -/
theorem factorizationProduct_add_le (r : ℕ) (f g : ℕ →₀ ℕ) :
    (f + g).prod (fun _ e ↦ r.multichoose e) ≤
      f.prod (fun _ e ↦ r.multichoose e) *
        g.prod (fun _ e ↦ r.multichoose e) := by
  classical
  let s := f.support ∪ g.support
  rw [Finsupp.prod_of_support_subset (f + g) Finsupp.support_add _
      (by intro i hi; simp),
    Finsupp.prod_of_support_subset f Finset.subset_union_left _
      (by intro i hi; simp),
    Finsupp.prod_of_support_subset g Finset.subset_union_right _
      (by intro i hi; simp),
    ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod'
  intro p hp
  simp only [Finsupp.add_apply]
  exact multichoose_add_le_mul r (f p) (g p)

/-- Full divisor-function submultiplicativity, with no coprimality assumption. -/
theorem tauAF_submultiplicative (r m n : ℕ) :
    tauAF r (m * n) ≤ tauAF r m * tauAF r n := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [tauAF_eq_factorization_prod r (m * n) (Nat.mul_ne_zero hm hn),
    tauAF_eq_factorization_prod r m hm, tauAF_eq_factorization_prod r n hn,
    Nat.factorization_mul hm hn]
  exact factorizationProduct_add_le r m.factorization n.factorization

/-- Finite Euler-factor domination by a geometric sum. -/
theorem tauAF_square_localFactor_le (k p J : ℕ) (hp : p.Prime) :
    (∑ e ∈ Finset.range J, tauAF k (p ^ e) ^ 2) ≤
      ∑ e ∈ Finset.range J, (k * k) ^ e := by
  exact Finset.sum_le_sum fun e he ↦ tauAF_square_prime_pow_le k e p hp

/-- Mathlib's exact long-interval progression count, exposed in the notation
used by `progressionSum`.  This is the unconditional elementary progression
estimate available before any divisor weights are introduced. -/
theorem progression_card_exact (lo hi modulus residue : ℕ) (hmod : 0 < modulus) :
    (({n ∈ Finset.Ioc lo hi | n ≡ residue [MOD modulus]} : Finset ℕ).card : ℤ) =
      max (⌊((hi : ℤ) - residue) / (modulus : ℚ)⌋ -
        ⌊((lo : ℤ) - residue) / (modulus : ℚ)⌋) 0 := by
  simpa using Nat.Ioc_filter_modEq_card lo hi hmod residue

/-- The literal quotient of `(N,2N]` by a known content. -/
def quotientDyadic (N content : ℕ) : Finset ℕ :=
  Finset.Ioc (N / content) ((2 * N) / content)

/-- Dividing an actual multiple in `(N,2N]` lands in the exact quotient
interval.  No false identity `(2*N)/d = 2*(N/d)` is used. -/
theorem div_mem_quotientDyadic {N n content : ℕ} (hcontent : 0 < content)
    (hdiv : content ∣ n) (hn : n ∈ dyadic N) :
    n / content ∈ quotientDyadic N content := by
  simp only [dyadic, Finset.mem_Ioc] at hn
  simp only [quotientDyadic, Finset.mem_Ioc]
  constructor
  · rw [Nat.div_lt_iff_lt_mul hcontent, Nat.div_mul_cancel hdiv]
    exact hn.1
  · exact Nat.div_le_div_right hn.2

/-- Exact upper-endpoint/length representation of the quotient interval for
the Shiu proposition. -/
theorem quotientDyadic_eq_shiuWindow (N content : ℕ) :
    quotientDyadic N content =
      Finset.Ioc (((2 * N) / content) -
        (((2 * N) / content) - (N / content))) ((2 * N) / content) := by
  have hle : N / content ≤ (2 * N) / content :=
    Nat.div_le_div_right (by omega)
  simp [quotientDyadic, Nat.sub_sub_self hle]

/-- Both exact content divisibilities and reduced equations in a positive
fiber. -/
theorem positiveFiber_reduced_equations {N a b ell : ℕ} {n : ℕ × ℕ}
    (hab : a.Coprime b) (ha : 0 < a) (hb : 0 < b)
    (hn : n ∈ positiveEquationFiber N a b ell) :
    let d₁ := ell.gcd b
    let d₂ := ell.gcd a
    d₁ ∣ n.1 ∧ d₂ ∣ n.2 ∧
      n.1 / d₁ ∈ quotientDyadic N d₁ ∧
      n.2 / d₂ ∈ quotientDyadic N d₂ ∧
      (n.1 / d₁).Coprime (b / d₁) ∧
      (n.2 / d₂).Coprime (a / d₂) ∧
      a * (n.1 / d₁) = ell / d₁ + (b / d₁) * n.2 ∧
      b * (n.2 / d₂) + ell / d₂ = (a / d₂) * n.1 := by
  dsimp
  obtain ⟨hdet, hleft, hright, _⟩ := positiveEquationFiber_content hab hn
  have hd₁ : ell.gcd b ∣ n.1 := by
    rw [← hleft]
    exact Nat.gcd_dvd_left n.1 b
  have hd₂ : ell.gcd a ∣ n.2 := by
    rw [← hright]
    exact Nat.gcd_dvd_left n.2 a
  have hd₁b : ell.gcd b ∣ b := Nat.gcd_dvd_right ell b
  have hd₁ell : ell.gcd b ∣ ell := Nat.gcd_dvd_left ell b
  have hd₂a : ell.gcd a ∣ a := Nat.gcd_dvd_right ell a
  have hd₂ell : ell.gcd a ∣ ell := Nat.gcd_dvd_left ell a
  have hd₁pos : 0 < ell.gcd b := Nat.gcd_pos_of_pos_right ell hb
  have hd₂pos : 0 < ell.gcd a := Nat.gcd_pos_of_pos_right ell ha
  have hell₁ : ell.gcd b * (ell / ell.gcd b) = ell := Nat.mul_div_cancel' hd₁ell
  have hb₁ : ell.gcd b * (b / ell.gcd b) = b := Nat.mul_div_cancel' hd₁b
  have hn₂ : ell.gcd a * (n.2 / ell.gcd a) = n.2 := Nat.mul_div_cancel' hd₂
  have hell₂ : ell.gcd a * (ell / ell.gcd a) = ell := Nat.mul_div_cancel' hd₂ell
  have ha₂ : ell.gcd a * (a / ell.gcd a) = a := Nat.mul_div_cancel' hd₂a
  have hnbox := (Finset.mem_filter.mp hn).1
  rcases Finset.mem_product.mp hnbox with ⟨hn₁box, hn₂box⟩
  refine ⟨hd₁, hd₂, div_mem_quotientDyadic hd₁pos hd₁ hn₁box,
    div_mem_quotientDyadic hd₂pos hd₂ hn₂box,
    reduced_left_residue_coprime hab hb hdet,
    reduced_right_residue_coprime hab ha hdet, ?_, ?_⟩
  · apply Nat.eq_of_mul_eq_mul_left hd₁pos
    calc
      ell.gcd b * (a * (n.1 / ell.gcd b)) =
          a * ((n.1 / ell.gcd b) * ell.gcd b) := by ac_rfl
      _ = a * n.1 := by rw [Nat.div_mul_cancel hd₁]
      _ = ell + b * n.2 := hdet
      _ = ell.gcd b * (ell / ell.gcd b + (b / ell.gcd b) * n.2) := by
        calc
          ell + b * n.2 =
              ell.gcd b * (ell / ell.gcd b) +
                (ell.gcd b * (b / ell.gcd b)) * n.2 := by rw [hell₁, hb₁]
          _ = _ := by ring
  · apply Nat.eq_of_mul_eq_mul_left hd₂pos
    calc
      ell.gcd a * (b * (n.2 / ell.gcd a) + ell / ell.gcd a) =
          b * n.2 + ell := by
            calc
              _ = b * (ell.gcd a * (n.2 / ell.gcd a)) +
                  ell.gcd a * (ell / ell.gcd a) := by ring
              _ = _ := by rw [hn₂, hell₂]
      _ = a * n.1 := by omega
      _ = ell.gcd a * ((a / ell.gcd a) * n.1) := by
        calc
          a * n.1 = (ell.gcd a * (a / ell.gcd a)) * n.1 := by rw [ha₂]
          _ = _ := by ring

/-- Negative fibers have the same reduced progression structure after the
literal swap `(a,b,n₁,n₂) ↦ (b,a,n₂,n₁)`. -/
theorem negativeFiber_reduced_equations {N a b ell : ℕ} {n : ℕ × ℕ}
    (hab : a.Coprime b) (ha : 0 < a) (hb : 0 < b)
    (hn : n ∈ negativeEquationFiber N a b ell) :
    let d₁ := ell.gcd b
    let d₂ := ell.gcd a
    d₁ ∣ n.1 ∧ d₂ ∣ n.2 ∧
      n.1 / d₁ ∈ quotientDyadic N d₁ ∧
      n.2 / d₂ ∈ quotientDyadic N d₂ ∧
      (n.1 / d₁).Coprime (b / d₁) ∧
      (n.2 / d₂).Coprime (a / d₂) ∧
      a * (n.1 / d₁) + ell / d₁ = (b / d₁) * n.2 ∧
      b * (n.2 / d₂) = ell / d₂ + (a / d₂) * n.1 := by
  have hswap : (n.2, n.1) ∈ positiveEquationFiber N b a ell := by
    simp only [negativeEquationFiber, positiveEquationFiber,
      Finset.mem_filter] at hn ⊢
    rcases hn with ⟨hnbox, hdet⟩
    rcases Finset.mem_product.mp hnbox with ⟨hn₁, hn₂⟩
    exact ⟨Finset.mem_product.mpr ⟨hn₂, hn₁⟩, hdet⟩
  obtain ⟨hd₂, hd₁, hn₂box, hn₁box, hc₂, hc₁, heq₂, heq₁⟩ :=
    positiveFiber_reduced_equations hab.symm hb ha hswap
  exact ⟨hd₁, hd₂, hn₁box, hn₂box, hc₁, hc₂, heq₁, heq₂⟩

/-- Cauchy's inequality reduces either literal weighted fiber to its two
one-coordinate divisor-square sums.  The remaining analytic task is exactly
to bound those sums in the primitive quotient progressions above. -/
theorem fiberMass_tauAF_sq_le (k : ℕ) (s : Finset (ℕ × ℕ)) :
    (fiberMass (fun n₁ n₂ ↦ tauAF k n₁ * tauAF k n₂) s) ^ 2 ≤
      (∑ n ∈ s, tauAF k n.1 ^ 2) *
        ∑ n ∈ s, tauAF k n.2 ^ 2 := by
  simpa [fiberMass] using
    (Finset.sum_mul_sq_le_sq_mul_sq s
      (fun n ↦ tauAF k n.1) (fun n ↦ tauAF k n.2))

/-- One theorem packaging the unconditional reduction for both signs. -/
theorem signedFiber_unconditional_reduction
    (k N a b ell : ℕ) (hab : a.Coprime b) (ha : 0 < a) (hb : 0 < b) :
    (∀ n ∈ positiveEquationFiber N a b ell,
      let d₁ := ell.gcd b
      let d₂ := ell.gcd a
      n.1 / d₁ ∈ quotientDyadic N d₁ ∧
      n.2 / d₂ ∈ quotientDyadic N d₂ ∧
      (n.1 / d₁).Coprime (b / d₁) ∧
      (n.2 / d₂).Coprime (a / d₂)) ∧
    (∀ n ∈ negativeEquationFiber N a b ell,
      let d₁ := ell.gcd b
      let d₂ := ell.gcd a
      n.1 / d₁ ∈ quotientDyadic N d₁ ∧
      n.2 / d₂ ∈ quotientDyadic N d₂ ∧
      (n.1 / d₁).Coprime (b / d₁) ∧
      (n.2 / d₂).Coprime (a / d₂)) ∧
    (fiberMass (fun n₁ n₂ ↦ tauAF k n₁ * tauAF k n₂)
        (positiveEquationFiber N a b ell)) ^ 2 ≤
      (∑ n ∈ positiveEquationFiber N a b ell, tauAF k n.1 ^ 2) *
        ∑ n ∈ positiveEquationFiber N a b ell, tauAF k n.2 ^ 2 ∧
    (fiberMass (fun n₁ n₂ ↦ tauAF k n₁ * tauAF k n₂)
        (negativeEquationFiber N a b ell)) ^ 2 ≤
      (∑ n ∈ negativeEquationFiber N a b ell, tauAF k n.1 ^ 2) *
        ∑ n ∈ negativeEquationFiber N a b ell, tauAF k n.2 ^ 2 := by
  refine ⟨?_, ?_, fiberMass_tauAF_sq_le k _, fiberMass_tauAF_sq_le k _⟩
  · intro n hn
    obtain ⟨_, _, h₁, h₂, hc₁, hc₂, _, _⟩ :=
      positiveFiber_reduced_equations hab ha hb hn
    exact ⟨h₁, h₂, hc₁, hc₂⟩
  · intro n hn
    obtain ⟨_, _, h₁, h₂, hc₁, hc₂, _, _⟩ :=
      negativeFiber_reduced_equations hab ha hb hn
    exact ⟨h₁, h₂, hc₁, hc₂⟩

end ShiuFoundation
