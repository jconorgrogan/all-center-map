import ShiuFoundation
import MixedMeanFrontend

/-!
# Unconditional determinant-sector bounds for the MAP mixed mean

This file advances the finite mixed-mean frontend without assuming the desired
weighted tuple-count estimate or Shiu's theorem.  It proves a uniform
arithmetic-progression cardinal bound for each nonzero signed determinant
fiber, sums those bounds over the exact determinant range, and reduces the
entire zero-determinant fiber to a literal one-dimensional divisor-square
moment.

The zero-sector theorem retains the sharp parameter
`min (2*N/a) (2*N/b)`.  The remaining divisor-square moment is displayed as a
concrete finite sum, not hidden behind an analytic hypothesis.
-/

namespace MAPMixedMean

open ArithmeticFunction MixedMellinCert DeterminantCountWeld ShiuFoundation
  MixedMeanFrontend

noncomputable section

/-- The elementary progression envelope used for one coordinate of a signed
determinant fiber.  It is deliberately independent of the residue. -/
def progressionCardEnvelope (N modulus : ℕ) : ℕ :=
  (2 * N + 1) / modulus + 1

/-- The exact finite divisor-square moment left by the zero determinant
parametrization. -/
def zeroSecondMoment (k R : ℕ) : ℕ :=
  ∑ s ∈ Finset.Icc 1 R, tauAF k s ^ 2

/-- The filtered quotient-dyadic square sum is literally the progression sum
used by the Shiu interface. -/
theorem quotientDyadic_tauSquare_eq_progressionSum
    (k N content modulus residue : ℕ) :
    (∑ q ∈ (quotientDyadic N content).filter
        (fun q => q ≡ residue [MOD modulus]), tauAF k q ^ 2) =
      progressionSum ((tauAF k).pmul (tauAF k))
        ((2 * N) / content)
        (((2 * N) / content) - (N / content)) modulus residue := by
  rw [quotientDyadic_eq_shiuWindow]
  unfold progressionSum
  simp only [Finset.sum_filter, ArithmeticFunction.pmul_apply, pow_two]

/-- Projection to the second coordinate is injective on a positive equation
fiber: the determinant equation and `b > 0` recover the first coordinate. -/
theorem positiveEquationFiber_snd_injOn {N a b ell : ℕ} (ha : 0 < a) :
    Set.InjOn Prod.snd (positiveEquationFiber N a b ell : Set (ℕ × ℕ)) := by
  intro x hx y hy hxy
  change x ∈ positiveEquationFiber N a b ell at hx
  change y ∈ positiveEquationFiber N a b ell at hy
  simp only [positiveEquationFiber, Finset.mem_filter] at hx hy
  rcases hx with ⟨_, hx⟩
  rcases hy with ⟨_, hy⟩
  apply Prod.ext
  · apply Nat.eq_of_mul_eq_mul_left ha
    calc
      a * x.1 = ell + b * x.2 := hx
      _ = ell + b * y.2 := by rw [hxy]
      _ = a * y.1 := hy.symm
  · exact hxy

/-- Projection to the first coordinate is injective on a negative equation
fiber. -/
theorem negativeEquationFiber_fst_injOn {N a b ell : ℕ} (hb : 0 < b) :
    Set.InjOn Prod.fst (negativeEquationFiber N a b ell : Set (ℕ × ℕ)) := by
  intro x hx y hy hxy
  change x ∈ negativeEquationFiber N a b ell at hx
  change y ∈ negativeEquationFiber N a b ell at hy
  simp only [negativeEquationFiber, Finset.mem_filter] at hx hy
  rcases hx with ⟨_, hx⟩
  rcases hy with ⟨_, hy⟩
  apply Prod.ext
  · exact hxy
  · apply Nat.eq_of_mul_eq_mul_left hb
    calc
      b * x.2 = ell + a * x.1 := hx
      _ = ell + a * y.1 := by rw [hxy]
      _ = b * y.2 := hy.symm

/-- Any two second coordinates in one positive determinant fiber occupy the
same residue class modulo `a`. -/
theorem positiveEquationFiber_snd_modEq {N a b ell : ℕ} (hab : a.Coprime b)
    {x y : ℕ × ℕ} (hx : x ∈ positiveEquationFiber N a b ell)
    (hy : y ∈ positiveEquationFiber N a b ell) :
    x.2 ≡ y.2 [MOD a] := by
  simp only [positiveEquationFiber, Finset.mem_filter] at hx hy
  rcases hx with ⟨_, hx⟩
  rcases hy with ⟨_, hy⟩
  have hx0 : ell + b * x.2 ≡ 0 [MOD a] := by
    rw [← hx]
    exact (Nat.dvd_mul_right a x.1).modEq_zero_nat
  have hy0 : ell + b * y.2 ≡ 0 [MOD a] := by
    rw [← hy]
    exact (Nat.dvd_mul_right a y.1).modEq_zero_nat
  have hmul : b * x.2 ≡ b * y.2 [MOD a] :=
    Nat.ModEq.add_left_cancel' ell (hx0.trans hy0.symm)
  exact hmul.cancel_left_of_coprime hab

/-- The symmetric residue-class statement for a negative determinant fiber. -/
theorem negativeEquationFiber_fst_modEq {N a b ell : ℕ} (hab : a.Coprime b)
    {x y : ℕ × ℕ} (hx : x ∈ negativeEquationFiber N a b ell)
    (hy : y ∈ negativeEquationFiber N a b ell) :
    x.1 ≡ y.1 [MOD b] := by
  simp only [negativeEquationFiber, Finset.mem_filter] at hx hy
  rcases hx with ⟨_, hx⟩
  rcases hy with ⟨_, hy⟩
  have hx0 : ell + a * x.1 ≡ 0 [MOD b] := by
    rw [← hx]
    exact (Nat.dvd_mul_right b x.2).modEq_zero_nat
  have hy0 : ell + a * y.1 ≡ 0 [MOD b] := by
    rw [← hy]
    exact (Nat.dvd_mul_right b y.2).modEq_zero_nat
  have hmul : a * x.1 ≡ a * y.1 [MOD b] :=
    Nat.ModEq.add_left_cancel' ell (hx0.trans hy0.symm)
  exact hmul.cancel_left_of_coprime hab.symm

/-- Dividing the first coordinate by its exact content remains injective on a
positive determinant fiber. -/
theorem positiveEquationFiber_firstDiv_injOn
    {N a b ell : ℕ} (hab : a.Coprime b) (ha : 0 < a) (hb : 0 < b) :
    let d₁ := ell.gcd b
    Set.InjOn (fun n : ℕ × ℕ => n.1 / d₁)
      (positiveEquationFiber N a b ell : Set (ℕ × ℕ)) := by
  dsimp
  intro x hx y hy hxy
  change x ∈ positiveEquationFiber N a b ell at hx
  change y ∈ positiveEquationFiber N a b ell at hy
  obtain ⟨hdx, _, _, _, _, _, _, _⟩ :=
    positiveFiber_reduced_equations hab ha hb hx
  obtain ⟨hdy, _, _, _, _, _, _, _⟩ :=
    positiveFiber_reduced_equations hab ha hb hy
  have hdpos : 0 < ell.gcd b := Nat.gcd_pos_of_pos_right ell hb
  have hx₁ : x.1 = ell.gcd b * (x.1 / ell.gcd b) :=
    (Nat.mul_div_cancel' hdx).symm
  have hy₁ : y.1 = ell.gcd b * (y.1 / ell.gcd b) :=
    (Nat.mul_div_cancel' hdy).symm
  have hfirst : x.1 = y.1 := by
    rw [hx₁, hy₁]
    exact congrArg (fun z => ell.gcd b * z) hxy
  have hxdet := (Finset.mem_filter.mp hx).2
  have hydet := (Finset.mem_filter.mp hy).2
  apply Prod.ext hfirst
  apply Nat.eq_of_mul_eq_mul_left hb
  calc
    b * x.2 = a * x.1 - ell := by omega
    _ = a * y.1 - ell := by rw [hfirst]
    _ = b * y.2 := by omega

/-- After exact-content division, all first coordinates in a positive fiber
remain in one primitive residue class modulo `b / gcd(ell,b)`. -/
theorem positiveEquationFiber_firstDiv_modEq
    {N a b ell : ℕ} (hab : a.Coprime b) (ha : 0 < a) (hb : 0 < b)
    {x y : ℕ × ℕ} (hx : x ∈ positiveEquationFiber N a b ell)
    (hy : y ∈ positiveEquationFiber N a b ell) :
    x.1 / ell.gcd b ≡ y.1 / ell.gcd b [MOD b / ell.gcd b] := by
  obtain ⟨_, _, _, _, _, _, hxeq, _⟩ :=
    positiveFiber_reduced_equations hab ha hb hx
  obtain ⟨_, _, _, _, _, _, hyeq, _⟩ :=
    positiveFiber_reduced_equations hab ha hb hy
  have hx0 : a * (x.1 / ell.gcd b) ≡ ell / ell.gcd b
      [MOD b / ell.gcd b] := by
    rw [hxeq]
    simpa only [Nat.add_comm] using (Nat.ModEq.modulus_mul_add
      (m := b / ell.gcd b) (a := x.2) (b := ell / ell.gcd b))
  have hy0 : a * (y.1 / ell.gcd b) ≡ ell / ell.gcd b
      [MOD b / ell.gcd b] := by
    rw [hyeq]
    simpa only [Nat.add_comm] using (Nat.ModEq.modulus_mul_add
      (m := b / ell.gcd b) (a := y.2) (b := ell / ell.gcd b))
  have hmul : a * (x.1 / ell.gcd b) ≡ a * (y.1 / ell.gcd b)
      [MOD b / ell.gcd b] :=
    hx0.trans hy0.symm
  have hdvd : b / ell.gcd b ∣ b :=
    Nat.div_dvd_of_dvd (Nat.gcd_dvd_right ell b)
  have hcop : a.Coprime (b / ell.gcd b) := hab.coprime_dvd_right hdvd
  exact hmul.cancel_left_of_coprime hcop.symm

/-- Shiu-ready first-coordinate estimate for every nonempty positive
determinant fiber.  It produces the primitive residue explicitly and bounds
the original divisor-square sum by the literal quotient-window progression
sum, with the exact content factor retained. -/
theorem exists_positiveFiber_first_progression_bound
    (k N a b ell : ℕ) (hab : a.Coprime b) (ha : 0 < a) (hb : 0 < b)
    (hne : (positiveEquationFiber N a b ell).Nonempty) :
    let d₁ := ell.gcd b
    let modulus := b / d₁
    ∃ residue : ℕ,
      residue < modulus ∧ residue.Coprime modulus ∧
      (∑ n ∈ positiveEquationFiber N a b ell, tauAF k n.1 ^ 2) ≤
        tauAF k d₁ ^ 2 *
          progressionSum ((tauAF k).pmul (tauAF k))
            ((2 * N) / d₁) (((2 * N) / d₁) - (N / d₁))
            modulus residue := by
  dsimp
  classical
  obtain ⟨base, hbase⟩ := hne
  let d₁ := ell.gcd b
  let modulus := b / d₁
  let baseReduced := base.1 / d₁
  let residue := baseReduced % modulus
  have hdpos : 0 < d₁ := Nat.gcd_pos_of_pos_right ell hb
  have hdvd : d₁ ∣ b := Nat.gcd_dvd_right ell b
  have hdle : d₁ ≤ b := Nat.le_of_dvd hb hdvd
  have hmodpos : 0 < modulus := Nat.div_pos hdle hdpos
  have hbaseData := positiveFiber_reduced_equations hab ha hb hbase
  have hbaseCoprime : baseReduced.Coprime modulus := by
    simpa [d₁, modulus, baseReduced] using hbaseData.2.2.2.2.1
  have hresidueLt : residue < modulus := Nat.mod_lt _ hmodpos
  have hresidueCoprime : residue.Coprime modulus :=
    (ZMod.coprime_mod_iff_coprime baseReduced modulus).2 hbaseCoprime
  refine ⟨residue, hresidueLt, hresidueCoprime, ?_⟩
  let projection : ℕ × ℕ → ℕ := fun n => n.1 / d₁
  let image := (positiveEquationFiber N a b ell).image projection
  let target := (quotientDyadic N d₁).filter
    (fun q => q ≡ residue [MOD modulus])
  have hinj : Set.InjOn projection
      (positiveEquationFiber N a b ell : Set (ℕ × ℕ)) := by
    simpa [projection, d₁] using
      (positiveEquationFiber_firstDiv_injOn hab ha hb)
  have himage : image ⊆ target := by
    intro q hq
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hq
    have hdata := positiveFiber_reduced_equations hab ha hb hn
    have hquotient : n.1 / d₁ ∈ quotientDyadic N d₁ := by
      simpa [d₁] using hdata.2.2.1
    have hsame : n.1 / d₁ ≡ baseReduced [MOD modulus] := by
      simpa [d₁, modulus, baseReduced] using
        (positiveEquationFiber_firstDiv_modEq hab ha hb hn hbase)
    have hres : n.1 / d₁ ≡ residue [MOD modulus] :=
      hsame.trans (Nat.mod_modEq baseReduced modulus).symm
    exact Finset.mem_filter.mpr ⟨hquotient, hres⟩
  calc
    (∑ n ∈ positiveEquationFiber N a b ell, tauAF k n.1 ^ 2) ≤
        ∑ n ∈ positiveEquationFiber N a b ell,
          tauAF k d₁ ^ 2 * tauAF k (projection n) ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      have hdata := positiveFiber_reduced_equations hab ha hb hn
      have hdiv : d₁ ∣ n.1 := by simpa [d₁] using hdata.1
      have hnfac : d₁ * projection n = n.1 := by
        simpa [projection] using Nat.mul_div_cancel' hdiv
      rw [← hnfac]
      calc
        tauAF k (d₁ * projection n) ^ 2 ≤
            (tauAF k d₁ * tauAF k (projection n)) ^ 2 :=
          Nat.pow_le_pow_left (tauAF_submultiplicative k d₁ (projection n)) 2
        _ = tauAF k d₁ ^ 2 * tauAF k (projection n) ^ 2 := by ring
    _ = ∑ q ∈ image, tauAF k d₁ ^ 2 * tauAF k q ^ 2 := by
      simpa [image] using
        (Finset.sum_image
          (f := fun q => tauAF k d₁ ^ 2 * tauAF k q ^ 2) hinj).symm
    _ ≤ ∑ q ∈ target, tauAF k d₁ ^ 2 * tauAF k q ^ 2 :=
      Finset.sum_le_sum_of_subset himage
    _ = tauAF k d₁ ^ 2 *
          progressionSum ((tauAF k).pmul (tauAF k))
            ((2 * N) / d₁) (((2 * N) / d₁) - (N / d₁))
            modulus residue := by
      rw [← Finset.mul_sum]
      congr 1
      simpa [target] using
        (quotientDyadic_tauSquare_eq_progressionSum
          k N d₁ modulus residue)

/-- Exact-content division of the second coordinate is injective on a
positive determinant fiber. -/
theorem positiveEquationFiber_secondDiv_injOn
    {N a b ell : ℕ} (hab : a.Coprime b) (ha : 0 < a) (hb : 0 < b) :
    let d₂ := ell.gcd a
    Set.InjOn (fun n : ℕ × ℕ => n.2 / d₂)
      (positiveEquationFiber N a b ell : Set (ℕ × ℕ)) := by
  dsimp
  intro x hx y hy hxy
  change x ∈ positiveEquationFiber N a b ell at hx
  change y ∈ positiveEquationFiber N a b ell at hy
  obtain ⟨_, hdx, _, _, _, _, _, _⟩ :=
    positiveFiber_reduced_equations hab ha hb hx
  obtain ⟨_, hdy, _, _, _, _, _, _⟩ :=
    positiveFiber_reduced_equations hab ha hb hy
  have hx₂ : x.2 = ell.gcd a * (x.2 / ell.gcd a) :=
    (Nat.mul_div_cancel' hdx).symm
  have hy₂ : y.2 = ell.gcd a * (y.2 / ell.gcd a) :=
    (Nat.mul_div_cancel' hdy).symm
  have hsecond : x.2 = y.2 := by
    rw [hx₂, hy₂]
    exact congrArg (fun z => ell.gcd a * z) hxy
  have hxdet := (Finset.mem_filter.mp hx).2
  have hydet := (Finset.mem_filter.mp hy).2
  apply Prod.ext
  · apply Nat.eq_of_mul_eq_mul_left ha
    calc
      a * x.1 = ell + b * x.2 := hxdet
      _ = ell + b * y.2 := by rw [hsecond]
      _ = a * y.1 := hydet.symm
  · exact hsecond

/-- The exact-content second coordinates lie in one primitive residue class
modulo `a / gcd(ell,a)`. -/
theorem positiveEquationFiber_secondDiv_modEq
    {N a b ell : ℕ} (hab : a.Coprime b) (ha : 0 < a) (hb : 0 < b)
    {x y : ℕ × ℕ} (hx : x ∈ positiveEquationFiber N a b ell)
    (hy : y ∈ positiveEquationFiber N a b ell) :
    x.2 / ell.gcd a ≡ y.2 / ell.gcd a [MOD a / ell.gcd a] := by
  obtain ⟨_, _, _, _, _, _, _, hxeq⟩ :=
    positiveFiber_reduced_equations hab ha hb hx
  obtain ⟨_, _, _, _, _, _, _, hyeq⟩ :=
    positiveFiber_reduced_equations hab ha hb hy
  have hx0 : ell / ell.gcd a + b * (x.2 / ell.gcd a) ≡ 0
      [MOD a / ell.gcd a] := by
    rw [add_comm, hxeq]
    exact (Nat.dvd_mul_right (a / ell.gcd a) x.1).modEq_zero_nat
  have hy0 : ell / ell.gcd a + b * (y.2 / ell.gcd a) ≡ 0
      [MOD a / ell.gcd a] := by
    rw [add_comm, hyeq]
    exact (Nat.dvd_mul_right (a / ell.gcd a) y.1).modEq_zero_nat
  have hmul : b * (x.2 / ell.gcd a) ≡ b * (y.2 / ell.gcd a)
      [MOD a / ell.gcd a] :=
    Nat.ModEq.add_left_cancel' (ell / ell.gcd a) (hx0.trans hy0.symm)
  have hdvd : a / ell.gcd a ∣ a :=
    Nat.div_dvd_of_dvd (Nat.gcd_dvd_right ell a)
  have hcop : b.Coprime (a / ell.gcd a) := hab.symm.coprime_dvd_right hdvd
  exact hmul.cancel_left_of_coprime hcop.symm

/-- Shiu-ready second-coordinate estimate, symmetric to the first-coordinate
bound but retaining its own content and modulus. -/
theorem exists_positiveFiber_second_progression_bound
    (k N a b ell : ℕ) (hab : a.Coprime b) (ha : 0 < a) (hb : 0 < b)
    (hne : (positiveEquationFiber N a b ell).Nonempty) :
    let d₂ := ell.gcd a
    let modulus := a / d₂
    ∃ residue : ℕ,
      residue < modulus ∧ residue.Coprime modulus ∧
      (∑ n ∈ positiveEquationFiber N a b ell, tauAF k n.2 ^ 2) ≤
        tauAF k d₂ ^ 2 *
          progressionSum ((tauAF k).pmul (tauAF k))
            ((2 * N) / d₂) (((2 * N) / d₂) - (N / d₂))
            modulus residue := by
  dsimp
  classical
  obtain ⟨base, hbase⟩ := hne
  let d₂ := ell.gcd a
  let modulus := a / d₂
  let baseReduced := base.2 / d₂
  let residue := baseReduced % modulus
  have hdpos : 0 < d₂ := Nat.gcd_pos_of_pos_right ell ha
  have hdvd : d₂ ∣ a := Nat.gcd_dvd_right ell a
  have hdle : d₂ ≤ a := Nat.le_of_dvd ha hdvd
  have hmodpos : 0 < modulus := Nat.div_pos hdle hdpos
  have hbaseData := positiveFiber_reduced_equations hab ha hb hbase
  have hbaseCoprime : baseReduced.Coprime modulus := by
    simpa [d₂, modulus, baseReduced] using hbaseData.2.2.2.2.2.1
  have hresidueLt : residue < modulus := Nat.mod_lt _ hmodpos
  have hresidueCoprime : residue.Coprime modulus :=
    (ZMod.coprime_mod_iff_coprime baseReduced modulus).2 hbaseCoprime
  refine ⟨residue, hresidueLt, hresidueCoprime, ?_⟩
  let projection : ℕ × ℕ → ℕ := fun n => n.2 / d₂
  let image := (positiveEquationFiber N a b ell).image projection
  let target := (quotientDyadic N d₂).filter
    (fun q => q ≡ residue [MOD modulus])
  have hinj : Set.InjOn projection
      (positiveEquationFiber N a b ell : Set (ℕ × ℕ)) := by
    simpa [projection, d₂] using
      (positiveEquationFiber_secondDiv_injOn hab ha hb)
  have himage : image ⊆ target := by
    intro q hq
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hq
    have hdata := positiveFiber_reduced_equations hab ha hb hn
    have hquotient : n.2 / d₂ ∈ quotientDyadic N d₂ := by
      simpa [d₂] using hdata.2.2.2.1
    have hsame : n.2 / d₂ ≡ baseReduced [MOD modulus] := by
      simpa [d₂, modulus, baseReduced] using
        (positiveEquationFiber_secondDiv_modEq hab ha hb hn hbase)
    have hres : n.2 / d₂ ≡ residue [MOD modulus] :=
      hsame.trans (Nat.mod_modEq baseReduced modulus).symm
    exact Finset.mem_filter.mpr ⟨hquotient, hres⟩
  calc
    (∑ n ∈ positiveEquationFiber N a b ell, tauAF k n.2 ^ 2) ≤
        ∑ n ∈ positiveEquationFiber N a b ell,
          tauAF k d₂ ^ 2 * tauAF k (projection n) ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      have hdata := positiveFiber_reduced_equations hab ha hb hn
      have hdiv : d₂ ∣ n.2 := by simpa [d₂] using hdata.2.1
      have hnfac : d₂ * projection n = n.2 := by
        simpa [projection] using Nat.mul_div_cancel' hdiv
      rw [← hnfac]
      calc
        tauAF k (d₂ * projection n) ^ 2 ≤
            (tauAF k d₂ * tauAF k (projection n)) ^ 2 :=
          Nat.pow_le_pow_left (tauAF_submultiplicative k d₂ (projection n)) 2
        _ = tauAF k d₂ ^ 2 * tauAF k (projection n) ^ 2 := by ring
    _ = ∑ q ∈ image, tauAF k d₂ ^ 2 * tauAF k q ^ 2 := by
      simpa [image] using
        (Finset.sum_image
          (f := fun q => tauAF k d₂ ^ 2 * tauAF k q ^ 2) hinj).symm
    _ ≤ ∑ q ∈ target, tauAF k d₂ ^ 2 * tauAF k q ^ 2 :=
      Finset.sum_le_sum_of_subset himage
    _ = tauAF k d₂ ^ 2 *
          progressionSum ((tauAF k).pmul (tauAF k))
            ((2 * N) / d₂) (((2 * N) / d₂) - (N / d₂))
            modulus residue := by
      rw [← Finset.mul_sum]
      congr 1
      simpa [target] using
        (quotientDyadic_tauSquare_eq_progressionSum
          k N d₂ modulus residue)

/-- Complete Shiu-ready positive-fiber reduction.  Both residue classes are
primitive, both quotient windows are literal, and Cauchy's inequality ends at
the product of the two finite progression sums.  Shiu's analytic bound is not
assumed here. -/
theorem exists_positiveFiber_shiuReady_bound
    (k N a b ell : ℕ) (hab : a.Coprime b) (ha : 0 < a) (hb : 0 < b)
    (hne : (positiveEquationFiber N a b ell).Nonempty) :
    let d₁ := ell.gcd b
    let d₂ := ell.gcd a
    let modulus₁ := b / d₁
    let modulus₂ := a / d₂
    ∃ residue₁ residue₂ : ℕ,
      residue₁ < modulus₁ ∧ residue₁.Coprime modulus₁ ∧
      residue₂ < modulus₂ ∧ residue₂.Coprime modulus₂ ∧
      (fiberMass (fun n₁ n₂ => tauAF k n₁ * tauAF k n₂)
          (positiveEquationFiber N a b ell)) ^ 2 ≤
        (tauAF k d₁ ^ 2 * tauAF k d₂ ^ 2) *
          (progressionSum ((tauAF k).pmul (tauAF k))
              ((2 * N) / d₁) (((2 * N) / d₁) - (N / d₁))
              modulus₁ residue₁ *
            progressionSum ((tauAF k).pmul (tauAF k))
              ((2 * N) / d₂) (((2 * N) / d₂) - (N / d₂))
              modulus₂ residue₂) := by
  dsimp
  obtain ⟨residue₁, hr₁lt, hr₁cop, hfirst⟩ :=
    exists_positiveFiber_first_progression_bound k N a b ell hab ha hb hne
  obtain ⟨residue₂, hr₂lt, hr₂cop, hsecond⟩ :=
    exists_positiveFiber_second_progression_bound k N a b ell hab ha hb hne
  refine ⟨residue₁, residue₂, hr₁lt, hr₁cop, hr₂lt, hr₂cop, ?_⟩
  calc
    (fiberMass (fun n₁ n₂ => tauAF k n₁ * tauAF k n₂)
        (positiveEquationFiber N a b ell)) ^ 2 ≤
        (∑ n ∈ positiveEquationFiber N a b ell, tauAF k n.1 ^ 2) *
          ∑ n ∈ positiveEquationFiber N a b ell, tauAF k n.2 ^ 2 :=
      fiberMass_tauAF_sq_le k _
    _ ≤ (tauAF k (ell.gcd b) ^ 2 *
          progressionSum ((tauAF k).pmul (tauAF k))
            ((2 * N) / ell.gcd b)
            (((2 * N) / ell.gcd b) - (N / ell.gcd b))
            (b / ell.gcd b) residue₁) *
        (tauAF k (ell.gcd a) ^ 2 *
          progressionSum ((tauAF k).pmul (tauAF k))
            ((2 * N) / ell.gcd a)
            (((2 * N) / ell.gcd a) - (N / ell.gcd a))
            (a / ell.gcd a) residue₂) := Nat.mul_le_mul hfirst hsecond
    _ = (tauAF k (ell.gcd b) ^ 2 * tauAF k (ell.gcd a) ^ 2) *
        (progressionSum ((tauAF k).pmul (tauAF k))
            ((2 * N) / ell.gcd b)
            (((2 * N) / ell.gcd b) - (N / ell.gcd b))
            (b / ell.gcd b) residue₁ *
          progressionSum ((tauAF k).pmul (tauAF k))
            ((2 * N) / ell.gcd a)
            (((2 * N) / ell.gcd a) - (N / ell.gcd a))
            (a / ell.gcd a) residue₂) := by ring

/-- Swap the two long coordinates. -/
def swapLongPair (n : ℕ × ℕ) : ℕ × ℕ := (n.2, n.1)

@[simp] theorem swapLongPair_involutive (n : ℕ × ℕ) :
    swapLongPair (swapLongPair n) = n := by
  rcases n with ⟨n₁, n₂⟩
  rfl

theorem swapLongPair_injective : Function.Injective swapLongPair := by
  intro x y hxy
  calc
    x = swapLongPair (swapLongPair x) := (swapLongPair_involutive x).symm
    _ = swapLongPair (swapLongPair y) := by rw [hxy]
    _ = y := swapLongPair_involutive y

/-- Swapping the long coordinates identifies a negative determinant equation
with the corresponding positive equation having `a` and `b` exchanged. -/
theorem image_swapLongPair_negativeEquationFiber
    (N a b ell : ℕ) :
    (negativeEquationFiber N a b ell).image swapLongPair =
      positiveEquationFiber N b a ell := by
  ext n
  constructor
  · intro hn
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hn
    simp only [negativeEquationFiber, positiveEquationFiber,
      Finset.mem_filter] at hq ⊢
    rcases hq with ⟨hqbox, hqdet⟩
    rcases Finset.mem_product.mp hqbox with ⟨hq₁, hq₂⟩
    exact ⟨Finset.mem_product.mpr ⟨hq₂, hq₁⟩, hqdet⟩
  · intro hn
    apply Finset.mem_image.mpr
    refine ⟨swapLongPair n, ?_, swapLongPair_involutive n⟩
    simp only [negativeEquationFiber, positiveEquationFiber,
      Finset.mem_filter] at hn ⊢
    rcases hn with ⟨hnbox, hndet⟩
    rcases Finset.mem_product.mp hnbox with ⟨hn₁, hn₂⟩
    exact ⟨Finset.mem_product.mpr ⟨hn₂, hn₁⟩, hndet⟩

/-- The symmetric divisor-product weight is preserved by the long-coordinate
swap. -/
theorem negativeFiber_tauMass_eq_positiveSwapped
    (k N a b ell : ℕ) :
    fiberMass (fun n₁ n₂ => tauAF k n₁ * tauAF k n₂)
        (negativeEquationFiber N a b ell) =
      fiberMass (fun n₁ n₂ => tauAF k n₁ * tauAF k n₂)
        (positiveEquationFiber N b a ell) := by
  classical
  unfold fiberMass
  rw [← image_swapLongPair_negativeEquationFiber N a b ell]
  rw [Finset.sum_image swapLongPair_injective.injOn]
  apply Finset.sum_congr rfl
  intro n hn
  simp [swapLongPair, mul_comm]

/-- Complete Shiu-ready reduction for a negative determinant fiber, obtained
from the literal sign swap.  The first displayed content belongs to the
original second coordinate, exactly as the swapped equation dictates. -/
theorem exists_negativeFiber_shiuReady_bound
    (k N a b ell : ℕ) (hab : a.Coprime b) (ha : 0 < a) (hb : 0 < b)
    (hne : (negativeEquationFiber N a b ell).Nonempty) :
    let d₂ := ell.gcd a
    let d₁ := ell.gcd b
    let modulus₂ := a / d₂
    let modulus₁ := b / d₁
    ∃ residue₂ residue₁ : ℕ,
      residue₂ < modulus₂ ∧ residue₂.Coprime modulus₂ ∧
      residue₁ < modulus₁ ∧ residue₁.Coprime modulus₁ ∧
      (fiberMass (fun n₁ n₂ => tauAF k n₁ * tauAF k n₂)
          (negativeEquationFiber N a b ell)) ^ 2 ≤
        (tauAF k d₂ ^ 2 * tauAF k d₁ ^ 2) *
          (progressionSum ((tauAF k).pmul (tauAF k))
              ((2 * N) / d₂) (((2 * N) / d₂) - (N / d₂))
              modulus₂ residue₂ *
            progressionSum ((tauAF k).pmul (tauAF k))
              ((2 * N) / d₁) (((2 * N) / d₁) - (N / d₁))
              modulus₁ residue₁) := by
  dsimp
  have hneSwapped : (positiveEquationFiber N b a ell).Nonempty := by
    obtain ⟨n, hn⟩ := hne
    refine ⟨swapLongPair n, ?_⟩
    rw [← image_swapLongPair_negativeEquationFiber N a b ell]
    exact Finset.mem_image.mpr ⟨n, hn, rfl⟩
  obtain ⟨residue₂, residue₁, hr₂lt, hr₂cop, hr₁lt, hr₁cop, hbound⟩ :=
    exists_positiveFiber_shiuReady_bound k N b a ell hab.symm hb ha hneSwapped
  refine ⟨residue₂, residue₁, hr₂lt, hr₂cop, hr₁lt, hr₁cop, ?_⟩
  rw [negativeFiber_tauMass_eq_positiveSwapped]
  exact hbound

/-- A residue class below `2*N+1` contains at most the explicit elementary
progression envelope. -/
theorem card_modEq_range_le_progressionCardEnvelope
    (N modulus residue : ℕ) (hmodulus : 0 < modulus) :
    ({x ∈ Finset.range (2 * N + 1) | x ≡ residue [MOD modulus]} : Finset ℕ).card ≤
      progressionCardEnvelope N modulus := by
  rw [← Nat.count_eq_card_filter_range,
    Nat.count_modEq_card (2 * N + 1) hmodulus residue]
  unfold progressionCardEnvelope
  split_ifs <;> omega

/-- Uniform, unconditional cardinal bound for every positive nonzero
determinant equation.  No Shiu estimate is used. -/
theorem card_positiveEquationFiber_le (N a b ell : ℕ)
    (hab : a.Coprime b) (ha : 0 < a) :
    (positiveEquationFiber N a b ell).card ≤ progressionCardEnvelope N a := by
  classical
  by_cases hempty : positiveEquationFiber N a b ell = ∅
  · simp [hempty, progressionCardEnvelope]
  · obtain ⟨base, hbase⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    let residue := base.2 % a
    let target : Finset ℕ :=
      {x ∈ Finset.range (2 * N + 1) | x ≡ residue [MOD a]}
    have himage : (positiveEquationFiber N a b ell).image Prod.snd ⊆ target := by
      intro x hx
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
      have hqbox := (Finset.mem_filter.mp hq).1
      have hq₂ := (Finset.mem_product.mp hqbox).2
      have hq₂upper : q.2 < 2 * N + 1 := by
        simp only [dyadic, Finset.mem_Ioc] at hq₂
        omega
      have hmodBase : q.2 ≡ base.2 [MOD a] :=
        positiveEquationFiber_snd_modEq hab hq hbase
      have hmodResidue : q.2 ≡ residue [MOD a] :=
        hmodBase.trans (Nat.mod_modEq base.2 a).symm
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr hq₂upper, hmodResidue⟩
    calc
      (positiveEquationFiber N a b ell).card =
          ((positiveEquationFiber N a b ell).image Prod.snd).card :=
        (Finset.card_image_of_injOn (positiveEquationFiber_snd_injOn ha)).symm
      _ ≤ target.card := Finset.card_le_card himage
      _ ≤ progressionCardEnvelope N a :=
        card_modEq_range_le_progressionCardEnvelope N a residue ha

/-- Uniform bound for the negative determinant equation. -/
theorem card_negativeEquationFiber_le (N a b ell : ℕ)
    (hab : a.Coprime b) (hb : 0 < b) :
    (negativeEquationFiber N a b ell).card ≤ progressionCardEnvelope N b := by
  classical
  by_cases hempty : negativeEquationFiber N a b ell = ∅
  · simp [hempty, progressionCardEnvelope]
  · obtain ⟨base, hbase⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    let residue := base.1 % b
    let target : Finset ℕ :=
      {x ∈ Finset.range (2 * N + 1) | x ≡ residue [MOD b]}
    have himage : (negativeEquationFiber N a b ell).image Prod.fst ⊆ target := by
      intro x hx
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
      have hqbox := (Finset.mem_filter.mp hq).1
      have hq₁ := (Finset.mem_product.mp hqbox).1
      have hq₁upper : q.1 < 2 * N + 1 := by
        simp only [dyadic, Finset.mem_Ioc] at hq₁
        omega
      have hmodBase : q.1 ≡ base.1 [MOD b] :=
        negativeEquationFiber_fst_modEq hab hq hbase
      have hmodResidue : q.1 ≡ residue [MOD b] :=
        hmodBase.trans (Nat.mod_modEq base.1 b).symm
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr hq₁upper, hmodResidue⟩
    calc
      (negativeEquationFiber N a b ell).card =
          ((negativeEquationFiber N a b ell).image Prod.fst).card :=
        (Finset.card_image_of_injOn (negativeEquationFiber_fst_injOn hb)).symm
      _ ≤ target.card := Finset.card_le_card himage
      _ ≤ progressionCardEnvelope N b :=
        card_modEq_range_le_progressionCardEnvelope N b residue hb

/-- Summing the per-equation bounds over the exact range `1 <= ell <= H/d`
controls the entire fixed-pair nonzero collar, uniformly in every parameter. -/
theorem card_nonzeroReducedCollar_le
    (N H d a b : ℕ) (hab : a.Coprime b)
    (hd : 0 < d) (ha : 0 < a) (hb : 0 < b) :
    (nonzeroReducedCollar N H d a b).card ≤
      (H / d) *
        (progressionCardEnvelope N a + progressionCardEnvelope N b) := by
  rw [nonzeroReducedCollar_eq_signedEquationFibers N H d a b hd]
  unfold signedEquationFibers
  calc
    ((Finset.Icc 1 (H / d)).biUnion fun ell =>
        positiveEquationFiber N a b ell ∪
          negativeEquationFiber N a b ell).card ≤
        ∑ ell ∈ Finset.Icc 1 (H / d),
          (positiveEquationFiber N a b ell ∪
            negativeEquationFiber N a b ell).card := Finset.card_biUnion_le
    _ ≤ ∑ _ell ∈ Finset.Icc 1 (H / d),
        (progressionCardEnvelope N a + progressionCardEnvelope N b) := by
      apply Finset.sum_le_sum
      intro ell hell
      exact (Finset.card_union_le _ _).trans
        (Nat.add_le_add
          (card_positiveEquationFiber_le N a b ell hab ha)
          (card_negativeEquationFiber_le N a b ell hab hb))
    _ = (H / d) *
        (progressionCardEnvelope N a + progressionCardEnvelope N b) := by simp

/-- Projection is injective on the literal fixed-short-pair nonzero slice. -/
theorem fixedNonzeroLiteralSlice_snd_injOn
    {M N K Y d a b : ℕ} :
    Set.InjOn Prod.snd
      (fixedNonzeroLiteralSlice M N K Y d a b : Set LiteralTuple) := by
  intro x hx y hy hxy
  change x ∈ fixedNonzeroLiteralSlice M N K Y d a b at hx
  change y ∈ fixedNonzeroLiteralSlice M N K Y d a b at hy
  have hxshort := (Finset.mem_filter.mp hx).2.1
  have hyshort := (Finset.mem_filter.mp hy).2.1
  apply Prod.ext
  · exact hxshort.trans hyshort.symm
  · exact hxy

/-- The fixed-pair bound is attached to the actual four-variable literal
slice, not only to its reduced two-variable projection. -/
theorem card_fixedNonzeroLiteralSlice_le
    (M N K Y d a b : ℕ) (hab : a.Coprime b)
    (hd : 0 < d) (ha : 0 < a) (hb : 0 < b)
    (hshortBox : (d * a, d * b) ∈ (dyadic M).product (dyadic M))
    (hshortNe : d * a ≠ d * b)
    (hshortK : (d * a).dist (d * b) ≤ K) :
    (fixedNonzeroLiteralSlice M N K Y d a b).card ≤
      (Y / d) *
        (progressionCardEnvelope N a + progressionCardEnvelope N b) := by
  rw [← Finset.card_image_of_injOn fixedNonzeroLiteralSlice_snd_injOn,
    image_fixedNonzeroLiteralSlice_eq_nonzeroReducedCollar
      M N K Y d a b hshortBox hshortNe hshortK]
  exact card_nonzeroReducedCollar_le N Y d a b hab hd ha hb

/-- A literal fixed-short-pair slice of the unequal-short-index zero
determinant sector. -/
def fixedZeroLiteralSlice (M N K Y d a b : ℕ) : Finset LiteralTuple :=
  (literalTuples M N K Y).filter fun t =>
    t.1 = (d * a, d * b) ∧ determinant t = 0

/-- The zero slice projects exactly to the range-sensitive zero fiber. -/
theorem image_fixedZeroLiteralSlice_eq_zeroFiber
    (M N K Y d a b : ℕ) (hd : 0 < d)
    (hshortBox : (d * a, d * b) ∈ (dyadic M).product (dyadic M))
    (hshortNe : d * a ≠ d * b)
    (hshortK : (d * a).dist (d * b) ≤ K) :
    (fixedZeroLiteralSlice M N K Y d a b).image Prod.snd =
      zeroFiber N a b := by
  ext n
  constructor
  · intro hn
    obtain ⟨t, ht, ht₂⟩ := Finset.mem_image.mp hn
    rcases Finset.mem_filter.mp ht with ⟨htLiteral, htShort, htDetZero⟩
    have htEq : t = ((d * a, d * b), n) := Prod.ext htShort ht₂
    subst t
    rcases Finset.mem_filter.mp htLiteral with ⟨htBox, _, _, _⟩
    have hnBox : n ∈ (dyadic N).product (dyadic N) :=
      (Finset.mem_product.mp htBox).2
    have hdist : (d * a * n.1).dist (d * b * n.2) = 0 := by
      rw [← determinant_natAbs_eq_product_dist
        (((d * a, d * b), n) : LiteralTuple), htDetZero]
      rfl
    have hproduct : d * (a * n.1) = d * (b * n.2) := by
      simpa [mul_assoc] using Nat.eq_of_dist_eq_zero hdist
    have hreduced : a * n.1 = b * n.2 := Nat.eq_of_mul_eq_mul_left hd hproduct
    exact Finset.mem_filter.mpr ⟨hnBox, hreduced⟩
  · intro hn
    rcases Finset.mem_filter.mp hn with ⟨hnBox, hreduced⟩
    apply Finset.mem_image.mpr
    refine ⟨(((d * a, d * b), n) : LiteralTuple), ?_, rfl⟩
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨hshortBox, hnBox⟩,
        hshortNe, hshortK, ?_⟩
      rw [determinant_natAbs_eq_product_dist]
      have hproduct : d * a * n.1 = d * b * n.2 := by
        calc
          d * a * n.1 = d * (a * n.1) := by ac_rfl
          _ = d * (b * n.2) := by rw [hreduced]
          _ = d * b * n.2 := by ac_rfl
      simp [hproduct]
    · refine ⟨rfl, ?_⟩
      apply Int.natAbs_eq_zero.mp
      rw [determinant_natAbs_eq_product_dist]
      have hproduct : d * a * n.1 = d * b * n.2 := by
        calc
          d * a * n.1 = d * (a * n.1) := by ac_rfl
          _ = d * (b * n.2) := by rw [hreduced]
          _ = d * b * n.2 := by ac_rfl
      exact Nat.dist_eq_zero hproduct

theorem fixedZeroLiteralSlice_snd_injOn
    {M N K Y d a b : ℕ} :
    Set.InjOn Prod.snd
      (fixedZeroLiteralSlice M N K Y d a b : Set LiteralTuple) := by
  intro x hx y hy hxy
  change x ∈ fixedZeroLiteralSlice M N K Y d a b at hx
  change y ∈ fixedZeroLiteralSlice M N K Y d a b at hy
  have hxshort := (Finset.mem_filter.mp hx).2.1
  have hyshort := (Finset.mem_filter.mp hy).2.1
  apply Prod.ext
  · exact hxshort.trans hyshort.symm
  · exact hxy

/-- The legal zero parameters lie in the exact positive range forced by both
dyadic upper bounds. -/
theorem zeroParameters_subset_Icc (N a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    zeroParameters N a b ⊆
      Finset.Icc 1 (min ((2 * N) / a) ((2 * N) / b)) := by
  intro s hs
  simp only [zeroParameters, Finset.mem_filter, Finset.mem_range] at hs
  rcases hs with ⟨_, hbLower, hbUpper, haLower, haUpper⟩
  simp only [Finset.mem_Icc]
  constructor
  · exact Nat.one_le_iff_ne_zero.mpr fun hs0 => by
      subst s
      simp at hbLower
  · apply le_min
    · exact (Nat.le_div_iff_mul_le ha).2 (by simpa [Nat.mul_comm] using haUpper)
    · exact (Nat.le_div_iff_mul_le hb).2 (by simpa [Nat.mul_comm] using hbUpper)

/-- Sharp elementary cardinal bound for a fixed zero determinant fiber. -/
theorem card_zeroFiber_le (N a b : ℕ) (hab : a.Coprime b)
    (ha : 0 < a) (hb : 0 < b) :
    (zeroFiber N a b).card ≤ min ((2 * N) / a) ((2 * N) / b) := by
  rw [card_zeroFiber_eq_card_zeroParameters N a b hab hb]
  calc
    (zeroParameters N a b).card ≤
        (Finset.Icc 1 (min ((2 * N) / a) ((2 * N) / b))).card :=
      Finset.card_le_card (zeroParameters_subset_Icc N a b ha hb)
    _ = min ((2 * N) / a) ((2 * N) / b) := by simp

/-- The sharp fixed-fiber zero bound, welded back to the literal four-index
slice. -/
theorem card_fixedZeroLiteralSlice_le
    (M N K Y d a b : ℕ) (hab : a.Coprime b)
    (hd : 0 < d) (ha : 0 < a) (hb : 0 < b)
    (hshortBox : (d * a, d * b) ∈ (dyadic M).product (dyadic M))
    (hshortNe : d * a ≠ d * b)
    (hshortK : (d * a).dist (d * b) ≤ K) :
    (fixedZeroLiteralSlice M N K Y d a b).card ≤
      min ((2 * N) / a) ((2 * N) / b) := by
  rw [← Finset.card_image_of_injOn fixedZeroLiteralSlice_snd_injOn,
    image_fixedZeroLiteralSlice_eq_zeroFiber
      M N K Y d a b hd hshortBox hshortNe hshortK]
  exact card_zeroFiber_le N a b hab ha hb

/-- A pointwise real weight bounded by `W` has total mass at most cardinality
times `W`.  This is the safe bridge from the cardinal sector estimates to the
frontend's literal pointwise weighting. -/
theorem weightedMass_le_card_mul
    (w : LiteralTuple → ℝ) (s : Finset LiteralTuple) (W : ℝ)
    (hw : ∀ q ∈ s, w q ≤ W) :
    weightedMass w s ≤ (s.card : ℝ) * W := by
  unfold weightedMass
  calc
    (∑ q ∈ s, w q) ≤ ∑ _q ∈ s, W := by
      apply Finset.sum_le_sum
      intro q hq
      exact hw q hq
    _ = (s.card : ℝ) * W := by simp

/-- Pointwise-bounded weighted estimate for the literal fixed-pair nonzero
sector.  All parameter dependence is explicit. -/
theorem weighted_fixedNonzeroLiteralSlice_le
    (w : LiteralTuple → ℝ) (W : ℝ)
    (M N K Y d a b : ℕ) (hab : a.Coprime b)
    (hd : 0 < d) (ha : 0 < a) (hb : 0 < b)
    (hW : 0 ≤ W)
    (hshortBox : (d * a, d * b) ∈ (dyadic M).product (dyadic M))
    (hshortNe : d * a ≠ d * b)
    (hshortK : (d * a).dist (d * b) ≤ K)
    (hw : ∀ q ∈ fixedNonzeroLiteralSlice M N K Y d a b, w q ≤ W) :
    weightedMass w (fixedNonzeroLiteralSlice M N K Y d a b) ≤
      ((Y / d) *
        (progressionCardEnvelope N a + progressionCardEnvelope N b) : ℕ) * W := by
  calc
    weightedMass w (fixedNonzeroLiteralSlice M N K Y d a b) ≤
        ((fixedNonzeroLiteralSlice M N K Y d a b).card : ℝ) * W :=
      weightedMass_le_card_mul w _ W hw
    _ ≤ ((Y / d) *
          (progressionCardEnvelope N a + progressionCardEnvelope N b) : ℕ) * W := by
      apply mul_le_mul_of_nonneg_right _ hW
      exact_mod_cast card_fixedNonzeroLiteralSlice_le M N K Y d a b
        hab hd ha hb hshortBox hshortNe hshortK

/-- Pointwise-bounded weighted estimate for the literal fixed-pair zero
sector. -/
theorem weighted_fixedZeroLiteralSlice_le
    (w : LiteralTuple → ℝ) (W : ℝ)
    (M N K Y d a b : ℕ) (hab : a.Coprime b)
    (hd : 0 < d) (ha : 0 < a) (hb : 0 < b)
    (hW : 0 ≤ W)
    (hshortBox : (d * a, d * b) ∈ (dyadic M).product (dyadic M))
    (hshortNe : d * a ≠ d * b)
    (hshortK : (d * a).dist (d * b) ≤ K)
    (hw : ∀ q ∈ fixedZeroLiteralSlice M N K Y d a b, w q ≤ W) :
    weightedMass w (fixedZeroLiteralSlice M N K Y d a b) ≤
      (min ((2 * N) / a) ((2 * N) / b) : ℕ) * W := by
  calc
    weightedMass w (fixedZeroLiteralSlice M N K Y d a b) ≤
        ((fixedZeroLiteralSlice M N K Y d a b).card : ℝ) * W :=
      weightedMass_le_card_mul w _ W hw
    _ ≤ (min ((2 * N) / a) ((2 * N) / b) : ℕ) * W := by
      apply mul_le_mul_of_nonneg_right _ hW
      exact_mod_cast card_fixedZeroLiteralSlice_le M N K Y d a b
        hab hd ha hb hshortBox hshortNe hshortK

/-- Exact reindexing of an arbitrary pointwise weight on the zero fiber. -/
theorem zeroFiberMass_eq_parameterSum
    (w : ℕ → ℕ → ℕ) (N a b : ℕ) (hab : a.Coprime b) (hb : 0 < b) :
    fiberMass w (zeroFiber N a b) =
      ∑ s ∈ zeroParameters N a b, w (b * s) (a * s) := by
  classical
  unfold fiberMass
  rw [← image_zeroParameters_eq_zeroFiber N a b hab hb]
  rw [Finset.sum_image]
  intro s hs t ht hst
  have hbst : b * s = b * t := congrArg Prod.fst hst
  exact Nat.eq_of_mul_eq_mul_left hb hbst

/-- The full weighted zero determinant sector is bounded by one explicit
divisor-square moment.  This is the paper's zero-sector reduction before the
classical second-moment estimate is invoked. -/
theorem zeroFiber_tauMass_le_secondMoment
    (k N a b : ℕ) (hab : a.Coprime b) (ha : 0 < a) (hb : 0 < b) :
    fiberMass (fun n₁ n₂ => tauAF k n₁ * tauAF k n₂) (zeroFiber N a b) ≤
      (tauAF k b * tauAF k a) *
        zeroSecondMoment k (min ((2 * N) / a) ((2 * N) / b)) := by
  rw [zeroFiberMass_eq_parameterSum _ N a b hab hb]
  calc
    (∑ s ∈ zeroParameters N a b,
        tauAF k (b * s) * tauAF k (a * s)) ≤
        ∑ s ∈ zeroParameters N a b,
          (tauAF k b * tauAF k a) * tauAF k s ^ 2 := by
      apply Finset.sum_le_sum
      intro s hs
      calc
        tauAF k (b * s) * tauAF k (a * s) ≤
            (tauAF k b * tauAF k s) * (tauAF k a * tauAF k s) :=
          Nat.mul_le_mul (tauAF_submultiplicative k b s)
            (tauAF_submultiplicative k a s)
        _ = (tauAF k b * tauAF k a) * tauAF k s ^ 2 := by ring
    _ ≤ ∑ s ∈ Finset.Icc 1 (min ((2 * N) / a) ((2 * N) / b)),
          (tauAF k b * tauAF k a) * tauAF k s ^ 2 :=
      Finset.sum_le_sum_of_subset (zeroParameters_subset_Icc N a b ha hb)
    _ = (tauAF k b * tauAF k a) *
        zeroSecondMoment k (min ((2 * N) / a) ((2 * N) / b)) := by
      unfold zeroSecondMoment
      rw [Finset.mul_sum]

end

end MAPMixedMean
