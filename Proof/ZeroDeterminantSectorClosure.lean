import DeterminantSectorBounds

namespace MAPMixedMeanZeroClose

open ArithmeticFunction MixedMellinCert DeterminantCountWeld ShiuFoundation MAPMixedMean
open scoped ArithmeticFunction.zeta

 theorem multichoose_sq_le (k e : ℕ) :
    k.multichoose e ^ 2 ≤ (k * k).multichoose e := by
  induction e with
  | zero => simp
  | succ e ih =>
      cases k with
      | zero => simp [Nat.multichoose_zero_succ]
      | succ k =>
          have hfactor : (k + 1 + e) ^ 2 ≤ (e + 1) * ((k + 1) * (k + 1) + e) := by
            nlinarith [sq_nonneg (k : ℤ)]
          have hA :
              (e + 1) * (k + 1).multichoose (e + 1) =
                (k + 1 + e) * (k + 1).multichoose e := by
            rw [Nat.multichoose_eq, Nat.multichoose_eq]
            rw [show k + 1 + e - 1 = k + e by omega,
              show k + 1 + (e + 1) - 1 = k + e + 1 by omega]
            simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, mul_comm] using
              (Nat.add_one_mul_choose_eq (k + e) e).symm
          have hB :
              (e + 1) * ((k + 1) * (k + 1)).multichoose (e + 1) =
                ((k + 1) * (k + 1) + e) *
                  ((k + 1) * (k + 1)).multichoose e := by
            rw [Nat.multichoose_eq, Nat.multichoose_eq]
            have hkpos : 0 < (k + 1) * (k + 1) := Nat.mul_pos (by omega) (by omega)
            rw [show (k + 1) * (k + 1) + e - 1 =
                  ((k + 1) * (k + 1) - 1) + e by omega,
              show (k + 1) * (k + 1) + (e + 1) - 1 =
                  ((k + 1) * (k + 1) - 1) + e + 1 by omega]
            simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, mul_comm] using
              (Nat.add_one_mul_choose_eq
                ((k + 1) * (k + 1) - 1 + e) e).symm
          apply Nat.le_of_mul_le_mul_left (c := (e + 1) ^ 2) (hc := pow_pos (by omega) 2)
          calc
            (e + 1) ^ 2 * (k + 1).multichoose (e + 1) ^ 2 =
                ((e + 1) * (k + 1).multichoose (e + 1)) ^ 2 := by ring
            _ = ((k + 1 + e) * (k + 1).multichoose e) ^ 2 := by rw [hA]
            _ = (k + 1 + e) ^ 2 * ((k + 1).multichoose e) ^ 2 := by ring
            _ ≤ ((e + 1) * ((k + 1) * (k + 1) + e)) *
                ((k + 1) * (k + 1)).multichoose e :=
              Nat.mul_le_mul hfactor ih
            _ = (e + 1) * (((k + 1) * (k + 1) + e) *
                ((k + 1) * (k + 1)).multichoose e) := by ring
            _ = (e + 1) * ((e + 1) *
                ((k + 1) * (k + 1)).multichoose (e + 1)) := by rw [hB]
            _ = (e + 1) ^ 2 *
                ((k + 1) * (k + 1)).multichoose (e + 1) := by ring


 theorem tauAF_sq_le_tauAF_mul (k n : ℕ) : tauAF k n ^ 2 ≤ tauAF (k*k) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [tauAF_eq_factorization_prod k n hn,
    tauAF_eq_factorization_prod (k*k) n hn, pow_two]
  rw [← Finsupp.prod_mul]
  let s := n.factorization.support
  rw [Finsupp.prod_of_support_subset n.factorization (s := s) (by rfl)
      (fun _ e => k.multichoose e * k.multichoose e) (by intro i hi; simp),
    Finsupp.prod_of_support_subset n.factorization (s := s) (by rfl)
      (fun _ e => (k * k).multichoose e) (by intro i hi; simp)]
  apply Finset.prod_le_prod'
  intro p hp
  simpa [pow_two] using multichoose_sq_le k (n.factorization p)



 def reciprocalTwist (f : ArithmeticFunction ℚ) : ArithmeticFunction ℚ :=
  ⟨fun n => if n = 0 then 0 else f n / n, by simp⟩

 @[simp] theorem reciprocalTwist_apply (f : ArithmeticFunction ℚ) (n : ℕ) :
    reciprocalTwist f n = if n = 0 then 0 else f n / n := rfl

 theorem reciprocalTwist_mul (f g : ArithmeticFunction ℚ) :
    reciprocalTwist (f * g) = reciprocalTwist f * reciprocalTwist g := by
  ext n
  rcases n with _ | n
  · simp [reciprocalTwist]
  · rw [reciprocalTwist_apply, if_neg (Nat.succ_ne_zero n),
      ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro p hp
    obtain ⟨hprod, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hp
    obtain ⟨hp1, hp2⟩ := Nat.ne_zero_of_mem_divisorsAntidiagonal hp
    rw [reciprocalTwist_apply, reciprocalTwist_apply, if_neg hp1, if_neg hp2]
    rw [← hprod]
    field_simp
    rw [Nat.cast_mul]
    ring



 def tauRat (r : ℕ) : ArithmeticFunction ℚ := (tauAF r : ArithmeticFunction ℚ)

 theorem tauRat_succ (r : ℕ) : tauRat (r + 1) = tauRat r * (ζ : ArithmeticFunction ℚ) := by
  unfold tauRat tauAF
  rw [pow_succ', mul_comm]
  ext n
  simp only [ArithmeticFunction.natCoe_apply, ArithmeticFunction.mul_apply]
  push_cast
  rfl

 theorem harmonic_mono {x y : ℕ} (hxy : x ≤ y) : harmonic x ≤ harmonic y := by
  induction y, hxy using Nat.le_induction with
  | base => rfl
  | succ y hxy ih =>
      rw [harmonic_succ]
      have hnonneg : (0 : ℚ) ≤ ((y + 1 : ℕ) : ℚ)⁻¹ := by positivity
      exact ih.trans (le_add_of_nonneg_right hnonneg)

 theorem sum_reciprocalTwist_zeta_eq_harmonic (X : ℕ) :
    ∑ n ∈ Finset.Ioc 0 X, reciprocalTwist (ζ : ArithmeticFunction ℚ) n = harmonic X := by
  rw [harmonic_eq_sum_Icc]
  have hset : Finset.Ioc 0 X = Finset.Icc 1 X := by ext n; simp; omega
  rw [hset]
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := by simp only [Finset.mem_Icc] at hn; omega
  simp [reciprocalTwist, ArithmeticFunction.zeta_apply, hn0]

 def weightedTauSum (r X : ℕ) : ℚ :=
  ∑ n ∈ Finset.Ioc 0 X, reciprocalTwist (tauRat r) n

 theorem weightedTauSum_le_harmonic_pow (r X : ℕ) :
    weightedTauSum r X ≤ harmonic X ^ r := by
  induction r with
  | zero =>
      unfold weightedTauSum tauRat tauAF
      simp only [pow_zero]
      by_cases hX : X = 0
      · subst X; simp
      · have h1X : 1 ≤ X := Nat.one_le_iff_ne_zero.mpr hX
        have hmem : 1 ∈ Finset.Ioc 0 X := by simp [h1X]
        rw [Finset.sum_eq_single 1]
        · simp [reciprocalTwist, ArithmeticFunction.one_apply]
        · intro n hn hn1
          have hn0 : n ≠ 0 := by simp only [Finset.mem_Ioc] at hn; omega
          simp [reciprocalTwist, ArithmeticFunction.one_apply, hn0, hn1]
        · intro hnot
          exact (hnot hmem).elim
  | succ r ihr =>
      unfold weightedTauSum at ihr ⊢
      rw [tauRat_succ, reciprocalTwist_mul,
        ArithmeticFunction.sum_Ioc_mul_eq_sum_sum]
      calc
        (∑ n ∈ Finset.Ioc 0 X,
            reciprocalTwist (tauRat r) n *
              ∑ m ∈ Finset.Ioc 0 (X / n),
                reciprocalTwist (ζ : ArithmeticFunction ℚ) m) =
            ∑ n ∈ Finset.Ioc 0 X,
              reciprocalTwist (tauRat r) n * harmonic (X / n) := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [sum_reciprocalTwist_zeta_eq_harmonic]
        _ ≤ ∑ n ∈ Finset.Ioc 0 X,
              reciprocalTwist (tauRat r) n * harmonic X := by
          apply Finset.sum_le_sum
          intro n hn
          apply mul_le_mul_of_nonneg_left
          · exact harmonic_mono (Nat.div_le_self X n)
          · have hn0 : n ≠ 0 := by simp only [Finset.mem_Ioc] at hn; omega
            simp only [reciprocalTwist_apply, if_neg hn0]
            change 0 ≤ (tauAF r n : ℚ) / (n : ℚ)
            exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        _ = (∑ n ∈ Finset.Ioc 0 X, reciprocalTwist (tauRat r) n) * harmonic X := by
          rw [Finset.sum_mul]
        _ ≤ harmonic X ^ r * harmonic X :=
          mul_le_mul_of_nonneg_right ihr (by
            have hz := harmonic_mono (x := 0) (y := X) (Nat.zero_le X)
            simpa using hz)
        _ = harmonic X ^ (r + 1) := by rw [pow_succ]



 def tauSummatory (r X : ℕ) : ℕ :=
  ∑ n ∈ Finset.Ioc 0 X, tauAF r n

 theorem tauSummatory_succ_cast_le (r X : ℕ) :
    (tauSummatory (r + 1) X : ℚ) ≤ (X : ℚ) * harmonic X ^ r := by
  unfold tauSummatory
  calc
    ((∑ n ∈ Finset.Ioc 0 X, tauAF (r + 1) n : ℕ) : ℚ) =
        ∑ n ∈ Finset.Ioc 0 X, tauRat (r + 1) n := by
      simp [tauRat]
    _ = ∑ n ∈ Finset.Ioc 0 X,
        (tauRat r * (ζ : ArithmeticFunction ℚ)) n := by rw [tauRat_succ]
    _ = ∑ n ∈ Finset.Ioc 0 X, tauRat r n * (X / n : ℕ) := by
      rw [ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum]
    _ ≤ ∑ n ∈ Finset.Ioc 0 X,
        reciprocalTwist (tauRat r) n * X := by
      apply Finset.sum_le_sum
      intro n hn
      have hnpos : 0 < n := by simp only [Finset.mem_Ioc] at hn; omega
      have hfloor : ((X / n : ℕ) : ℚ) ≤ (X : ℚ) / (n : ℚ) := by
        apply (le_div_iff₀ (by exact_mod_cast hnpos)).2
        norm_cast
        exact Nat.div_mul_le_self X n
      rw [reciprocalTwist_apply, if_neg hnpos.ne']
      change (tauAF r n : ℚ) * (X / n : ℕ) ≤
        ((tauAF r n : ℚ) / (n : ℚ)) * (X : ℚ)
      calc
        (tauAF r n : ℚ) * (X / n : ℕ) ≤
            (tauAF r n : ℚ) * ((X : ℚ) / (n : ℚ)) :=
          mul_le_mul_of_nonneg_left hfloor (Nat.cast_nonneg _)
        _ = ((tauAF r n : ℚ) / (n : ℚ)) * (X : ℚ) := by ring
    _ = weightedTauSum r X * X := by
      unfold weightedTauSum
      rw [Finset.sum_mul]
    _ ≤ harmonic X ^ r * X :=
      mul_le_mul_of_nonneg_right (weightedTauSum_le_harmonic_pow r X)
        (Nat.cast_nonneg _)
    _ = (X : ℚ) * harmonic X ^ r := by ring

 theorem zeroSecondMoment_cast_le_harmonic (k X : ℕ) (hk : 1 ≤ k) :
    (zeroSecondMoment k X : ℚ) ≤ (X : ℚ) * harmonic X ^ (k * k - 1) := by
  unfold zeroSecondMoment
  have hset : Finset.Icc 1 X = Finset.Ioc 0 X := by ext n; simp; omega
  rw [hset]
  calc
    ((∑ s ∈ Finset.Ioc 0 X, tauAF k s ^ 2 : ℕ) : ℚ) ≤
        (∑ s ∈ Finset.Ioc 0 X, tauAF (k * k) s : ℕ) := by
      exact_mod_cast Finset.sum_le_sum (fun s hs => tauAF_sq_le_tauAF_mul k s)
    _ = (tauSummatory (k * k) X : ℚ) := by rfl
    _ ≤ (X : ℚ) * harmonic X ^ (k * k - 1) := by
      have hkkpos : 0 < k * k := Nat.mul_pos (by omega) (by omega)
      have hkk : k * k = (k * k - 1) + 1 := by omega
      rw [hkk]
      exact tauSummatory_succ_cast_le (k * k - 1) X



/-- The fixed coprime zero fiber is fully bounded using only the one-variable
fixed-order divisor-square moment proved above. -/
theorem zeroFiber_tauMass_cast_le_harmonic
    (k N a b : ℕ) (hk : 1 ≤ k) (hab : a.Coprime b)
    (ha : 0 < a) (hb : 0 < b) :
    (fiberMass (fun n₁ n₂ => tauAF k n₁ * tauAF k n₂)
        (zeroFiber N a b) : ℚ) ≤
      ((tauAF k b * tauAF k a : ℕ) : ℚ) *
        (min ((2 * N) / a) ((2 * N) / b) : ℕ) *
          harmonic (min ((2 * N) / a) ((2 * N) / b)) ^ (k * k - 1) := by
  let R := min ((2 * N) / a) ((2 * N) / b)
  calc
    (fiberMass (fun n₁ n₂ => tauAF k n₁ * tauAF k n₂)
        (zeroFiber N a b) : ℚ) ≤
        (((tauAF k b * tauAF k a) * zeroSecondMoment k R : ℕ) : ℚ) := by
      exact_mod_cast zeroFiber_tauMass_le_secondMoment k N a b hab ha hb
    _ = ((tauAF k b * tauAF k a : ℕ) : ℚ) *
        (zeroSecondMoment k R : ℚ) := by push_cast; ring
    _ ≤ ((tauAF k b * tauAF k a : ℕ) : ℚ) *
        ((R : ℚ) * harmonic R ^ (k * k - 1)) := by
      apply mul_le_mul_of_nonneg_left
      · exact zeroSecondMoment_cast_le_harmonic k R hk
      · positivity
    _ = _ := by dsimp [R]; ring

/-- Paper-normalized fixed-fiber estimate.  The dyadic condition `M < d*a`
turns the exact parameter length into `2*N*d/M`; no modulus, `q`, or `U`
factor is introduced. -/
theorem zeroFiber_tauMass_paper_normalized
    (k M N d a b : ℕ) (hk : 1 ≤ k) (hM : 0 < M)
    (_hd : 0 < d) (hab : a.Coprime b) (ha : 0 < a) (hb : 0 < b)
    (hshortA : d * a ∈ dyadic M) :
    (fiberMass (fun n₁ n₂ => tauAF k n₁ * tauAF k n₂)
        (zeroFiber N a b) : ℚ) ≤
      ((tauAF k b * tauAF k a : ℕ) : ℚ) *
        (((2 * N * d : ℕ) : ℚ) / (M : ℚ)) *
          harmonic (2 * N) ^ (k * k - 1) := by
  let R := min ((2 * N) / a) ((2 * N) / b)
  have hRle : R ≤ (2 * N) / a := min_le_left _ _
  have hshortLower : M < d * a := by
    have hs := hshortA
    simp only [dyadic, Finset.mem_Ioc] at hs
    exact hs.1
  have hRM : R * M ≤ 2 * N * d := by
    calc
      R * M ≤ R * (d * a) := Nat.mul_le_mul_left R hshortLower.le
      _ = (R * a) * d := by ring
      _ ≤ (2 * N) * d := by
        apply Nat.mul_le_mul_right d
        exact (Nat.le_div_iff_mul_le ha).mp hRle
  have hRrat : (R : ℚ) ≤ ((2 * N * d : ℕ) : ℚ) / (M : ℚ) := by
    apply (le_div_iff₀ (by exact_mod_cast hM)).2
    exact_mod_cast hRM
  have hR2N : R ≤ 2 * N :=
    hRle.trans (Nat.div_le_self (2 * N) a)
  have hH : harmonic R ^ (k * k - 1) ≤ harmonic (2 * N) ^ (k * k - 1) :=
    pow_le_pow_left₀ (by
      have hz := harmonic_mono (x := 0) (y := R) (Nat.zero_le R)
      simpa using hz) (harmonic_mono hR2N) _
  calc
    (fiberMass (fun n₁ n₂ => tauAF k n₁ * tauAF k n₂)
        (zeroFiber N a b) : ℚ) ≤
      ((tauAF k b * tauAF k a : ℕ) : ℚ) *
        (R : ℚ) * harmonic R ^ (k * k - 1) := by
          simpa [R, mul_assoc] using
            zeroFiber_tauMass_cast_le_harmonic k N a b hk hab ha hb
    _ ≤ ((tauAF k b * tauAF k a : ℕ) : ℚ) *
        (((2 * N * d : ℕ) : ℚ) / (M : ℚ)) *
          harmonic (2 * N) ^ (k * k - 1) := by
      have hHnonneg : 0 ≤ harmonic R ^ (k * k - 1) := by
        have hz := harmonic_mono (x := 0) (y := R) (Nat.zero_le R)
        have : (0 : ℚ) ≤ harmonic R := by simpa using hz
        positivity
      calc
        ((tauAF k b * tauAF k a : ℕ) : ℚ) *
            (R : ℚ) * harmonic R ^ (k * k - 1) ≤
            ((tauAF k b * tauAF k a : ℕ) : ℚ) *
              (((2 * N * d : ℕ) : ℚ) / (M : ℚ)) *
                harmonic R ^ (k * k - 1) := by
          gcongr
        _ ≤ _ := by gcongr

end MAPMixedMeanZeroClose

#print axioms MAPMixedMeanZeroClose.multichoose_sq_le
#print axioms MAPMixedMeanZeroClose.tauAF_sq_le_tauAF_mul
#print axioms MAPMixedMeanZeroClose.weightedTauSum_le_harmonic_pow
#print axioms MAPMixedMeanZeroClose.zeroSecondMoment_cast_le_harmonic
#print axioms MAPMixedMeanZeroClose.zeroFiber_tauMass_cast_le_harmonic
#print axioms MAPMixedMeanZeroClose.zeroFiber_tauMass_paper_normalized
