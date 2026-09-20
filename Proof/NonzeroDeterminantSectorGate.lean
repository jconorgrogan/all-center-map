import ShiuSieveSlice
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.NumberTheory.Harmonic.Bounds
import ShiuQuotientRanges
import FloorTightCollars
import NormalizedCoefficientWrapper
import MixedMeanMajorantWeld
import ZeroSectorFiniteWeld

/-!
# Positive and negative nonzero determinant sector gate

This module reindexes the literal Fourier survivor sectors into the exact
gcd-reduced determinant fibers to which the Shiu interface applies.  It proves
the complete finite set and weight reductions for both signs.  It does not
assert the still-missing uniform progression estimate.
-/

namespace MAPNonzeroSectorGate

open ArithmeticFunction MixedMellinCert DeterminantCountWeld ShiuFoundation
  MixedMeanFrontend MAPMixedMean MAPMixedMeanFloor MAPMixedMeanZeroClose
  MixedMeanMajorantWeld MAPShiuSpecialization
open scoped ArithmeticFunction.zeta BigOperators

noncomputable section

set_option maxHeartbeats 800000

/-- The literal positive Fourier survivors lie in the floor-tight positive
arithmetic determinant sector. -/
theorem positiveFrequencySector_subset_positiveSector
    (M N : ℕ) {T U : ℝ} (hT : 0 < T) (hU : 0 < U) :
    positiveFrequencySector M N (Real.pi / (2 * U))
        (Real.pi / (2 * T)) ⊆
      positiveSector M N (shortFloorCollar M U)
        (productFloorCollar M N T) := by
  intro q hq
  have hqData := Finset.mem_filter.mp hq
  have hqExact : q ∈ exactFrequencySurvivors M N T U := hqData.1
  have hcollar := exactFrequencySurvivor_mem_floorCollars hT hU hqExact
  have hbox := (Finset.mem_filter.mp hqExact).1
  exact Finset.mem_filter.mpr ⟨
    Finset.mem_filter.mpr ⟨hbox, hqData.2.1, hcollar.1,
      by simpa [determinant_natAbs_eq_product_dist] using hcollar.2⟩,
    hqData.2.2⟩

/-- The literal negative Fourier survivors lie in the corresponding
floor-tight negative arithmetic determinant sector. -/
theorem negativeFrequencySector_subset_negativeSector
    (M N : ℕ) {T U : ℝ} (hT : 0 < T) (hU : 0 < U) :
    negativeFrequencySector M N (Real.pi / (2 * U))
        (Real.pi / (2 * T)) ⊆
      negativeSector M N (shortFloorCollar M U)
        (productFloorCollar M N T) := by
  intro q hq
  have hqData := Finset.mem_filter.mp hq
  have hqExact : q ∈ exactFrequencySurvivors M N T U := hqData.1
  have hcollar := exactFrequencySurvivor_mem_floorCollars hT hU hqExact
  have hbox := (Finset.mem_filter.mp hqExact).1
  exact Finset.mem_filter.mpr ⟨
    Finset.mem_filter.mpr ⟨hbox, hqData.2.1, hcollar.1,
      by simpa [determinant_natAbs_eq_product_dist] using hcollar.2⟩,
    hqData.2.2⟩

/-- The real frontend weight is exactly the cast of the natural literal mass. -/
theorem weightedMass_tauTupleWeight_eq_literalTauMass
    (k : ℕ) (s : Finset LiteralTuple) :
    weightedMass (tauTupleWeight k) s = (literalTauMass k s : ℝ) := by
  unfold weightedMass tauTupleWeight literalTauMass
  push_cast
  rfl

/-- Monotonicity of the nonnegative literal divisor weight. -/
theorem literalTauMass_mono {k : ℕ} {s t : Finset LiteralTuple}
    (hst : s ⊆ t) : literalTauMass k s ≤ literalTauMass k t :=
  Finset.sum_le_sum_of_subset hst

/-- The positive exact-survivor mass is bounded by the floor-tight arithmetic
positive sector without changing its pointwise weight. -/
theorem positiveFrequency_tauMass_le_positiveSector
    (k M N : ℕ) {T U : ℝ} (hT : 0 < T) (hU : 0 < U) :
    weightedMass (tauTupleWeight k)
        (positiveFrequencySector M N (Real.pi / (2 * U))
          (Real.pi / (2 * T))) ≤
      (literalTauMass k
        (positiveSector M N (shortFloorCollar M U)
          (productFloorCollar M N T)) : ℝ) := by
  rw [weightedMass_tauTupleWeight_eq_literalTauMass]
  exact_mod_cast literalTauMass_mono
    (positiveFrequencySector_subset_positiveSector M N hT hU)

/-- The negative exact-survivor mass obeys the identical floor-tight
arithmetic reduction. -/
theorem negativeFrequency_tauMass_le_negativeSector
    (k M N : ℕ) {T U : ℝ} (hT : 0 < T) (hU : 0 < U) :
    weightedMass (tauTupleWeight k)
        (negativeFrequencySector M N (Real.pi / (2 * U))
          (Real.pi / (2 * T))) ≤
      (literalTauMass k
        (negativeSector M N (shortFloorCollar M U)
          (productFloorCollar M N T)) : ℝ) := by
  rw [weightedMass_tauTupleWeight_eq_literalTauMass]
  exact_mod_cast literalTauMass_mono
    (negativeFrequencySector_subset_negativeSector M N hT hU)

/-! ## Exact gcd reindexing of the positive arithmetic sector -/

/-- A fixed reduced short-pair slice of the positive determinant sector. -/
def fixedPositiveLiteralSlice (M N K Y d a b : ℕ) : Finset LiteralTuple :=
  (literalTuples M N K Y).filter fun t =>
    t.1 = (d * a, d * b) ∧ 0 < determinant t

/-- Union of the fixed positive slices over their unique gcd content and
coprime reduced short pair. -/
def reducedPositiveSliceUnion (M N K Y : ℕ) : Finset LiteralTuple :=
  (Finset.Icc 1 K).biUnion fun d =>
    (reducedShortPairs M K d).biUnion fun p =>
      fixedPositiveLiteralSlice M N K Y d p.1 p.2

/-- Every positive arithmetic tuple has one gcd-reduced short representation;
conversely every displayed slice is literally positive. -/
theorem positiveSector_eq_reducedPositiveSliceUnion (M N K Y : ℕ) :
    positiveSector M N K Y = reducedPositiveSliceUnion M N K Y := by
  classical
  ext t
  constructor
  · intro ht
    have ht' := Finset.mem_filter.mp ht
    have hlit := ht'.1
    have hdet := ht'.2
    have hlit' := Finset.mem_filter.mp hlit
    rcases hlit'.2 with ⟨hshortNe, hshortK, hdetY⟩
    obtain ⟨hshortBox, hlongBox⟩ := Finset.mem_product.mp hlit'.1
    obtain ⟨hm1, hm2⟩ := Finset.mem_product.mp hshortBox
    let m1 := t.1.1
    let m2 := t.1.2
    let d := m1.gcd m2
    let a := m1 / d
    let b := m2 / d
    have hm1bounds : M < m1 ∧ m1 ≤ 2 * M := by
      simpa only [m1, dyadic, Finset.mem_Ioc] using hm1
    have hm2bounds : M < m2 ∧ m2 ≤ 2 * M := by
      simpa only [m2, dyadic, Finset.mem_Ioc] using hm2
    have hm1pos : 0 < m1 := (Nat.zero_le M).trans_lt hm1bounds.1
    have hm2pos : 0 < m2 := (Nat.zero_le M).trans_lt hm2bounds.1
    have hd : 0 < d := Nat.gcd_pos_of_pos_left m2 hm1pos
    have hda : d * a = m1 :=
      Nat.mul_div_cancel' (Nat.gcd_dvd_left m1 m2)
    have hdb : d * b = m2 :=
      Nat.mul_div_cancel' (Nat.gcd_dvd_right m1 m2)
    have ha : 0 < a := Nat.div_pos (Nat.gcd_le_left m2 hm1pos) hd
    have hb : 0 < b := Nat.div_pos (Nat.gcd_le_right m1 hm2pos) hd
    have hab : a.Coprime b := Nat.coprime_div_gcd_div_gcd hd
    have habne : a ≠ b := by
      intro heq
      apply hshortNe
      change m1 = m2
      rw [← hda, ← hdb, heq]
    have hdist : d * a.dist b ≤ K := by
      rw [← Nat.dist_mul_left, hda, hdb]
      exact hshortK
    have hdK : d ≤ K := by
      have hdistpos : 0 < a.dist b := Nat.dist_pos_of_ne habne
      exact (Nat.le_mul_of_pos_right d hdistpos).trans hdist
    have haRange : a ∈ positiveRange ((2 * M) / d) := by
      simp only [positiveRange, Finset.mem_Icc]
      exact ⟨ha, Nat.div_le_div_right hm1bounds.2⟩
    have hbRange : b ∈ positiveRange ((2 * M) / d) := by
      simp only [positiveRange, Finset.mem_Icc]
      exact ⟨hb, Nat.div_le_div_right hm2bounds.2⟩
    have hp : (a, b) ∈ reducedShortPairs M K d := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨haRange, hbRange⟩, ?_⟩
      exact ⟨by rw [hda]; exact hm1, by rw [hdb]; exact hm2,
        habne, hab, hdist⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨d, Finset.mem_Icc.mpr ⟨hd, hdK⟩, ?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨(a, b), hp, ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨hlit, ?_, hdet⟩
    change t.1 = (d * a, d * b)
    apply Prod.ext
    · exact hda.symm
    · exact hdb.symm
  · intro ht
    obtain ⟨d, hd, htd⟩ := Finset.mem_biUnion.mp ht
    obtain ⟨p, hp, htp⟩ := Finset.mem_biUnion.mp htd
    have htp' := Finset.mem_filter.mp htp
    exact Finset.mem_filter.mpr ⟨htp'.1, htp'.2.2⟩

/-- The symmetric long-coordinate divisor weight is invariant under the
literal sign-changing tuple involution. -/
theorem literalTauMass_positiveSector_eq_negativeSector
    (k M N K Y : ℕ) :
    literalTauMass k (positiveSector M N K Y) =
      literalTauMass k (negativeSector M N K Y) := by
  classical
  unfold literalTauMass
  rw [← image_swap_positiveSector M N K Y]
  rw [Finset.sum_image swapTuple_injective.injOn]
  apply Finset.sum_congr rfl
  intro t ht
  simp [swapTuple, mul_comm]

/-- The exact union of positive determinant equations allowed by the product
collar for one reduced short pair. -/
def positiveEquationFiberUnion (N Y d a b : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 (Y / d)).biUnion fun ell =>
    positiveEquationFiber N a b ell

/-- Projection of a fixed positive literal slice is exactly the union of its
positive reduced determinant fibers, including the floor endpoint `Y / d`. -/
theorem image_fixedPositiveLiteralSlice_eq_positiveEquationFiberUnion
    (M N K Y d a b : ℕ) (hd : 0 < d)
    (hshortBox : (d * a, d * b) ∈ (dyadic M).product (dyadic M))
    (hshortNe : d * a ≠ d * b)
    (hshortK : (d * a).dist (d * b) ≤ K) :
    (fixedPositiveLiteralSlice M N K Y d a b).image Prod.snd =
      positiveEquationFiberUnion N Y d a b := by
  classical
  ext n
  constructor
  · intro hn
    obtain ⟨t, ht, htn⟩ := Finset.mem_image.mp hn
    have ht' := Finset.mem_filter.mp ht
    have hlit := Finset.mem_filter.mp ht'.1
    have htshort := ht'.2.1
    have hdetpos := ht'.2.2
    have hteq : t = ((d * a, d * b), n) := Prod.ext htshort htn
    subst t
    obtain ⟨hbox, hshortNe', hshortK', hdetY⟩ := hlit
    have hnbox := (Finset.mem_product.mp hbox).2
    have hcollar :
        (d * a * n.1).dist (d * b * n.2) ≠ 0 ∧
          (d * a * n.1).dist (d * b * n.2) ≤ Y := by
      rw [← determinant_natAbs_eq_product_dist
        (((d * a, d * b), n) : LiteralTuple)]
      exact ⟨Int.natAbs_ne_zero.mpr hdetpos.ne', hdetY⟩
    obtain ⟨ell, hell, hpos | hneg⟩ :=
      (reduced_collar_iff_sign_equations hd).1 hcollar
    · exact Finset.mem_biUnion.mpr ⟨ell, hell,
        Finset.mem_filter.mpr ⟨hnbox, hpos⟩⟩
    · exfalso
      have hellData := Finset.mem_Icc.mp hell
      have hnegZ : (b : ℤ) * n.2 = ell + (a : ℤ) * n.1 := by
        exact_mod_cast hneg
      have hdZ : (0 : ℤ) < d := by exact_mod_cast hd
      have hellZ : (0 : ℤ) < ell := by exact_mod_cast hellData.1
      have hdetneg : determinant (((d * a, d * b), n) : LiteralTuple) < 0 := by
        calc
          determinant (((d * a, d * b), n) : LiteralTuple) =
              (d : ℤ) * ((a : ℤ) * n.1 - (b : ℤ) * n.2) := by
            unfold determinant
            push_cast
            ring
          _ = -(d : ℤ) * ell := by rw [hnegZ]; ring
          _ < 0 := mul_neg_of_neg_of_pos (neg_neg_of_pos hdZ) hellZ
      omega
  · intro hn
    obtain ⟨ell, hell, hnell⟩ := Finset.mem_biUnion.mp hn
    have hnell' := Finset.mem_filter.mp hnell
    have hcollar := (reduced_collar_iff_sign_equations hd).2
      ⟨ell, hell, Or.inl hnell'.2⟩
    have hellData := Finset.mem_Icc.mp hell
    have hposZ : (a : ℤ) * n.1 = ell + (b : ℤ) * n.2 := by
      exact_mod_cast hnell'.2
    have hdZ : (0 : ℤ) < d := by exact_mod_cast hd
    have hellZ : (0 : ℤ) < ell := by exact_mod_cast hellData.1
    have hdetpos :
        0 < determinant (((d * a, d * b), n) : LiteralTuple) := by
      calc
        (0 : ℤ) < (d : ℤ) * ell := mul_pos hdZ hellZ
        _ = determinant (((d * a, d * b), n) : LiteralTuple) := by
          unfold determinant
          push_cast
          calc
            (d : ℤ) * ell =
                (d : ℤ) * ((a : ℤ) * n.1 - (b : ℤ) * n.2) := by
              rw [hposZ]
              ring
            _ = (d : ℤ) * (a : ℤ) * n.1 -
                (d : ℤ) * (b : ℤ) * n.2 := by ring
    apply Finset.mem_image.mpr
    refine ⟨(((d * a, d * b), n) : LiteralTuple), ?_, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨
      Finset.mem_product.mpr ⟨hshortBox, hnell'.1⟩,
      hshortNe, hshortK, ?_⟩, rfl, hdetpos⟩
    rw [determinant_natAbs_eq_product_dist]
    exact hcollar.2

/-- On a fixed short pair, the long-coordinate projection loses no tuple
information. -/
theorem fixedPositiveLiteralSlice_snd_injOn
    {M N K Y d a b : ℕ} :
    Set.InjOn Prod.snd
      (fixedPositiveLiteralSlice M N K Y d a b : Set LiteralTuple) := by
  intro x hx y hy hxy
  change x ∈ fixedPositiveLiteralSlice M N K Y d a b at hx
  change y ∈ fixedPositiveLiteralSlice M N K Y d a b at hy
  have hxshort := (Finset.mem_filter.mp hx).2.1
  have hyshort := (Finset.mem_filter.mp hy).2.1
  apply Prod.ext
  · exact hxshort.trans hyshort.symm
  · exact hxy

/-- Exact preservation of the divisor-square mass under the fixed-slice
projection to the union of positive determinant equations. -/
theorem fixedPositiveLiteralSlice_tauMass_eq_fiberUnion
    (k M N K Y d a b : ℕ) (hd : 0 < d)
    (hshortBox : (d * a, d * b) ∈ (dyadic M).product (dyadic M))
    (hshortNe : d * a ≠ d * b)
    (hshortK : (d * a).dist (d * b) ≤ K) :
    literalTauMass k (fixedPositiveLiteralSlice M N K Y d a b) =
      fiberMass (fun n₁ n₂ => tauAF k n₁ * tauAF k n₂)
        (positiveEquationFiberUnion N Y d a b) := by
  classical
  unfold literalTauMass fiberMass
  rw [← image_fixedPositiveLiteralSlice_eq_positiveEquationFiberUnion
    M N K Y d a b hd hshortBox hshortNe hshortK]
  rw [Finset.sum_image fixedPositiveLiteralSlice_snd_injOn]

/-- Removing overlaps between determinant equations can only increase the
nonnegative mass. -/
theorem positiveEquationFiberUnion_tauMass_le_sum
    (k N Y d a b : ℕ) :
    fiberMass (fun n₁ n₂ => tauAF k n₁ * tauAF k n₂)
        (positiveEquationFiberUnion N Y d a b) ≤
      ∑ ell ∈ Finset.Icc 1 (Y / d),
        fiberMass (fun n₁ n₂ => tauAF k n₁ * tauAF k n₂)
          (positiveEquationFiber N a b ell) := by
  unfold fiberMass positiveEquationFiberUnion
  exact sum_biUnion_le_sum _ _ _

/-- Complete unconditional finite aggregation of the positive arithmetic
sector into the literal positive determinant-equation fibers. -/
theorem positiveSector_tauMass_le_tripleFiberSum (k M N K Y : ℕ) :
    literalTauMass k (positiveSector M N K Y) ≤
      ∑ d ∈ Finset.Icc 1 K, ∑ p ∈ reducedShortPairs M K d,
        ∑ ell ∈ Finset.Icc 1 (Y / d),
          fiberMass (fun n₁ n₂ => tauAF k n₁ * tauAF k n₂)
            (positiveEquationFiber N p.1 p.2 ell) := by
  classical
  rw [positiveSector_eq_reducedPositiveSliceUnion]
  unfold reducedPositiveSliceUnion literalTauMass
  calc
    (∑ t ∈ (Finset.Icc 1 K).biUnion fun d =>
        (reducedShortPairs M K d).biUnion fun p =>
          fixedPositiveLiteralSlice M N K Y d p.1 p.2,
        tauAF k t.2.1 * tauAF k t.2.2) ≤
      ∑ d ∈ Finset.Icc 1 K,
        ∑ t ∈ (reducedShortPairs M K d).biUnion fun p =>
          fixedPositiveLiteralSlice M N K Y d p.1 p.2,
          tauAF k t.2.1 * tauAF k t.2.2 :=
      sum_biUnion_le_sum _ _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 K, ∑ p ∈ reducedShortPairs M K d,
        literalTauMass k (fixedPositiveLiteralSlice M N K Y d p.1 p.2) := by
      apply Finset.sum_le_sum
      intro d hdmem
      exact sum_biUnion_le_sum _ _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 K, ∑ p ∈ reducedShortPairs M K d,
        ∑ ell ∈ Finset.Icc 1 (Y / d),
          fiberMass (fun n₁ n₂ => tauAF k n₁ * tauAF k n₂)
            (positiveEquationFiber N p.1 p.2 ell) := by
      apply Finset.sum_le_sum
      intro d hdmem
      apply Finset.sum_le_sum
      intro p hp
      have hd : 0 < d := by
        simp only [Finset.mem_Icc] at hdmem
        omega
      have hpData := Finset.mem_filter.mp hp
      rcases hpData.2 with ⟨hpa, hpb, hpne, hpcoprime, hpdist⟩
      have hscaledNe : d * p.1 ≠ d * p.2 := by
        intro heq
        exact hpne (Nat.eq_of_mul_eq_mul_left hd heq)
      have hscaledDist : (d * p.1).dist (d * p.2) ≤ K := by
        simpa [Nat.dist_mul_left] using hpdist
      rw [fixedPositiveLiteralSlice_tauMass_eq_fiberUnion
        k M N K Y d p.1 p.2 hd
        (Finset.mem_product.mpr ⟨hpa, hpb⟩) hscaledNe hscaledDist]
      exact positiveEquationFiberUnion_tauMass_le_sum
        k N Y d p.1 p.2

/-- The negative arithmetic sector has exactly the same total divisor weight,
so the positive-fiber aggregation handles the second determinant sign without
changing a normalization or logarithmic factor. -/
theorem negativeSector_tauMass_le_tripleFiberSum (k M N K Y : ℕ) :
    literalTauMass k (negativeSector M N K Y) ≤
      ∑ d ∈ Finset.Icc 1 K, ∑ p ∈ reducedShortPairs M K d,
        ∑ ell ∈ Finset.Icc 1 (Y / d),
          fiberMass (fun n₁ n₂ => tauAF k n₁ * tauAF k n₂)
            (positiveEquationFiber N p.1 p.2 ell) := by
  rw [← literalTauMass_positiveSector_eq_negativeSector]
  exact positiveSector_tauMass_le_tripleFiberSum k M N K Y

/-! ## The exact quotient geometry used after Cauchy -/

/-- The two quotient lengths divided by their primitive moduli have the
paper's `(N*d/M)^2` scale.  The additive one is only the exact natural-number
ceiling; it is not an exceptional-fiber hypothesis. -/
theorem quotientLength_product_le_scale_sq_mul_moduli
    (M N d a b D₁ D₂ : ℕ) (hM : 0 < M) (hd : 0 < d)
    (hDa : D₂ ∣ a) (hDb : D₁ ∣ b)
    (hD₁ : 0 < D₁) (hD₂ : 0 < D₂)
    (haLower : M < d * a) (hbLower : M < d * b) :
    quotientLength N D₁ * quotientLength N D₂ ≤
      (2 * (N * d / M + 1)) ^ 2 * ((b / D₁) * (a / D₂)) := by
  let H := N * d / M + 1
  have hceil : N * d ≤ H * M := by
    have hlt := Nat.lt_mul_div_succ (N * d) hM
    dsimp [H]
    simpa [mul_comm] using hlt.le
  have hMab : M ^ 2 ≤ d ^ 2 * (a * b) := by
    have hprod : M * M ≤ (d * a) * (d * b) :=
      Nat.mul_le_mul haLower.le hbLower.le
    calc
      M ^ 2 = M * M := by ring
      _ ≤ (d * a) * (d * b) := hprod
      _ = d ^ 2 * (a * b) := by ring
  have hNab : N ^ 2 ≤ H ^ 2 * (a * b) := by
    have hscaled : d ^ 2 * N ^ 2 ≤ d ^ 2 * (H ^ 2 * (a * b)) := by
      calc
        d ^ 2 * N ^ 2 = (N * d) ^ 2 := by ring
        _ ≤ (H * M) ^ 2 := Nat.pow_le_pow_left hceil 2
        _ = H ^ 2 * M ^ 2 := by ring
        _ ≤ H ^ 2 * (d ^ 2 * (a * b)) :=
          Nat.mul_le_mul_left (H ^ 2) hMab
        _ = d ^ 2 * (H ^ 2 * (a * b)) := by ring
    exact Nat.le_of_mul_le_mul_left hscaled (pow_pos hd 2)
  have hlength₁ : quotientLength N D₁ * D₁ ≤ 2 * N := by
    calc
      quotientLength N D₁ * D₁ ≤ quotientUpper N D₁ * D₁ :=
        Nat.mul_le_mul_right D₁ (quotientLength_le_upper N D₁)
      _ ≤ 2 * N := by
        exact Nat.div_mul_le_self (2 * N) D₁
  have hlength₂ : quotientLength N D₂ * D₂ ≤ 2 * N := by
    calc
      quotientLength N D₂ * D₂ ≤ quotientUpper N D₂ * D₂ :=
        Nat.mul_le_mul_right D₂ (quotientLength_le_upper N D₂)
      _ ≤ 2 * N := by
        exact Nat.div_mul_le_self (2 * N) D₂
  have hprodLengths :
      (D₁ * D₂) * (quotientLength N D₁ * quotientLength N D₂) ≤
        (D₁ * D₂) *
          ((2 * H) ^ 2 * ((b / D₁) * (a / D₂))) := by
    calc
      (D₁ * D₂) *
          (quotientLength N D₁ * quotientLength N D₂) =
        (quotientLength N D₁ * D₁) *
          (quotientLength N D₂ * D₂) := by ring
      _ ≤ (2 * N) * (2 * N) := Nat.mul_le_mul hlength₁ hlength₂
      _ = 4 * N ^ 2 := by ring
      _ ≤ 4 * (H ^ 2 * (a * b)) := Nat.mul_le_mul_left 4 hNab
      _ = (D₁ * D₂) *
          ((2 * H) ^ 2 * ((b / D₁) * (a / D₂))) := by
        have hbEq : D₁ * (b / D₁) = b := Nat.mul_div_cancel' hDb
        have haEq : D₂ * (a / D₂) = a := Nat.mul_div_cancel' hDa
        calc
          4 * (H ^ 2 * (a * b)) =
              4 * H ^ 2 * ((D₁ * (b / D₁)) * (D₂ * (a / D₂))) := by
            rw [hbEq, haEq]
            ring
          _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left hprodLengths (Nat.mul_pos hD₁ hD₂)

/-- On the range where both exact quotient endpoints exceed the fixed Shiu
threshold, the published dyadic target gives the literal positive-fiber
bound used in identity (2.3).  All constants are uniform in the content and
determinant level. -/
theorem dyadicTarget_large_positiveFiber_bound
    (hShiu : DyadicTauSquareShiuTarget) (A k : ℕ) (hA : 0 < A) (hk : 1 ≤ k) :
    ∃ C x₀ : ℕ, 0 < C ∧ 2 ≤ x₀ ∧
      ∀ M N d a b ell : ℕ,
        M ^ 2 ≤ A * N →
        d * a ∈ dyadic M → d * b ∈ dyadic M →
        a.Coprime b → 0 < ell →
        max x₀ (2 * (8 * A) ^ 3 + 2) ≤ quotientUpper N (ell.gcd b) →
        max x₀ (2 * (8 * A) ^ 3 + 2) ≤ quotientUpper N (ell.gcd a) →
        fiberMass (fun n₁ n₂ => tauAF k n₁ * tauAF k n₂)
            (positiveEquationFiber N a b ell) ≤
          2 * C * (N * d / M + 1) *
            (Nat.log 2 (2 * N + 2) + 1) ^ (k * k) *
              tauAF (max 2 (k * k)) (ell.gcd (a * b)) := by
  obtain ⟨C, x₀, hC, hx₀, hbound⟩ := hShiu k hk
  refine ⟨C, x₀, hC, hx₀, ?_⟩
  intro M N d a b ell hscale haBox hbBox hab hell hx₁ hx₂
  have haData := Finset.mem_Ioc.mp haBox
  have hbData := Finset.mem_Ioc.mp hbBox
  have hM : 0 < M := by omega
  have hd : 0 < d := by
    by_contra hd0
    have : d = 0 := Nat.eq_zero_of_not_pos hd0
    subst d
    simp at haData
  have ha : 0 < a := by
    by_contra ha0
    have : a = 0 := Nat.eq_zero_of_not_pos ha0
    subst a
    simp at haData
  have hb : 0 < b := by
    by_contra hb0
    have : b = 0 := Nat.eq_zero_of_not_pos hb0
    subst b
    simp at hbData
  let D₁ := ell.gcd b
  let D₂ := ell.gcd a
  let q₁ := b / D₁
  let q₂ := a / D₂
  let y₁ := quotientLength N D₁
  let y₂ := quotientLength N D₂
  let L := Nat.log 2 (2 * N + 2) + 1
  let R := max 2 (k * k)
  have hD₁ : 0 < D₁ := Nat.gcd_pos_of_pos_right ell hb
  have hD₂ : 0 < D₂ := Nat.gcd_pos_of_pos_right ell ha
  have hD₁b : D₁ ∣ b := Nat.gcd_dvd_right ell b
  have hD₂a : D₂ ∣ a := Nat.gcd_dvd_right ell a
  have hrange₁ := ShiuAnalyticLayer.quotient_shiu_ranges
    A M N d b D₁ hA hd hb hD₁ hscale hbData.2 hD₁b
      (le_trans (Nat.le_max_right _ _) hx₁)
  have hrange₂ := ShiuAnalyticLayer.quotient_shiu_ranges
    A M N d a D₂ hA hd ha hD₂ hscale haData.2 hD₂a
      (le_trans (Nat.le_max_right _ _) hx₂)
  dsimp only at hrange₁ hrange₂
  rcases hrange₁ with ⟨hq₁, hy₁x, hx₁y, hq₁y⟩
  rcases hrange₂ with ⟨hq₂, hy₂x, hx₂y, hq₂y⟩
  by_cases hne : (positiveEquationFiber N a b ell).Nonempty
  · obtain ⟨residue₁, residue₂, hres₁lt, hres₁cop,
        hres₂lt, hres₂cop, hready⟩ :=
      exists_positiveFiber_shiuReady_bound k N a b ell hab ha hb hne
    have hprog₁ := hbound (quotientUpper N D₁) y₁ q₁ residue₁
      (le_trans (Nat.le_max_left _ _) hx₁) hq₁ hres₁lt hres₁cop
      hy₁x hx₁y hq₁y
    have hprog₂ := hbound (quotientUpper N D₂) y₂ q₂ residue₂
      (le_trans (Nat.le_max_left _ _) hx₂) hq₂ hres₂lt hres₂cop
      hy₂x hx₂y hq₂y
    have hxupper₁ : quotientUpper N D₁ ≤ 2 * N := Nat.div_le_self _ _
    have hxupper₂ : quotientUpper N D₂ ≤ 2 * N := Nat.div_le_self _ _
    have hlog₁ : Nat.log 2 (quotientUpper N D₁ + 2) + 1 ≤ L := by
      dsimp [L]
      exact Nat.add_le_add_right (Nat.log_mono_right (Nat.add_le_add_right hxupper₁ 2)) 1
    have hlog₂ : Nat.log 2 (quotientUpper N D₂ + 2) + 1 ≤ L := by
      dsimp [L]
      exact Nat.add_le_add_right (Nat.log_mono_right (Nat.add_le_add_right hxupper₂ 2)) 1
    have hprog₁' : q₁ * progressionSum ((tauAF k).pmul (tauAF k))
          (quotientUpper N D₁) y₁ q₁ residue₁ ≤ C * y₁ * L ^ (k * k) :=
      hprog₁.trans (Nat.mul_le_mul_left (C * y₁)
        (Nat.pow_le_pow_left hlog₁ (k * k)))
    have hprog₂' : q₂ * progressionSum ((tauAF k).pmul (tauAF k))
          (quotientUpper N D₂) y₂ q₂ residue₂ ≤ C * y₂ * L ^ (k * k) :=
      hprog₂.trans (Nat.mul_le_mul_left (C * y₂)
        (Nat.pow_le_pow_left hlog₂ (k * k)))
    have hgeom : y₁ * y₂ ≤
        (2 * (N * d / M + 1)) ^ 2 * (q₁ * q₂) := by
      exact quotientLength_product_le_scale_sq_mul_moduli
        M N d a b D₁ D₂ hM hd hD₂a hD₁b hD₁ hD₂
          haData.1 hbData.1
    have hkR : k ≤ R := by
      dsimp [R]
      have hkk : k ≤ k * k := by
        calc
          k = k * 1 := by simp
          _ ≤ k * k := Nat.mul_le_mul_left k hk
      exact hkk.trans (Nat.le_max_right _ _)
    have hDcop : D₁.Coprime D₂ := by
      exact (Nat.Coprime.coprime_dvd_right hD₂a
        (hab.symm.gcd_left ell))
    have hDprod : D₁ * D₂ = ell.gcd (a * b) := by
      change ell.gcd b * ell.gcd a = ell.gcd (a * b)
      rw [mul_comm]
      exact gcd_mul_gcd_of_coprime hab
    have hcontent : tauAF k D₁ * tauAF k D₂ ≤
        tauAF R (ell.gcd (a * b)) := by
      calc
        tauAF k D₁ * tauAF k D₂ ≤ tauAF R D₁ * tauAF R D₂ :=
          Nat.mul_le_mul (ShiuAnalyticLayer.tauAF_mono_order hkR D₁)
            (ShiuAnalyticLayer.tauAF_mono_order hkR D₂)
        _ = tauAF R (D₁ * D₂) :=
          ((tauAF_isMultiplicative R).map_mul_of_coprime hDcop.gcd_eq_one).symm
        _ = tauAF R (ell.gcd (a * b)) := by rw [hDprod]
    let mass := fiberMass (fun n₁ n₂ => tauAF k n₁ * tauAF k n₂)
      (positiveEquationFiber N a b ell)
    let B := 2 * C * (N * d / M + 1) * L ^ (k * k) *
      tauAF R (ell.gcd (a * b))
    have hsquareWithModuli : (q₁ * q₂) * mass ^ 2 ≤
        (q₁ * q₂) * B ^ 2 := by
      calc
        (q₁ * q₂) * mass ^ 2 ≤
            (q₁ * q₂) *
              ((tauAF k D₁ ^ 2 * tauAF k D₂ ^ 2) *
                (progressionSum ((tauAF k).pmul (tauAF k))
                    (quotientUpper N D₁) y₁ q₁ residue₁ *
                  progressionSum ((tauAF k).pmul (tauAF k))
                    (quotientUpper N D₂) y₂ q₂ residue₂)) :=
          Nat.mul_le_mul_left (q₁ * q₂) hready
        _ = (tauAF k D₁ * tauAF k D₂) ^ 2 *
            ((q₁ * progressionSum ((tauAF k).pmul (tauAF k))
                (quotientUpper N D₁) y₁ q₁ residue₁) *
              (q₂ * progressionSum ((tauAF k).pmul (tauAF k))
                (quotientUpper N D₂) y₂ q₂ residue₂)) := by ring
        _ ≤ (tauAF R (ell.gcd (a * b))) ^ 2 *
            ((C * y₁ * L ^ (k * k)) * (C * y₂ * L ^ (k * k))) :=
          Nat.mul_le_mul (Nat.pow_le_pow_left hcontent 2)
            (Nat.mul_le_mul hprog₁' hprog₂')
        _ ≤ (tauAF R (ell.gcd (a * b))) ^ 2 *
            (C ^ 2 *
              ((2 * (N * d / M + 1)) ^ 2 * (q₁ * q₂)) *
                (L ^ (k * k)) ^ 2) := by
          apply Nat.mul_le_mul_left
          calc
            (C * y₁ * L ^ (k * k)) * (C * y₂ * L ^ (k * k)) =
                C ^ 2 * (y₁ * y₂) * (L ^ (k * k)) ^ 2 := by ring
            _ ≤ C ^ 2 *
                ((2 * (N * d / M + 1)) ^ 2 * (q₁ * q₂)) *
                  (L ^ (k * k)) ^ 2 := by
              exact Nat.mul_le_mul_right ((L ^ (k * k)) ^ 2)
                (Nat.mul_le_mul_left (C ^ 2) hgeom)
        _ = (q₁ * q₂) * B ^ 2 := by
          dsimp [B]
          ring
    have hsquare : mass ^ 2 ≤ B ^ 2 :=
      Nat.le_of_mul_le_mul_left hsquareWithModuli (Nat.mul_pos hq₁ hq₂)
    exact (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp hsquare
  · have hempty : positiveEquationFiber N a b ell = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp [hempty, fiberMass]

/-- The negative determinant sign has the identical large-quotient estimate,
with the two exact contents interchanged by the proved long-coordinate swap. -/
theorem dyadicTarget_large_negativeFiber_bound
    (hShiu : DyadicTauSquareShiuTarget) (A k : ℕ) (hA : 0 < A) (hk : 1 ≤ k) :
    ∃ C x₀ : ℕ, 0 < C ∧ 2 ≤ x₀ ∧
      ∀ M N d a b ell : ℕ,
        M ^ 2 ≤ A * N →
        d * a ∈ dyadic M → d * b ∈ dyadic M →
        a.Coprime b → 0 < ell →
        max x₀ (2 * (8 * A) ^ 3 + 2) ≤ quotientUpper N (ell.gcd b) →
        max x₀ (2 * (8 * A) ^ 3 + 2) ≤ quotientUpper N (ell.gcd a) →
        fiberMass (fun n₁ n₂ => tauAF k n₁ * tauAF k n₂)
            (negativeEquationFiber N a b ell) ≤
          2 * C * (N * d / M + 1) *
            (Nat.log 2 (2 * N + 2) + 1) ^ (k * k) *
              tauAF (max 2 (k * k)) (ell.gcd (a * b)) := by
  obtain ⟨C, x₀, hC, hx₀, hpos⟩ :=
    dyadicTarget_large_positiveFiber_bound hShiu A k hA hk
  refine ⟨C, x₀, hC, hx₀, ?_⟩
  intro M N d a b ell hscale haBox hbBox hab hell hx₁ hx₂
  rw [negativeFiber_tauMass_eq_positiveSwapped]
  simpa [mul_comm] using
    hpos M N d b a ell hscale hbBox haBox hab.symm hell hx₂ hx₁

/-! ## The genuinely finite small-quotient exception -/

/-- If a content quotient is below a fixed threshold, the MAP scale
`M^2 ≤ A*N` forces `N` itself into a finite box.  This is the exceptional
range argument required to remove Shiu's fixed endpoint threshold. -/
theorem small_quotient_implies_N_lt
    (A X M N d b D : ℕ) (hA : 0 < A) (hX : 0 < X)
    (hscale : M ^ 2 ≤ A * N) (hM : 0 < M) (hd : 0 < d)
    (hb : 0 < b) (hDb : D ∣ b) (hD : 0 < D)
    (hshort : d * b ≤ 2 * M)
    (hsmall : quotientUpper N D < X) :
    N < A * X ^ 2 := by
  have hDle : D ≤ b := Nat.le_of_dvd hb hDb
  have hdiv : 2 * N < X * D := by
    exact (Nat.div_lt_iff_lt_mul hD).mp hsmall
  have hNd : N * d < X * M := by
    have htwo : 2 * (N * d) < 2 * (X * M) := by
      calc
        2 * (N * d) = (2 * N) * d := by ring
        _ < (X * D) * d := Nat.mul_lt_mul_of_pos_right hdiv hd
        _ ≤ (X * b) * d := Nat.mul_le_mul_right d (Nat.mul_le_mul_left X hDle)
        _ ≤ 2 * (X * M) := by
          calc
            (X * b) * d = X * (d * b) := by ring
            _ ≤ X * (2 * M) := Nat.mul_le_mul_left X hshort
            _ = 2 * (X * M) := by ring
    exact Nat.lt_of_mul_lt_mul_left htwo
  have hMd : M * d < A * X := by
    have hscaled : M ^ 2 * d < A * X * M := by
      calc
        M ^ 2 * d ≤ (A * N) * d := Nat.mul_le_mul_right d hscale
        _ < A * (X * M) := by
          simpa [mul_assoc] using Nat.mul_lt_mul_of_pos_left hNd hA
        _ = A * X * M := by ring
    have hcancel : M * (M * d) < M * (A * X) := by
      simpa [pow_two, mul_assoc, mul_comm, mul_left_comm] using hscaled
    exact (Nat.mul_lt_mul_left hM).mp hcancel
  have hMbound : M < A * X := by
    exact lt_of_le_of_lt (Nat.le_mul_of_pos_right M hd) hMd
  calc
    N ≤ N * d := Nat.le_mul_of_pos_right N hd
    _ < X * M := hNd
    _ < X * (A * X) := Nat.mul_lt_mul_of_pos_left hMbound hX
    _ = A * X ^ 2 := by ring

/-- An explicit finite mass containing every long pair once `N < B`. -/
def boundedLongPairTauMass (k B : ℕ) : ℕ :=
  fiberMass (fun n₁ n₂ => tauAF k n₁ * tauAF k n₂)
    ((Finset.range (2 * B + 1)).product (Finset.range (2 * B + 1)))

/-- Either small exact quotient endpoint puts either signed determinant fiber
inside one fixed finite mass depending only on `A`, `k`, and the threshold. -/
theorem exceptional_signedFiber_tauMass_le_bounded
    (A X k M N d a b ell : ℕ) (hA : 0 < A) (hX : 0 < X)
    (hscale : M ^ 2 ≤ A * N)
    (haBox : d * a ∈ dyadic M) (hbBox : d * b ∈ dyadic M)
    (hsmall : quotientUpper N (ell.gcd b) < X ∨
      quotientUpper N (ell.gcd a) < X) :
    fiberMass (fun n₁ n₂ => tauAF k n₁ * tauAF k n₂)
          (positiveEquationFiber N a b ell) ≤
        boundedLongPairTauMass k (A * X ^ 2) ∧
      fiberMass (fun n₁ n₂ => tauAF k n₁ * tauAF k n₂)
          (negativeEquationFiber N a b ell) ≤
        boundedLongPairTauMass k (A * X ^ 2) := by
  have haData := Finset.mem_Ioc.mp haBox
  have hbData := Finset.mem_Ioc.mp hbBox
  have hM : 0 < M := by omega
  have hd : 0 < d := by
    by_contra hd0
    have : d = 0 := Nat.eq_zero_of_not_pos hd0
    subst d
    simp at haData
  have ha : 0 < a := by
    by_contra ha0
    have : a = 0 := Nat.eq_zero_of_not_pos ha0
    subst a
    simp at haData
  have hb : 0 < b := by
    by_contra hb0
    have : b = 0 := Nat.eq_zero_of_not_pos hb0
    subst b
    simp at hbData
  have hNbound : N < A * X ^ 2 := by
    rcases hsmall with hsmall₁ | hsmall₂
    · exact small_quotient_implies_N_lt A X M N d b (ell.gcd b)
        hA hX hscale hM hd hb (Nat.gcd_dvd_right ell b)
          (Nat.gcd_pos_of_pos_right ell hb) hbData.2 hsmall₁
    · exact small_quotient_implies_N_lt A X M N d a (ell.gcd a)
        hA hX hscale hM hd ha (Nat.gcd_dvd_right ell a)
          (Nat.gcd_pos_of_pos_right ell ha) haData.2 hsmall₂
  have hsubset (s : Finset (ℕ × ℕ))
      (hs : s ⊆ (dyadic N).product (dyadic N)) :
      fiberMass (fun n₁ n₂ => tauAF k n₁ * tauAF k n₂) s ≤
        boundedLongPairTauMass k (A * X ^ 2) := by
    unfold fiberMass boundedLongPairTauMass
    apply Finset.sum_le_sum_of_subset
    intro n hn
    obtain ⟨hn₁, hn₂⟩ := Finset.mem_product.mp (hs hn)
    apply Finset.mem_product.mpr
    constructor
    · simp only [Finset.mem_range]
      have hn₁upper := (Finset.mem_Ioc.mp hn₁).2
      omega
    · simp only [Finset.mem_range]
      have hn₂upper := (Finset.mem_Ioc.mp hn₂).2
      omega
  constructor
  · apply hsubset
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  · apply hsubset
    intro n hn
    exact (Finset.mem_filter.mp hn).1

/-- Every positive argument has at least one ordered `r`-divisor
factorization once `r ≥ 1`. -/
theorem one_le_tauAF_of_pos (r n : ℕ) (hr : 1 ≤ r) (hn : 0 < n) :
    1 ≤ tauAF r n := by
  have hmono := ShiuAnalyticLayer.tauAF_mono_order hr n
  have hone : tauAF 1 n = 1 := by
    simp [tauAF, hn.ne']
  simpa [hone] using hmono

/-- Full signed determinant-fiber estimate.  Large quotient endpoints use
`DyadicTauSquareShiuTarget`; if either endpoint is small, the scale
`M^2 ≤ A*N` puts the whole fiber in the explicit finite box above.  Thus no
extra progression theorem or exceptional-range premise remains. -/
theorem dyadicTarget_signedFiber_content_bound
    (hShiu : DyadicTauSquareShiuTarget) (A k : ℕ) (hA : 0 < A) (hk : 1 ≤ k) :
    ∃ C : ℕ, 0 < C ∧
      ∀ M N d a b ell : ℕ,
        M ^ 2 ≤ A * N →
        d * a ∈ dyadic M → d * b ∈ dyadic M →
        a.Coprime b → 0 < ell →
        fiberMass (fun n₁ n₂ => tauAF k n₁ * tauAF k n₂)
              (positiveEquationFiber N a b ell) ≤
            2 * C * (N * d / M + 1) *
              (Nat.log 2 (2 * N + 2) + 1) ^ (k * k) *
                tauAF (max 2 (k * k)) (ell.gcd (a * b)) ∧
          fiberMass (fun n₁ n₂ => tauAF k n₁ * tauAF k n₂)
              (negativeEquationFiber N a b ell) ≤
            2 * C * (N * d / M + 1) *
              (Nat.log 2 (2 * N + 2) + 1) ^ (k * k) *
                tauAF (max 2 (k * k)) (ell.gcd (a * b)) := by
  obtain ⟨C, x₀, hC, hx₀, hlarge⟩ :=
    dyadicTarget_large_positiveFiber_bound hShiu A k hA hk
  let X := max x₀ (2 * (8 * A) ^ 3 + 2)
  let E := boundedLongPairTauMass k (A * X ^ 2) + 1
  refine ⟨C + E, by omega, ?_⟩
  intro M N d a b ell hscale haBox hbBox hab hell
  have haData := Finset.mem_Ioc.mp haBox
  have hbData := Finset.mem_Ioc.mp hbBox
  have ha : 0 < a := by
    by_contra ha0
    have : a = 0 := Nat.eq_zero_of_not_pos ha0
    subst a
    simp at haData
  have hb : 0 < b := by
    by_contra hb0
    have : b = 0 := Nat.eq_zero_of_not_pos hb0
    subst b
    simp at hbData
  let R := max 2 (k * k)
  let L := Nat.log 2 (2 * N + 2) + 1
  let S := N * d / M + 1
  let G := tauAF R (ell.gcd (a * b))
  have hR : 1 ≤ R := by dsimp [R]; omega
  have habpos : 0 < a * b := Nat.mul_pos ha hb
  have hgcdpos : 0 < ell.gcd (a * b) := Nat.gcd_pos_of_pos_right ell habpos
  have hG : 1 ≤ G := one_le_tauAF_of_pos R _ hR hgcdpos
  have hL : 1 ≤ L := by dsimp [L]; omega
  have hS : 1 ≤ S := by
    dsimp [S]
    simpa [Nat.succ_eq_add_one] using
      Nat.succ_le_succ (Nat.zero_le (N * d / M))
  have hfactor : 0 < 2 * S * L ^ (k * k) * G := by positivity
  have hExceptional : E ≤ 2 * (C + E) * S * L ^ (k * k) * G := by
    calc
      E ≤ C + E := by omega
      _ ≤ (C + E) * (2 * S * L ^ (k * k) * G) :=
        Nat.le_mul_of_pos_right (C + E) hfactor
      _ = 2 * (C + E) * S * L ^ (k * k) * G := by ring
  have hBoxExceptional :
      boundedLongPairTauMass k (A * X ^ 2) ≤
        2 * (C + E) * S * L ^ (k * k) * G := by
    exact (show boundedLongPairTauMass k (A * X ^ 2) ≤ E by
      dsimp [E]
      omega).trans hExceptional
  by_cases hq₁ : X ≤ quotientUpper N (ell.gcd b)
  · by_cases hq₂ : X ≤ quotientUpper N (ell.gcd a)
    · have hp := hlarge M N d a b ell hscale haBox hbBox hab hell hq₁ hq₂
      have hn := hlarge M N d b a ell hscale hbBox haBox hab.symm hell hq₂ hq₁
      have hIncrease :
          2 * C * S * L ^ (k * k) * G ≤
            2 * (C + E) * S * L ^ (k * k) * G := by
        have hCE : C ≤ C + E := by omega
        simpa [mul_assoc] using Nat.mul_le_mul_right (S * L ^ (k * k) * G)
          (Nat.mul_le_mul_left 2 hCE)
      constructor
      · exact hp.trans (by simpa [S, L, G, R] using hIncrease)
      · rw [negativeFiber_tauMass_eq_positiveSwapped]
        have hn' :
            fiberMass (fun n₁ n₂ => tauAF k n₁ * tauAF k n₂)
                (positiveEquationFiber N b a ell) ≤
              2 * C * S * L ^ (k * k) * G := by
          simpa [S, L, G, R, mul_comm] using hn
        exact hn'.trans hIncrease
    · have hex := exceptional_signedFiber_tauMass_le_bounded
        A X k M N d a b ell hA (by dsimp [X]; omega) hscale haBox hbBox
          (Or.inr (lt_of_not_ge hq₂))
      constructor
      · exact hex.1.trans (by simpa [E, S, L, G, R] using hBoxExceptional)
      · exact hex.2.trans (by simpa [E, S, L, G, R] using hBoxExceptional)
  · have hex := exceptional_signedFiber_tauMass_le_bounded
      A X k M N d a b ell hA (by dsimp [X]; omega) hscale haBox hbBox
        (Or.inl (lt_of_not_ge hq₁))
    constructor
    · exact hex.1.trans (by simpa [E, S, L, G, R] using hBoxExceptional)
    · exact hex.2.trans (by simpa [E, S, L, G, R] using hBoxExceptional)

/-! ## Identity (2.3) and global reduced-pair aggregation -/

/-- The divisor-floor side of identity (2.3) is bounded by the reciprocal
divisor moment already certified in the zero-sector harmonic layer. -/
theorem divisorFloorTau_cast_le_harmonic
    (r Y d q X : ℕ) (hq : 0 < q) (hqX : q ≤ X) :
    ((∑ v ∈ q.divisors, (Y / (d * v)) * tauAF r v : ℕ) : ℚ) ≤
      (Y / d : ℕ) * harmonic X ^ r := by
  have hdivisorSum :
      (∑ v ∈ q.divisors, ((tauAF r v : ℕ) : ℚ) / (v : ℚ)) ≤
        weightedTauSum r X := by
    have hsubset : q.divisors ⊆ Finset.Ioc 0 X := by
      intro v hv
      have hvData := Nat.mem_divisors.mp hv
      simp only [Finset.mem_Ioc]
      exact ⟨Nat.pos_of_dvd_of_pos hvData.1 hq,
        (Nat.le_of_dvd hq hvData.1).trans hqX⟩
    calc
      (∑ v ∈ q.divisors, ((tauAF r v : ℕ) : ℚ) / (v : ℚ)) ≤
          ∑ v ∈ Finset.Ioc 0 X, ((tauAF r v : ℕ) : ℚ) / (v : ℚ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
          intro v hv hnot
          positivity)
      _ = weightedTauSum r X := by
        unfold weightedTauSum
        apply Finset.sum_congr rfl
        intro v hv
        have hvpos : 0 < v := (Finset.mem_Ioc.mp hv).1
        simp [reciprocalTwist, tauRat, hvpos.ne']
  calc
    ((∑ v ∈ q.divisors, (Y / (d * v)) * tauAF r v : ℕ) : ℚ) =
        ∑ v ∈ q.divisors,
          (((Y / d) / v : ℕ) : ℚ) * (tauAF r v : ℚ) := by
      push_cast
      simp only [Nat.div_div_eq_div_mul]
    _ ≤ ∑ v ∈ q.divisors,
        ((Y / d : ℕ) : ℚ) * (((tauAF r v : ℕ) : ℚ) / (v : ℚ)) := by
      apply Finset.sum_le_sum
      intro v hv
      have hvpos : 0 < v := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hv).1 hq
      have hfloor : (((Y / d) / v : ℕ) : ℚ) ≤
          ((Y / d : ℕ) : ℚ) / (v : ℚ) := by
        apply (le_div_iff₀ (by exact_mod_cast hvpos)).2
        norm_cast
        exact Nat.div_mul_le_self (Y / d) v
      calc
        (((Y / d) / v : ℕ) : ℚ) * (tauAF r v : ℚ) ≤
            (((Y / d : ℕ) : ℚ) / (v : ℚ)) * (tauAF r v : ℚ) :=
          mul_le_mul_of_nonneg_right hfloor (by positivity)
        _ = ((Y / d : ℕ) : ℚ) *
            (((tauAF r v : ℕ) : ℚ) / (v : ℚ)) := by ring
    _ = ((Y / d : ℕ) : ℚ) *
        ∑ v ∈ q.divisors, ((tauAF r v : ℕ) : ℚ) / (v : ℚ) := by
      rw [Finset.mul_sum]
    _ ≤ ((Y / d : ℕ) : ℚ) * weightedTauSum r X := by
      exact mul_le_mul_of_nonneg_left hdivisorSum (by positivity)
    _ ≤ ((Y / d : ℕ) : ℚ) * harmonic X ^ r := by
      exact mul_le_mul_of_nonneg_left (weightedTauSum_le_harmonic_pow r X)
        (by positivity)
    _ = _ := by push_cast; rfl

/-- The unweighted number of reduced neighboring short pairs has the exact
`(M/d)(K/d)` geometry. -/
theorem reducedShortPairs_card_cast_le (M K d : ℕ) (hd : 0 < d) :
    ((reducedShortPairs M K d).card : ℚ) ≤
      (2 * (K / d) * ((2 * M) / d) : ℕ) := by
  have hmass := reducedShortPairs_tauMass_cast_le 1 M K d (by omega) hd
  have hsum :
      ∑ p ∈ reducedShortPairs M K d, tauAF 1 p.1 * tauAF 1 p.2 =
        (reducedShortPairs M K d).card := by
    calc
      (∑ p ∈ reducedShortPairs M K d, tauAF 1 p.1 * tauAF 1 p.2) =
          ∑ p ∈ reducedShortPairs M K d, 1 := by
        apply Finset.sum_congr rfl
        intro p hp
        have hpRange := (Finset.mem_filter.mp hp).1
        obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.mp hpRange
        have hp₁pos : 0 < p.1 := (Finset.mem_Icc.mp hp₁).1
        have hp₂pos : 0 < p.2 := (Finset.mem_Icc.mp hp₂).1
        simp [tauAF, hp₁pos.ne', hp₂pos.ne']
      _ = (reducedShortPairs M K d).card := by simp
  rw [hsum] at hmass
  simpa using hmass

/-- Both literal Fourier determinant signs are bounded by twice one and the
same positive-equation fiber sum.  This is the exact global finite gate before
the missing progression estimate. -/
theorem signedFrequency_tauMass_le_two_tripleFiberSum
    (k M N : ℕ) {T U : ℝ} (hT : 0 < T) (hU : 0 < U) :
    weightedMass (tauTupleWeight k)
          (positiveFrequencySector M N (Real.pi / (2 * U))
            (Real.pi / (2 * T))) +
        weightedMass (tauTupleWeight k)
          (negativeFrequencySector M N (Real.pi / (2 * U))
            (Real.pi / (2 * T))) ≤
      2 * ((∑ d ∈ Finset.Icc 1 (shortFloorCollar M U),
        ∑ p ∈ reducedShortPairs M (shortFloorCollar M U) d,
          ∑ ell ∈ Finset.Icc 1 (productFloorCollar M N T / d),
            fiberMass (fun n₁ n₂ => tauAF k n₁ * tauAF k n₂)
              (positiveEquationFiber N p.1 p.2 ell) : ℕ) : ℝ) := by
  let K := shortFloorCollar M U
  let Y := productFloorCollar M N T
  let S := ∑ d ∈ Finset.Icc 1 K, ∑ p ∈ reducedShortPairs M K d,
    ∑ ell ∈ Finset.Icc 1 (Y / d),
      fiberMass (fun n₁ n₂ => tauAF k n₁ * tauAF k n₂)
        (positiveEquationFiber N p.1 p.2 ell)
  have hpos := positiveFrequency_tauMass_le_positiveSector
    k M N hT hU
  have hneg := negativeFrequency_tauMass_le_negativeSector
    k M N hT hU
  have hposNat : literalTauMass k (positiveSector M N K Y) ≤ S := by
    exact positiveSector_tauMass_le_tripleFiberSum k M N K Y
  have hnegNat : literalTauMass k (negativeSector M N K Y) ≤ S := by
    exact negativeSector_tauMass_le_tripleFiberSum k M N K Y
  have hposReal :
      (literalTauMass k (positiveSector M N K Y) : ℝ) ≤ (S : ℝ) := by
    exact_mod_cast hposNat
  have hnegReal :
      (literalTauMass k (negativeSector M N K Y) : ℝ) ≤ (S : ℝ) := by
    exact_mod_cast hnegNat
  change _ ≤ 2 * (S : ℝ)
  calc
    _ ≤ (literalTauMass k (positiveSector M N K Y) : ℝ) +
        (literalTauMass k (negativeSector M N K Y) : ℝ) :=
      add_le_add hpos hneg
    _ ≤ (S : ℝ) + (S : ℝ) := add_le_add hposReal hnegReal
    _ = 2 * (S : ℝ) := by ring

/-- The floor-tight nonzero-sector geometric scale gives exactly the
manuscript `M*N` contribution after multiplication by `T*U/(M*N)`.  The
factor `2*pi^2` records both collar constants literally; no logarithmic factor
is hidden in this algebraic step. -/
theorem normalized_floor_nonzero_scale_le
    (M N : ℕ) {T U : ℝ} (hM : 0 < M) (hN : 0 < N)
    (hT : 0 < T) (hU : 0 < U) :
    (T * U / ((M : ℝ) * (N : ℝ))) *
        ((N : ℝ) * (shortFloorCollar M U : ℝ) *
          (productFloorCollar M N T : ℝ)) ≤
      2 * Real.pi ^ 2 * (M : ℝ) * (N : ℝ) := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hscale : 0 ≤ T * U / ((M : ℝ) * (N : ℝ)) := by positivity
  calc
    (T * U / ((M : ℝ) * (N : ℝ))) *
        ((N : ℝ) * (shortFloorCollar M U : ℝ) *
          (productFloorCollar M N T : ℝ)) ≤
      (T * U / ((M : ℝ) * (N : ℝ))) *
        ((N : ℝ) * (Real.pi * (M : ℝ) / U) *
          (2 * Real.pi * (M : ℝ) * (N : ℝ) / T)) := by
      apply mul_le_mul_of_nonneg_left _ hscale
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (shortFloorCollar_cast_le M hU)
          (by positivity))
        (productFloorCollar_cast_le M N hT) (by positivity) (by positivity)
    _ = 2 * Real.pi ^ 2 * (M : ℝ) * (N : ℝ) := by
      field_simp [ne_of_gt hMr, ne_of_gt hNr, ne_of_gt hT, ne_of_gt hU]

end




/-! ## Global aggregation of the nonzero determinant fibers -/

/-- Reindex the positive integers `1,...,L` by `e ↦ e+1`. -/
theorem sum_Icc_one_eq_sum_range_succ (f : ℕ → ℕ) (L : ℕ) :
    (∑ ell ∈ Finset.Icc 1 L, f ell) =
      ∑ e ∈ Finset.range L, f (e + 1) := by
  classical
  have hset : Finset.Icc 1 L = (Finset.range L).image (fun e => e + 1) := by
    ext ell
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨hell, hellL⟩
      refine ⟨ell - 1, by omega, by omega⟩
    · rintro ⟨e, he, rfl⟩
      omega
  rw [hset, Finset.sum_image]
  intro x hx y hy hxy
  exact Nat.add_right_cancel hxy

/-- A uniform content bound on each determinant fiber sums exactly through
identity (2.3); the gcd weight is never replaced pointwise. -/
theorem positiveFiber_Icc_sum_le_divisorFloor
    (k R N Y d a b B : ℕ) (hR : 1 ≤ R)
    (ha : 0 < a) (hb : 0 < b)
    (hfiber : ∀ ell ∈ Finset.Icc 1 (Y / d),
      fiberMass (fun n₁ n₂ => tauAF k n₁ * tauAF k n₂)
          (positiveEquationFiber N a b ell) ≤
        B * tauAF R (ell.gcd (a * b))) :
    (∑ ell ∈ Finset.Icc 1 (Y / d),
      fiberMass (fun n₁ n₂ => tauAF k n₁ * tauAF k n₂)
        (positiveEquationFiber N a b ell)) ≤
      B * ∑ v ∈ (a * b).divisors,
        (Y / (d * v)) * tauAF (R - 1) v := by
  have hq : a * b ≠ 0 := Nat.mul_ne_zero ha.ne' hb.ne'
  rw [sum_Icc_one_eq_sum_range_succ]
  calc
    (∑ e ∈ Finset.range (Y / d),
      fiberMass (fun n₁ n₂ => tauAF k n₁ * tauAF k n₂)
        (positiveEquationFiber N a b (e + 1))) ≤
      ∑ e ∈ Finset.range (Y / d),
        B * tauAF R ((e + 1).gcd (a * b)) := by
      apply Finset.sum_le_sum
      intro e he
      apply hfiber
      simp only [Finset.mem_Icc, Finset.mem_range] at *
      omega
    _ = B * ∑ e ∈ Finset.range (Y / d),
        tauAF R ((e + 1).gcd (a * b)) := by rw [Finset.mul_sum]
    _ = B * ∑ v ∈ (a * b).divisors,
        ((Y / d) / v) * tauAF (R - 1) v := by
      have hsucc : R - 1 + 1 = R := by omega
      have hid := tau_gcd_sum_exact (R - 1) (Y / d) (a * b) hq
      rw [hsucc] at hid
      exact congrArg (fun z : ℕ => B * z) hid
    _ = B * ∑ v ∈ (a * b).divisors,
        (Y / (d * v)) * tauAF (R - 1) v := by
      simp only [Nat.div_div_eq_div_mul]

/-- The pure floor geometry of the global `d` and reduced-short-pair sum.
The only use of `M² ≤ A N` is to absorb the `+1` in `N*d/M+1` without
losing a factor of `M`. -/
theorem reducedPair_geometric_sum_cast_le
    (A M N K Y : ℕ) (hA : 0 < A) (hM : 0 < M)
    (hscale : M ^ 2 ≤ A * N) :
    ((∑ d ∈ Finset.Icc 1 K,
      (reducedShortPairs M K d).card * (N * d / M + 1) * (Y / d) : ℕ) : ℚ) ≤
      (4 * (A + 1) * N * K * Y : ℕ) * harmonic K := by
  have hMr : (0 : ℚ) < M := by exact_mod_cast hM
  have hscaleQ : (M : ℚ) ^ 2 ≤ (A : ℚ) * N := by exact_mod_cast hscale
  have hconst0 : (0 : ℚ) ≤ (4 * (A + 1) * N * K * Y : ℕ) := by positivity
  calc
    ((∑ d ∈ Finset.Icc 1 K,
      (reducedShortPairs M K d).card * (N * d / M + 1) * (Y / d) : ℕ) : ℚ) =
      ∑ d ∈ Finset.Icc 1 K,
        ((reducedShortPairs M K d).card : ℚ) *
          ((N * d / M + 1 : ℕ) : ℚ) * ((Y / d : ℕ) : ℚ) := by
      push_cast
      rfl
    _ ≤ ∑ d ∈ Finset.Icc 1 K,
        (4 * (A + 1) * N * K * Y : ℕ) * ((d : ℚ)⁻¹) := by
      apply Finset.sum_le_sum
      intro d hdmem
      have hd : 0 < d := (Finset.mem_Icc.mp hdmem).1
      have hdr : (0 : ℚ) < d := by exact_mod_cast hd
      have hcard := reducedShortPairs_card_cast_le M K d hd
      have hKdiv : ((K / d : ℕ) : ℚ) ≤ (K : ℚ) / d := Nat.cast_div_le
      have hMdiv : (((2 * M) / d : ℕ) : ℚ) ≤ (2 * M : ℚ) / d := by
        simpa using (Nat.cast_div_le (α := ℚ) (m := 2 * M) (n := d))
      have hcard' : ((reducedShortPairs M K d).card : ℚ) ≤
          4 * (K : ℚ) * M / (d : ℚ) ^ 2 := by
        calc
          ((reducedShortPairs M K d).card : ℚ) ≤
              (2 * (K / d) * ((2 * M) / d) : ℕ) := hcard
          _ ≤ 2 * ((K : ℚ) / d) * ((2 * M : ℚ) / d) := by
            push_cast
            gcongr
          _ = 4 * (K : ℚ) * M / (d : ℚ) ^ 2 := by field_simp; ring
      have hNdFloor : ((N * d / M : ℕ) : ℚ) ≤
          ((N : ℚ) * d) / M := by
        simpa using (Nat.cast_div_le (α := ℚ) (m := N * d) (n := M))
      have hMleANd : M ≤ A * N * d := by
        calc
          M ≤ M ^ 2 := by nlinarith
          _ ≤ A * N := hscale
          _ ≤ A * N * d := Nat.le_mul_of_pos_right _ hd
      have hone : (1 : ℚ) ≤ ((A : ℚ) * N * d) / M := by
        apply (le_div_iff₀ hMr).2
        norm_num
        exact_mod_cast hMleANd
      have hscaleTerm : ((N * d / M + 1 : ℕ) : ℚ) ≤
          (A + 1 : ℕ) * (N : ℚ) * d / M := by
        calc
          ((N * d / M + 1 : ℕ) : ℚ) =
              ((N * d / M : ℕ) : ℚ) + 1 := by push_cast; rfl
          _ ≤ ((N : ℚ) * d) / M + ((A : ℚ) * N * d) / M :=
            add_le_add hNdFloor hone
          _ = (A + 1 : ℕ) * (N : ℚ) * d / M := by
            simp only [Nat.cast_add, Nat.cast_one]
            ring
      have hYdiv : ((Y / d : ℕ) : ℚ) ≤ (Y : ℚ) / d := by
        simpa using (Nat.cast_div_le (α := ℚ) (m := Y) (n := d))
      calc
        ((reducedShortPairs M K d).card : ℚ) *
              ((N * d / M + 1 : ℕ) : ℚ) * ((Y / d : ℕ) : ℚ) ≤
            (4 * (K : ℚ) * M / (d : ℚ) ^ 2) *
              (((A + 1 : ℕ) : ℚ) * N * d / M) * ((Y : ℚ) / d) := by
          gcongr
        _ = ((4 * (A + 1) * N * K * Y : ℕ) : ℚ) /
              (d : ℚ) ^ 2 := by
          push_cast
          field_simp
        _ ≤ ((4 * (A + 1) * N * K * Y : ℕ) : ℚ) * (d : ℚ)⁻¹ := by
          have hd1 : (1 : ℚ) ≤ d := by exact_mod_cast hd
          have hinv2 : (d : ℚ)⁻¹ ^ 2 ≤ (d : ℚ)⁻¹ := by
            have hi0 : 0 ≤ (d : ℚ)⁻¹ := by positivity
            have hi1 : (d : ℚ)⁻¹ ≤ 1 := (inv_le_one₀ hdr).2 hd1
            nlinarith
          rw [div_eq_mul_inv, ← inv_pow]
          exact mul_le_mul_of_nonneg_left hinv2 hconst0
    _ = (4 * (A + 1) * N * K * Y : ℕ) * harmonic K := by
      push_cast
      rw [harmonic_eq_sum_Icc, Finset.mul_sum]


/-- The complete triple-fiber aggregation at the manuscript geometric scale.
The sole analytic input is `DyadicTauSquareShiuTarget`; every gcd, determinant
level, reduced short pair, floor endpoint, and small-quotient exception is
handled before this theorem. -/
theorem tripleFiberSum_cast_le_geometric_harmonic_of_contentBound
    (A k C M N K Y : ℕ)
    (hA : 0 < A) (hk : 1 ≤ k) (hM : 0 < M)
    (hscale : M ^ 2 ≤ A * N)
    (hfiber : ∀ M N d a b ell : ℕ,
      M ^ 2 ≤ A * N →
      d * a ∈ dyadic M → d * b ∈ dyadic M →
      a.Coprime b → 0 < ell →
      fiberMass (fun n₁ n₂ => tauAF k n₁ * tauAF k n₂)
            (positiveEquationFiber N a b ell) ≤
          2 * C * (N * d / M + 1) *
            (Nat.log 2 (2 * N + 2) + 1) ^ (k * k) *
              tauAF (max 2 (k * k)) (ell.gcd (a * b)) ∧
        fiberMass (fun n₁ n₂ => tauAF k n₁ * tauAF k n₂)
            (negativeEquationFiber N a b ell) ≤
          2 * C * (N * d / M + 1) *
            (Nat.log 2 (2 * N + 2) + 1) ^ (k * k) *
              tauAF (max 2 (k * k)) (ell.gcd (a * b))) :
      ((∑ d ∈ Finset.Icc 1 K,
        ∑ p ∈ reducedShortPairs M K d,
          ∑ ell ∈ Finset.Icc 1 (Y / d),
            fiberMass (fun n₁ n₂ => tauAF k n₁ * tauAF k n₂)
              (positiveEquationFiber N p.1 p.2 ell) : ℕ) : ℚ) ≤
        (8 * C * (A + 1) * N * K * Y : ℕ) *
          (Nat.log 2 (2 * N + 2) + 1 : ℕ) ^ (k * k) *
          harmonic ((2 * M) ^ 2) ^ (max 2 (k * k) - 1) * harmonic K := by
  let R := max 2 (k * k)
  let L := Nat.log 2 (2 * N + 2) + 1
  let H := harmonic ((2 * M) ^ 2) ^ (R - 1)
  have hR : 1 ≤ R := by dsimp [R]; omega
  have hH0 : (0 : ℚ) ≤ H := by
    dsimp [H]
    exact pow_nonneg (by
      have hz := harmonic_mono (x := 0) (y := (2 * M) ^ 2) (Nat.zero_le _)
      simpa using hz) _
  have hGeom := reducedPair_geometric_sum_cast_le A M N K Y hA hM hscale
  calc
    ((∑ d ∈ Finset.Icc 1 K,
        ∑ p ∈ reducedShortPairs M K d,
          ∑ ell ∈ Finset.Icc 1 (Y / d),
            fiberMass (fun n₁ n₂ => tauAF k n₁ * tauAF k n₂)
              (positiveEquationFiber N p.1 p.2 ell) : ℕ) : ℚ) =
      ∑ d ∈ Finset.Icc 1 K,
        ∑ p ∈ reducedShortPairs M K d,
          ((∑ ell ∈ Finset.Icc 1 (Y / d),
            fiberMass (fun n₁ n₂ => tauAF k n₁ * tauAF k n₂)
              (positiveEquationFiber N p.1 p.2 ell) : ℕ) : ℚ) := by
      push_cast
      rfl
    _ ≤ ∑ d ∈ Finset.Icc 1 K,
        ∑ p ∈ reducedShortPairs M K d,
          ((2 * C * (N * d / M + 1) * L ^ (k * k) : ℕ) : ℚ) *
            ((Y / d : ℕ) : ℚ) * H := by
      apply Finset.sum_le_sum
      intro d hdmem
      have hd : 0 < d := (Finset.mem_Icc.mp hdmem).1
      apply Finset.sum_le_sum
      intro p hp
      have hpData := Finset.mem_filter.mp hp
      rcases hpData.2 with ⟨hpaBox, hpbBox, hpne, hpcoprime, hpdist⟩
      have hpaData := Finset.mem_Icc.mp (Finset.mem_product.mp hpData.1).1
      have hpbData := Finset.mem_Icc.mp (Finset.mem_product.mp hpData.1).2
      have hpa : 0 < p.1 := hpaData.1
      have hpb : 0 < p.2 := hpbData.1
      let B := 2 * C * (N * d / M + 1) * L ^ (k * k)
      have hsumNat := positiveFiber_Icc_sum_le_divisorFloor
        k R N Y d p.1 p.2 B hR hpa hpb (by
          intro ell hell
          exact (hfiber M N d p.1 p.2 ell hscale hpaBox hpbBox
            hpcoprime (Finset.mem_Icc.mp hell).1).1)
      have hsumQ :
          (((∑ ell ∈ Finset.Icc 1 (Y / d),
            fiberMass (fun n₁ n₂ => tauAF k n₁ * tauAF k n₂)
              (positiveEquationFiber N p.1 p.2 ell)) : ℕ) : ℚ) ≤
            (B : ℚ) *
              (((∑ v ∈ (p.1 * p.2).divisors,
                (Y / (d * v)) * tauAF (R - 1) v) : ℕ) : ℚ) := by
        exact_mod_cast hsumNat
      have hpProduct : p.1 * p.2 ≤ ((2 * M) / d) ^ 2 := by
        nlinarith [hpaData.2, hpbData.2]
      have hfloor := divisorFloorTau_cast_le_harmonic
        (R - 1) Y d (p.1 * p.2) (((2 * M) / d) ^ 2)
        (Nat.mul_pos hpa hpb) hpProduct
      have hAmono : ((2 * M) / d) ^ 2 ≤ (2 * M) ^ 2 := by
        exact Nat.pow_le_pow_left (Nat.div_le_self (2 * M) d) 2
      have hharm :
          harmonic (((2 * M) / d) ^ 2) ^ (R - 1) ≤ H := by
        dsimp [H]
        exact pow_le_pow_left₀ (by
          have hz := harmonic_mono (x := 0) (y := ((2 * M) / d) ^ 2) (Nat.zero_le _)
          simpa using hz) (harmonic_mono hAmono) _
      have hfloorH :
          (((∑ v ∈ (p.1 * p.2).divisors,
              (Y / (d * v)) * tauAF (R - 1) v) : ℕ) : ℚ) ≤
            ((Y / d : ℕ) : ℚ) * H :=
        hfloor.trans (mul_le_mul_of_nonneg_left hharm (by positivity))
      calc
        (((∑ ell ∈ Finset.Icc 1 (Y / d),
          fiberMass (fun n₁ n₂ => tauAF k n₁ * tauAF k n₂)
            (positiveEquationFiber N p.1 p.2 ell)) : ℕ) : ℚ) ≤
            (B : ℚ) *
              (((∑ v ∈ (p.1 * p.2).divisors,
                (Y / (d * v)) * tauAF (R - 1) v) : ℕ) : ℚ) := hsumQ
        _ ≤ (B : ℚ) * ((Y / d : ℕ) : ℚ) * H := by
          calc
            (B : ℚ) *
                (((∑ v ∈ (p.1 * p.2).divisors,
                  (Y / (d * v)) * tauAF (R - 1) v) : ℕ) : ℚ) ≤
              (B : ℚ) * (((Y / d : ℕ) : ℚ) * H) :=
                mul_le_mul_of_nonneg_left hfloorH (by positivity)
            _ = _ := by ring
        _ = ((2 * C * (N * d / M + 1) * L ^ (k * k) : ℕ) : ℚ) *
              ((Y / d : ℕ) : ℚ) * H := by rfl
    _ = ((2 * C * L ^ (k * k) : ℕ) : ℚ) * H *
        ((∑ d ∈ Finset.Icc 1 K,
          (reducedShortPairs M K d).card *
            (N * d / M + 1) * (Y / d) : ℕ) : ℚ) := by
      push_cast
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.sum_const]
      simp only [nsmul_eq_mul]
      push_cast
      ring
    _ ≤ ((2 * C * L ^ (k * k) : ℕ) : ℚ) * H *
        ((4 * (A + 1) * N * K * Y : ℕ) : ℚ) * harmonic K := by
      have hfactor0 : (0 : ℚ) ≤ ((2 * C * L ^ (k * k) : ℕ) : ℚ) * H :=
        mul_nonneg (by positivity) hH0
      simpa [mul_assoc] using mul_le_mul_of_nonneg_left hGeom hfactor0
    _ = (8 * C * (A + 1) * N * K * Y : ℕ) *
          (L : ℕ) ^ (k * k) * H * harmonic K := by
      push_cast
      ring
    _ = (8 * C * (A + 1) * N * K * Y : ℕ) *
          (Nat.log 2 (2 * N + 2) + 1 : ℕ) ^ (k * k) *
          harmonic ((2 * M) ^ 2) ^ (max 2 (k * k) - 1) * harmonic K := by
      rfl


/-- Uniform version whose only analytic input is the published dyadic Shiu
contract. -/
theorem tripleFiberSum_cast_le_geometric_harmonic
    (hShiu : DyadicTauSquareShiuTarget) (A k M N K Y : ℕ)
    (hA : 0 < A) (hk : 1 ≤ k) (hM : 0 < M)
    (hscale : M ^ 2 ≤ A * N) :
    ∃ C : ℕ, 0 < C ∧
      ((∑ d ∈ Finset.Icc 1 K,
        ∑ p ∈ reducedShortPairs M K d,
          ∑ ell ∈ Finset.Icc 1 (Y / d),
            fiberMass (fun n₁ n₂ => tauAF k n₁ * tauAF k n₂)
              (positiveEquationFiber N p.1 p.2 ell) : ℕ) : ℚ) ≤
        (8 * C * (A + 1) * N * K * Y : ℕ) *
          (Nat.log 2 (2 * N + 2) + 1 : ℕ) ^ (k * k) *
          harmonic ((2 * M) ^ 2) ^ (max 2 (k * k) - 1) * harmonic K := by
  obtain ⟨C, hC, hfiber⟩ :=
    dyadicTarget_signedFiber_content_bound hShiu A k hA hk
  exact ⟨C, hC,
    tripleFiberSum_cast_le_geometric_harmonic_of_contentBound
      A k C M N K Y hA hk hM hscale hfiber⟩


/-! ## Conversion to the literal raw nonzero-survivor endpoint -/

private theorem one_le_nonzeroCommonLog
    (M N : ℕ) (hM : 2 ≤ M) (hN : 2 ≤ N) :
    (1 : ℝ) ≤ Real.log (2 * (M : ℝ) * (N : ℝ)) := by
  have hMr : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hexp : Real.exp 1 ≤ 2 * (M : ℝ) * (N : ℝ) :=
    Real.exp_one_lt_three.le.trans (by nlinarith)
  calc
    (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ _ := Real.log_le_log (Real.exp_pos 1) hexp

private theorem natLogFactor_le_three_nonzeroCommonLog
    (M N : ℕ) (hM : 2 ≤ M) (hN : 2 ≤ N) :
    ((Nat.log 2 (2 * N + 2) + 1 : ℕ) : ℝ) ≤
      3 * Real.log (2 * (M : ℝ) * (N : ℝ)) := by
  let X := 2 * N + 2
  let L := Real.log (2 * (M : ℝ) * (N : ℝ))
  have hX1 : 1 ≤ X := by dsimp [X]; omega
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hX1)
  have hXle : X ≤ 2 * M * N := by dsimp [X]; nlinarith
  have hlogX0 : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg (by exact_mod_cast hX1)
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hlog2pos : (0 : ℝ) < Real.log 2 := by linarith
  have hlogb : Real.logb 2 (X : ℝ) ≤ 2 * Real.log (X : ℝ) := by
    rw [Real.logb]
    apply (div_le_iff₀ hlog2pos).2
    nlinarith
  have hlogXL : Real.log (X : ℝ) ≤ L := by
    apply Real.log_le_log hXpos
    exact_mod_cast hXle
  have hnat := Real.natLog_le_logb X 2
  have hL1 : 1 ≤ L := one_le_nonzeroCommonLog M N hM hN
  change ((Nat.log 2 X + 1 : ℕ) : ℝ) ≤ 3 * L
  push_cast
  calc
    ((Nat.log 2 X : ℕ) : ℝ) + 1 ≤ 2 * Real.log (X : ℝ) + 1 :=
      by simpa [add_comm] using add_le_add_left (hnat.trans hlogb) 1
    _ ≤ 2 * L + 1 := by linarith
    _ ≤ 3 * L := by linarith

private theorem harmonic_squareM_le_three_nonzeroCommonLog
    (M N : ℕ) (hM : 2 ≤ M) (hN : 2 ≤ N) :
    (((harmonic ((2 * M) ^ 2) : ℚ) : ℝ)) ≤
      3 * Real.log (2 * (M : ℝ) * (N : ℝ)) := by
  let X := (2 * M) ^ 2
  let L := Real.log (2 * (M : ℝ) * (N : ℝ))
  have hbase : (0 : ℝ) < 2 * (M : ℝ) * N := by positivity
  have hXpos : (0 : ℝ) < X := by dsimp [X]; positivity
  have hXle : (X : ℝ) ≤ (2 * (M : ℝ) * N) ^ 2 := by
    exact_mod_cast (Nat.pow_le_pow_left (by nlinarith : 2 * M ≤ 2 * M * N) 2)
  have hlogX : Real.log (X : ℝ) ≤ 2 * L := by
    calc
      Real.log (X : ℝ) ≤ Real.log ((2 * (M : ℝ) * N) ^ 2) :=
        Real.log_le_log hXpos hXle
      _ = 2 * L := by rw [Real.log_pow]; dsimp [L]
  have hh := harmonic_le_one_add_log X
  have hL1 : 1 ≤ L := one_le_nonzeroCommonLog M N hM hN
  exact hh.trans (by dsimp [L] at hlogX hL1 ⊢; linarith)

private theorem harmonic_shortFloor_le_two_nonzeroCommonLog
    (M N : ℕ) {U : ℝ} (hM : 2 ≤ M) (hN : 2 ≤ N) :
    (((harmonic (shortFloorCollar M U) : ℚ) : ℝ)) ≤
      2 * Real.log (2 * (M : ℝ) * (N : ℝ)) := by
  let K := shortFloorCollar M U
  let L := Real.log (2 * (M : ℝ) * (N : ℝ))
  have hMle : M ≤ 2 * M * N := by nlinarith
  have hKle : K ≤ 2 * M * N := by
    dsimp [K, shortFloorCollar]
    exact (min_le_left _ _).trans hMle
  have hL1 : 1 ≤ L := one_le_nonzeroCommonLog M N hM hN
  by_cases hK0 : K = 0
  · have hz : (((harmonic K : ℚ) : ℝ)) = 0 := by rw [hK0]; norm_num
    rw [hz]
    exact mul_nonneg (by norm_num) (zero_le_one.trans hL1)
  · have hKpos : (0 : ℝ) < K := by exact_mod_cast Nat.pos_of_ne_zero hK0
    have hKreal : (K : ℝ) ≤ 2 * (M : ℝ) * N := by exact_mod_cast hKle
    have hlogK : Real.log (K : ℝ) ≤ L := Real.log_le_log hKpos hKreal
    exact (harmonic_le_one_add_log K).trans (by
      dsimp [L] at hL1 hlogK ⊢
      linarith)

private theorem collar_NKY_le_rawScale
    (M N : ℕ) {T U : ℝ} (hT : 0 < T) (hU : 0 < U) :
    (N : ℝ) * (shortFloorCollar M U : ℝ) *
        (productFloorCollar M N T : ℝ) ≤
      2 * Real.pi ^ 2 * (((M : ℝ) * N) ^ 2 / (T * U)) := by
  have hK := shortFloorCollar_cast_le M hU
  have hY := productFloorCollar_cast_le M N hT
  calc
    (N : ℝ) * (shortFloorCollar M U : ℝ) *
        (productFloorCollar M N T : ℝ) ≤
      (N : ℝ) * (Real.pi * M / U) *
        (2 * Real.pi * M * N / T) := by gcongr
    _ = 2 * Real.pi ^ 2 * (((M : ℝ) * N) ^ 2 / (T * U)) := by
      field_simp [ne_of_gt hT, ne_of_gt hU]

/-- Exact raw nonzero-sector estimate at natural scale `M² ≤ A N`.
Only `DyadicTauSquareShiuTarget` remains as an analytic input. -/
theorem signedFrequency_tauMass_raw_bound_natScale
    (hShiu : DyadicTauSquareShiuTarget) (A k : ℕ)
    (hA : 0 < A) (hk : 1 ≤ k) :
    ∃ Cnonzero : ℝ, 0 < Cnonzero ∧
      ∀ (M N : ℕ) (T U : ℝ),
        2 ≤ M → 2 ≤ N → M ^ 2 ≤ A * N →
        1 ≤ T → 1 ≤ U →
        weightedMass (tauTupleWeight k)
              (positiveFrequencySector M N
                (Real.pi / (2 * U)) (Real.pi / (2 * T))) +
            weightedMass (tauTupleWeight k)
              (negativeFrequencySector M N
                (Real.pi / (2 * U)) (Real.pi / (2 * T))) ≤
          Cnonzero * ((((M : ℝ) * N) ^ 2) / (T * U)) *
            Real.log (2 * (M : ℝ) * N) ^
              (2 * max 2 (k * k) + 2) := by
  obtain ⟨Cf, hCf, hfiberCf⟩ := dyadicTarget_signedFiber_content_bound hShiu A k hA hk
  let R := max 2 (k * k)
  let Cnonzero : ℝ :=
    64 * Cf * (A + 1) * Real.pi ^ 2 * 3 ^ (k * k + (R - 1))
  refine ⟨Cnonzero, by dsimp [Cnonzero]; positivity, ?_⟩
  intro M N T U hM hN hscale hT hU
  have hMpos : 0 < M := by omega
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hUpos : 0 < U := lt_of_lt_of_le zero_lt_one hU
  let K := shortFloorCollar M U
  let Y := productFloorCollar M N T
  let S := ∑ d ∈ Finset.Icc 1 K,
    ∑ p ∈ reducedShortPairs M K d,
      ∑ ell ∈ Finset.Icc 1 (Y / d),
        fiberMass (fun n₁ n₂ => tauAF k n₁ * tauAF k n₂)
          (positiveEquationFiber N p.1 p.2 ell)
  have hgate := signedFrequency_tauMass_le_two_tripleFiberSum
    k M N hTpos hUpos
  change _ ≤ Cnonzero * (((M : ℝ) * N) ^ 2 / (T * U)) *
      Real.log (2 * (M : ℝ) * N) ^ (2 * max 2 (k * k) + 2)
  change _ ≤ 2 * (S : ℝ) at hgate
  have htripleQ :=
    tripleFiberSum_cast_le_geometric_harmonic_of_contentBound
      A k Cf M N K Y hA hk hMpos hscale hfiberCf
  have htripleR : (S : ℝ) ≤
      (8 * Cf * (A + 1) * N * K * Y : ℕ) *
        (Nat.log 2 (2 * N + 2) + 1 : ℕ) ^ (k * k) *
        (((harmonic ((2 * M) ^ 2) : ℚ) : ℝ)) ^ (R - 1) *
        (((harmonic K : ℚ) : ℝ)) := by
    exact_mod_cast htripleQ
  let Lc := Real.log (2 * (M : ℝ) * N)
  have hLc1 : 1 ≤ Lc := one_le_nonzeroCommonLog M N hM hN
  have hnat := natLogFactor_le_three_nonzeroCommonLog M N hM hN
  have hHM := harmonic_squareM_le_three_nonzeroCommonLog M N hM hN
  have hHK : (((harmonic K : ℚ) : ℝ)) ≤ 2 * Lc := by
    simpa [K, Lc] using
      harmonic_shortFloor_le_two_nonzeroCommonLog M N (U := U) hM hN
  have hHM0 : (0 : ℝ) ≤ (((harmonic ((2 * M) ^ 2) : ℚ) : ℝ)) := by
    exact_mod_cast (show (0 : ℚ) ≤ harmonic ((2 * M) ^ 2) by
      have hz := harmonic_mono (x := 0) (y := (2 * M) ^ 2) (Nat.zero_le _)
      simpa using hz)
  have hHK0 : (0 : ℝ) ≤ (((harmonic K : ℚ) : ℝ)) := by
    exact_mod_cast (show (0 : ℚ) ≤ harmonic K by
      have hz := harmonic_mono (x := 0) (y := K) (Nat.zero_le _)
      simpa using hz)
  have hpowNat :
      ((Nat.log 2 (2 * N + 2) + 1 : ℕ) : ℝ) ^ (k * k) ≤
        (3 * Lc) ^ (k * k) := pow_le_pow_left₀ (by positivity) hnat _
  have hpowHM :
      (((harmonic ((2 * M) ^ 2) : ℚ) : ℝ)) ^ (R - 1) ≤
        (3 * Lc) ^ (R - 1) := pow_le_pow_left₀ hHM0 hHM _
  have hNKY := collar_NKY_le_rawScale M N hTpos hUpos
  have hexp : k * k + R ≤ 2 * R + 2 := by
    have hkR : k * k ≤ R := Nat.le_max_right _ _
    omega
  have hpowCommon : Lc ^ (k * k + R) ≤ Lc ^ (2 * R + 2) :=
    pow_le_pow_right₀ hLc1 hexp
  calc
    _ ≤ 2 * (S : ℝ) := hgate
    _ ≤ 2 * ((8 * Cf * (A + 1) : ℕ) *
        ((N : ℝ) * K * Y) *
        ((Nat.log 2 (2 * N + 2) + 1 : ℕ) : ℝ) ^ (k * k) *
        (((harmonic ((2 * M) ^ 2) : ℚ) : ℝ)) ^ (R - 1) *
        (((harmonic K : ℚ) : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      calc
        (S : ℝ) ≤ (8 * Cf * (A + 1) * N * K * Y : ℕ) *
            ((Nat.log 2 (2 * N + 2) + 1 : ℕ) : ℝ) ^ (k * k) *
            (((harmonic ((2 * M) ^ 2) : ℚ) : ℝ)) ^ (R - 1) *
            (((harmonic K : ℚ) : ℝ)) := htripleR
        _ = (8 * Cf * (A + 1) : ℕ) * ((N : ℝ) * K * Y) *
            ((Nat.log 2 (2 * N + 2) + 1 : ℕ) : ℝ) ^ (k * k) *
            (((harmonic ((2 * M) ^ 2) : ℚ) : ℝ)) ^ (R - 1) *
            (((harmonic K : ℚ) : ℝ)) := by push_cast; ring
    _ ≤ 2 * ((8 * Cf * (A + 1) : ℕ) *
        (2 * Real.pi ^ 2 * (((M : ℝ) * N) ^ 2 / (T * U))) *
        (3 * Lc) ^ (k * k) * (3 * Lc) ^ (R - 1) * (2 * Lc)) := by
      gcongr
    _ = Cnonzero * (((M : ℝ) * N) ^ 2 / (T * U)) *
        Lc ^ (k * k + R) := by
      dsimp [Cnonzero]
      rw [pow_add, pow_add]
      rw [show Lc ^ R = Lc ^ (R - 1) * Lc by
        rw [← pow_succ]
        congr 1
        omega]
      push_cast
      ring
    _ ≤ Cnonzero * (((M : ℝ) * N) ^ 2 / (T * U)) *
        Lc ^ (2 * R + 2) := by
      exact mul_le_mul_of_nonneg_left hpowCommon (by positivity)
    _ = Cnonzero * (((M : ℝ) * N) ^ 2 / (T * U)) *
        Real.log (2 * (M : ℝ) * N) ^ (2 * max 2 (k * k) + 2) := by rfl


/-- Literal raw nonzero-sector estimate in the manuscript's real scale
`c M² ≤ N`.  The Archimedean integer `A > 1/c` is chosen once, so the
constant remains uniform in `M,N,T,U`. -/
theorem signedFrequency_tauMass_raw_bound
    (hShiu : DyadicTauSquareShiuTarget) (c : ℝ) (k : ℕ)
    (hc : 0 < c) (hk : 1 ≤ k) :
    ∃ Cnonzero : ℝ, 0 < Cnonzero ∧
      ∀ (M N : ℕ) (T U : ℝ),
        2 ≤ M → 2 ≤ N → c * (M : ℝ) ^ 2 ≤ (N : ℝ) →
        1 ≤ T → 1 ≤ U →
        weightedMass (tauTupleWeight k)
              (positiveFrequencySector M N
                (Real.pi / (2 * U)) (Real.pi / (2 * T))) +
            weightedMass (tauTupleWeight k)
              (negativeFrequencySector M N
                (Real.pi / (2 * U)) (Real.pi / (2 * T))) ≤
          Cnonzero * ((((M : ℝ) * N) ^ 2) / (T * U)) *
            Real.log (2 * (M : ℝ) * N) ^
              (2 * max 2 (k * k) + 2) := by
  obtain ⟨A, hAgt⟩ := exists_nat_gt (1 / c)
  have honec : (0 : ℝ) < 1 / c := by positivity
  have hAposR : (0 : ℝ) < A := honec.trans hAgt
  have hA : 0 < A := by exact_mod_cast hAposR
  obtain ⟨Cnonzero, hCnonzero, hbound⟩ :=
    signedFrequency_tauMass_raw_bound_natScale hShiu A k hA hk
  refine ⟨Cnonzero, hCnonzero, ?_⟩
  intro M N T U hM hN hscale hT hU
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hMscale : (M : ℝ) ^ 2 ≤ (N : ℝ) / c := by
    apply (le_div_iff₀ hc).2
    simpa [mul_comm] using hscale
  have hAupper : (N : ℝ) / c ≤ (A : ℝ) * N := by
    calc
      (N : ℝ) / c = (1 / c) * N := by ring
      _ ≤ (A : ℝ) * N := mul_le_mul_of_nonneg_right hAgt.le hN0
  have hscaleNat : M ^ 2 ≤ A * N := by
    exact_mod_cast hMscale.trans hAupper
  exact hbound M N T U hM hN hscaleNat hT hU

end MAPNonzeroSectorGate
