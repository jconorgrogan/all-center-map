import GuthMaynardS3LiteralTruncation
import GuthMaynardS3LiteralGlobalReduction
import GuthMaynardS3LiteralDyadicBlock

/-!
# Finite balanced ordered sectors for the literal S3 cube

The retained sector is ordered by absolute frequency.  The largest coordinate
is not forced into the same dyadic window as the middle coordinate: under the
literal unbalanced cutoff it lies in one of the four windows
`2^(k+d)`, `d = 0,1,2,3`.
-/

namespace GuthMaynardS3LiteralBalancedSectorGeometry

open scoped BigOperators
open GuthMaynardS3LiteralTruncation
open GuthMaynardEquation55Infinite
open GuthMaynardS3LiteralGlobalReduction
open GuthMaynardS3LiteralDyadicBlock
open GuthMaynardS3LiteralAffineReduction
open GuthMaynardS3LiteralScaleComparison
open GuthMaynardS3LiteralRadialDecay
open GuthMaynardS3LiteralLocalization

noncomputable section

set_option maxHeartbeats 800000

def dyadicExponents (Mcut : ℕ) : Finset ℕ :=
  Finset.range (Nat.log 2 (max Mcut 1) + 1)

def orderedBalancedBlock (Mcut i k d : ℕ) : Finset Frequency :=
  (prefixFrequencyCube Mcut).filter fun p =>
    (2 ^ i : ℝ) ≤ |(p.1.1 : ℝ)| ∧ |(p.1.1 : ℝ)| ≤ 2 * (2 ^ i : ℝ) ∧
    (2 ^ k : ℝ) ≤ |(p.1.2 : ℝ)| ∧ |(p.1.2 : ℝ)| ≤ 2 * (2 ^ k : ℝ) ∧
    (2 ^ (k + d) : ℝ) ≤ |(p.2 : ℝ)| ∧ |(p.2 : ℝ)| ≤ 2 * (2 ^ (k + d) : ℝ) ∧
    |(p.1.1 : ℝ)| ≤ |(p.1.2 : ℝ)| ∧ |(p.1.2 : ℝ)| ≤ |(p.2 : ℝ)|

def orderedBalancedBlockAffine (N : ℕ) (W : Finset ℝ) (rho : ℝ)
    (Mcut i k d : ℕ) : ℝ :=
  (16 * radialDerivativeBudget 0 * rho * (N : ℝ) ^ 2 / (2 ^ k : ℝ)) *
    (∑ p ∈ orderedBalancedBlock Mcut i k d,
      affineProfileIntegral ((N : ℝ) * (2 ^ k : ℝ) / (4 * rho)) W
        p.1.1 p.1.2 p.2)

theorem affineFrequencyMajorant_le_balancedBlockAffine {N : ℕ}
    (hN : 0 < N) {rho : ℝ} (hrho : 0 < rho) (W : Finset ℝ)
    {Mcut i k d : ℕ} {p : Frequency}
    (hp : p ∈ orderedBalancedBlock Mcut i k d) :
    affineFrequencyMajorant N W rho p ≤
      (16 * radialDerivativeBudget 0 * rho * (N : ℝ) ^ 2 / (2 ^ k : ℝ)) *
        affineProfileIntegral ((N : ℝ) * (2 ^ k : ℝ) / (4 * rho)) W
          p.1.1 p.1.2 p.2 := by
  have h := (Finset.mem_filter.mp hp).2
  have hlo : (2 ^ k : ℝ) ≤ |(p.1.2 : ℝ)| := h.2.2.1
  have hhi : |(p.1.2 : ℝ)| ≤ 2 * (2 ^ k : ℝ) := h.2.2.2.1
  let B0 := (N : ℝ) * (2 ^ k : ℝ) / (4 * rho)
  let B := (N : ℝ) * |(p.1.2 : ℝ)| / (2 * rho)
  have hB0 : 0 < B0 := by
    dsimp [B0]
    exact div_pos (mul_pos (Nat.cast_pos.mpr hN) (by positivity))
      (by positivity)
  have hBlo : 2 * B0 ≤ B := by
    dsimp [B0, B]
    have h := mul_le_mul_of_nonneg_left hlo (Nat.cast_nonneg N)
    field_simp
    nlinarith only [hlo]
  have hBhi : B ≤ 4 * B0 := by
    dsimp [B0, B]
    have h := mul_le_mul_of_nonneg_left hhi (Nat.cast_nonneg N)
    field_simp
    nlinarith only [hhi]
  have hpint := affineProfileIntegral_le_four hB0 hBlo hBhi W
    p.1.1 p.1.2 p.2
  have hc := div_le_div_of_nonneg_left
    (show 0 ≤ 4 * radialDerivativeBudget 0 * rho * (N : ℝ) ^ 2 by
      exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
        (radialDerivativeBudget_nonneg 0)) hrho.le) (sq_nonneg _))
    (show 0 < (2 ^ k : ℝ) by positivity) hlo
  have hm := mul_le_mul hc hpint
    (affineProfileIntegral_nonneg B W p.1.1 p.1.2 p.2)
    (div_nonneg (by
      have hC := radialDerivativeBudget_nonneg 0
      positivity) (by positivity))
  unfold affineFrequencyMajorant
  convert hm using 1 <;> ring

theorem orderedBalancedBlock_majorant_le {N : ℕ} (hN : 0 < N)
    {rho : ℝ} (hrho : 0 < rho) (W : Finset ℝ)
    (Mcut i k d : ℕ) :
    (∑ p ∈ orderedBalancedBlock Mcut i k d,
      affineFrequencyMajorant N W rho p) ≤
      orderedBalancedBlockAffine N W rho Mcut i k d := by
  unfold orderedBalancedBlockAffine
  calc
    (∑ p ∈ orderedBalancedBlock Mcut i k d,
        affineFrequencyMajorant N W rho p) ≤
        ∑ p ∈ orderedBalancedBlock Mcut i k d,
          (16 * radialDerivativeBudget 0 * rho * (N : ℝ) ^ 2 /
              (2 ^ k : ℝ)) *
            affineProfileIntegral ((N : ℝ) * (2 ^ k : ℝ) / (4 * rho)) W
              p.1.1 p.1.2 p.2 := by
      apply Finset.sum_le_sum
      intro p hp
      exact affineFrequencyMajorant_le_balancedBlockAffine hN hrho W hp
    _ = _ := by rw [Finset.mul_sum]

theorem abs_cast_natAbs (m : ℤ) : |(m : ℝ)| = (m.natAbs : ℝ) := by
  simpa only [Int.cast_abs] using (Nat.cast_natAbs (α := ℝ) m).symm

theorem log_window {n : ℕ} (hn : 1 ≤ n) :
    (2 ^ Nat.log 2 n : ℝ) ≤ n ∧ (n : ℝ) ≤ 2 * (2 ^ Nat.log 2 n : ℝ) := by
  have hne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
  have hlo := Nat.pow_log_le_self 2 hne
  have hhi := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) n
  constructor
  · exact_mod_cast hlo
  · have h : n < 2 * 2 ^ Nat.log 2 n := by
      simpa [pow_succ, Nat.mul_comm] using hhi
    norm_num
    exact_mod_cast h.le

theorem log_mem {n Mcut : ℕ} (hn : 1 ≤ n) (hnM : n ≤ Mcut) :
    Nat.log 2 n ∈ dyadicExponents Mcut := by
  unfold dyadicExponents
  apply Finset.mem_range.mpr
  have hmono : Nat.log 2 n ≤ Nat.log 2 (max Mcut 1) :=
    Nat.log_mono_right (le_trans hnM (le_max_left _ _))
  omega

theorem natAbs_mem_nonzeroPrefix {M : ℕ} {m : ℤ} (hm : m ∈ nonzeroPrefix M) :
    1 ≤ m.natAbs ∧ m.natAbs ≤ M := by
  rcases Finset.mem_union.mp hm with h | h
  · obtain ⟨n, hn, heq⟩ := Finset.mem_image.mp h
    rw [← heq]
    simpa using Finset.mem_Icc.mp hn
  · obtain ⟨n, hn, heq⟩ := Finset.mem_image.mp h
    rw [← heq]
    simpa [Int.natAbs_neg] using Finset.mem_Icc.mp hn

theorem log_gap_four {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hba : b ≤ 5 * a) :
    Nat.log 2 b < Nat.log 2 a + 4 := by
  have hne : b ≠ 0 := by omega
  have hpow := Nat.pow_log_le_self 2 hne
  by_contra hn
  have hkj : Nat.log 2 a + 4 ≤ Nat.log 2 b := by omega
  have hpow' := Nat.pow_le_pow_right (by omega : 2 > 0) hkj
  have h16 : 16 * 2 ^ Nat.log 2 a ≤ 2 ^ Nat.log 2 b := by
    calc
      16 * 2 ^ Nat.log 2 a = 2 ^ (Nat.log 2 a + 4) := by
        rw [pow_add]
        norm_num
        ring
      _ ≤ 2 ^ Nat.log 2 b := hpow'
  have haPow : a ≤ 2 * 2 ^ Nat.log 2 a := by
    have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) a
    simpa [pow_succ, Nat.mul_comm] using h.le
  have h10 : b ≤ 10 * 2 ^ Nat.log 2 a := by omega
  have hpos : 1 ≤ 2 ^ Nat.log 2 a := by
    exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))
  omega

theorem mem_orderedBalancedBlock_of_sorted_balanced
    {Mcut : ℕ} {p : Frequency} (hp : p ∈ prefixFrequencyCube Mcut)
    (horder : |(p.1.1 : ℝ)| ≤ |(p.1.2 : ℝ)| ∧
      |(p.1.2 : ℝ)| ≤ |(p.2 : ℝ)|)
    (hbal : |(p.2 : ℝ)| ≤ 5 * |(p.1.2 : ℝ)|) :
    ∃ i ∈ dyadicExponents Mcut, ∃ k ∈ dyadicExponents Mcut,
      ∃ d ∈ Finset.range 4,
        p ∈ orderedBalancedBlock Mcut i k d := by
  obtain ⟨h12, h3⟩ := Finset.mem_product.mp hp
  obtain ⟨h1, h2⟩ := Finset.mem_product.mp h12
  have hm1 := (GuthMaynardS3LiteralTruncation.nonzeroPrefix_ne_zero h1)
  have hm2 := (GuthMaynardS3LiteralTruncation.nonzeroPrefix_ne_zero h2)
  have hm3 := (GuthMaynardS3LiteralTruncation.nonzeroPrefix_ne_zero h3)
  have hn1 := natAbs_mem_nonzeroPrefix h1
  have hn2 := natAbs_mem_nonzeroPrefix h2
  have hn3 := natAbs_mem_nonzeroPrefix h3
  let i := Nat.log 2 p.1.1.natAbs
  let k := Nat.log 2 p.1.2.natAbs
  let j := Nat.log 2 p.2.natAbs
  have hi : i ∈ dyadicExponents Mcut := by
    dsimp [i]; exact log_mem hn1.1 hn1.2
  have hk : k ∈ dyadicExponents Mcut := by
    dsimp [k]; exact log_mem hn2.1 hn2.2
  have hj : j ∈ dyadicExponents Mcut := by
    dsimp [j]; exact log_mem hn3.1 hn3.2
  have hnatorder : p.1.2.natAbs ≤ p.2.natAbs := by
    rw [← Nat.cast_le (α := ℝ)]
    simpa only [abs_cast_natAbs] using horder.2
  have hnatbal : p.2.natAbs ≤ 5 * p.1.2.natAbs := by
    rw [← Nat.cast_le (α := ℝ)]
    simpa only [abs_cast_natAbs, Nat.cast_mul, Nat.cast_ofNat] using hbal
  have hkj : k ≤ j := by
    dsimp [k, j]
    exact Nat.log_mono_right hnatorder
  have hjgap : j < k + 4 := by
    dsimp [k, j]
    exact log_gap_four hn2.1 hn3.1 hnatbal
  let d := j - k
  have hd : d ∈ Finset.range 4 := by
    dsimp [d]
    apply Finset.mem_range.mpr
    omega
  refine ⟨i, hi, k, hk, d, hd, Finset.mem_filter.mpr ⟨hp, ?_⟩⟩
  have hw1 := log_window hn1.1
  have hw2 := log_window hn2.1
  have hw3 := log_window hn3.1
  have hthird : k + d = j := by
    dsimp [d]
    omega
  have hw1' :
      (2 ^ i : ℝ) ≤ |(p.1.1 : ℝ)| ∧ |(p.1.1 : ℝ)| ≤ 2 * (2 ^ i : ℝ) := by
    dsimp [i]
    rw [abs_cast_natAbs]
    exact hw1
  have hw2' :
      (2 ^ k : ℝ) ≤ |(p.1.2 : ℝ)| ∧ |(p.1.2 : ℝ)| ≤ 2 * (2 ^ k : ℝ) := by
    dsimp [k]
    rw [abs_cast_natAbs]
    exact hw2
  have hw3' :
      (2 ^ (k + d) : ℝ) ≤ |(p.2 : ℝ)| ∧ |(p.2 : ℝ)| ≤
        2 * (2 ^ (k + d) : ℝ) := by
    rw [abs_cast_natAbs]
    rw [hthird]
    exact hw3
  exact ⟨hw1'.1, hw1'.2, hw2'.1, hw2'.2, hw3'.1, hw3'.2,
    horder.1, horder.2⟩

def orderedBalancedKeys (Mcut : ℕ) : Finset ((ℕ × ℕ) × ℕ) :=
  (dyadicExponents Mcut).product (dyadicExponents Mcut) |>.product (Finset.range 4)

def orderedBalancedUnion (Mcut : ℕ) : Finset Frequency :=
  (orderedBalancedKeys Mcut).biUnion fun key =>
    orderedBalancedBlock Mcut key.1.1 key.1.2 key.2

theorem orderedBalancedKeys_card (Mcut : ℕ) :
    (orderedBalancedKeys Mcut).card =
      4 * (dyadicExponents Mcut).card ^ 2 := by
  simp [orderedBalancedKeys, Finset.card_product, pow_two, Nat.mul_assoc,
    Nat.mul_left_comm, Nat.mul_comm]

theorem orderedBalancedKeys_nonempty (Mcut : ℕ) :
    (orderedBalancedKeys Mcut).Nonempty := by
  refine ⟨((0, 0), 0), ?_⟩
  simp [orderedBalancedKeys, dyadicExponents]

theorem sorted_balanced_subset_orderedBalancedUnion {Mcut : ℕ} {p : Frequency}
    (hp : p ∈ prefixFrequencyCube Mcut)
    (horder : |(p.1.1 : ℝ)| ≤ |(p.1.2 : ℝ)| ∧
      |(p.1.2 : ℝ)| ≤ |(p.2 : ℝ)|)
    (hbal : |(p.2 : ℝ)| ≤ 5 * |(p.1.2 : ℝ)|) :
    p ∈ orderedBalancedUnion Mcut := by
  obtain ⟨i, hi, k, hk, d, hd, hblock⟩ :=
    mem_orderedBalancedBlock_of_sorted_balanced hp horder hbal
  exact Finset.mem_biUnion.mpr
    ⟨((i, k), d), by simp [orderedBalancedKeys, hi, hk, hd], hblock⟩

theorem sum_biUnion_le_sum_nonneg {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (s : Finset κ) (t : κ → Finset ι) (f : ι → ℝ) (hf : ∀ x, 0 ≤ f x) :
    (∑ x ∈ s.biUnion t, f x) ≤ ∑ a ∈ s, ∑ x ∈ t a, f x := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert ha]
      let left := t a
      let right := s.biUnion t
      rw [show left ∪ right = left ∪ (right \ left) by
        ext x; simp [left, right]]
      rw [Finset.sum_union (Finset.disjoint_sdiff)]
      have hs : (∑ x ∈ right \ left, f x) ≤ ∑ x ∈ right, f x :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
          (fun x _ _ => hf x)
      exact add_le_add_right (hs.trans ih) _

theorem exists_max_orderedBalancedBlockAffine (N : ℕ) (W : Finset ℝ)
    (rho : ℝ) (Mcut : ℕ) :
    ∃ i ∈ dyadicExponents Mcut, ∃ k ∈ dyadicExponents Mcut,
      ∃ d ∈ Finset.range 4,
        ∀ i' ∈ dyadicExponents Mcut, ∀ k' ∈ dyadicExponents Mcut,
          ∀ d' ∈ Finset.range 4,
            orderedBalancedBlockAffine N W rho Mcut i' k' d' ≤
              orderedBalancedBlockAffine N W rho Mcut i k d := by
  obtain ⟨key, hkey, hmax⟩ :=
    Finset.exists_max_image (orderedBalancedKeys Mcut)
      (fun key => orderedBalancedBlockAffine N W rho Mcut key.1.1 key.1.2 key.2)
      (orderedBalancedKeys_nonempty Mcut)
  refine ⟨key.1.1, ?_, key.1.2, ?_, key.2, ?_, ?_⟩
  · exact (Finset.mem_product.mp (Finset.mem_product.mp hkey).1).1
  · exact (Finset.mem_product.mp (Finset.mem_product.mp hkey).1).2
  · exact (Finset.mem_product.mp hkey).2
  · intro i' hi' k' hk' d' hd'
    exact hmax ((i', k'), d') (by
      simp [orderedBalancedKeys, hi', hk', hd'])

theorem sum_orderedBalancedUnion_majorant_le_selected {N : ℕ} (hN : 0 < N)
    {rho : ℝ} (hrho : 0 < rho) (W : Finset ℝ) (Mcut : ℕ) :
    ∃ i ∈ dyadicExponents Mcut, ∃ k ∈ dyadicExponents Mcut,
      ∃ d ∈ Finset.range 4,
        (∑ p ∈ orderedBalancedUnion Mcut,
          affineFrequencyMajorant N W rho p) ≤
          ((orderedBalancedKeys Mcut).card : ℝ) *
            orderedBalancedBlockAffine N W rho Mcut i k d := by
  obtain ⟨i, hi, k, hk, d, hd, hmax⟩ :=
    exists_max_orderedBalancedBlockAffine N W rho Mcut
  refine ⟨i, hi, k, hk, d, hd, ?_⟩
  have hnonneg : ∀ p, 0 ≤ affineFrequencyMajorant N W rho p := by
    intro p
    unfold affineFrequencyMajorant
    have hC := radialDerivativeBudget_nonneg 0
    have hp := affineProfileIntegral_nonneg
      ((N : ℝ) * |(p.1.2 : ℝ)| / (2 * rho)) W p.1.1 p.1.2 p.2
    positivity
  have hsum := sum_biUnion_le_sum_nonneg (orderedBalancedKeys Mcut)
    (fun key => orderedBalancedBlock Mcut key.1.1 key.1.2 key.2)
    (fun p => affineFrequencyMajorant N W rho p) hnonneg
  have hcell : ∀ key ∈ orderedBalancedKeys Mcut,
      (∑ p ∈ orderedBalancedBlock Mcut key.1.1 key.1.2 key.2,
        affineFrequencyMajorant N W rho p) ≤
      orderedBalancedBlockAffine N W rho Mcut key.1.1 key.1.2 key.2 := by
    intro key hkey
    exact orderedBalancedBlock_majorant_le hN hrho W Mcut key.1.1 key.1.2 key.2
  have hcells := Finset.sum_le_sum hcell
  have hmaxsum :
      (∑ key ∈ orderedBalancedKeys Mcut,
        orderedBalancedBlockAffine N W rho Mcut key.1.1 key.1.2 key.2) ≤
      ((orderedBalancedKeys Mcut).card : ℝ) *
        orderedBalancedBlockAffine N W rho Mcut i k d := by
    have hpoint : ∀ key ∈ orderedBalancedKeys Mcut,
        orderedBalancedBlockAffine N W rho Mcut key.1.1 key.1.2 key.2 ≤
          orderedBalancedBlockAffine N W rho Mcut i k d := by
      intro key hkey
      obtain ⟨⟨i', k'⟩, d'⟩ := key
      exact hmax i' ((Finset.mem_product.mp (Finset.mem_product.mp hkey).1).1)
        k' ((Finset.mem_product.mp (Finset.mem_product.mp hkey).1).2)
        d' ((Finset.mem_product.mp hkey).2)
    apply (Finset.sum_le_sum hpoint).trans
    simp [Finset.sum_const, nsmul_eq_mul]
  exact hsum.trans (hcells.trans hmaxsum)

def freq123 (p : Frequency) : Frequency := p
def freq132 (p : Frequency) : Frequency := ((p.1.1, p.2), p.1.2)
def freq213 (p : Frequency) : Frequency := ((p.1.2, p.1.1), p.2)
def freq231 (p : Frequency) : Frequency := ((p.1.2, p.2), p.1.1)
def freq312 (p : Frequency) : Frequency := ((p.2, p.1.1), p.1.2)
def freq321 (p : Frequency) : Frequency := ((p.2, p.1.2), p.1.1)

theorem freq312_freq231 (p : Frequency) : freq312 (freq231 p) = p := by
  rcases p with ⟨⟨a, b⟩, c⟩
  simp [freq231, freq312]

theorem freq231_freq312 (p : Frequency) : freq231 (freq312 p) = p := by
  rcases p with ⟨⟨a, b⟩, c⟩
  simp [freq231, freq312]

def sixSectorUnion (Mcut i k d : ℕ) : Finset Frequency :=
  orderedBalancedBlock Mcut i k d ∪
    ((orderedBalancedBlock Mcut i k d).image freq132 ∪
      ((orderedBalancedBlock Mcut i k d).image freq213 ∪
        ((orderedBalancedBlock Mcut i k d).image freq231 ∪
          ((orderedBalancedBlock Mcut i k d).image freq312 ∪
            (orderedBalancedBlock Mcut i k d).image freq321))))

theorem prefix_mem_freq132 {p : Frequency} (hp : p ∈ prefixFrequencyCube Mcut) :
    freq132 p ∈ prefixFrequencyCube Mcut := by
  obtain ⟨h12, h3⟩ := Finset.mem_product.mp hp
  obtain ⟨h1, h2⟩ := Finset.mem_product.mp h12
  exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨h1, h3⟩, h2⟩

theorem prefix_mem_freq213 {p : Frequency} (hp : p ∈ prefixFrequencyCube Mcut) :
    freq213 p ∈ prefixFrequencyCube Mcut := by
  obtain ⟨h12, h3⟩ := Finset.mem_product.mp hp
  obtain ⟨h1, h2⟩ := Finset.mem_product.mp h12
  exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨h2, h1⟩, h3⟩

theorem prefix_mem_freq231 {p : Frequency} (hp : p ∈ prefixFrequencyCube Mcut) :
    freq231 p ∈ prefixFrequencyCube Mcut := by
  obtain ⟨h12, h3⟩ := Finset.mem_product.mp hp
  obtain ⟨h1, h2⟩ := Finset.mem_product.mp h12
  exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨h2, h3⟩, h1⟩

theorem prefix_mem_freq312 {p : Frequency} (hp : p ∈ prefixFrequencyCube Mcut) :
    freq312 p ∈ prefixFrequencyCube Mcut := by
  obtain ⟨h12, h3⟩ := Finset.mem_product.mp hp
  obtain ⟨h1, h2⟩ := Finset.mem_product.mp h12
  exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨h3, h1⟩, h2⟩

theorem prefix_mem_freq321 {p : Frequency} (hp : p ∈ prefixFrequencyCube Mcut) :
    freq321 p ∈ prefixFrequencyCube Mcut := by
  obtain ⟨h12, h3⟩ := Finset.mem_product.mp hp
  obtain ⟨h1, h2⟩ := Finset.mem_product.mp h12
  exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨h3, h2⟩, h1⟩

theorem mem_sixSectorUnion_of_ordered_case {Mcut : ℕ} {p : Frequency}
    (hp : p ∈ prefixFrequencyCube Mcut)
    (hcase :
      (|(p.1.1 : ℝ)| ≤ |(p.1.2 : ℝ)| ∧ |(p.1.2 : ℝ)| ≤ |(p.2 : ℝ)| ∧
        |(p.2 : ℝ)| ≤ 5 * |(p.1.2 : ℝ)|) ∨
      (|(p.1.1 : ℝ)| ≤ |(p.2 : ℝ)| ∧ |(p.2 : ℝ)| ≤ |(p.1.2 : ℝ)| ∧
        |(p.1.2 : ℝ)| ≤ 5 * |(p.2 : ℝ)|) ∨
      (|(p.1.2 : ℝ)| ≤ |(p.1.1 : ℝ)| ∧ |(p.1.1 : ℝ)| ≤ |(p.2 : ℝ)| ∧
        |(p.2 : ℝ)| ≤ 5 * |(p.1.1 : ℝ)|) ∨
      (|(p.1.2 : ℝ)| ≤ |(p.2 : ℝ)| ∧ |(p.2 : ℝ)| ≤ |(p.1.1 : ℝ)| ∧
        |(p.1.1 : ℝ)| ≤ 5 * |(p.2 : ℝ)|) ∨
      (|(p.2 : ℝ)| ≤ |(p.1.1 : ℝ)| ∧ |(p.1.1 : ℝ)| ≤ |(p.1.2 : ℝ)| ∧
        |(p.1.2 : ℝ)| ≤ 5 * |(p.1.1 : ℝ)|) ∨
      (|(p.2 : ℝ)| ≤ |(p.1.2 : ℝ)| ∧ |(p.1.2 : ℝ)| ≤ |(p.1.1 : ℝ)| ∧
        |(p.1.1 : ℝ)| ≤ 5 * |(p.1.2 : ℝ)|)) :
    ∃ i ∈ dyadicExponents Mcut, ∃ k ∈ dyadicExponents Mcut,
      ∃ d ∈ Finset.range 4, p ∈ sixSectorUnion Mcut i k d := by
  rcases hcase with h | h | h | h | h | h
  · obtain ⟨i, hi, k, hk, d, hd, hq⟩ :=
      mem_orderedBalancedBlock_of_sorted_balanced hp ⟨h.1, h.2.1⟩ h.2.2
    exact ⟨i, hi, k, hk, d, hd, by simp [sixSectorUnion, hq]⟩
  · have hqorder :
        |((freq132 p).1.1 : ℝ)| ≤ |((freq132 p).1.2 : ℝ)| ∧
        |((freq132 p).1.2 : ℝ)| ≤ |((freq132 p).2 : ℝ)| := by
      simpa [freq132] using ⟨h.1, h.2.1⟩
    have hqbal : |((freq132 p).2 : ℝ)| ≤
        5 * |((freq132 p).1.2 : ℝ)| := by
      simpa [freq132] using h.2.2
    obtain ⟨i, hi, k, hk, d, hd, hq⟩ :=
      mem_orderedBalancedBlock_of_sorted_balanced (prefix_mem_freq132 hp)
        hqorder hqbal
    exact ⟨i, hi, k, hk, d, hd, by
      simp only [sixSectorUnion, Finset.mem_union]
      exact Or.inr (Or.inl (Finset.mem_image.mpr ⟨freq132 p, hq, by rfl⟩))⟩
  · obtain ⟨i, hi, k, hk, d, hd, hq⟩ :=
      mem_orderedBalancedBlock_of_sorted_balanced (prefix_mem_freq213 hp)
        (by simpa [freq213] using ⟨h.1, h.2.1⟩)
        (by simpa [freq213] using h.2.2)
    exact ⟨i, hi, k, hk, d, hd, by
      simp only [sixSectorUnion, Finset.mem_union]
      exact Or.inr (Or.inr (Or.inl (Finset.mem_image.mpr
        ⟨freq213 p, hq, by rfl⟩)))⟩
  · obtain ⟨i, hi, k, hk, d, hd, hq⟩ :=
      mem_orderedBalancedBlock_of_sorted_balanced (prefix_mem_freq231 hp)
        (by simpa [freq231] using ⟨h.1, h.2.1⟩)
        (by simpa [freq231] using h.2.2)
    exact ⟨i, hi, k, hk, d, hd, by
      simp only [sixSectorUnion, Finset.mem_union]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Finset.mem_image.mpr
        ⟨freq231 p, hq, freq312_freq231 p⟩)))))⟩
  · obtain ⟨i, hi, k, hk, d, hd, hq⟩ :=
      mem_orderedBalancedBlock_of_sorted_balanced (prefix_mem_freq312 hp)
        (by simpa [freq312] using ⟨h.1, h.2.1⟩)
        (by simpa [freq312] using h.2.2)
    exact ⟨i, hi, k, hk, d, hd, by
      simp only [sixSectorUnion, Finset.mem_union]
      exact Or.inr (Or.inr (Or.inr (Or.inl (Finset.mem_image.mpr
        ⟨freq312 p, hq, freq231_freq312 p⟩))))⟩
  · obtain ⟨i, hi, k, hk, d, hd, hq⟩ :=
      mem_orderedBalancedBlock_of_sorted_balanced (prefix_mem_freq321 hp)
        (by simpa [freq321] using ⟨h.1, h.2.1⟩)
        (by simpa [freq321] using h.2.2)
    exact ⟨i, hi, k, hk, d, hd, by
      simp only [sixSectorUnion, Finset.mem_union]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Finset.mem_image.mpr ⟨freq321 p, hq, by rfl⟩)))))⟩


end
end GuthMaynardS3LiteralBalancedSectorGeometry

#print axioms GuthMaynardS3LiteralBalancedSectorGeometry.mem_orderedBalancedBlock_of_sorted_balanced
