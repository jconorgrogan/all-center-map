import MixedMeanMajorantWeld
import FloorTightCollars
import ZeroSectorFiniteWeld

/-!
# Global equal-short sector for MAP Lemma 2.1

This module closes the equal-short part of the exact Fourier survivor mass.
It uses only the already certified divisor-square moment and the finite
neighbor-pair estimate; no sector-count proposition is assumed.
-/

noncomputable section

namespace MAPMixedMeanCompletion

open DeterminantCountWeld MixedMeanFrontend MixedMeanMajorantWeld
open MAPMixedMeanFloor MAPMixedMeanZeroClose MAPMixedMean MixedMellinCert

/-- Ordered positive pairs at distance at most `H`, including the diagonal. -/
def weakNeighborPairs (A H : ℕ) : Finset (ℕ × ℕ) :=
  ((positiveRange A).product (positiveRange A)).filter fun p =>
    p.1.dist p.2 ≤ H

/-- The diagonal inside `[1,A]^2`. -/
def diagonalPairs (A : ℕ) : Finset (ℕ × ℕ) :=
  (positiveRange A).image fun n => (n, n)

theorem weakNeighborPairs_eq_symmetric_union_diagonal (A H : ℕ) :
    weakNeighborPairs A H =
      symmetricNeighborPairs A H ∪ diagonalPairs A := by
  ext p
  constructor
  · intro hp
    rcases Finset.mem_filter.mp hp with ⟨hpbox, hdist⟩
    rcases Finset.mem_product.mp hpbox with ⟨hp₁, hp₂⟩
    by_cases heq : p.1 = p.2
    · apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨p.1, hp₁, ?_⟩
      exact Prod.ext rfl heq
    · apply Finset.mem_union_left
      exact Finset.mem_filter.mpr ⟨hpbox, heq, hdist⟩
  · intro hp
    rcases Finset.mem_union.mp hp with hsym | hdiag
    · rcases Finset.mem_filter.mp hsym with ⟨hpbox, hne, hdist⟩
      exact Finset.mem_filter.mpr ⟨hpbox, hdist⟩
    · obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hdiag
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hn, hn⟩, by simp⟩

theorem symmetricNeighborPairs_disjoint_diagonalPairs (A H : ℕ) :
    Disjoint (symmetricNeighborPairs A H) (diagonalPairs A) := by
  rw [Finset.disjoint_left]
  intro p hsym hdiag
  have hne := (Finset.mem_filter.mp hsym).2.1
  obtain ⟨n, hn, hnp⟩ := Finset.mem_image.mp hdiag
  subst p
  exact hne rfl

/-- The inclusive neighbor-pair mass is one diagonal moment plus the existing
off-diagonal neighbor bound. -/
theorem weakNeighbor_tauMass_le (k A H : ℕ) :
    (∑ p ∈ weakNeighborPairs A H,
      tauAF k p.1 * tauAF k p.2) ≤
      (2 * H + 1) * zeroSecondMoment k A := by
  rw [weakNeighborPairs_eq_symmetric_union_diagonal,
    Finset.sum_union (symmetricNeighborPairs_disjoint_diagonalPairs A H)]
  have hdiag :
      (∑ p ∈ diagonalPairs A, tauAF k p.1 * tauAF k p.2) =
        zeroSecondMoment k A := by
    unfold diagonalPairs zeroSecondMoment positiveRange
    rw [Finset.sum_image]
    · simp [pow_two]
    · intro x hx y hy hxy
      exact congrArg Prod.fst hxy
  rw [hdiag]
  calc
    (∑ p ∈ symmetricNeighborPairs A H,
        tauAF k p.1 * tauAF k p.2) + zeroSecondMoment k A ≤
      2 * H * zeroSecondMoment k A + zeroSecondMoment k A :=
        Nat.add_le_add_right (symmetricNeighbor_tauMass_le k A H) _
    _ = (2 * H + 1) * zeroSecondMoment k A := by ring

/-- Ambient equal-short tuples with the sharp long-index floor collar. -/
def equalShortAmbient (M N H : ℕ) : Finset LiteralTuple :=
  (dyadic M).biUnion fun m =>
    (weakNeighborPairs (2 * N) H).image fun p => ((m, m), p)

/-- An exact equal-short Fourier survivor lands in the inclusive long-index
neighbor set at radius `floor(pi*N/T)`. -/
theorem equalShortFrequencySector_subset_ambient
    (M N : ℕ) {T U : ℝ} (hT : 0 < T) :
    equalShortFrequencySector M N
        (Real.pi / (2 * U)) (Real.pi / (2 * T)) ⊆
      equalShortAmbient M N ⌊Real.pi * (N : ℝ) / T⌋₊ := by
  intro q hq
  rcases q with ⟨⟨m₁, m₂⟩, ⟨n₁, n₂⟩⟩
  rcases Finset.mem_filter.mp hq with ⟨hqfreq, hm⟩
  rcases Finset.mem_filter.mp hqfreq with ⟨hqbox, hshort, hjoint⟩
  unfold dyadicTupleBox at hqbox
  have houter := Finset.mem_product.mp hqbox
  have hshortBox := Finset.mem_product.mp houter.1
  have hlongBox := Finset.mem_product.mp houter.2
  rcases hshortBox with ⟨hm₁, hm₂⟩
  rcases hlongBox with ⟨hn₁, hn₂⟩
  change m₁ = m₂ at hm
  subst m₂
  have hlongFreq :
      |Real.log n₂ - Real.log n₁| ≤ Real.pi / (2 * T) := by
    simpa [jointFrequency, shortFrequency] using hjoint
  have hdistReal :
      (n₁.dist n₂ : ℝ) ≤ Real.pi * (N : ℝ) / T :=
    shortFrequency_dist_real_le hn₁ hn₂ hlongFreq
  have hdist : n₁.dist n₂ ≤ ⌊Real.pi * (N : ℝ) / T⌋₊ :=
    Nat.le_floor hdistReal
  apply Finset.mem_biUnion.mpr
  refine ⟨m₁, hm₁, ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨(n₁, n₂), ?_, rfl⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, hdist⟩
  · have hn₁' := hn₁
    simp only [dyadic, Finset.mem_Ioc] at hn₁'
    exact Finset.mem_Icc.mpr ⟨by omega, hn₁'.2⟩
  · have hn₂' := hn₂
    simp only [dyadic, Finset.mem_Ioc] at hn₂'
    exact Finset.mem_Icc.mpr ⟨by omega, hn₂'.2⟩

theorem literalTauMass_equalShortAmbient_le
    (k M N H : ℕ) :
    literalTauMass k (equalShortAmbient M N H) ≤
      M * ((2 * H + 1) * zeroSecondMoment k (2 * N)) := by
  unfold equalShortAmbient literalTauMass
  calc
    (∑ t ∈ (dyadic M).biUnion fun m =>
        (weakNeighborPairs (2 * N) H).image fun p => ((m, m), p),
        tauAF k t.2.1 * tauAF k t.2.2) ≤
      ∑ m ∈ dyadic M,
        ∑ t ∈ (weakNeighborPairs (2 * N) H).image
          (fun p => ((m, m), p)),
          tauAF k t.2.1 * tauAF k t.2.2 :=
        sum_biUnion_le_sum _ _ _
    _ = ∑ _m ∈ dyadic M,
        ∑ p ∈ weakNeighborPairs (2 * N) H,
          tauAF k p.1 * tauAF k p.2 := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.sum_image]
      · intro x hx y hy hxy
        exact congrArg Prod.snd hxy
    _ ≤ ∑ _m ∈ dyadic M,
        ((2 * H + 1) * zeroSecondMoment k (2 * N)) := by
      apply Finset.sum_le_sum
      intro m hm
      exact weakNeighbor_tauMass_le k (2 * N) H
    _ = M * ((2 * H + 1) * zeroSecondMoment k (2 * N)) := by
      have hcard : (dyadic M).card = M := by
        simp only [dyadic, Nat.card_Ioc]
        omega
      simp only [Finset.sum_const, hcard, Nat.nsmul_eq_mul]

/-- Global exact equal-short sector bound.  This is the `UT+UN` arithmetic
piece before replacing the divisor-square moment by its harmonic envelope. -/
theorem equalShortFrequencySector_tauMass_le_secondMoment
    (k M N : ℕ) {T U : ℝ} (hT : 0 < T) :
    weightedMass (tauTupleWeight k)
        (equalShortFrequencySector M N
          (Real.pi / (2 * U)) (Real.pi / (2 * T))) ≤
      (M * ((2 * ⌊Real.pi * (N : ℝ) / T⌋₊ + 1) *
        zeroSecondMoment k (2 * N)) : ℕ) := by
  rw [show weightedMass (tauTupleWeight k)
      (equalShortFrequencySector M N
        (Real.pi / (2 * U)) (Real.pi / (2 * T))) =
      (literalTauMass k
        (equalShortFrequencySector M N
          (Real.pi / (2 * U)) (Real.pi / (2 * T))) : ℝ) by
        unfold weightedMass tauTupleWeight literalTauMass
        push_cast
        rfl]
  exact_mod_cast
    ((Finset.sum_le_sum_of_subset
      (equalShortFrequencySector_subset_ambient M N hT)).trans
        (literalTauMass_equalShortAmbient_le
          k M N ⌊Real.pi * (N : ℝ) / T⌋₊))

/-- Real paper-scale form of the equal-short bound after the certified
divisor-square moment estimate. -/
theorem equalShortFrequencySector_tauMass_le_harmonic
    (k M N : ℕ) {T U : ℝ} (hk : 1 ≤ k) (hT : 0 < T) :
    weightedMass (tauTupleWeight k)
        (equalShortFrequencySector M N
          (Real.pi / (2 * U)) (Real.pi / (2 * T))) ≤
      (2 : ℝ) * M * N *
        (2 * Real.pi * N / T + 1) *
          ((harmonic (2 * N) : ℚ) : ℝ) ^ (k * k - 1) := by
  let H : ℕ := ⌊Real.pi * (N : ℝ) / T⌋₊
  have hfinite := equalShortFrequencySector_tauMass_le_secondMoment
    k M N (U := U) hT
  have hfloor : (H : ℝ) ≤ Real.pi * (N : ℝ) / T := by
    dsimp [H]
    exact Nat.floor_le (by positivity)
  have hmomentQ := zeroSecondMoment_cast_le_harmonic k (2 * N) hk
  have hmomentR :
      (zeroSecondMoment k (2 * N) : ℝ) ≤
        (2 * N : ℝ) *
          ((harmonic (2 * N) : ℚ) : ℝ) ^ (k * k - 1) := by
    exact_mod_cast hmomentQ
  calc
    weightedMass (tauTupleWeight k)
        (equalShortFrequencySector M N
          (Real.pi / (2 * U)) (Real.pi / (2 * T))) ≤
      (M * ((2 * H + 1) * zeroSecondMoment k (2 * N)) : ℕ) := by
        simpa [H] using hfinite
    _ = (M : ℝ) * (2 * (H : ℝ) + 1) *
        (zeroSecondMoment k (2 * N) : ℝ) := by
      push_cast
      ring
    _ ≤ (M : ℝ) * (2 * (Real.pi * (N : ℝ) / T) + 1) *
        ((2 * N : ℝ) *
          ((harmonic (2 * N) : ℚ) : ℝ) ^ (k * k - 1)) := by
      gcongr
    _ = (2 : ℝ) * M * N * (2 * Real.pi * N / T + 1) *
        ((harmonic (2 * N) : ℚ) : ℝ) ^ (k * k - 1) := by ring

/-- The exact contribution of the equal-short sector after the already
certified harmonic and coefficient prefactor.  It is the manuscript's
`UT+UN` term, with constants exposed. -/
theorem equalShort_paper_prefactor_bound
    (a k M N : ℕ) {T U : ℝ}
    (hk : 1 ≤ k) (hM : 0 < M) (hN : 0 < N)
    (hT : 0 < T) (hU : 0 < U) :
    256 * T * U *
        (Real.log (2 * (M : ℝ) * (N : ℝ)) ^ (4 * a) /
          ((M : ℝ) * (N : ℝ))) *
      weightedMass (tauTupleWeight k)
        (equalShortFrequencySector M N
          (Real.pi / (2 * U)) (Real.pi / (2 * T))) ≤
      512 * (U * T + 2 * Real.pi * U * N) *
        Real.log (2 * (M : ℝ) * (N : ℝ)) ^ (4 * a) *
          ((harmonic (2 * N) : ℚ) : ℝ) ^ (k * k - 1) := by
  let L4 := Real.log (2 * (M : ℝ) * (N : ℝ)) ^ (4 * a)
  let HN := ((harmonic (2 * N) : ℚ) : ℝ) ^ (k * k - 1)
  have hmass := equalShortFrequencySector_tauMass_le_harmonic
    k M N (U := U) hk hT
  have hL4 : 0 ≤ L4 := by
    dsimp [L4]
    rw [show 4 * a = a * 4 by omega, pow_mul]
    positivity
  have hpref : 0 ≤ 256 * T * U *
      (L4 / ((M : ℝ) * (N : ℝ))) := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hT.le) hU.le)
      (div_nonneg hL4 (by positivity))
  calc
    256 * T * U * (L4 / ((M : ℝ) * (N : ℝ))) *
        weightedMass (tauTupleWeight k)
          (equalShortFrequencySector M N
            (Real.pi / (2 * U)) (Real.pi / (2 * T))) ≤
      256 * T * U * (L4 / ((M : ℝ) * (N : ℝ))) *
        ((2 : ℝ) * M * N * (2 * Real.pi * N / T + 1) * HN) := by
          exact mul_le_mul_of_nonneg_left hmass hpref
    _ = 512 * (U * T + 2 * Real.pi * U * N) * L4 * HN := by
      have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
      have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      field_simp [hMr, hNr, hT.ne']
      ring

/-! ## Exact zero-sector import into the four-sector sum -/

/-- The exact unequal-short zero-frequency survivors lie in the certified
floor-collar zero sector. -/
theorem zeroFrequencySector_subset_floorZeroSector
    (M N : ℕ) {T U : ℝ} (hT : 0 < T) (hU : 0 < U) :
    zeroFrequencySector M N
        (Real.pi / (2 * U)) (Real.pi / (2 * T)) ⊆
      zeroSector M N (shortFloorCollar M U)
        (productFloorCollar M N T) := by
  intro q hq
  rcases Finset.mem_filter.mp hq with ⟨hqfreq, hne, hdet⟩
  have hqExact : q ∈ exactFrequencySurvivors M N T U := hqfreq
  have hcollars := exactFrequencySurvivor_mem_floorCollars hT hU hqExact
  have hbox := (Finset.mem_filter.mp hqfreq).1
  unfold zeroSector literalTuples
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_filter.mpr ⟨?_, hne, hcollars.1, ?_⟩, hdet⟩
  · exact hbox
  · simp [hdet]

/-- The main map's certified global zero-sector theorem, pulled back to the
exact Fourier survivor sector and cast to the frontend's real weight. -/
theorem zeroFrequencySector_tauMass_le_harmonic
    (k M N : ℕ) {T U : ℝ}
    (hk : 1 ≤ k) (hM : 0 < M) (hT : 0 < T) (hU : 0 < U) :
    weightedMass (tauTupleWeight k)
        (zeroFrequencySector M N
          (Real.pi / (2 * U)) (Real.pi / (2 * T))) ≤
      (8 * N * shortFloorCollar M U : ℕ) *
        ((harmonic (shortFloorCollar M U) : ℚ) : ℝ) *
        ((harmonic (2 * N) : ℚ) : ℝ) ^ (k * k - 1) *
        ((harmonic (2 * M) : ℚ) : ℝ) ^ (k * k - 1) := by
  let K := shortFloorCollar M U
  let Y := productFloorCollar M N T
  have hsubset := zeroFrequencySector_subset_floorZeroSector M N hT hU
  have hnat :
      literalTauMass k
          (zeroFrequencySector M N
            (Real.pi / (2 * U)) (Real.pi / (2 * T))) ≤
        literalTauMass k (zeroSector M N K Y) :=
    Finset.sum_le_sum_of_subset hsubset
  have hzeroQ := zeroSector_tauMass_paper_bound k M N K Y hk hM
  calc
    weightedMass (tauTupleWeight k)
        (zeroFrequencySector M N
          (Real.pi / (2 * U)) (Real.pi / (2 * T))) =
      (literalTauMass k
        (zeroFrequencySector M N
          (Real.pi / (2 * U)) (Real.pi / (2 * T))) : ℝ) := by
        unfold weightedMass tauTupleWeight literalTauMass
        push_cast
        rfl
    _ ≤ (literalTauMass k (zeroSector M N K Y) : ℝ) := by
      exact_mod_cast hnat
    _ ≤ (8 * N * K : ℕ) * ((harmonic K : ℚ) : ℝ) *
        ((harmonic (2 * N) : ℚ) : ℝ) ^ (k * k - 1) *
        ((harmonic (2 * M) : ℚ) : ℝ) ^ (k * k - 1) := by
      exact_mod_cast hzeroQ
    _ = _ := by rfl

/-- After the harmonic/coefficient prefactor, the certified zero sector is
an explicit multiple of the manuscript's `T` term. -/
theorem zeroSector_paper_prefactor_bound
    (a k M N : ℕ) {T U : ℝ}
    (hk : 1 ≤ k) (hM : 0 < M) (hN : 0 < N)
    (hT : 0 < T) (hU : 0 < U) :
    256 * T * U *
        (Real.log (2 * (M : ℝ) * (N : ℝ)) ^ (4 * a) /
          ((M : ℝ) * (N : ℝ))) *
      weightedMass (tauTupleWeight k)
        (zeroFrequencySector M N
          (Real.pi / (2 * U)) (Real.pi / (2 * T))) ≤
      2048 * Real.pi * T *
        Real.log (2 * (M : ℝ) * (N : ℝ)) ^ (4 * a) *
        ((harmonic (shortFloorCollar M U) : ℚ) : ℝ) *
        ((harmonic (2 * N) : ℚ) : ℝ) ^ (k * k - 1) *
        ((harmonic (2 * M) : ℚ) : ℝ) ^ (k * k - 1) := by
  let L4 := Real.log (2 * (M : ℝ) * (N : ℝ)) ^ (4 * a)
  let HK := ((harmonic (shortFloorCollar M U) : ℚ) : ℝ)
  let HN := ((harmonic (2 * N) : ℚ) : ℝ) ^ (k * k - 1)
  let HM := ((harmonic (2 * M) : ℚ) : ℝ) ^ (k * k - 1)
  have hmass := zeroFrequencySector_tauMass_le_harmonic
    k M N hk hM hT hU
  have hL4 : 0 ≤ L4 := by
    dsimp [L4]
    rw [show 4 * a = a * 4 by omega, pow_mul]
    positivity
  have hpref : 0 ≤ 256 * T * U *
      (L4 / ((M : ℝ) * (N : ℝ))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hT.le) hU.le)
      (div_nonneg hL4 (by positivity))
  have hK := shortFloorCollar_cast_le M hU
  have hHK0 : 0 ≤ HK := by
    dsimp [HK]
    exact_mod_cast
      (show (0 : ℚ) ≤ harmonic (shortFloorCollar M U) by
        have hz := harmonic_mono (x := 0)
          (y := shortFloorCollar M U) (Nat.zero_le _)
        simpa using hz)
  have hHN0 : 0 ≤ HN := by
    dsimp [HN]
    exact pow_nonneg (by
      exact_mod_cast
        (show (0 : ℚ) ≤ harmonic (2 * N) by
          have hz := harmonic_mono (x := 0) (y := 2 * N) (Nat.zero_le _)
          simpa using hz)) _
  have hHM0 : 0 ≤ HM := by
    dsimp [HM]
    exact pow_nonneg (by
      exact_mod_cast
        (show (0 : ℚ) ≤ harmonic (2 * M) by
          have hz := harmonic_mono (x := 0) (y := 2 * M) (Nat.zero_le _)
          simpa using hz)) _
  have htail0 : 0 ≤ HK * HN * HM := by
    positivity
  calc
    256 * T * U * (L4 / ((M : ℝ) * (N : ℝ))) *
        weightedMass (tauTupleWeight k)
          (zeroFrequencySector M N
            (Real.pi / (2 * U)) (Real.pi / (2 * T))) ≤
      256 * T * U * (L4 / ((M : ℝ) * (N : ℝ))) *
        ((8 * N * shortFloorCollar M U : ℕ) * HK * HN * HM) := by
          exact mul_le_mul_of_nonneg_left hmass hpref
    _ ≤ 256 * T * U * (L4 / ((M : ℝ) * (N : ℝ))) *
        ((8 : ℝ) * N * (Real.pi * M / U) * HK * HN * HM) := by
      apply mul_le_mul_of_nonneg_left _ hpref
      have hKscaled :
          ((8 * N * shortFloorCollar M U : ℕ) : ℝ) ≤
            (8 : ℝ) * N * (Real.pi * M / U) := by
        push_cast
        exact mul_le_mul_of_nonneg_left hK (by positivity)
      calc
        ((8 * N * shortFloorCollar M U : ℕ) : ℝ) * HK * HN * HM =
            ((8 * N * shortFloorCollar M U : ℕ) : ℝ) * (HK * HN * HM) := by
              ring
        _ ≤ ((8 : ℝ) * N * (Real.pi * M / U)) * (HK * HN * HM) :=
          mul_le_mul_of_nonneg_right hKscaled htail0
        _ = (8 : ℝ) * N * (Real.pi * M / U) * HK * HN * HM := by ring
    _ = 2048 * Real.pi * T * L4 * HK * HN * HM := by
      have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
      have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      field_simp [hMr, hNr, hU.ne']
      ring

end MAPMixedMeanCompletion
