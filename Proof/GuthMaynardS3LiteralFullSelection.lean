import GuthMaynardS3LiteralBalancedSectorGeometry
import GuthMaynardS3LiteralActualSixSectorBound

namespace GuthMaynardS3LiteralFullSelection

open scoped BigOperators
open GuthMaynardS3LiteralBalancedSectorGeometry
open GuthMaynardS3LiteralActualSixSectorBound
open GuthMaynardS3LiteralTruncation
open GuthMaynardEquation55Infinite
open GuthMaynardEquation55Split
open GuthMaynardS3LiteralGlobalReduction
open GuthMaynardS3LiteralDyadicBlock
open GuthMaynardS3LiteralRadialDecay
open GuthMaynardS3LiteralAffineReduction
open GuthMaynardS3LiteralLocalization

noncomputable section

/-- A triple is balanced when it belongs to one of the finitely many ordered
six-sector blocks.  The geometry module proves this predicate from the
sorted inequalities and `|m₃| ≤ 5|m₂|`. -/
def balancedCube (Mcut : ℕ) : Finset Frequency :=
  (prefixFrequencyCube Mcut).filter fun p =>
    ∃ i ∈ dyadicExponents Mcut, ∃ k ∈ dyadicExponents Mcut,
      ∃ d ∈ Finset.range 4, p ∈ sixSectorUnion Mcut i k d

def sixSectorKeysUnion (Mcut : ℕ) : Finset Frequency :=
  (orderedBalancedKeys Mcut).biUnion fun key =>
    sixSectorUnion Mcut key.1.1 key.1.2 key.2

theorem balancedCube_subset_sixSectorKeysUnion (Mcut : ℕ) :
    balancedCube Mcut ⊆ sixSectorKeysUnion Mcut := by
  intro p hp
  obtain ⟨hpCube, i, hi, k, hk, d, hd, hpSector⟩ :=
    Finset.mem_filter.mp hp
  exact Finset.mem_biUnion.mpr
    ⟨((i, k), d), by simp [orderedBalancedKeys, hi, hk, hd], hpSector⟩

theorem sixSectorKeysUnion_sum_norm_le_sum_keys (N : ℕ) (W : Finset ℝ)
    (Mcut : ℕ) :
    (∑ p ∈ sixSectorKeysUnion Mcut, f N W p) ≤
      ∑ key ∈ orderedBalancedKeys Mcut,
        ∑ p ∈ sixSectorUnion Mcut key.1.1 key.1.2 key.2, f N W p := by
  have hnonneg : ∀ p, 0 ≤ f N W p := fun p => norm_nonneg _
  exact sum_biUnion_le_sum_nonneg _ _ _ hnonneg

theorem balancedCube_sum_norm_le_sum_keys (N : ℕ) (W : Finset ℝ)
    (Mcut : ℕ) :
    (∑ p ∈ balancedCube Mcut, f N W p) ≤
      ∑ key ∈ orderedBalancedKeys Mcut,
        ∑ p ∈ sixSectorUnion Mcut key.1.1 key.1.2 key.2, f N W p := by
  have hnonneg : ∀ p, 0 ≤ f N W p := fun p => norm_nonneg _
  have hsubset := Finset.sum_le_sum_of_subset_of_nonneg
    (balancedCube_subset_sixSectorKeysUnion Mcut)
    (fun p _ _ => hnonneg p)
  exact hsubset.trans (sixSectorKeysUnion_sum_norm_le_sum_keys N W Mcut)

theorem sixSectorKeys_sum_norm_le_six_sum_blocks (N : ℕ) (W : Finset ℝ)
    (Mcut : ℕ) :
    (∑ key ∈ orderedBalancedKeys Mcut,
      ∑ p ∈ sixSectorUnion Mcut key.1.1 key.1.2 key.2, f N W p) ≤
      6 * (∑ key ∈ orderedBalancedKeys Mcut,
        ∑ p ∈ orderedBalancedBlock Mcut key.1.1 key.1.2 key.2, f N W p) := by
  have hpoint : ∀ key ∈ orderedBalancedKeys Mcut,
      (∑ p ∈ sixSectorUnion Mcut key.1.1 key.1.2 key.2, f N W p) ≤
        6 * (∑ p ∈ orderedBalancedBlock Mcut key.1.1 key.1.2 key.2, f N W p) := by
    intro key hkey
    exact sum_norm_sixSectorUnion_actual N W Mcut key.1.1 key.1.2 key.2
  calc
    _ ≤ ∑ key ∈ orderedBalancedKeys Mcut,
        6 * (∑ p ∈ orderedBalancedBlock Mcut key.1.1 key.1.2 key.2, f N W p) :=
      Finset.sum_le_sum hpoint
    _ = _ := by rw [Finset.mul_sum]

theorem exists_max_orderedBalancedBlockNorm (N : ℕ) (W : Finset ℝ)
    (Mcut : ℕ) :
    ∃ i ∈ dyadicExponents Mcut, ∃ k ∈ dyadicExponents Mcut,
      ∃ d ∈ Finset.range 4,
        ∀ i' ∈ dyadicExponents Mcut, ∀ k' ∈ dyadicExponents Mcut,
          ∀ d' ∈ Finset.range 4,
            (∑ p ∈ orderedBalancedBlock Mcut i' k' d', f N W p) ≤
              (∑ p ∈ orderedBalancedBlock Mcut i k d, f N W p) := by
  obtain ⟨key, hkey, hmax⟩ :=
    Finset.exists_max_image (orderedBalancedKeys Mcut)
      (fun key => ∑ p ∈ orderedBalancedBlock Mcut key.1.1 key.1.2 key.2,
        f N W p)
      (orderedBalancedKeys_nonempty Mcut)
  refine ⟨key.1.1, ?_, key.1.2, ?_, key.2, ?_, ?_⟩
  · exact (Finset.mem_product.mp (Finset.mem_product.mp hkey).1).1
  · exact (Finset.mem_product.mp (Finset.mem_product.mp hkey).1).2
  · exact (Finset.mem_product.mp hkey).2
  · intro i' hi' k' hk' d' hd'
    exact hmax ((i', k'), d') (by simp [orderedBalancedKeys, hi', hk', hd'])

theorem orderedBalancedBlock_norm_le_affine_add_tail {N : ℕ}
    (hN : 0 < N) {rho : ℝ} (hrho : 0 < rho) (W : Finset ℝ)
    (Mcut i k d q : ℕ) :
    (∑ p ∈ orderedBalancedBlock Mcut i k d, f N W p) ≤
      orderedBalancedBlockAffine N W rho Mcut i k d +
        ((orderedBalancedBlock Mcut i k d).card : ℝ) *
          ((9 / 4 : ℝ) * (N : ℝ) ^ 3 * radialDerivativeBudget q *
            (W.card : ℝ) ^ 3 / rho ^ q) := by
  have hpoint : ∀ p ∈ orderedBalancedBlock Mcut i k d,
      f N W p ≤
        (16 * radialDerivativeBudget 0 * rho * (N : ℝ) ^ 2 / (2 ^ k : ℝ)) *
          affineProfileIntegral ((N : ℝ) * (2 ^ k : ℝ) / (4 * rho)) W
            p.1.1 p.1.2 p.2 +
          ((9 / 4 : ℝ) * (N : ℝ) ^ 3 * radialDerivativeBudget q *
            (W.card : ℝ) ^ 3 / rho ^ q) := by
    intro p hp
    have h := (Finset.mem_filter.mp hp).2
    have hlo : (2 ^ k : ℝ) ≤ |(p.1.2 : ℝ)| := h.2.2.1
    have hhi : |(p.1.2 : ℝ)| ≤ 2 * (2 ^ k : ℝ) := h.2.2.2.1
    exact norm_sourceIm_le_common_profile hN (by positivity) hrho W
      p.1.1 p.1.2 p.2 hlo hhi q
  calc
    _ ≤ ∑ p ∈ orderedBalancedBlock Mcut i k d,
        ((16 * radialDerivativeBudget 0 * rho * (N : ℝ) ^ 2 / (2 ^ k : ℝ)) *
          affineProfileIntegral ((N : ℝ) * (2 ^ k : ℝ) / (4 * rho)) W
            p.1.1 p.1.2 p.2 +
          ((9 / 4 : ℝ) * (N : ℝ) ^ 3 * radialDerivativeBudget q *
            (W.card : ℝ) ^ 3 / rho ^ q)) := Finset.sum_le_sum hpoint
    _ = _ := by
      unfold orderedBalancedBlockAffine
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp [Finset.sum_const, nsmul_eq_mul]

theorem norm_sourceS3Prefix_le_selected_block
    {N : ℕ} (hN : 0 < N) (W : Finset ℝ) (Mcut : ℕ)
    {rho : ℝ} (hrho : 0 < rho) (q : ℕ)
    (hunbal : ∀ p ∈ prefixFrequencyCube Mcut, p ∉ balancedCube Mcut →
      f N W p ≤ (9 / 4 : ℝ) * (N : ℝ) ^ 3 * radialDerivativeBudget q *
        (W.card : ℝ) ^ 3 / rho ^ q) :
    ∃ i ∈ dyadicExponents Mcut, ∃ k ∈ dyadicExponents Mcut,
      ∃ d ∈ Finset.range 4,
        ‖sourceS3Prefix N Mcut W‖ ≤
          6 * ((orderedBalancedKeys Mcut).card : ℝ) *
            (∑ p ∈ orderedBalancedBlock Mcut i k d, f N W p) +
          ((prefixFrequencyCube Mcut).card : ℝ) *
            ((9 / 4 : ℝ) * (N : ℝ) ^ 3 * radialDerivativeBudget q *
              (W.card : ℝ) ^ 3 / rho ^ q) := by
  obtain ⟨i, hi, k, hk, d, hd, hmax⟩ :=
    exists_max_orderedBalancedBlockNorm N W Mcut
  refine ⟨i, hi, k, hk, d, hd, ?_⟩
  let tail : ℝ := (9 / 4 : ℝ) * (N : ℝ) ^ 3 * radialDerivativeBudget q *
      (W.card : ℝ) ^ 3 / rho ^ q
  have hfinite := sourceS3Prefix_eq_finite_frequency_block N Mcut W
  rw [hfinite]
  have hnorm := norm_sum_le (prefixFrequencyCube Mcut) (fun p =>
    if exactlyThreeNonzero p.1.1 p.1.2 p.2 then frequencyTerm N W p else 0)
  have hsplit :
      (∑ p ∈ prefixFrequencyCube Mcut,
        ‖if exactlyThreeNonzero p.1.1 p.1.2 p.2 then frequencyTerm N W p else 0‖) ≤
      (∑ p ∈ balancedCube Mcut, f N W p) +
        ((prefixFrequencyCube Mcut).card : ℝ) * tail := by
    have htail0 : 0 ≤ tail := by
      dsimp [tail]
      have hC := radialDerivativeBudget_nonneg q
      positivity
    calc
      _ ≤ ∑ p ∈ prefixFrequencyCube Mcut,
          ((if p ∈ balancedCube Mcut then f N W p else 0) + tail) := by
        apply Finset.sum_le_sum
        intro p hp
        by_cases hb : p ∈ balancedCube Mcut
        · rw [if_pos hb]
          have hmask : exactlyThreeNonzero p.1.1 p.1.2 p.2 := by
            obtain ⟨hbase, _⟩ := Finset.mem_filter.mp hb
            obtain ⟨h12, h3⟩ := Finset.mem_product.mp hbase
            obtain ⟨h1, h2⟩ := Finset.mem_product.mp h12
            exact ⟨nonzeroPrefix_ne_zero h1, nonzeroPrefix_ne_zero h2,
              nonzeroPrefix_ne_zero h3⟩
          rw [if_pos hmask]
          exact le_add_of_nonneg_right htail0
        · simp only [hb, if_false]
          by_cases hm : exactlyThreeNonzero p.1.1 p.1.2 p.2
          · simp only [hm, if_pos]
            simpa [tail] using hunbal p hp hb
          · simp only [hm, if_neg]
            simpa using htail0
      _ = (∑ p ∈ balancedCube Mcut, f N W p) +
          ((prefixFrequencyCube Mcut).card : ℝ) * tail := by
        rw [Finset.sum_add_distrib]
        have hfilter :
            (∑ p ∈ prefixFrequencyCube Mcut,
              if p ∈ balancedCube Mcut then f N W p else 0) =
              ∑ p ∈ balancedCube Mcut, f N W p := by
          have hset :
              (prefixFrequencyCube Mcut).filter (fun p => p ∈ balancedCube Mcut) =
                balancedCube Mcut := by
            apply Finset.Subset.antisymm
            · intro p hp
              exact (Finset.mem_filter.mp hp).2
            · intro p hp
              apply Finset.mem_filter.mpr
              exact ⟨(Finset.mem_filter.mp hp).1, hp⟩
          rw [← Finset.sum_filter, hset]
        rw [hfilter]
        simp [Finset.sum_const, nsmul_eq_mul]
  have hnorm' := hnorm.trans hsplit
  have hbal := balancedCube_sum_norm_le_sum_keys N W Mcut
  have hsector := sixSectorKeys_sum_norm_le_six_sum_blocks N W Mcut
  have hmaxsum :
      (∑ key ∈ orderedBalancedKeys Mcut,
        ∑ p ∈ orderedBalancedBlock Mcut key.1.1 key.1.2 key.2, f N W p) ≤
      ((orderedBalancedKeys Mcut).card : ℝ) *
        (∑ p ∈ orderedBalancedBlock Mcut i k d, f N W p) := by
    have hpoint : ∀ key ∈ orderedBalancedKeys Mcut,
        (∑ p ∈ orderedBalancedBlock Mcut key.1.1 key.1.2 key.2, f N W p) ≤
          (∑ p ∈ orderedBalancedBlock Mcut i k d, f N W p) := by
      intro key hkey
      obtain ⟨⟨i', k'⟩, d'⟩ := key
      exact hmax i' ((Finset.mem_product.mp (Finset.mem_product.mp hkey).1).1)
        k' ((Finset.mem_product.mp (Finset.mem_product.mp hkey).1).2)
        d' ((Finset.mem_product.mp hkey).2)
    apply (Finset.sum_le_sum hpoint).trans
    simp [Finset.sum_const, nsmul_eq_mul]
  have hmaxsum6 := mul_le_mul_of_nonneg_left hmaxsum (by positivity : (0 : ℝ) ≤ 6)
  have hkeys := hbal.trans (hsector.trans hmaxsum6)
  have htotal := hnorm'.trans (add_le_add_left hkeys _)
  calc
    ‖∑ p ∈ prefixFrequencyCube Mcut,
        if exactlyThreeNonzero p.1.1 p.1.2 p.2 then frequencyTerm N W p else 0‖ ≤
      6 * ((orderedBalancedKeys Mcut).card : ℝ) *
          (∑ p ∈ orderedBalancedBlock Mcut i k d, f N W p) +
        ((prefixFrequencyCube Mcut).card : ℝ) * tail := by
      simpa [mul_assoc] using htotal

end
end GuthMaynardS3LiteralFullSelection
