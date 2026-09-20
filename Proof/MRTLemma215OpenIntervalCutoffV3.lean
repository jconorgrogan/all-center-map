import MRTLemma215DynamicClassificationV3

/-!
# Exact open-left source cutoff

The MAP source is supported on `(X,2X]`, while MRT Corollary 2.5 accepts an
arbitrary closed real cutoff `[X1,X2]`.  Taking `X1 = floor(X)+1` represents
the source mask literally, including when `X` is an integer.  Thus no endpoint
atom is silently added and no artificial boundary error is needed.
-/

namespace MRTLemma215OpenIntervalCutoffV3

open MAPMRTCorollary25
open MAPHBPerronSourceData MAPDynamicHBSourceV3
open MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MRTLemma215DynamicPreliminaryV3 MRTLemma215DynamicFactorExtractionV3
open MRTLemma215DynamicClassificationV3

noncomputable section

/-- The exact closed interval representing the integer points in `(X,2X]`. -/
def openSourceLeft (X : ℝ) : ℝ := (⌊X⌋₊ : ℝ) + 1

theorem mem_Ioc_floor_iff_closed_openSourceLeft
    {X : ℝ} (hX : 0 ≤ X) (n : ℕ) :
    n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊ ↔
      openSourceLeft X ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * X := by
  rw [Finset.mem_Ioc]
  constructor
  · intro hn
    constructor
    · unfold openSourceLeft
      exact_mod_cast hn.1
    · have htwoX : 0 ≤ 2 * X := by positivity
      have hnFloor : (n : ℝ) ≤ (⌊2 * X⌋₊ : ℝ) := by exact_mod_cast hn.2
      exact hnFloor.trans (Nat.floor_le htwoX)
  · intro hn
    constructor
    · unfold openSourceLeft at hn
      have hcast : ((⌊X⌋₊ : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by
        simpa using hn.1
      exact_mod_cast hcast
    · have htwoX : 0 ≤ 2 * X := by positivity
      have hnFloor : n ≤ ⌊2 * X⌋₊ := Nat.le_floor hn.2
      exact hnFloor

/-- Any open-left source mask is exactly an MRT closed cutoff after shifting
the real left endpoint to `floor(X)+1`. -/
theorem openMask_eq_intervalCutoff
    {X : ℝ} (hX : 0 ≤ X) (f : ℕ → ℂ) :
    (fun n ↦ if n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊ then f n else 0) =
      intervalCutoff (openSourceLeft X) (2 * X) f := by
  funext n
  unfold intervalCutoff
  by_cases hn : n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊
  · have hn' := (mem_Ioc_floor_iff_closed_openSourceLeft hX n).mp hn
    simp [hn, hn']
  · have hn' := not_congr (mem_Ioc_floor_iff_closed_openSourceLeft hX n) |>.mp hn
    simp [hn, hn']

theorem maskedDynamicComponentV3_eq_intervalCutoff
    {X : ℝ} (hX : 0 ≤ X) {K k : ℕ}
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1)) :
    maskedDynamicComponentV3 logIndex zbag mbag =
      intervalCutoff (openSourceLeft X) (2 * X)
        (dynamicPreliminaryComponent (some logIndex) zbag mbag) := by
  exact openMask_eq_intervalCutoff hX _

end
end MRTLemma215OpenIntervalCutoffV3

#print axioms MRTLemma215OpenIntervalCutoffV3.mem_Ioc_floor_iff_closed_openSourceLeft
#print axioms MRTLemma215OpenIntervalCutoffV3.openMask_eq_intervalCutoff
#print axioms MRTLemma215OpenIntervalCutoffV3.maskedDynamicComponentV3_eq_intervalCutoff
