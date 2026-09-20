import GuthMaynardLemma295RawHorizontalIntegral
import GuthMaynardLemma295ExactMScale

/-!
# Exact-source-scale horizontal edges for Lemma 29.5

These are interface specializations of the certified horizontal-edge limits at
the literal source choice `M = T^(1+epsilon)/N`, `K = floor M`.
-/

namespace GuthMaynardLemma295ExactMHorizontal

open Complex Real Set Filter Topology
open GuthMaynardJutilaReflection2941
open GuthMaynardLemma295DualTail
open GuthMaynardLemma295FiniteContour
open GuthMaynardLemma295ReflectedFiniteContour
open GuthMaynardLemma295HorizontalIntegral
open GuthMaynardLemma295RawHorizontalIntegral

noncomputable section

/-- Upper reflected horizontal edge at the exact source truncation. -/
theorem tendsto_exactM_reflectedFinite_horizontalIntegral_zero
    {T epsilon N : ℝ} (hN : 0 < N) (g : ℝ) (n : ℕ) :
    Tendsto (fun B : ℝ =>
      ∫ x : ℝ in deepLeftSigma n..(1 / 2),
        lemma295ReflectedFiniteIntegrand N g
          ⌊reflectedLength29_40 T epsilon N⌋₊
          ((x : ℂ) + B * I))
      atTop (𝓝 0) := by
  exact tendsto_lemma295ReflectedFinite_horizontalIntegral_zero
    hN g ⌊reflectedLength29_40 T epsilon N⌋₊ n

/-- Lower reflected horizontal edge at the exact source truncation. -/
theorem tendsto_exactM_reflectedFinite_lowerHorizontalIntegral_zero
    {T epsilon N : ℝ} (hN : 0 < N) (g : ℝ) (n : ℕ) :
    Tendsto (fun B : ℝ =>
      ∫ x : ℝ in deepLeftSigma n..(1 / 2),
        lemma295ReflectedFiniteIntegrand N g
          ⌊reflectedLength29_40 T epsilon N⌋₊
          ((x : ℂ) + (-B) * I))
      atTop (𝓝 0) := by
  exact tendsto_lemma295ReflectedFinite_lowerHorizontalIntegral_zero
    hN g ⌊reflectedLength29_40 T epsilon N⌋₊ n

/-- Upper raw horizontal edge in the same exact-source-scale interface. -/
theorem tendsto_exactM_raw_horizontalIntegral_zero
    {N : ℝ} (hN : 0 < N) (g : ℝ) (n : ℕ) :
    Tendsto (fun B : ℝ =>
      ∫ x : ℝ in deepLeftSigma n..2,
        lemma295RawIntegrand N g ((x : ℂ) + B * I))
      atTop (𝓝 0) := by
  exact tendsto_lemma295Raw_horizontalIntegral_zero hN g n

/-- Lower raw horizontal edge in the same exact-source-scale interface. -/
theorem tendsto_exactM_raw_lowerHorizontalIntegral_zero
    {N : ℝ} (hN : 0 < N) (g : ℝ) (n : ℕ) :
    Tendsto (fun B : ℝ =>
      ∫ x : ℝ in deepLeftSigma n..2,
        lemma295RawIntegrand N g ((x : ℂ) + (-B) * I))
      atTop (𝓝 0) := by
  exact tendsto_lemma295Raw_lowerHorizontalIntegral_zero hN g n

end
end GuthMaynardLemma295ExactMHorizontal

#print axioms GuthMaynardLemma295ExactMHorizontal.tendsto_exactM_reflectedFinite_horizontalIntegral_zero
#print axioms GuthMaynardLemma295ExactMHorizontal.tendsto_exactM_reflectedFinite_lowerHorizontalIntegral_zero
#print axioms GuthMaynardLemma295ExactMHorizontal.tendsto_exactM_raw_horizontalIntegral_zero
#print axioms GuthMaynardLemma295ExactMHorizontal.tendsto_exactM_raw_lowerHorizontalIntegral_zero
