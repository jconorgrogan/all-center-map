import MRTCorollary25CarrierIntegral

/-!
# Full raw-prefix Perron inequality behind MRT Corollary 2.5
-/

namespace MAPMRTCorollary25RawPrefixFormula

open scoped BigOperators
open MAPMRTCorollary25 MAPMRTCorollary25PerronCore
open MAPMRTCorollary25RawPrefix MAPMRTCorollary25RawPrefixEstimate
open MAPMRTCorollary25CarrierIntegral
open MixedMeanFrontend PrimitiveTruncatedExplicitFormulaBridge

noncomputable section

/-- The exact raw-prefix inequality obtained by welding the certified carrier
integral to the certified transition-band sum. -/
theorem norm_rawPrefixOn_le_sourcePerron
    {C X T B t : ℝ} (hC : 1 < C) (hX : 1 ≤ X) (hT : 1 ≤ T)
    (hB : 0 ≤ B) {f : ℕ → ℂ} (hSupp : SupportedNear X C f)
    (hf : ∀ n : ℕ, ‖f n‖ ≤ B)
    {N : ℕ} (hN : N ≤ Nat.ceil (C * X)) :
    ‖rawPrefixOn (Finset.Icc 1 (Nat.ceil (C * X))) N f t‖ ≤
      3 * Real.sqrt ((C + 2) * X) *
        (∫ u in (-T)..T,
          ‖halfLineDirichletPolynomial X C f (t + u)‖ / (1 + |u|)) +
      24 * (1 + Real.sqrt (C * (C + 2))) * (C + 2) *
        B * X * (1 + Real.log (2 + T)) / T := by
  let S := Finset.Icc 1 (Nat.ceil (C * X))
  have hS : ∀ n ∈ S, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  have hkernel := norm_kernelPrefixOn_le_criticalIntegral
    S N f t (by linarith : 0 ≤ T) hS
  have herr := norm_rawPrefixOn_sub_kernelPrefixOn_le_sourceScale
    hC hX hT hB hSupp hf hN (t := t)
  have hxBound := halfInteger_prefix_le_supportScale hC hX hN
  have hsqrt : Real.sqrt (halfIntegerPoint N) ≤ Real.sqrt ((C + 2) * X) :=
    Real.sqrt_le_sqrt hxBound
  have hInt0 : 0 ≤
      ∫ u in (-T)..T,
        ‖halfLineDirichletPolynomial X C f (t + u)‖ / (1 + |u|) := by
    apply intervalIntegral.integral_nonneg (by linarith)
    intro u hu
    positivity
  have hkernel' :
      ‖kernelPrefixOn S N f t (1 / 2 : ℝ) T‖ ≤
        3 * Real.sqrt ((C + 2) * X) *
          (∫ u in (-T)..T,
            ‖halfLineDirichletPolynomial X C f (t + u)‖ / (1 + |u|)) := by
    have hpoly : finiteHalfLinePolynomial S f =
        halfLineDirichletPolynomial X C f := rfl
    rw [hpoly] at hkernel
    exact hkernel.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsqrt (by norm_num)) hInt0)
  calc
    ‖rawPrefixOn S N f t‖ ≤
        ‖kernelPrefixOn S N f t (1 / 2 : ℝ) T‖ +
          ‖rawPrefixOn S N f t -
            kernelPrefixOn S N f t (1 / 2 : ℝ) T‖ := by
      have h := norm_add_le
        (kernelPrefixOn S N f t (1 / 2 : ℝ) T)
        (rawPrefixOn S N f t - kernelPrefixOn S N f t (1 / 2 : ℝ) T)
      convert h using 1 <;> ring
    _ ≤ _ := add_le_add hkernel' herr

end
end MAPMRTCorollary25RawPrefixFormula

#print axioms MAPMRTCorollary25RawPrefixFormula.norm_rawPrefixOn_le_sourcePerron
