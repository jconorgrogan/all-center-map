import MRTProposition61TypeIIFullNormWeldV3
import MRTLemma215DynamicPacketComponentIntegralV3
import MAPDynamicHBCanonicalPerronConstantV3

/-!
# One literal masked Type-II cell through Corollary 2.5 and Lemma 2.10

This is the local analytic weld missing between dynamic Type-II packetization
and the final finite packet/logarithm absorption.  The certified Perron error
is displayed rather than hidden.
-/

namespace MRTProposition61TypeIICellWeldV3

open scoped BigOperators
open MeasureTheory
open MontgomeryVaughanFiniteReduction
open MAPMRTCorollary25 MAPMRTCorollary25Instantiation
open MAPMRTCorollary25TypeD1LiteralWeld
open MAPMRTCorollary25TypeD1IntegratedWeld
open MAPMRTCorollary25Minkowski
open MAPMRTCorollary53Source MAPHBPerronSourceData
open MRTLemma215OpenIntervalCutoffV3
open MRTLemma215DynamicPacketComponentIntegralV3
open MRTProposition61TypeIILemma210InstantiationV3
open MRTProposition61TypeIIFullNormWeldV3
open MAPDynamicHBCanonicalPerronConstantV3

noncomputable section

/-- Exact source component bound for one masked Type-II cell.  The first
summand on the right is discharged premise-free by the two Lemma-2.10 mean
squares; the second is the literal certified Perron remainder. -/
theorem componentIntegral_typeIICell_le_lemma210_add_perron
    {X H beta eta T B : ℝ} {q N M : ℕ} [NeZero q]
    (hN : 1 ≤ N) (hM : 1 ≤ M)
    {alpha gamma : ℕ → ℂ}
    (halpha : SupportedNatDyadic N alpha)
    (hgamma : SupportedNatDyadic M gamma)
    (hT : 1 ≤ T) (hB : 0 ≤ B)
    (hcoeff : ∀ n, ‖literalDirichletConvolution alpha gamma n‖ ≤ B)
    (component : OuterComponent)
    (hab : (componentEndpoints X beta eta component).1 ≤
      (componentEndpoints X beta eta component).2)
    (hU : 0 ≤ stationaryWidth beta H) :
    componentIntegral X H 1 q
        (intervalCutoff (openSourceLeft X) (2 * X)
          (literalDirichletConvolution alpha gamma))
        beta eta component ≤
      2 * canonicalPerronKFour ^ 2 *
        ((∫ u in (-T)..T, perronWeight u) ^ 2 *
          (2 * stationaryWidth beta H *
            (((q : ℝ) * (2 * stationaryWidth beta H) +
                8 * Real.pi * (N : ℝ)) *
              coefficientEnergy (criticalDyadicCoefficient alpha) N) *
            (((q : ℝ) *
                  ((componentEndpoints X beta eta component).2 -
                    (componentEndpoints X beta eta component).1 +
                    2 * T + 2 * stationaryWidth beta H) +
                8 * Real.pi * (M : ℝ)) *
              coefficientEnergy (criticalDyadicCoefficient gamma) M)) +
          ((componentEndpoints X beta eta component).2 -
              (componentEndpoints X beta eta component).1) *
            (2 * stationaryWidth beta H *
              (Fintype.card (DirichletCharacter ℂ q) : ℝ) *
              (B * Real.sqrt ((N : ℝ) * (M : ℝ)) *
                Real.log (2 + T) / T)) ^ 2) := by
  let a := (componentEndpoints X beta eta component).1
  let b := (componentEndpoints X beta eta component).2
  let U := stationaryWidth beta H
  rw [componentIntegral_intervalConvolution_eq_clipped_open
    hN hM halpha hgamma component]
  have hcut := literalTypeD1_component95_cutoff_transfer_canonical
    (N := (N : ℝ)) (M := (M : ℝ)) (T := T)
    (X1 := openSourceLeft X) (X2 := 2 * X) (B := B)
    (U := U) (a := a) (b := b)
    (by exact_mod_cast hN) (by exact_mod_cast hM)
    (by exact_mod_cast Nat.mul_le_mul hN hM)
    hT hB hU (by simpa [a, b] using hab)
    (supportedDyadic_coe_of_supportedNatDyadic halpha)
    (supportedDyadic_coe_of_supportedNatDyadic hgamma)
    (fun (chi : DirichletCharacter ℂ q) n ↦
      DirichletCharacter.norm_le_one chi n)
    hcoeff
  have habLarge : a - T ≤ b + T := by
    have hT0 : 0 ≤ T := le_trans (by norm_num) hT
    dsimp [a, b]
    linarith
  have hmain := typeD1FullNorm_outerMass_le_lemma210
    (q := q) (a := a - T) (b := b + T) (U := U)
    hN hM alpha gamma halpha hgamma habLarge hU
  have hmain' :
      (∫ s in (a - T)..(b + T),
        (characterMovingMass
          (typeD1FullNorm (N : ℝ) (M : ℝ)
            (fun chi : DirichletCharacter ℂ q ↦ fun n ↦ chi n)
            alpha gamma) U s) ^ 2) ≤
        2 * U *
          (((q : ℝ) * (2 * U) + 8 * Real.pi * (N : ℝ)) *
            coefficientEnergy (criticalDyadicCoefficient alpha) N) *
          (((q : ℝ) * (b - a + 2 * T + 2 * U) +
              8 * Real.pi * (M : ℝ)) *
            coefficientEnergy (criticalDyadicCoefficient gamma) M) := by
    convert hmain using 1 <;> ring
  calc
    (∫ t in a..b,
      (characterMovingMass
        (typeD1ClippedNorm (N : ℝ) (M : ℝ)
          (openSourceLeft X) (2 * X)
          (fun chi : DirichletCharacter ℂ q ↦ fun n ↦ chi n)
          alpha gamma) U t) ^ 2) ≤ _ := hcut
    _ ≤ 2 * canonicalPerronKFour ^ 2 *
        ((∫ u in (-T)..T, perronWeight u) ^ 2 *
          (2 * U *
            (((q : ℝ) * (2 * U) + 8 * Real.pi * (N : ℝ)) *
              coefficientEnergy (criticalDyadicCoefficient alpha) N) *
            (((q : ℝ) * (b - a + 2 * T + 2 * U) +
                8 * Real.pi * (M : ℝ)) *
              coefficientEnergy (criticalDyadicCoefficient gamma) M)) +
          (b - a) *
            (2 * U * (Fintype.card (DirichletCharacter ℂ q) : ℝ) *
              (B * Real.sqrt ((N : ℝ) * (M : ℝ)) *
                Real.log (2 + T) / T)) ^ 2) := by
      gcongr
    _ = _ := by
      simp only [a, b, U]

end
end MRTProposition61TypeIICellWeldV3

#print axioms MRTProposition61TypeIICellWeldV3.componentIntegral_typeIICell_le_lemma210_add_perron
