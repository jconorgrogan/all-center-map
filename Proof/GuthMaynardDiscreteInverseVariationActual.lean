import GuthMaynardDiscreteFirstDerivative
import GuthMaynardDiscreteInverseVariation
import GuthMaynardDiscreteImagVariation
import GuthMaynardDiscreteHalfAngle

namespace GuthMaynardDiscreteInverseVariationActual

open GuthMaynardDiscreteFirstDerivative
open GuthMaynardDiscreteInverseVariation
open GuthMaynardDiscreteImagVariation
open GuthMaynardDiscreteHalfAngle

noncomputable section

theorem sum_norm_inverseCoeff_diff
    (k : ℕ) (d : ℕ → ℝ)
    (hd0 : ∀ n, 0 < d n) (hd1 : ∀ n, d n ≤ 1)
    (hdanti : Antitone d) :
    ∑ n ∈ Finset.range k,
        ‖inverseCoeff (d (n + 1)) - inverseCoeff (d n)‖ =
      (Real.cot (d k / 2) - Real.cot (d 0 / 2)) / 2 := by
  let b : ℕ → ℝ := fun n => Real.cot (d n / 2) / 2
  have hb : Monotone b := by
    intro n m hnm
    unfold b
    have hdnm : d m ≤ d n := hdanti hnm
    have hnmem : d n / 2 ∈ Set.Ioc (0 : ℝ) 1 := by
      constructor
      · nlinarith [hd0 n]
      · nlinarith [hd1 n]
    have hmmem : d m / 2 ∈ Set.Ioc (0 : ℝ) 1 := by
      constructor
      · nlinarith [hd0 m]
      · nlinarith [hd1 m]
    have hhalf : d m / 2 ≤ d n / 2 := by linarith
    have hc := cot_antitone_on_unit hmmem hnmem hhalf
    linarith
  calc
    ∑ n ∈ Finset.range k,
        ‖inverseCoeff (d (n + 1)) - inverseCoeff (d n)‖ =
      ∑ n ∈ Finset.range k,
        ‖imagCoeff (b (n + 1)) - imagCoeff (b n)‖ := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [inverseCoeff_halfAngle (hd0 (n + 1)) (hd1 (n + 1)),
            inverseCoeff_halfAngle (hd0 n) (hd1 n)]
          simp [imagCoeff, b]
    _ = b k - b 0 := sum_norm_imagCoeff_diff_of_monotone k b hb
    _ = (Real.cot (d k / 2) - Real.cot (d 0 / 2)) / 2 := by
      unfold b
      ring

end
end GuthMaynardDiscreteInverseVariationActual

#print axioms GuthMaynardDiscreteInverseVariationActual.sum_norm_inverseCoeff_diff
