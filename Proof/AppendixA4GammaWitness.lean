import AppendixA4Detector
import GammaCompactStrip

namespace GammaCompactStripScratch

open scoped Real

/-- Premise-free inhabitant of the Gamma-decay interface previously left open
by the Appendix A.4 contour module. -/
theorem appendixA4_GammaCompactStripExponentialDecay :
    MAPAppendixA4Detector.GammaCompactStripExponentialDecay := by
  refine ⟨12, 1, by norm_num, by norm_num, ?_⟩
  intro a t halo hahi ht
  apply norm_Gamma_compactStrip_le_exp_pi_div_four
  · convert halo using 1 <;> norm_num
  · exact hahi
  · exact ht

end GammaCompactStripScratch

#print axioms GammaCompactStripScratch.appendixA4_GammaCompactStripExponentialDecay
