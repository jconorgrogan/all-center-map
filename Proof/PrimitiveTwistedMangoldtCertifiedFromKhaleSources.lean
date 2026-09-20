import PrimitiveTwistedMangoldtCertified
import KhaleAppendixB104FromSources
import KhaleAppendixB1LazyKeyReduction

/-!
# Primitive twisted-Mangoldt certification with Khale B.104 opened

These are stable endpoint adapters.  They replace the opaque B.104 proposition
by Ford's exact `(76.2,4.45)` estimate and progressively opened statements from
Khale's proof of Appendix B.  The final pair of adapters uses the separate
principal/nonprincipal source split: compactness handles bounded principal-zeta
zeros, so McCurley's finite-height theorem is not needed by the live endpoint.
-/

namespace MAPPrimitiveTwistedMangoldtCertifiedFromKhaleSources

open MAPKhaleAppendixBSource
open MAPKhaleAppendixB1PenultimateReduction

noncomputable section

/-- Exact split primitive binder from the current lowest Khale source leaves. -/
theorem primitiveTwistedMangoldtPsi_of_khale_penultimate_sources
    (hFord : FordHurwitzEquation12 76.2 4.45)
    (hPenultimate : AppendixBPenultimateZeroEstimate)
    (hMcCurley : McCurleyTheorem11RealException) :
    ∀ A B : ℕ, ∃ C X0 : ℝ,
      0 < C ∧ 2 ≤ X0 ∧
        ∀ X : ℝ, X0 ≤ X →
        ∀ q : ℕ, 1 ≤ q →
          (q : ℝ) ≤ (Real.log X) ^ B →
        ∀ chi : DirichletCharacter ℂ q, chi.IsPrimitive →
        ∀ t : ℝ, t ∈ Set.Icc X (2 * X) →
          ‖APFoundation.twistedMangoldtSum chi (Finset.Icc 1 ⌊t⌋₊) -
              MAPSiegelWalfiszCharacterReduction.characterMain chi t‖ ≤
            C * X / (Real.log X) ^ A :=
  MAPPrimitiveTwistedMangoldtCertified.primitiveTwistedMangoldtPsi_of_appendixB
    (MAPKhaleAppendixB104FromSources.appendixBCorollary104_of_ford_penultimate_mccurley
      hFord hPenultimate hMcCurley)

/-- The source-facing uniform primitive theorem consumed by the live endpoint. -/
theorem uniformTwistedMangoldtPsi_of_khale_penultimate_sources
    (hFord : FordHurwitzEquation12 76.2 4.45)
    (hPenultimate : AppendixBPenultimateZeroEstimate)
    (hMcCurley : McCurleyTheorem11RealException) :
    MAPSiegelWalfiszCharacterReduction.UniformTwistedMangoldtPsi :=
  MAPPrimitiveTwistedMangoldtCertified.uniformTwistedMangoldtPsi_of_appendixB
    (MAPKhaleAppendixB104FromSources.appendixBCorollary104_of_ford_penultimate_mccurley
      hFord hPenultimate hMcCurley)

/-- Exact split primitive binder with Khale B.1 reduced through `(lazykey)`. -/
theorem primitiveTwistedMangoldtPsi_of_khale_lazyKey_sources
    (hFord : FordHurwitzEquation12 76.2 4.45)
    (hLazy : MAPKhaleAppendixB1LazyKeyReduction.AppendixBLazyKeyAfterZetaEstimate)
    (hMcCurley : McCurleyTheorem11RealException) :
    ∀ A B : ℕ, ∃ C X0 : ℝ,
      0 < C ∧ 2 ≤ X0 ∧
        ∀ X : ℝ, X0 ≤ X →
        ∀ q : ℕ, 1 ≤ q →
          (q : ℝ) ≤ (Real.log X) ^ B →
        ∀ chi : DirichletCharacter ℂ q, chi.IsPrimitive →
        ∀ t : ℝ, t ∈ Set.Icc X (2 * X) →
          ‖APFoundation.twistedMangoldtSum chi (Finset.Icc 1 ⌊t⌋₊) -
              MAPSiegelWalfiszCharacterReduction.characterMain chi t‖ ≤
            C * X / (Real.log X) ^ A :=
  MAPPrimitiveTwistedMangoldtCertified.primitiveTwistedMangoldtPsi_of_appendixB
    (MAPKhaleAppendixB104FromSources.appendixBCorollary104_of_ford_lazyKey_mccurley
      hFord hLazy hMcCurley)

/-- Uniform source-facing primitive theorem with B.1 reduced through
`(lazykey)`. -/
theorem uniformTwistedMangoldtPsi_of_khale_lazyKey_sources
    (hFord : FordHurwitzEquation12 76.2 4.45)
    (hLazy : MAPKhaleAppendixB1LazyKeyReduction.AppendixBLazyKeyAfterZetaEstimate)
    (hMcCurley : McCurleyTheorem11RealException) :
    MAPSiegelWalfiszCharacterReduction.UniformTwistedMangoldtPsi :=
  MAPPrimitiveTwistedMangoldtCertified.uniformTwistedMangoldtPsi_of_appendixB
    (MAPKhaleAppendixB104FromSources.appendixBCorollary104_of_ford_lazyKey_mccurley
      hFord hLazy hMcCurley)

/-- Uniform source-facing primitive theorem with Khale B.1 reduced to the
exact `firstpart` inequality and pointwise zeta bound. -/
theorem uniformTwistedMangoldtPsi_of_khale_firstPart_sources
    (hFord : FordHurwitzEquation12 76.2 4.45)
    (hFirst : MAPKhaleAppendixB1FirstPartReduction.AppendixBFirstPartEstimate)
    (hZeta : MAPKhaleAppendixB1ZetaReduction.AppendixBZetaPointwise06)
    (hMcCurley : McCurleyTheorem11RealException) :
    MAPSiegelWalfiszCharacterReduction.UniformTwistedMangoldtPsi :=
  MAPPrimitiveTwistedMangoldtCertified.uniformTwistedMangoldtPsi_of_appendixB
    (MAPKhaleAppendixB104FromSources.appendixBCorollary104_of_ford_firstPart_zeta_mccurley
      hFord hFirst hZeta hMcCurley)

/-- Deepest current endpoint adapter: the remaining first-part premise is only
the displayed upper inequality.  The bundled `beta < 1` fact is discharged by
Mathlib's closed-half-plane nonvanishing theorem. -/
theorem uniformTwistedMangoldtPsi_of_khale_firstPartUpper_sources
    (hFord : FordHurwitzEquation12 76.2 4.45)
    (hFirstUpper :
      MAPKhaleAppendixBFirstPartSourceReduction.AppendixBFirstPartUpperEstimate)
    (hZeta : MAPKhaleAppendixB1ZetaReduction.AppendixBZetaPointwise06)
    (hMcCurley : McCurleyTheorem11RealException) :
    MAPSiegelWalfiszCharacterReduction.UniformTwistedMangoldtPsi :=
  MAPPrimitiveTwistedMangoldtCertified.uniformTwistedMangoldtPsi_of_appendixB
    (MAPKhaleAppendixB104FromSources.appendixBCorollary104_of_ford_firstPartUpper_zeta_mccurley
      hFord hFirstUpper hZeta hMcCurley)

/-- Deepest current endpoint adapter: both elementary Appendix-B leaves
(cotangent and sharp zeta) are certified internally. -/
theorem uniformTwistedMangoldtPsi_of_khale_firstPartUpper_mccurley
    (hFord : FordHurwitzEquation12 76.2 4.45)
    (hFirstUpper :
      MAPKhaleAppendixBFirstPartSourceReduction.AppendixBFirstPartUpperEstimate)
    (hMcCurley : McCurleyTheorem11RealException) :
    MAPSiegelWalfiszCharacterReduction.UniformTwistedMangoldtPsi :=
  MAPPrimitiveTwistedMangoldtCertified.uniformTwistedMangoldtPsi_of_appendixB
    (MAPKhaleAppendixB104FromSources.appendixBCorollary104_of_ford_firstPartUpper_mccurley
      hFord hFirstUpper hMcCurley)

/-- Endpoint adapter with the first-part sign structure retained: the remaining
Khale inputs are the raw Lemma-4.1 estimate and specialized Lemma 5.1. -/
theorem uniformTwistedMangoldtPsi_of_khale_raw_lemma51_mccurley
    (hFord : FordHurwitzEquation12 76.2 4.45)
    (hRaw :
      MAPKhaleAppendixBFirstPartAnalyticReduction.AppendixBFirstPartRawEstimate)
    (h51 :
      MAPKhaleAppendixBFirstPartAnalyticReduction.AppendixBLemma51Specialized)
    (hMcCurley : McCurleyTheorem11RealException) :
    MAPSiegelWalfiszCharacterReduction.UniformTwistedMangoldtPsi :=
  MAPPrimitiveTwistedMangoldtCertified.uniformTwistedMangoldtPsi_of_appendixB
    (MAPKhaleAppendixB104FromSources.appendixBCorollary104_of_ford_raw_lemma51_mccurley
      hFord hRaw h51 hMcCurley)

/-- Endpoint adapter with Khale Lemma 5.1 opened through the exact
Euler/Fourier expansion, Ford transform, and zeta prime-power identity. -/
theorem uniformTwistedMangoldtPsi_of_khale_raw_expansions_mccurley
    (hFordHurwitz : FordHurwitzEquation12 76.2 4.45)
    (hRaw :
      MAPKhaleAppendixBFirstPartAnalyticReduction.AppendixBFirstPartRawEstimate)
    (hEuler :
      MAPKhaleAppendixBLemma51ExpansionReduction.AppendixBLemma51EulerFourierExpansion)
    (hFourier :
      MAPKhaleAppendixBLemma51KernelCertified.FordCoshSqFourierIdentity)
    (hZetaEuler :
      MAPKhaleAppendixBLemma51ExpansionReduction.AppendixBZetaPrimePowerIdentity)
    (hMcCurley : McCurleyTheorem11RealException) :
    MAPSiegelWalfiszCharacterReduction.UniformTwistedMangoldtPsi :=
  MAPPrimitiveTwistedMangoldtCertified.uniformTwistedMangoldtPsi_of_appendixB
    (MAPKhaleAppendixB104FromSources.appendixBCorollary104_of_ford_raw_expansions_mccurley
      hFordHurwitz hRaw hEuler hFourier hZetaEuler hMcCurley)

/-- Endpoint adapter with the zeta prime-power identity fully certified.  The
remaining Lemma-5.1 leaves are the exact Euler/Fourier integral identity and
Ford's `cosh^{-2}` transform. -/
theorem uniformTwistedMangoldtPsi_of_khale_raw_eulerFourier_mccurley
    (hFordHurwitz : FordHurwitzEquation12 76.2 4.45)
    (hRaw :
      MAPKhaleAppendixBFirstPartAnalyticReduction.AppendixBFirstPartRawEstimate)
    (hEuler :
      MAPKhaleAppendixBLemma51ExpansionReduction.AppendixBLemma51EulerFourierExpansion)
    (hFourier :
      MAPKhaleAppendixBLemma51KernelCertified.FordCoshSqFourierIdentity)
    (hMcCurley : McCurleyTheorem11RealException) :
    MAPSiegelWalfiszCharacterReduction.UniformTwistedMangoldtPsi :=
  MAPPrimitiveTwistedMangoldtCertified.uniformTwistedMangoldtPsi_of_appendixB
    (MAPKhaleAppendixB104FromSources.appendixBCorollary104_of_ford_raw_eulerFourier_mccurley
      hFordHurwitz hRaw hEuler hFourier hMcCurley)

/-- Current deepest primitive endpoint: Khale Lemma 5.1 has no remaining
premises.  Only the preceding raw Lemma-4.1 estimate, Ford's Hurwitz-zeta
estimate, and McCurley's real-exception theorem remain external. -/
theorem uniformTwistedMangoldtPsi_of_khale_raw_mccurley
    (hFordHurwitz : FordHurwitzEquation12 76.2 4.45)
    (hRaw :
      MAPKhaleAppendixBFirstPartAnalyticReduction.AppendixBFirstPartRawEstimate)
    (hMcCurley : McCurleyTheorem11RealException) :
    MAPSiegelWalfiszCharacterReduction.UniformTwistedMangoldtPsi :=
  MAPPrimitiveTwistedMangoldtCertified.uniformTwistedMangoldtPsi_of_appendixB
    (MAPKhaleAppendixB104FromSources.appendixBCorollary104_of_ford_raw_mccurley
      hFordHurwitz hRaw hMcCurley)

/-- Exact primitive binder at the current live source boundary.  The
nonprincipal branch is certified internally.  The conductor-one principal
branch uses compactness for bounded zeros and the high Khale argument, leaving
only Ford's exact Hurwitz estimate and Khale's raw Lemma-4.1 estimate. -/
theorem primitiveTwistedMangoldtPsi_of_ford_raw
    (hFord : FordHurwitzEquation12 76.2 4.45)
    (hRaw :
      MAPKhaleAppendixBFirstPartAnalyticReduction.AppendixBFirstPartRawEstimate) :
    ∀ A B : ℕ, ∃ C X0 : ℝ,
      0 < C ∧ 2 ≤ X0 ∧
        ∀ X : ℝ, X0 ≤ X →
        ∀ q : ℕ, 1 ≤ q →
          (q : ℝ) ≤ (Real.log X) ^ B →
        ∀ chi : DirichletCharacter ℂ q, chi.IsPrimitive →
        ∀ t : ℝ, t ∈ Set.Icc X (2 * X) →
          ‖APFoundation.twistedMangoldtSum chi (Finset.Icc 1 ⌊t⌋₊) -
              MAPSiegelWalfiszCharacterReduction.characterMain chi t‖ ≤
            C * X / (Real.log X) ^ A :=
  MAPPrimitiveTwistedMangoldtSourceSplit.primitiveTwistedMangoldtPsi_of_split
    MAPNonprincipalTwistedMangoldtPsiCertified.primitiveNonprincipalTwistedMangoldtPsi
    (MAPPrincipalKoukSiegelFormula.primitivePrincipalOneTwistedMangoldtPsi_of_ford_raw
      hFord hRaw)

/-- Uniform twisted-Mangoldt source consumed by the live endpoint, with no
McCurley premise.  Its only remaining analytic source leaves are Ford's exact
Hurwitz estimate and Khale's raw Lemma-4.1 estimate. -/
theorem uniformTwistedMangoldtPsi_of_ford_raw
    (hFord : FordHurwitzEquation12 76.2 4.45)
    (hRaw :
      MAPKhaleAppendixBFirstPartAnalyticReduction.AppendixBFirstPartRawEstimate) :
    MAPSiegelWalfiszCharacterReduction.UniformTwistedMangoldtPsi :=
  MAPPrimitiveTwistedMangoldtSourceSplit.uniformTwistedMangoldtPsi_of_split
    MAPNonprincipalTwistedMangoldtPsiCertified.primitiveNonprincipalTwistedMangoldtPsi
    (MAPPrincipalKoukSiegelFormula.primitivePrincipalOneTwistedMangoldtPsi_of_ford_raw
      hFord hRaw)

end
end MAPPrimitiveTwistedMangoldtCertifiedFromKhaleSources

#print axioms MAPPrimitiveTwistedMangoldtCertifiedFromKhaleSources.primitiveTwistedMangoldtPsi_of_khale_penultimate_sources
#print axioms MAPPrimitiveTwistedMangoldtCertifiedFromKhaleSources.uniformTwistedMangoldtPsi_of_khale_penultimate_sources
#print axioms MAPPrimitiveTwistedMangoldtCertifiedFromKhaleSources.primitiveTwistedMangoldtPsi_of_khale_lazyKey_sources
#print axioms MAPPrimitiveTwistedMangoldtCertifiedFromKhaleSources.uniformTwistedMangoldtPsi_of_khale_lazyKey_sources
#print axioms MAPPrimitiveTwistedMangoldtCertifiedFromKhaleSources.uniformTwistedMangoldtPsi_of_khale_firstPart_sources
#print axioms MAPPrimitiveTwistedMangoldtCertifiedFromKhaleSources.uniformTwistedMangoldtPsi_of_khale_firstPartUpper_sources
#print axioms MAPPrimitiveTwistedMangoldtCertifiedFromKhaleSources.uniformTwistedMangoldtPsi_of_khale_firstPartUpper_mccurley
#print axioms MAPPrimitiveTwistedMangoldtCertifiedFromKhaleSources.uniformTwistedMangoldtPsi_of_khale_raw_lemma51_mccurley
#print axioms MAPPrimitiveTwistedMangoldtCertifiedFromKhaleSources.uniformTwistedMangoldtPsi_of_khale_raw_expansions_mccurley
#print axioms MAPPrimitiveTwistedMangoldtCertifiedFromKhaleSources.uniformTwistedMangoldtPsi_of_khale_raw_eulerFourier_mccurley
#print axioms MAPPrimitiveTwistedMangoldtCertifiedFromKhaleSources.uniformTwistedMangoldtPsi_of_khale_raw_mccurley
#print axioms MAPPrimitiveTwistedMangoldtCertifiedFromKhaleSources.primitiveTwistedMangoldtPsi_of_ford_raw
#print axioms MAPPrimitiveTwistedMangoldtCertifiedFromKhaleSources.uniformTwistedMangoldtPsi_of_ford_raw
