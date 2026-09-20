import KhaleAppendixB1PenultimateReduction
import KhaleAppendixB1LazyKeyReduction
import KhaleAppendixB1FirstPartReduction
import KhaleAppendixBFirstPartSourceReduction
import KhaleAppendixBCotangentCertified
import KhaleAppendixBZetaPointwiseCertified
import KhaleAppendixBFirstPartAnalyticReduction
import KhaleAppendixBLemma51ExpansionReduction
import KhaleAppendixBZetaPrimePowerCertified
import KhaleAppendixBLemma51EulerFourierCertified

/-!
# The pre-McCurley high-zero Appendix-B chain

This is the source-facing composition of Khale's high-zero calculation.  It
stops before the height reduction and therefore has no McCurley or B.104
premise.  The only open analytic leaf is the literal signed Lemma-4.1 input
`AppendixBFirstPartRawEstimate`; Lemma 5.1 and the remaining numerical chain
are certified internally.
-/

namespace MAPKhaleAppendixBHighZeroFromRaw

open MAPKhaleAppendixBSource MAPKhaleAppendixB1HighZeroReduction

noncomputable section

/-- High-zero reciprocal estimate from the exact remaining Lemma-4.1 source
leaf. -/
theorem appendixBHighZeroReciprocalEstimate_of_raw
    (hRaw :
      MAPKhaleAppendixBFirstPartAnalyticReduction.AppendixBFirstPartRawEstimate) :
    AppendixBHighZeroReciprocalEstimate :=
  MAPKhaleAppendixB1PenultimateReduction.highZeroReciprocalEstimate_of_penultimate
    (MAPKhaleAppendixB1LazyKeyReduction.penultimateEstimate_of_lazyKeyAfterZeta
      (MAPKhaleAppendixB1ZetaReduction.lazyKeyAfterZeta_of_beforeZeta_and_zetaBound
        (MAPKhaleAppendixB1FirstPartReduction.lazyKeyBeforeZeta_of_firstPart_and_cotangent
          (MAPKhaleAppendixBFirstPartSourceReduction.firstPartEstimate_of_upper
            (MAPKhaleAppendixBFirstPartAnalyticReduction.firstPartUpper_of_raw_and_lemma51
              hRaw
              (MAPKhaleAppendixBLemma51ExpansionReduction.lemma51Specialized_of_expansions_and_ford
                MAPKhaleAppendixBLemma51EulerFourierCertified.appendixBLemma51EulerFourierExpansion
                MAPKhaleAppendixBLemma51KernelCertified.fordCoshSqFourierIdentity
                MAPKhaleAppendixBZetaPrimePowerCertified.appendixBZetaPrimePowerIdentity)))
          MAPKhaleAppendixBCotangentCertified.appendixBCotangent0012)
        (MAPKhaleAppendixB1ZetaReduction.lazyZetaBound_of_pointwise06
          MAPKhaleAppendixBZetaPointwiseCertified.appendixBZetaPointwise06)))

end

end MAPKhaleAppendixBHighZeroFromRaw

#print axioms MAPKhaleAppendixBHighZeroFromRaw.appendixBHighZeroReciprocalEstimate_of_raw
