import MRTLemma215DynamicHighPacketsV3

/-!
# Literal coefficient certificate for dynamic high packets

The signed HB/binomial/multinomial scalar is retained exactly and absorbed
into the selected short factor.  A packetwise logarithmic exponent is then
chosen by the elementary fact that powers of a number greater than one are
unbounded.  The long factor keeps the exact number of complementary factors
as its divisor-function order.
-/

namespace MRTLemma215DynamicHighPacketCertificateV3

open scoped ArithmeticFunction BigOperators
open ArithmeticFunction
open MAPHBPerronSourceData MAPDynamicHBSourceV3
open MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MRTLemma215DynamicSupportV3
open MRTLemma215DynamicFactorExtractionV3 MRTLemma215DynamicRegroupingV3
open MRTLemma215DynamicCoefficientBoundsV3
open MRTLemma215ComplementDyadicV3 MRTLemma215DynamicHighPacketsV3

noncomputable section

def dynamicComponentScalarValue
    {X : ℝ} {K k : ℕ}
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1)) : ℂ :=
  ((-1 : ℂ) ^ k * (K.choose (k + 1) : ℂ)) *
    ((↑zbag : Multiset
      (Option (Fin (sourceDyadicCount (hbFactorCutoff X))))).countPerms : ℂ) *
    ((↑mbag : Multiset
      (Option (Fin (sourceDyadicCount
        ⌊dynamicHBCutoff X K⌋₊)))).countPerms : ℂ)

theorem dynamicComponentScalar_mul_eq_smul
    {X : ℝ} {K k : ℕ}
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    (F : ArithmeticFunction ℂ) :
    dynamicComponentScalar zbag mbag * F =
      dynamicComponentScalarValue zbag mbag • F := by
  rw [dynamicComponentScalar_eq_smul_one]
  unfold dynamicComponentScalarValue
  rw [smul_mul_assoc, one_mul]

def scaledSelectedFactor
    {X : ℝ} {K k : ℕ}
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    (short : NatDyadicFactor) : NatDyadicFactor where
  length := short.length
  coeff := dynamicComponentScalar zbag mbag * short.coeff
  support := by
    intro n hn
    rw [dynamicComponentScalar_mul_eq_smul]
    change dynamicComponentScalarValue zbag mbag * short.coeff n = 0
    rw [short.support n hn]
    simp

@[simp] theorem scaledSelectedFactor_length
    {X : ℝ} {K k : ℕ}
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    (short : NatDyadicFactor) :
    (scaledSelectedFactor zbag mbag short).length = short.length := rfl

/-- Exact surviving-cell factorization of one high preliminary component. -/
theorem dynamicPreliminaryComponent_eq_sum_survivingPackets
    {X : ℝ} (hX : 1 ≤ X) {K k : ℕ} (hK : 1 ≤ K)
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    (s : ℕ)
    (hs : s < (sortedComponentFactorList logIndex zbag mbag).length)
    (hsquare : (sortedComponentFactorList logIndex zbag mbag)[s].length ^ 2 ≤
      factorLowerProduct (complementFactorList
        (sortedComponentFactorList logIndex zbag mbag) s))
    (hcomplement : ∃ head tail,
      complementFactorList (sortedComponentFactorList logIndex zbag mbag) s =
        head :: tail) :
    dynamicPreliminaryComponent (some logIndex) zbag mbag =
      let factors := sortedComponentFactorList logIndex zbag mbag
      let short := scaledSelectedFactor zbag mbag factors[s]
      let complement := complementFactorList factors s
      ∑ cell ∈ survivingComplementCells short.length complement,
        short.coeff *
          sourceDyadicArithmetic (factorUpperProduct complement)
            (factorConvolution complement) cell := by
  dsimp only
  let factors := sortedComponentFactorList logIndex zbag mbag
  let originalShort := factors[s]
  let short := scaledSelectedFactor zbag mbag originalShort
  let complement := complementFactorList factors s
  obtain ⟨head, tail, htail⟩ := hcomplement
  have htail' : complement = head :: tail := by
    simpa [complement, factors] using htail
  have hone : ∀ f ∈ head :: tail, 1 ≤ f.length := by
    intro f hf
    apply dynamicComponentFactorList_length_one logIndex zbag mbag
    have hfComp : f ∈ complement := by
      rw [htail']
      exact hf
    unfold complement at hfComp
    rcases List.mem_append.mp hfComp with hfTake | hfDrop
    · exact List.mem_of_mem_take hfTake
    · exact List.mem_of_mem_drop hfDrop
  have hcomponent := dynamicPreliminaryComponent_some_eq_factorConvolution
    hX hK logIndex zbag mbag
  rw [hcomponent]
  rw [← factorConvolution_sortedComponentFactorList logIndex zbag mbag]
  rw [factorConvolution_regroup_at factors (by simpa [factors] using hs)]
  rw [dynamicComponentScalar_mul_eq_smul]
  change dynamicComponentScalarValue zbag mbag •
      (originalShort.coeff * factorConvolution complement) = _
  rw [← smul_mul_assoc]
  have hshortCoeff : short.coeff =
      dynamicComponentScalarValue zbag mbag • originalShort.coeff := by
    exact dynamicComponentScalar_mul_eq_smul zbag mbag originalShort.coeff
  rw [← hshortCoeff]
  have hsquare' : short.length ^ 2 ≤ factorLowerProduct (head :: tail) := by
    rw [← htail]
    simpa [short, originalShort, factors] using hsquare
  have hpacket := mul_factorConvolution_eq_sum_survivingDyadicComplement
    short head tail hone hsquare'
  rw [htail]
  rw [htail']
  change short.coeff * factorConvolution (head :: tail) =
    ∑ cell ∈ survivingComplementCells short.length (head :: tail),
      short.coeff *
        sourceDyadicArithmetic (factorUpperProduct (head :: tail))
          (factorConvolution (head :: tail)) cell
  exact hpacket

theorem exists_nat_pow_ge_of_one_lt {x C : ℝ}
    (hx : 1 < x) : ∃ a : ℕ, C ≤ x ^ a := by
  exact ((tendsto_pow_atTop_atTop_of_one_lt hx).eventually_ge_atTop C).exists

theorem one_lt_log_two_mul_succ {M : ℕ} (hM : 2 ≤ M) :
    1 < Real.log (2 * ((M + 1 : ℕ) : ℝ)) := by
  rw [Real.lt_log_iff_exp_lt (by positivity)]
  exact Real.exp_one_lt_three.trans_le (by
    exact_mod_cast (show 3 ≤ 2 * (M + 1) by omega))

/-- The scalar-absorbed selected factor has a genuine power-log coefficient
bound on its complete dyadic support. -/
theorem exists_scaledSelectedFactor_log_bound
    {X : ℝ} {K k : ℕ}
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    {short : NatDyadicFactor}
    (hshortMem : short ∈ sortedComponentFactorList logIndex zbag mbag)
    (hM : 2 ≤ short.length) :
    ∃ a : ℕ, ∀ n ∈ DeterminantCountWeld.dyadic short.length,
      ‖(scaledSelectedFactor zbag mbag short).coeff n‖ ≤
        Real.log (2 * (n : ℝ)) ^ a := by
  let base := Real.log (2 * ((short.length + 1 : ℕ) : ℝ))
  obtain ⟨e, he⟩ := exists_nat_pow_ge_of_one_lt
    (C := ‖dynamicComponentScalarValue zbag mbag‖)
    (by simpa [base] using one_lt_log_two_mul_succ hM)
  refine ⟨e + 2, ?_⟩
  intro n hn
  have hnBounds := Finset.mem_Ioc.mp hn
  have hn2 : 2 ≤ n := by omega
  have hraw := sortedDynamicComponentFactor_coeff_le_logSq
    logIndex zbag mbag hshortMem n
  have hbaseLe : base ≤ Real.log (2 * (n : ℝ)) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast Nat.mul_le_mul_left 2 (by omega : short.length + 1 ≤ n)
  have hbaseNonneg : 0 ≤ base := (one_lt_log_two_mul_succ hM).le.trans' zero_le_one
  have hlogNonneg := log_two_mul_nonneg (show 1 ≤ n by omega)
  have hpow := pow_le_pow_left₀ hbaseNonneg hbaseLe e
  have he' : ‖dynamicComponentScalarValue zbag mbag‖ ≤ base ^ e := by
    simpa [base] using he
  change ‖(dynamicComponentScalar zbag mbag * short.coeff) n‖ ≤ _
  rw [dynamicComponentScalar_mul_eq_smul]
  change ‖dynamicComponentScalarValue zbag mbag * short.coeff n‖ ≤ _
  rw [norm_mul]
  calc
    ‖dynamicComponentScalarValue zbag mbag‖ * ‖short.coeff n‖ ≤
        base ^ e * Real.log (2 * (n : ℝ)) ^ 2 :=
      mul_le_mul he' hraw (norm_nonneg _) (pow_nonneg hbaseNonneg _)
    _ ≤ Real.log (2 * (n : ℝ)) ^ e *
        Real.log (2 * (n : ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_right hpow (pow_nonneg hlogNonneg _)
    _ = Real.log (2 * (n : ℝ)) ^ (e + 2) := by rw [pow_add]

/-- Common packetwise exponent for the scalar-absorbed short factor and one
surviving complementary output cell. -/
theorem exists_highPacket_coefficientBounds
    {X : ℝ} {K k : ℕ}
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    (s : ℕ)
    (hs : s < (sortedComponentFactorList logIndex zbag mbag).length)
    (hM : 2 ≤ (sortedComponentFactorList logIndex zbag mbag)[s].length)
    (cell : Fin (sourceDyadicCount (factorUpperProduct
      (complementFactorList
        (sortedComponentFactorList logIndex zbag mbag) s))))
    (hcell : cell ∈ survivingComplementCells
      (sortedComponentFactorList logIndex zbag mbag)[s].length
      (complementFactorList
        (sortedComponentFactorList logIndex zbag mbag) s)) :
    ∃ a : ℕ,
      (∀ n ∈ DeterminantCountWeld.dyadic
          (sortedComponentFactorList logIndex zbag mbag)[s].length,
        ‖(scaledSelectedFactor zbag mbag
            (sortedComponentFactorList logIndex zbag mbag)[s]).coeff n‖ ≤
          Real.log (2 * (n : ℝ)) ^ a) ∧
      (∀ n ∈ DeterminantCountWeld.dyadic (2 ^ (cell : ℕ)),
        ‖sourceDyadicArithmetic
            (factorUpperProduct (complementFactorList
              (sortedComponentFactorList logIndex zbag mbag) s))
            (factorConvolution (complementFactorList
              (sortedComponentFactorList logIndex zbag mbag) s)) cell n‖ ≤
          (MixedMellinCert.tauAF
            (complementFactorList
              (sortedComponentFactorList logIndex zbag mbag) s).length n : ℝ) *
            Real.log (2 * (n : ℝ)) ^ a) := by
  obtain ⟨ashort, hshort⟩ := exists_scaledSelectedFactor_log_bound
    logIndex zbag mbag (List.getElem_mem hs) hM
  let r := (complementFactorList
    (sortedComponentFactorList logIndex zbag mbag) s).length
  let a := max ashort (2 * r)
  refine ⟨a, ?_, ?_⟩
  · intro n hn
    have hn2 : 2 ≤ n := by
      have := (Finset.mem_Ioc.mp hn).1
      omega
    have hlogOne := one_le_log_two_mul_of_two_le hn2
    exact (hshort n hn).trans <|
      pow_le_pow_right₀ hlogOne (Nat.le_max_left _ _)
  · intro n hn
    have hN : 2 ≤ 2 ^ (cell : ℕ) :=
      survivingComplementCell_longLength_two hM hcell
    have hn2 : 2 ≤ n := by
      have := (Finset.mem_Ioc.mp hn).1
      omega
    have hbase := dyadicComplement_norm_le logIndex zbag mbag s cell hn2
    have hlogOne := one_le_log_two_mul_of_two_le hn2
    exact hbase.trans <| mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hlogOne (Nat.le_max_right _ _)) (by positivity)

end
end MRTLemma215DynamicHighPacketCertificateV3

#print axioms MRTLemma215DynamicHighPacketCertificateV3.dynamicPreliminaryComponent_eq_sum_survivingPackets
#print axioms MRTLemma215DynamicHighPacketCertificateV3.exists_scaledSelectedFactor_log_bound
#print axioms MRTLemma215DynamicHighPacketCertificateV3.exists_highPacket_coefficientBounds
