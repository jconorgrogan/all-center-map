import FordKCollisionFreeReduction
import FordMaskedKToL
import FordGoodKEnergy
import FordFiniteCoverSelection
import FordMaskedKToRaw
import FordGeometricPrimePool
import FordPrimeExponentGap
import FordCoordinatePrimeAvoidance
import FordPrimeMaskSpecialization
import FordGeometricMaskPool

open scoped BigOperators
open MAPFordType MAPFordP16Source35Triangular MAPFordP16Source35Reparam
open MAPFordLemma32LiteralContract
open MAPFordP16LiteralResidueBridge MAPFordGeometricPrimePool
open MAPFordP16SourceCountBridge
open FordGoodKEnergy MAPFordMaskedKToRaw

noncomputable section
namespace MAPFordLemma32GeometricRange

lemma exists_uniform_coordinate_pool_range
    (k d M P Q s : ℕ) (hk : 2 ≤ k) (hd : d ≤ k) (hM : k ≤ M)
    (hP : P ≤ (M+1)^(k+1))
    (hnative : (4*s)^2*(2^(k^3)*M) ≤ Q)
    (T : ℤ) (hT : T ≠ 0) (hTsize : T.natAbs ≤ P^d) :
    ∃ S : Finset ℕ, S.card = k^3 ∧
      (∀ p ∈ S, p.Prime ∧ M < p ∧ p ≤ 2^(k^3)*M ∧ (4*s)^2*p ≤ Q) ∧
      (∀ z w : Fin (k-d) → Fin (P+1), Function.Injective z → Function.Injective w →
        ∃ p ∈ S, (T : ZMod p) ≠ 0 ∧
          Function.Injective (fun i => ((z i).val : ZMod p)) ∧
          Function.Injective (fun i => ((w i).val : ZMod p))) := by
  obtain ⟨S, hc, hS, hprod⟩ :=
    MAPFordGeometricPrimePool.exists_geometric_prime_pool M (k^3) (by omega)
  have hsize : P^(d+(k-d)*(k-d-1)) < ∏ p ∈ S, p := by
    have hgap := MAPFordPrimeExponentGap.prime_exponent_margin k d hk hd
    have hexp : (k+1)*(d+(k-d)*(k-d-1)) < k^3 := by omega
    have hs : P^(d+(k-d)*(k-d-1)) < (M+1)^(k^3) := by
      calc
        _ ≤ ((M+1)^(k+1))^(d+(k-d)*(k-d-1)) := Nat.pow_le_pow_left hP _
        _ = (M+1)^((k+1)*(d+(k-d)*(k-d-1))) := by rw [pow_mul]
        _ < _ := Nat.pow_lt_pow_right (by omega) hexp
    exact hs.trans_le hprod
  refine ⟨S, hc, ?_, ?_⟩
  · intro p hp
    refine ⟨(hS p hp).1, (hS p hp).2.1, (hS p hp).2.2, ?_⟩
    exact (Nat.mul_le_mul_left ((4*s)^2) (hS p hp).2.2).trans hnative
  · intro z w hz hw
    exact MAPFordCoordinatePrimeAvoidance.exists_common_coordinate_prime
      (fun p hp => (hS p hp).1) hT hTsize z w hz hw hsize

lemma exists_uniform_mask_pool_range
    (k d M P Q s : ℕ) (hk : 2 ≤ k) (hd : d ≤ k) (hM : k ≤ M)
    (hP : P ≤ (M+1)^(k+1))
    (hnative : (4*s)^2*(2^(k^3)*M) ≤ Q)
    (T : ℤ) (hT : T ≠ 0) (hTsize : T.natAbs ≤ P^d)
    (m : ℕ) (psi : Fin k → Polynomial ℤ)
    (htype : FordType k d T m (psiNatSucc psi)) :
    ∃ S : Finset ℕ, S.card = k^3 ∧
      (∀ p ∈ S, p.Prime ∧ M < p ∧ p ≤ 2^(k^3)*M ∧ (4*s)^2*p ≤ Q) ∧
      (∀ z w : Fin k → Fin (P+1),
        (∀ i, 1 ≤ (z i).val) → (∀ i, 1 ≤ (w i).val) →
        Function.Injective z → Function.Injective w →
        ∃ p : ℕ, ∃ hp : p.Prime, p ∈ S ∧
          fordPolynomialMask hd hp psi z ∧ fordPolynomialMask hd hp psi w) := by
  obtain ⟨S, hc, hS, hcoords⟩ :=
    exists_uniform_coordinate_pool_range k d M P Q s hk hd hM hP hnative T hT hTsize
  refine ⟨S, hc, hS, ?_⟩
  intro z w hzpos hwpos hz hw
  obtain ⟨p, hpS, hpT, hpz, hpw⟩ := hcoords
    (fordTailCoordinates hd z) (fordTailCoordinates hd w)
    (MAPFordGeometricMaskPool.tail_injective hd z hz)
    (MAPFordGeometricMaskPool.tail_injective hd w hw)
  have hp := (hS p hpS).1
  refine ⟨p, hp, hpS, ?_, ?_⟩
  · exact FordTypeJacobian.fordPolynomialMask_of_fordType
      hd hk hp (lt_of_le_of_lt hM (hS p hpS).2.1) hpT psi htype z hzpos hpz
  · exact FordTypeJacobian.fordPolynomialMask_of_fordType
      hd hk hp (lt_of_le_of_lt hM (hS p hpS).2.1) hpT psi htype w hwpos hpw

lemma goodK_exists_large_mask_range
    {s k d P Q q m M : ℕ} {T : ℤ}
    (hk : 2 ≤ k) (hd : d ≤ k) (hM : k ≤ M)
    (hP : P ≤ (M+1)^(k+1))
    (hnative : (4*s)^2*(2^(k^3)*M) ≤ Q)
    (hT : T ≠ 0) (hTsize : T.natAbs ≤ P^d)
    (psi : Fin k → Polynomial ℤ)
    (htype : FordType k d T m (psiNatSucc psi)) :
    ∃ p : ℕ, ∃ hp : p.Prime,
      M < p ∧ p ≤ 2^(k^3)*M ∧ (4*s)^2*p ≤ Q ∧
      Fintype.card (GoodK (s := s) (P := P) (Q := Q) psi q) ≤
        k^3 * Fintype.card (MaskedK (s := s) (P := P) (Q := Q) (q := q) hd hp psi) := by
  classical
  obtain ⟨S, hc, hS, hcoverS⟩ :=
    exists_uniform_mask_pool_range k d M P Q s hk hd hM hP hnative T hT hTsize m psi htype
  have hSne : S.Nonempty := Finset.card_pos.mp (by rw [hc]; positivity)
  let I := ↥S
  letI : Nonempty I := by
    obtain ⟨p, hp⟩ := hSne
    exact ⟨⟨p, hp⟩⟩
  let mask : I → GoodK (s := s) (P := P) (Q := Q) psi q → Prop :=
    fun p a => fordPolynomialMask hd (hS p.val p.property).1 psi a.1.z ∧
      fordPolynomialMask hd (hS p.val p.property).1 psi a.1.w
  have hcover : ∀ a, ∃ i, mask i a := by
    intro a
    obtain ⟨p, hp, hpS, hz, hw⟩ := hcoverS a.1.z a.1.w
      a.1.z_pos a.1.w_pos a.2.1 a.2.2
    exact ⟨⟨p, hpS⟩, hz, hw⟩
  obtain ⟨i, hi⟩ := MAPFordFiniteCoverSelection.exists_large_mask mask hcover
  have hI : Fintype.card I = k^3 := by simpa [I] using hc
  rw [hI] at hi
  let hp := (hS i.val i.property).1
  let toMasked : {a : GoodK (s := s) (P := P) (Q := Q) psi q // mask i a} →
      MaskedK (s := s) (P := P) (Q := Q) (q := q) hd hp psi :=
    fun a => ⟨a.1.1, a.2⟩
  have hinj : Function.Injective toMasked := by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : MaskedK (s := s) (P := P) (Q := Q) (q := q) hd hp psi => x.val) h
  have hmask := Fintype.card_le_of_injective toMasked hinj
  refine ⟨i.val, hp, (hS i.val i.property).2.1,
    (hS i.val i.property).2.2.1, (hS i.val i.property).2.2.2, ?_⟩
  simp only [Nat.card_eq_fintype_card] at hi
  exact hi.trans (Nat.mul_le_mul_left _ hmask)

/-- Lemma-3.2 count with a geometric prime witness retaining `M < p`.
The additional lower-range fact is needed by the recurrence seam. -/
theorem K_exists_L_geometric_range
    {s k d P Q q r M : ℕ} {T : ℤ}
    (hk : 2 ≤ k) (hd : d ≤ k) (hds : d ≤ s) (hs : 1 ≤ s)
    (hr1 : 1 ≤ r) (hrk : r ≤ k) (hlarge : 16*k^4 < P) (hM : k ≤ M)
    (hP : P ≤ (M+1)^(k+1))
    (hnative : (4*s)^2*(2^(k^3)*M) ≤ Q) (hq : 0 < q)
    (hT : T ≠ 0) (hTsize : T.natAbs ≤ P^d)
    (m0 : ℕ) (psi0 : Fin k → Polynomial ℤ)
    (h0 : FordType k d T m0 (psiNatSucc psi0)) :
    ∃ p : ℕ, p.Prime ∧ k < p ∧ M < p ∧ p ≤ 2^(k^3)*M ∧ (4*s)^2*p ≤ Q ∧
      ∃ m phi, FordType k d T m (psiNatSucc phi) ∧
      Fintype.card (KPoint s k P Q psi0 q) ≤
        (4*k^3*Nat.factorial d*p^(2*s-d+(r-d)*(r-d-1)/2+r*d+(k-d))) *
          Fintype.card (LPoint s k P (Q/p) p q r phi) := by
  obtain ⟨m, psi, hpsi, hgood⟩ :=
    MAPFordKCollisionFreeReduction.exists_collision_free_reduction
      (s := s) (d := d) (P := P) (Q := Q) (q := q) hk hlarge m0 psi0 h0
  obtain ⟨p, hp, hMp, hupper, hnat, hmask⟩ :=
    goodK_exists_large_mask_range
      (s := s) (P := P) (Q := Q) (q := q)
      hk hd hM hP hnative hT hTsize psi hpsi
  letI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨b, hphi, hL⟩ := MAPFordMaskedKToL.maskedK_exists_L
    (s := s) (P := P) (Q := Q) (q := q)
    hp (lt_of_le_of_lt (hd.trans hM) hMp) hds hs hd hr1 hrk psi hpsi hq hnat
  refine ⟨p, hp, lt_of_le_of_lt hM hMp, hMp, hupper, hnat, m,
    phiRow psi (q : ℤ) (negResidue b).val, hphi, ?_⟩
  have h := hgood.trans (Nat.mul_le_mul_left 2
    (hmask.trans (Nat.mul_le_mul_left (k^3) hL)))
  convert h using 1 <;> ring

end MAPFordLemma32GeometricRange
#print axioms MAPFordLemma32GeometricRange.K_exists_L_geometric_range
