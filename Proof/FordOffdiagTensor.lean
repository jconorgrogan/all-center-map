import FordDifferencePairs
import FordRawCongruenceToL

open scoped BigOperators
open FordDifferencePairs MAPFordLemma32LiteralContract
open MAPFordP16SourceCountBridge MAPFordP16FiniteFourierBridge
noncomputable section
set_option autoImplicit false
namespace FordOffdiagTensor

abbrev Modulus (p r : ℕ) := p ^ r

structure TensorPoint (s k P Q p q r : ℕ) (phi : Fin k → Polynomial ℤ)
    (hm : 0 < Modulus p r) where
  sign : Fin k → Bool
  height : Fin k → PositiveHeight P (Modulus p r)
  base : Fin k → PositiveFin P
  u : Fin s → Fin (Q + 1)
  v : Fin s → Fin (Q + 1)
  u_pos : ∀ i, 0 < (u i).val
  v_pos : ∀ i, 0 < (v i).val
  equation : ∀ j : Fin k,
    (∑ i : Fin k,
      (if sign i then
        (phi j).eval ((base i).val + Modulus p r * (height i).1.val : ℤ) -
          (phi j).eval ((base i).val : ℤ)
      else
        -((phi j).eval ((base i).val + Modulus p r * (height i).1.val : ℤ) -
          (phi j).eval ((base i).val : ℤ)))) +
      (((p * q : ℕ) : ℤ) ^ (j.val + 1)) *
        (∑ i : Fin s,
          (((u i).val : ℤ) ^ (j.val + 1) - ((v i).val : ℤ) ^ (j.val + 1))) = 0

instance tensorPointFintype {s k P Q p q r : ℕ} (phi : Fin k → Polynomial ℤ)
    (hm : 0 < Modulus p r) : Fintype (TensorPoint s k P Q p q r phi hm) := by
  classical
  let proj : TensorPoint s k P Q p q r phi hm →
      (Fin k → Bool) × ((Fin k → PositiveHeight P (Modulus p r)) ×
        ((Fin k → PositiveFin P) × ((Fin s → Fin (Q + 1)) × (Fin s → Fin (Q + 1))))) :=
    fun a => (a.sign, (a.height, (a.base, (a.u, a.v))))
  letI : Finite (TensorPoint s k P Q p q r phi hm) := by
    apply Finite.of_injective proj
    intro a b h
    cases a; cases b
    simp only [proj, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl, rfl, rfl⟩
    rfl
  exact Fintype.ofFinite _

abbrev LOffdiag (s k P Q p q r : ℕ) (phi : Fin k → Polynomial ℤ) :=
  {a : LPoint s k P Q p q r phi // ∀ i, a.z i ≠ a.w i}

instance lOffdiagFintype {s k P Q p q r : ℕ} (phi : Fin k → Polynomial ℤ) :
    Fintype (LOffdiag s k P Q p q r phi) := by
  classical unfold LOffdiag; infer_instance

def pair_of_offdiag {s k P Q p q r : ℕ} {phi : Fin k → Polynomial ℤ}
    {a : LOffdiag s k P Q p q r phi} (i : Fin k) :
    DifferencePair P (Modulus p r) := by
  refine ⟨(a.1.z i, a.1.w i), ?_⟩
  refine ⟨a.1.z_pos i, a.1.w_pos i, ?_, ?_⟩
  · intro h
    apply a.2 i
    exact Fin.ext h
  · exact a.1.congruence i

noncomputable def tensorEncode {s k P Q p q r : ℕ} {phi : Fin k → Polynomial ℤ}
    (hm : 0 < Modulus p r) :
    LOffdiag s k P Q p q r phi → TensorPoint s k P Q p q r phi hm := by
  intro a
  let code : Fin k → DifferenceCode P (Modulus p r) :=
    fun i => encode P (Modulus p r) hm (pair_of_offdiag (a := a) i)
  refine {
    sign := fun i => (code i).1
    height := fun i => (code i).2.1
    base := fun i => (code i).2.2
    u := a.1.u
    v := a.1.v
    u_pos := a.1.u_pos
    v_pos := a.1.v_pos
    equation := ?_ }
  intro j
  have hL := a.1.equation j
  have hterm : ∀ i : Fin k,
      (phi j).eval ((a.1.z i).val : ℤ) - (phi j).eval ((a.1.w i).val : ℤ) =
      if (code i).1 then
        (phi j).eval ((code i).2.2.1.val + Modulus p r * (code i).2.1.1.val : ℤ) -
          (phi j).eval ((code i).2.2.1.val : ℤ)
      else
        -((phi j).eval ((code i).2.2.1.val + Modulus p r * (code i).2.1.1.val : ℤ) -
          (phi j).eval ((code i).2.2.1.val : ℤ)) := by
    intro i
    exact encode_difference_identity hm (fun n => (phi j).eval (n : ℤ)) (pair_of_offdiag (a := a) i)
  calc
    _ = (∑ i : Fin k,
        ((phi j).eval ((a.1.z i).val : ℤ) - (phi j).eval ((a.1.w i).val : ℤ))) +
        (((p * q : ℕ) : ℤ) ^ (j.val + 1)) *
          (∑ i : Fin s,
            (((a.1.u i).val : ℤ) ^ (j.val + 1) - ((a.1.v i).val : ℤ) ^ (j.val + 1))) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      exact (hterm i).symm
    _ = 0 := hL

lemma lpoint_ext {s k P Q p q r : ℕ} {phi : Fin k → Polynomial ℤ}
    (x y : LPoint s k P Q p q r phi)
    (hz : x.z = y.z) (hw : x.w = y.w) (hu : x.u = y.u) (hv : x.v = y.v) : x = y := by
  cases x
  cases y
  simp only [MAPFordLemma32LiteralContract.LPoint.mk.injEq]
  exact ⟨hz, hw, hu, hv⟩

lemma tensorEncode_injective {s k P Q p q r : ℕ} {phi : Fin k → Polynomial ℤ}
    (hm : 0 < Modulus p r) :
    Function.Injective (tensorEncode (s := s) (k := k) (P := P) (Q := Q)
      (p := p) (q := q) (r := r) (phi := phi) hm) := by
  intro a b h
  apply Subtype.ext
  have hs := congrArg TensorPoint.sign h
  have hh := congrArg TensorPoint.height h
  have hb := congrArg TensorPoint.base h
  have hu := congrArg TensorPoint.u h
  have hv := congrArg TensorPoint.v h
  have hc : ∀ i : Fin k,
      encode P (Modulus p r) hm (pair_of_offdiag (a := a) i) =
      encode P (Modulus p r) hm (pair_of_offdiag (a := b) i) := by
    intro i
    apply Prod.ext
    · simpa [tensorEncode] using congrFun hs i
    · apply Prod.ext
      · simpa [tensorEncode] using congrFun hh i
      · simpa [tensorEncode] using congrFun hb i
  have hpairs : ∀ i : Fin k,
      pair_of_offdiag (a := a) i = pair_of_offdiag (a := b) i := by
    intro i
    exact encode_injective hm (hc i)
  have hz : a.1.z = b.1.z := by
    funext i
    have hp := congrArg Subtype.val (hpairs i)
    exact Fin.ext (congrArg (fun x : Fin (P + 1) × Fin (P + 1) => x.1.val) hp)
  have hw : a.1.w = b.1.w := by
    funext i
    have hp := congrArg Subtype.val (hpairs i)
    exact Fin.ext (congrArg (fun x : Fin (P + 1) × Fin (P + 1) => x.2.val) hp)
  have hu' : a.1.u = b.1.u := by simpa [tensorEncode] using hu
  have hv' : a.1.v = b.1.v := by simpa [tensorEncode] using hv
  exact lpoint_ext a.1 b.1 hz hw hu' hv'


lemma lOffdiag_card_le_tensor {s k P Q p q r : ℕ} {phi : Fin k → Polynomial ℤ}
    (hm : 0 < Modulus p r) :
    Fintype.card (LOffdiag s k P Q p q r phi) ≤
      Fintype.card (TensorPoint s k P Q p q r phi hm) :=
  Fintype.card_le_of_injective (tensorEncode hm) (tensorEncode_injective hm)

end FordOffdiagTensor

#print axioms FordOffdiagTensor.tensorEncode_injective
#print axioms FordOffdiagTensor.lOffdiag_card_le_tensor
