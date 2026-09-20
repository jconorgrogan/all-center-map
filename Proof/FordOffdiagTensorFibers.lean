import FordOffdiagTensor

open scoped BigOperators
open FordDifferencePairs MAPFordLemma32LiteralContract FordOffdiagTensor
noncomputable section
set_option autoImplicit false
namespace FordOffdiagTensorFibers

abbrev FiberIndex (k P m : ℕ) := (Fin k → Bool) × (Fin k → PositiveHeight P m)

abbrev TensorFiber (s k P Q p q r : ℕ) (phi : Fin k → Polynomial ℤ)
    (hm : 0 < Modulus p r) (σ : Fin k → Bool)
    (η : Fin k → PositiveHeight P (Modulus p r)) :=
  {x : TensorPoint s k P Q p q r phi hm // x.sign = σ ∧ x.height = η}

instance tensorFiberFintype {s k P Q p q r : ℕ} (phi : Fin k → Polynomial ℤ)
    (hm : 0 < Modulus p r) (σ : Fin k → Bool)
    (η : Fin k → PositiveHeight P (Modulus p r)) :
    Fintype (TensorFiber s k P Q p q r phi hm σ η) := by
  classical infer_instance

def positiveHeightEquiv {P m : ℕ} : PositiveHeight P m ≃ Fin (P / m) :=
  { toFun := fun h => ⟨h.1.val - 1, by have hh := h.1.isLt; have hp := h.2; omega⟩
    invFun := fun x => ⟨⟨x.val + 1, by exact Nat.add_lt_add_right x.isLt 1⟩, by simpa [Nat.succ_eq_add_one] using Nat.succ_pos x.val⟩
    left_inv := by intro h; apply Subtype.ext; apply Fin.ext; dsimp; have hp := h.2; omega
    right_inv := by intro x; apply Fin.ext; dsimp }

lemma positiveHeight_card {P m : ℕ} :
    Fintype.card (PositiveHeight P m) = P / m := by
  simpa using Fintype.card_congr (positiveHeightEquiv (P := P) (m := m))

lemma fiberIndex_card {k P m : ℕ} :
    Fintype.card (FiberIndex k P m) = 2 ^ k * (P / m) ^ k := by
  simp only [FiberIndex, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool, positiveHeight_card]

def tensorToFiber {s k P Q p q r : ℕ} {phi : Fin k → Polynomial ℤ}
    (hm : 0 < Modulus p r) :
    TensorPoint s k P Q p q r phi hm →
      Sigma (fun idx : FiberIndex k P (Modulus p r) =>
        TensorFiber s k P Q p q r phi hm idx.1 idx.2) := by
  intro x
  exact ⟨(x.sign, x.height), x, rfl, rfl⟩

def fiberToTensor {s k P Q p q r : ℕ} {phi : Fin k → Polynomial ℤ}
    (hm : 0 < Modulus p r) :
    Sigma (fun idx : FiberIndex k P (Modulus p r) =>
      TensorFiber s k P Q p q r phi hm idx.1 idx.2) →
      TensorPoint s k P Q p q r phi hm := fun z => z.2.1

lemma fiberToTensor_left_inverse {s k P Q p q r : ℕ} {phi : Fin k → Polynomial ℤ}
    (hm : 0 < Modulus p r) (x : TensorPoint s k P Q p q r phi hm) :
    fiberToTensor hm (tensorToFiber hm x) = x := by
  rfl

lemma tensorToFiber_injective {s k P Q p q r : ℕ} {phi : Fin k → Polynomial ℤ}
    (hm : 0 < Modulus p r) : Function.Injective (tensorToFiber (s := s) (k := k) (P := P)
      (Q := Q) (p := p) (q := q) (r := r) (phi := phi) hm) := by
  intro x y h
  have hh := congrArg (fiberToTensor hm) h
  simpa [fiberToTensor, fiberToTensor_left_inverse] using hh

lemma fiberToTensor_injective {s k P Q p q r : ℕ} {phi : Fin k → Polynomial ℤ}
    (hm : 0 < Modulus p r) : Function.Injective (fiberToTensor (s := s) (k := k) (P := P)
      (Q := Q) (p := p) (q := q) (r := r) (phi := phi) hm) := by
  rintro ⟨idx, x⟩ ⟨idy, y⟩ h
  have hxy : x.1 = y.1 := by
    simpa [fiberToTensor] using h
  have hi : idx = idy := by
    apply Prod.ext
    · exact x.2.1.symm.trans ((congrArg TensorPoint.sign hxy).trans y.2.1)
    · exact x.2.2.symm.trans ((congrArg TensorPoint.height hxy).trans y.2.2)
  cases hi
  apply Sigma.ext
  · rfl
  · exact heq_of_eq (Subtype.ext hxy)


theorem tensor_card_eq_sum_fixed_sign_height {s k P Q p q r : ℕ}
    {phi : Fin k → Polynomial ℤ} (hm : 0 < Modulus p r) :
    Fintype.card (TensorPoint s k P Q p q r phi hm) =
      ∑ σ : Fin k → Bool, ∑ η : Fin k → PositiveHeight P (Modulus p r),
        Fintype.card (TensorFiber s k P Q p q r phi hm σ η) := by
  have h₁ : Fintype.card (TensorPoint s k P Q p q r phi hm) ≤
      Fintype.card (Sigma (fun idx : FiberIndex k P (Modulus p r) =>
        TensorFiber s k P Q p q r phi hm idx.1 idx.2)) :=
    Fintype.card_le_of_injective (tensorToFiber hm) (tensorToFiber_injective (s := s) (k := k) (P := P) (Q := Q) (p := p) (q := q) (r := r) (phi := phi) hm)
  have h₂ : Fintype.card (Sigma (fun idx : FiberIndex k P (Modulus p r) =>
        TensorFiber s k P Q p q r phi hm idx.1 idx.2)) ≤
      Fintype.card (TensorPoint s k P Q p q r phi hm) :=
    Fintype.card_le_of_injective (fiberToTensor (s := s) (k := k) (P := P) (Q := Q) (p := p) (q := q) (r := r) (phi := phi) hm) (fiberToTensor_injective (s := s) (k := k) (P := P) (Q := Q) (p := p) (q := q) (r := r) (phi := phi) hm)
  have hc : Fintype.card (TensorPoint s k P Q p q r phi hm) =
      Fintype.card (Sigma (fun idx : FiberIndex k P (Modulus p r) =>
        TensorFiber s k P Q p q r phi hm idx.1 idx.2)) := Nat.le_antisymm h₁ h₂
  rw [hc]
  simpa [FiberIndex] using
    (Fintype.sum_prod_type' (fun (σ : Fin k → Bool)
      (η : Fin k → PositiveHeight P (Modulus p r)) =>
      Fintype.card (TensorFiber s k P Q p q r phi hm σ η)))

end FordOffdiagTensorFibers

#print axioms FordOffdiagTensorFibers.tensor_card_eq_sum_fixed_sign_height
