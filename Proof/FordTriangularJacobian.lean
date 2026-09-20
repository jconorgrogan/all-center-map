import FordP16LiteralResidueBridge
import FordP16Source35Triangular
import FordTypeTriangularTranslation

open scoped BigOperators
open Polynomial

namespace MAPFordTriangularJacobian
noncomputable section
set_option maxHeartbeats 1200000

def translationMatrix {k d : ℕ} (hdk : d ≤ k) (q c : ℤ) :
    Matrix (Fin (k-d)) (Fin (k-d)) ℤ := fun i j =>
  if i.val ≤ j.val then
    (Nat.choose (d + j.val + 1) (d + i.val + 1) : ℤ) *
      (q*c) ^ (j.val - i.val)
  else 0

lemma translationMatrix_diag {k d : ℕ} (hdk : d ≤ k) (q c : ℤ) (i : Fin (k-d)) :
    translationMatrix hdk q c i i = 1 := by
  simp [translationMatrix]

lemma translationMatrix_upper {k d : ℕ} (hdk : d ≤ k) (q c : ℤ) :
    (translationMatrix hdk q c).BlockTriangular id := by
  intro i j hji
  have hji' : j.val < i.val := by exact_mod_cast hji
  have hnot : ¬ i.val ≤ j.val := by omega
  simp [translationMatrix, hnot]

lemma det_translationMatrix {k d : ℕ} (hdk : d ≤ k) (q c : ℤ) :
    (translationMatrix hdk q c).det = 1 := by
  rw [Matrix.det_of_upperTriangular (translationMatrix_upper hdk q c)]
  simp [translationMatrix_diag]

end
end MAPFordTriangularJacobian

namespace MAPFordP16LiteralResidueBridge
noncomputable section
set_option maxHeartbeats 1200000
open MAPFordCoarseP18Jacobian
open MAPFordP16Source35Triangular
open MAPFordType

/-- Literal binomial translation on the p.16 tail rows. -/
def triangularTailTranslation {k d : ℕ} (hdk : d ≤ k)
    (psi : Fin k → Polynomial ℤ) (q c : ℤ) :
    Fin (k-d) → Polynomial ℤ := fun j =>
  ∑ i : Fin (k-d),
    if i.val ≤ j.val then
      C (Nat.choose (d + j.val + 1) (d + i.val + 1) : ℤ) *
        psi ⟨d + i.val, by omega⟩ * C ((q*c) ^ (j.val - i.val))
    else 0

lemma triangularTailTranslation_sourceJacobian_mul
    {k d P : ℕ} (hdk : d ≤ k) (psi : Fin k → Polynomial ℤ)
    (q c : ℤ) (z : Fin k → Fin (P + 1)) :
    sourceJacobian (triangularTailTranslation hdk psi q c)
      (fordTailCoordinates hdk z) =
    sourceJacobian (fordTailPolynomials (k := k) (d := d) hdk psi) (fordTailCoordinates (k := k) (d := d) (P := P) hdk z) *
      MAPFordTriangularJacobian.translationMatrix hdk q c := by
  classical
  ext r j
  simp only [sourceJacobian, Matrix.mul_apply, triangularTailTranslation,
    fordTailCoordinates, fordTailPolynomials]
  simp only [Polynomial.derivative_sum]
  change (Polynomial.eval₂RingHom (RingHom.id ℤ) ((z ⟨r.val, by omega⟩).val : ℤ))
    (∑ b : Fin (k - d), Polynomial.derivative
      (if b.val ≤ j.val then C (Nat.choose (d + j.val + 1) (d + b.val + 1) : ℤ) *
        psi ⟨d + b.val, by omega⟩ * C ((q*c) ^ (j.val - b.val)) else 0)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hle : i.val ≤ j.val
  · rw [if_pos hle]
    simp [Polynomial.derivative_mul, Polynomial.derivative_pow,
      MAPFordTriangularJacobian.translationMatrix, hle]
    ring
  · rw [if_neg hle]
    simp [MAPFordTriangularJacobian.translationMatrix, hle]

lemma triangularTailTranslation_det_eq
    {k d P : ℕ} (hdk : d ≤ k) (psi : Fin k → Polynomial ℤ)
    (q c : ℤ) (z : Fin k → Fin (P + 1)) :
    (sourceJacobian (triangularTailTranslation hdk psi q c)
      (fordTailCoordinates hdk z)).det =
    (sourceJacobian (fordTailPolynomials hdk psi)
      (fordTailCoordinates hdk z)).det := by
  rw [triangularTailTranslation_sourceJacobian_mul]
  rw [Matrix.det_mul, MAPFordTriangularJacobian.det_translationMatrix, mul_one]

lemma triangularTailTranslation_mask_iff
    {p k d P : ℕ} (hdk : d ≤ k) (hp : p.Prime)
    (psi : Fin k → Polynomial ℤ) (q c : ℤ) (z : Fin k → Fin (P + 1)) :
    p.Coprime (sourceJacobian (triangularTailTranslation hdk psi q c)
      (fordTailCoordinates hdk z)).det.natAbs ↔
    p.Coprime (sourceJacobian (fordTailPolynomials hdk psi)
      (fordTailCoordinates hdk z)).det.natAbs := by
  rw [triangularTailTranslation_det_eq]

/-- Tail equality with the actual `phiRow` from the source-35 bridge. -/
lemma phiRow_tail_eq_triangularTailTranslation
    {k d : ℕ} (hdk : d ≤ k)
    (psi : Fin k → Polynomial ℤ) (q c : ℤ)
    (hzero : ∀ i : Fin k, i.val < d → psi i = 0) :
    fordTailPolynomials hdk (phiRow psi q c) =
      triangularTailTranslation hdk psi q c := by
  funext j
  simp only [fordTailPolynomials, phiRow, triangularTranslation,
    triangularTailTranslation]
  let F : ℕ → Polynomial ℤ := fun x =>
    C (Nat.choose (d + j.val + 1) x : ℤ) * psiNatSucc psi x *
      C ((q * c) ^ (d + j.val + 1 - x))
  change (∑ x ∈ Finset.range (d + j.val + 1 + 1), F x) = _
  have hlow : ∀ x ∈ Finset.range (d + 1), F x = 0 := by
    intro x hx
    have hxltall : x < d + 1 := Finset.mem_range.mp hx
    by_cases hx0 : x = 0
    · simp [F, psiNatSucc, hx0]
    · have hxpos : 1 ≤ x := Nat.one_le_iff_ne_zero.mpr hx0
      have hxlt : x - 1 < d := by omega
      have hpsi : psiNatSucc psi x = 0 := by
        simp [psiNatSucc, hx0, psiNat, hxlt, hzero]
      simp [F, hpsi]
  have hshift : ∀ i : Fin (k-d), i.val ≤ j.val →
      F (d + i.val + 1) =
        (if i.val ≤ j.val then
          C (Nat.choose (d + j.val + 1) (d + i.val + 1) : ℤ) *
            psi ⟨d + i.val, by omega⟩ * C ((q*c) ^ (j.val - i.val))
        else 0) := by
    intro i hi
    have hsum : d + (k - d) = k := Nat.add_sub_of_le hdk
    have hdi : d + i.val < k := by
      have hh : d + i.val < d + (k - d) := Nat.add_lt_add_left i.isLt d
      simpa only [hsum] using hh
    simp only [F, psiNatSucc, ne_eq, Nat.add_eq_zero, one_ne_zero, false_or,
      psiNat, show d + i.val + 1 - 1 = d + i.val by omega]
    rw [dif_pos hdi]
    have hpow : d + j.val + 1 - (d + i.val + 1) = j.val - i.val := by omega
    have hii : i ≤ j := Fin.mk_le_mk.mpr hi
    have hnot : ¬ j < i := not_lt_of_ge hii
    simp [hpow, hnot]
  have hsplit := Finset.sum_range_add F (d + 1) (j.val + 1)
  have hrest :
      (∑ i : Fin (k-d), if i.val ≤ j.val then
        C (Nat.choose (d + j.val + 1) (d + i.val + 1) : ℤ) *
          psi ⟨d + i.val, by omega⟩ * C ((q*c) ^ (j.val - i.val)) else 0) =
      ∑ i ∈ Finset.Iic j,
        (if i.val ≤ j.val then
          C (Nat.choose (d + j.val + 1) (d + i.val + 1) : ℤ) *
            psi ⟨d + i.val, by omega⟩ * C ((q*c) ^ (j.val - i.val)) else 0) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i hi hnot
    simp only [Finset.mem_Iic] at hnot
    simp [hnot]
  have hreindex :
      (∑ i ∈ Finset.Iic j,
        (if i.val ≤ j.val then
          C (Nat.choose (d + j.val + 1) (d + i.val + 1) : ℤ) *
            psi ⟨d + i.val, by omega⟩ * C ((q*c) ^ (j.val - i.val)) else 0)) =
      ∑ x ∈ Finset.range (j.val + 1), F (d + x + 1) := by
    apply Finset.sum_bij (fun i _ => i.val)
    · intro i hi
      simp only [Finset.mem_Iic] at hi
      simp
      omega
    · intro i₁ h₁ i₂ h₂ heq
      exact Fin.ext heq
    · intro x hx
      have hxj : x < j.val + 1 := Finset.mem_range.mp hx
      refine ⟨⟨x, by omega⟩, ?_, rfl⟩
      simp only [Finset.mem_Iic]
      exact Fin.mk_le_mk.mpr (by omega)
    · intro i hi
      rw [hshift i (by simp only [Finset.mem_Iic] at hi; exact hi)]
  rw [show d + j.val + 1 + 1 = (d + 1) + (j.val + 1) by omega]
  rw [hsplit]
  have hlow_sum : (∑ x ∈ Finset.range (d + 1), F x) = 0 :=
    Finset.sum_eq_zero hlow
  rw [hlow_sum, zero_add]
  have horder : (∑ x ∈ Finset.range (j.val + 1), F (d + 1 + x)) =
      ∑ x ∈ Finset.range (j.val + 1), F (d + x + 1) := by
    apply Finset.sum_congr rfl
    intro x hx
    congr 1 <;> omega
  calc
    (∑ x ∈ Finset.range (j.val + 1), F (d + 1 + x)) =
        ∑ x ∈ Finset.range (j.val + 1), F (d + x + 1) := horder
    _ = ∑ i ∈ Finset.Iic j, (if i.val ≤ j.val then
          C (Nat.choose (d + j.val + 1) (d + i.val + 1) : ℤ) *
            psi ⟨d + i.val, by omega⟩ * C ((q*c) ^ (j.val - i.val)) else 0) := hreindex.symm
    _ = ∑ i : Fin (k-d), if i.val ≤ j.val then
          C (Nat.choose (d + j.val + 1) (d + i.val + 1) : ℤ) *
            psi ⟨d + i.val, by omega⟩ * C ((q*c) ^ (j.val - i.val)) else 0 := hrest.symm

end
end MAPFordP16LiteralResidueBridge

namespace MAPFordP16LiteralResidueBridge
noncomputable section
open MAPFordP16Source35Triangular

theorem fordPolynomialMask_phiRow_iff
    {p k d P : ℕ} (hdk : d ≤ k) (hp : p.Prime)
    (psi : Fin k → Polynomial ℤ) (q c : ℤ)
    (hzero : ∀ i : Fin k, i.val < d → psi i = 0)
    (z : Fin k → Fin (P + 1)) :
    MAPFordP16LiteralResidueBridge.fordPolynomialMask (p := p) (k := k) (d := d) (P := P) hdk hp (phiRow psi q c) z ↔
      MAPFordP16LiteralResidueBridge.fordPolynomialMask (p := p) (k := k) (d := d) (P := P) hdk hp psi z := by
  simp only [MAPFordP16LiteralResidueBridge.fordPolynomialMask]
  rw [phiRow_tail_eq_triangularTailTranslation hdk psi q c hzero]
  constructor
  · intro h
    exact ⟨h.1, (triangularTailTranslation_mask_iff hdk hp psi q c z).mp h.2⟩
  · intro h
    exact ⟨h.1, (triangularTailTranslation_mask_iff hdk hp psi q c z).mpr h.2⟩

end
end MAPFordP16LiteralResidueBridge

#print axioms MAPFordP16LiteralResidueBridge.phiRow_tail_eq_triangularTailTranslation
#print axioms MAPFordP16LiteralResidueBridge.fordPolynomialMask_phiRow_iff
#print axioms MAPFordTriangularJacobian.translationMatrix_upper
#print axioms MAPFordTriangularJacobian.det_translationMatrix
#print axioms MAPFordP16LiteralResidueBridge.triangularTailTranslation_sourceJacobian_mul
#print axioms MAPFordP16LiteralResidueBridge.triangularTailTranslation_det_eq
#print axioms MAPFordP16LiteralResidueBridge.triangularTailTranslation_mask_iff
