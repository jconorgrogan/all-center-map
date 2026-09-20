import FordFamilyMaximum
import FordFamilyDoubling

open scoped BigOperators
open MAPFordType MAPFordP16Source35Triangular MAPFordLemma32LiteralContract
open MAPFordFamilyDoubling

noncomputable section
namespace FordFamilyMaxDouble

 theorem exists_maximal_doubling_member
    {s k d P Q q : ℕ} {T : ℤ}
    (m0 : ℕ) (psi0 : Fin k → Polynomial ℤ)
    (h0 : FordType k d T m0 (psiNatSucc psi0)) :
    ∃ (m : ℕ) (psi : Fin k → Polynomial ℤ),
      FordType k d T m (psiNatSucc psi) ∧
      FordType k d T (m + 1) (psiNatSucc (doublePsi psi)) ∧
      Fintype.card (KPoint s k P Q (doublePsi psi) q) ≤
        Fintype.card (KPoint s k P Q psi q) ∧
      ∀ (m' : ℕ) (psi' : Fin k → Polynomial ℤ),
        FordType k d T m' (psiNatSucc psi') →
          Fintype.card (KPoint s k P Q psi' q) ≤
            Fintype.card (KPoint s k P Q psi q) := by
  obtain ⟨m, psi, hpsi, hmax⟩ :=
    FordFamilyMaximum.exists_maximal_ford_family_member
      (s := s) (k := k) (d := d) (P := P) (Q := Q) (q := q)
      (T := T) m0 psi0 h0
  have hdouble : FordType k d T (m + 1)
      (psiNatSucc (doublePsi psi)) :=
    ford_type_double_fin psi hpsi
  have hdom := hmax (m + 1) (doublePsi psi) hdouble
  exact ⟨m, psi, hpsi, hdouble, hdom, hmax⟩

end FordFamilyMaxDouble

#print axioms FordFamilyMaxDouble.exists_maximal_doubling_member
