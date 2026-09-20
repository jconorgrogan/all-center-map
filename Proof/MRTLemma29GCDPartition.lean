import MRTLemma29CharacterExpansion

namespace MAPMRTLemma29Proof
open scoped BigOperators
open MAPMRTCorollary53Source
noncomputable section
set_option maxHeartbeats 800000

/-- Positive factorization/coprime coordinates whose product stays in `[1,N]`. -/
def gcdCoordinates (N q : ℕ) : Finset ((ℕ × ℕ) × ℕ) :=
  ((modulusFactorizations q).product (Finset.Icc 1 N)).filter fun p =>
    p.2.Coprime p.1.2 ∧ p.1.1 * p.2 ≤ N

def coprimeCoordinates (N q : ℕ) : Finset ((ℕ × ℕ) × ℕ) :=
  ((modulusFactorizations q).product (Finset.Icc 1 N)).filter fun p =>
    p.2.Coprime p.1.2

lemma gcd_mul_factorization {q q0 q1 n : ℕ}
    (hfac : q0 * q1 = q) (hcop : n.Coprime q1) :
    (q0 * n).gcd q = q0 := by
  rw [← hfac, Nat.gcd_mul_left, hcop.gcd_eq_one, mul_one]

lemma gcd_coordinate_partition
    {N q : ℕ} (hq : 1 ≤ q) (g : ℕ → ℂ) :
    (∑ m ∈ Finset.Icc 1 N, g m) =
      ∑ p ∈ gcdCoordinates N q, g (p.1.1 * p.2) := by
  let coord : (m : ℕ) → m ∈ Finset.Icc 1 N → ((ℕ × ℕ) × ℕ) :=
    fun m _ => (((m.gcd q), q / (m.gcd q)), m / (m.gcd q))
  apply Finset.sum_bij coord
  · intro m hm
    have hmI := Finset.mem_Icc.mp hm
    have hgpos : 0 < m.gcd q := Nat.gcd_pos_of_pos_left q hmI.1
    have hgdvdm : m.gcd q ∣ m := Nat.gcd_dvd_left m q
    have hgdvdq : m.gcd q ∣ q := Nat.gcd_dvd_right m q
    have hqdivpos : 0 < q / m.gcd q :=
      Nat.div_pos (Nat.le_of_dvd (by omega) hgdvdq) hgpos
    have hmdivpos : 0 < m / m.gcd q :=
      Nat.div_pos (Nat.le_of_dvd (by omega) hgdvdm) hgpos
    have hfac : m.gcd q * (q / m.gcd q) = q := Nat.mul_div_cancel' hgdvdq
    have hprod : m.gcd q * (m / m.gcd q) = m := Nat.mul_div_cancel' hgdvdm
    rw [gcdCoordinates, Finset.mem_filter]
    dsimp [coord]
    constructor
    · apply Finset.mem_product.mpr
      constructor
      · rw [modulusFactorizations, Finset.mem_filter]
        constructor
        · change (m.gcd q, q / m.gcd q) ∈
            (Finset.Icc 1 q).product (Finset.Icc 1 q)
          apply Finset.mem_product.mpr
          constructor <;> simp only [Finset.mem_Icc]
          · constructor
            · omega
            · exact (Nat.le_of_dvd (by omega) hgdvdq)
          · constructor
            · omega
            · exact Nat.div_le_self q _
        · exact hfac
      · exact Finset.mem_Icc.mpr ⟨by omega, (Nat.div_le_self m _).trans hmI.2⟩
    · constructor
      · exact Nat.coprime_div_gcd_div_gcd hgpos
      · simpa [hprod] using hmI.2
  · intro m hm n hn heq
    have hmul := congrArg (fun p : ((ℕ × ℕ) × ℕ) => p.1.1 * p.2) heq
    have hmdvd : m.gcd q ∣ m := Nat.gcd_dvd_left m q
    have hndvd : n.gcd q ∣ n := Nat.gcd_dvd_left n q
    simpa [coord, Nat.mul_div_cancel' hmdvd, Nat.mul_div_cancel' hndvd] using hmul
  · intro p hp
    rw [gcdCoordinates, Finset.mem_filter] at hp
    rcases hp with ⟨hpmem, hcop, hprodN⟩
    rcases Finset.mem_product.mp hpmem with ⟨hz, hnI⟩
    have hzfilter := (Finset.mem_filter.mp hz).2
    have hzprod := (Finset.mem_product.mp (Finset.mem_filter.mp hz).1)
    have hq0pos := (Finset.mem_Icc.mp hzprod.1).1
    have hq1pos := (Finset.mem_Icc.mp hzprod.2).1
    have hnpos := (Finset.mem_Icc.mp hnI).1
    refine ⟨p.1.1 * p.2, Finset.mem_Icc.mpr ⟨Nat.mul_pos hq0pos hnpos, hprodN⟩, ?_⟩
    dsimp [coord]
    have hgcd : (p.1.1 * p.2).gcd q = p.1.1 :=
      gcd_mul_factorization hzfilter hcop
    apply Prod.ext
    · apply Prod.ext
      · exact hgcd
      · rw [hgcd]
        rw [← hzfilter, Nat.mul_div_cancel_left]
        omega
    · rw [hgcd]
      rw [Nat.mul_div_cancel_left]
      omega
  · intro m hm
    dsimp [coord]
    have hgdvd : m.gcd q ∣ m := Nat.gcd_dvd_left m q
    rw [Nat.mul_div_cancel' hgdvd]

lemma gcd_coordinate_partition_supported
    {N q : ℕ} (hq : 1 ≤ q) (g : ℕ → ℂ)
    (hsupport : ∀ n, N < n → g n = 0) :
    (∑ m ∈ Finset.Icc 1 N, g m) =
      ∑ z ∈ modulusFactorizations q,
        ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n.Coprime z.2),
          g (z.1 * n) := by
  rw [gcd_coordinate_partition hq g]
  calc
    (∑ p ∈ gcdCoordinates N q, g (p.1.1 * p.2)) =
        ∑ p ∈ coprimeCoordinates N q, g (p.1.1 * p.2) := by
      apply Finset.sum_subset
      · intro p hp
        rw [gcdCoordinates, Finset.mem_filter] at hp
        rw [coprimeCoordinates, Finset.mem_filter]
        exact ⟨hp.1, hp.2.1⟩
      · intro p hpall hpnot
        rw [coprimeCoordinates, Finset.mem_filter] at hpall
        apply hsupport
        by_contra hle
        have hle' : p.1.1 * p.2 ≤ N := by omega
        apply hpnot
        rw [gcdCoordinates, Finset.mem_filter]
        exact ⟨hpall.1, hpall.2, hle'⟩
    _ = _ := by
      rw [coprimeCoordinates, Finset.sum_filter, Finset.product_eq_sprod,
        Finset.sum_product]
      apply Finset.sum_congr rfl
      intro z hz
      rw [Finset.sum_filter]

end
end MAPMRTLemma29Proof
