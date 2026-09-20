import FordTerminalKPower
import FordJ2PowerNormalization
import FordLemma33Actual

noncomputable section
set_option autoImplicit false
namespace FordJ2LPower
open MAPFordType MAPFordP16Source35Triangular MAPFordLemma32LiteralContract
open MAPFordCompleteSystemMoment FordJ2GeometricAlgebra MAPFordWeakPolicy

/-- The degree-zero L bound with the actual degree-one terminal theorem inserted.
Only the inductive uniform complete-moment estimate remains as analytic input. -/
theorem l_power_bound {s k r P Q M B p m : ℕ} {Delta C : ℝ}
    (hk : 2 ≤ k) (hs : 1 ≤ s) (hr : 2 ≤ r) (hrk : r ≤ k)
    (hP : 1 ≤ P) (hlarge : 16 * k ^ 4 < P)
    (hMfloor : M = Nat.floor ((P : ℝ) ^ (1 / (r : ℝ)))) (hM : k ≤ M)
    (hPsource : P ≤ (M + 1) ^ (k + 1)) (hB : 2 ^ (k ^ 3) ≤ B)
    (hQfloor : Q = Nat.floor ((P : ℝ) ^
      (1 - fordPhi1 (k : ℝ) Delta ((k : ℝ) - (r : ℝ)))))
    (hnative : (4 * s) ^ 2 * B * M ≤ Q)
    (hb : 1 / (r : ℝ) ≤ 1 - fordPhi1 (k : ℝ) Delta ((k : ℝ) - (r : ℝ)))
    (hp : Nat.floor ((P : ℝ) ^
      fordPhi1 (k : ℝ) Delta ((k : ℝ) - (r : ℝ))) < p)
    (phi : Fin k → Polynomial ℤ) (htype : FordType k 0 1 m (psiNatSucc phi))
    (hC : 0 ≤ C) (hlambda : 0 ≤ lambda (s : ℝ) (k : ℝ) Delta)
    (hJ : ∀ N : ℕ, 1 ≤ N → (completeMoment s k N : ℝ) ≤
      C * (N : ℝ) ^ lambda (s : ℝ) (k : ℝ) Delta) :
    (Fintype.card (LPoint s k P Q p 1 r phi) : ℝ) ≤
      (2 * (P : ℝ)) ^ k * C *
        (P : ℝ) ^ ((1 - fordPhi1 (k : ℝ) Delta ((k : ℝ) - (r : ℝ))) *
          lambda (s : ℝ) (k : ℝ) Delta) *
        max ((k : ℝ) ^ k)
          (2 * Real.sqrt (4 * (k : ℝ) ^ 3 * (B : ℝ) ^ countExponent s k r 1)) := by
  have hPpos : 0 < (P : ℝ) := by exact_mod_cast (show 0 < P by omega)
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hp0 : 0 < p := by omega
  have hB0 : 0 < B := lt_of_lt_of_le (by positivity) hB
  have hM0 : 0 < M := by omega
  have hQ1 : 1 ≤ Q := by
    have : 0 < (4 * s) ^ 2 * B * M := by positivity
    omega
  obtain ⟨upsilon, T, hnext, hTlo, hThi, hTsize, hL⟩ :=
    FordLemma33Actual.exists_typed_difference_count
      (s := s) (k := k) (d := 0) (m := m) (P := P) (Q := Q)
      (p := p) (q := 1) (r := r) (T := 1) phi htype (by norm_num)
      (by simp) hp0 (by norm_num) (by omega) hP (by omega)
  have hJbound : (completeMoment s k Q : ℝ) ≤ C * (P : ℝ) ^
      ((1 - fordPhi1 (k : ℝ) Delta ((k : ℝ) - (r : ℝ))) *
        lambda (s : ℝ) (k : ℝ) Delta) := by
    calc
      _ ≤ C * (Q : ℝ) ^ lambda (s : ℝ) (k : ℝ) Delta := hJ Q hQ1
      _ ≤ C * (((P : ℝ) ^
          (1 - fordPhi1 (k : ℝ) Delta ((k : ℝ) - (r : ℝ)))) ^
            lambda (s : ℝ) (k : ℝ) Delta) := by
        apply mul_le_mul_of_nonneg_left _ hC
        apply Real.rpow_le_rpow (Nat.cast_nonneg _) _ hlambda
        rw [hQfloor]
        exact Nat.floor_le (Real.rpow_nonneg hPpos.le _)
      _ = _ := by rw [← Real.rpow_mul hPpos.le]
  have hK := FordTerminalKPower.terminal_K_power_bound
    (s := s) (k := k) (r := r) (P := P) (Q := Q) (M := M) (B := B)
    (q := p) (T := T) hk hs hr hrk hP hlarge hMfloor hM hPsource hB
    hnative (le_of_eq hQfloor) hb (by omega) (by simpa using hTsize)
    hp0 m upsilon (by simpa using hnext) hC hlambda hJ
  have hE := countExponent_one hs (by omega : 1 ≤ k) hr
  change _ = eZero (s : ℝ) (k : ℝ) (r : ℝ) - 1 at hE
  rw [hE] at hK
  rw [FordJ2PowerNormalization.terminal_exponent_normalized hkpos.ne' hrpos.ne'] at hK
  have hpReal : (P : ℝ) ^ fordPhi1 (k : ℝ) Delta ((k : ℝ) - (r : ℝ)) ≤
      (p : ℝ) :=
    ((Nat.floor_lt (Real.rpow_nonneg hPpos.le _)).mp hp).le
  have hdiv := FordJ2PowerNormalization.divisor_power_lower
    (r := r) (k := k) hPpos hpReal
  exact FordJ2PowerNormalization.power_absorb
    (K := (Fintype.card (KPoint s k P Q upsilon p) : ℝ))
    hPpos (by positivity) (by positivity)
    (by positivity) (by positivity) hC (by positivity) (by positivity) hJbound
    (by simpa only [mul_assoc] using hK) hdiv (by simpa only [Nat.mul_one] using hL)

end FordJ2LPower
#print axioms FordJ2LPower.l_power_bound
