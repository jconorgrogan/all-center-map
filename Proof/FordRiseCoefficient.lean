import FordMixedKernelBounds

noncomputable section
namespace FordRiseCoefficient

open FordMixedKernelBounds

/-- The recursive coefficient is the cast of the natural ascending factorial. -/
theorem riseCoeff_eq_ascFactorial
    (p : ℕ) (hs : List ℝ) :
    riseCoeff p hs = (p.ascFactorial hs.length : ℝ) := by
  induction hs generalizing p with
  | nil => simp [riseCoeff, Nat.ascFactorial_zero]
  | cons h hs ih =>
      simp only [riseCoeff, List.length_cons]
      rw [ih]
      exact_mod_cast
        (Nat.succ_ascFactorial p hs.length).trans
          (Nat.ascFactorial_succ (n := p) (k := hs.length)).symm

/-- At base coefficient one, the recursive coefficient is exactly a factorial. -/
theorem riseCoeff_one_eq_factorial (hs : List ℝ) :
    riseCoeff 1 hs = (hs.length.factorial : ℝ) := by
  rw [riseCoeff_eq_ascFactorial, Nat.one_ascFactorial]

/-- The factorial coefficient is positive, including the empty-list case. -/
theorem riseCoeff_one_pos (hs : List ℝ) :
    0 < riseCoeff 1 hs := by
  exact riseCoeff_pos (p := 1) (by omega)

end FordRiseCoefficient

#print axioms FordRiseCoefficient.riseCoeff_eq_ascFactorial
#print axioms FordRiseCoefficient.riseCoeff_one_eq_factorial
#print axioms FordRiseCoefficient.riseCoeff_one_pos
