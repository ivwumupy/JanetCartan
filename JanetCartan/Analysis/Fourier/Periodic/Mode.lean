module

public import JanetCartan.Analysis.Fourier.Periodic

/-!
# Real Fourier modes

The shared real-pair reconstruction convention in Appendices A and B of `paper.tex`.
-/

@[expose] public noncomputable section

namespace JanetCartan

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The real Fourier mode associated with a pair of real coefficients. -/
def periodicFourierMode (k : Fin n → ℤ) (a : F × F) (x : Torus n) : F :=
  (UnitAddTorus.mFourier k x).re • a.1 - (UnitAddTorus.mFourier k x).im • a.2

/-- The same mode with its real and imaginary coefficient components supplied separately. -/
abbrev periodicFourierModeOfParts (k : Fin n → ℤ) (a b : F) (x : Torus n) : F :=
  periodicFourierMode k (a, b) x

end JanetCartan
