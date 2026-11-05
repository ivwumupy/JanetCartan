module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Derivative seminorms on compact coordinate domains

We use the sum of the suprema of the operator norms of the iterated derivatives.
On a fixed finite-dimensional domain this is equivalent to the componentwise maximum
used in paper.tex, so constants in estimates may change.

The real-valued supremum is used only with bounded derivative images (in particular,
smooth functions on compact sets). No estimate for an unbounded derivative image is intended.
-/

@[expose] public noncomputable section

open scoped ContDiff

namespace JanetCartan

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The C^r seminorm on a set; applications supply compactness and smoothness. -/
def cNorm (s : Set E) (r : ℕ) (f : E → F) : ℝ :=
  ∑ j ∈ Finset.range (r + 1), sSup ((fun x ↦ ‖iteratedFDeriv ℝ j f x‖) '' s)

/-- A graded derivative profile with a fixed baseline order. -/
def HasDerivativeProfile (s : Set E) (f : E → F) (r₀ : ℕ) (T : ℝ)
    (C : ℕ → ℝ) : Prop :=
  ∀ r : ℕ, cNorm s r f ≤ C r * T ^ (r - r₀)

end JanetCartan
