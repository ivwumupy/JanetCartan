module

public import JanetCartan.Iteration.PhysicalBackground.NativeDensityProfiles

/-!
# The one fixed source-profile shift used by the actual Source53 application

The native density producer gives the literal size-`σ` profile at order
`16 + rSrc` for the unscaled initial coefficient `A`.  The original Fourier
source consumes exactly the shifted coefficient `A(k+16)` at order `k`; this
lemma is only the index/reserve reindexing, with no new source row, threshold,
scalar, cutoff, or response estimate.  The existing Source39 row producer and
its sole native scalar getter remain downstream consumers.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

namespace JanetCartan.PhysicalPrimary.OriginalInitialSourceApplication

/-- Reindex the genuine size-`σ` native initial profile by the one fixed
Source53 shift.  `A` is unscaled; `σ` occurs exactly once and is not inferred
from a sample weight.  The set `I` is the native `labelSet` (definitionally the
Source53 closed ball), and `f` is the actual positive scalar field. -/
theorem after16 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (I : Set E) (f : E → ℝ) (K σ : ℝ) (A : ℕ → ℝ) (rSrc : ℕ)
    (hInitial : HasDerivativeProfile I f (16 + rSrc) K
      (fun k ↦ σ * A k)) :
    ∀ k, cNorm I (k + 16) f ≤ A (k + 16) * σ * K ^ (k - rSrc) := by
  intro k
  have hindex : k + 16 - (16 + rSrc) = k - rSrc := by omega
  have h := hInitial (k + 16)
  simpa only [hindex, mul_comm σ (A (k + 16))] using h

theorem source52_of_after16 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (I : Set E) (f : E → ℝ) (K σ : ℝ) (A : ℕ → ℝ) (rSrc : ℕ)
    (hInitial : HasDerivativeProfile I f (16 + rSrc) K
      (fun k ↦ σ * A k)) :
    ∀ k, cNorm I (k + 16) f ≤ A (k + 16) * σ * K ^ (k - rSrc) :=
  after16 I f K σ A rSrc hInitial

end JanetCartan.PhysicalPrimary.OriginalInitialSourceApplication

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalInitialSourceApplication
open Lean Meta

/-- Meta-level constructor used by the actual source39/Source53 spine. It
only applies the checked `after16` theorem; all native rows, scalar, history,
thresholds and response arguments are supplied by the consuming application. -/
def apply_source53_after16 (I f K σ A rSrc hInitial : Expr) : MetaM Expr :=
  mkAppM ``after16 #[I,f,K,σ,A,rSrc,hInitial]

end JanetCartan.PhysicalPrimary.OriginalInitialSourceApplication
end
