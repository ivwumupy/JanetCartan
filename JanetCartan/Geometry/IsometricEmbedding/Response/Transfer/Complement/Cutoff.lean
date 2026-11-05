module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.HighEnvelope.Cutoff
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# The internal envelope cutoff

Construct the smooth cutoff used only in the proof of the complete complement
in `app:ch_response:thm:response-literal-transfer`. This removes any cutoff
existence premise from the consuming forward/reverse graph estimates.
-/

@[expose] public noncomputable section
namespace JanetCartan.ResponseTransfer.Complement

/-- A genuine smooth cutoff equal to one through `Λ` and zero from `2Λ`,
bounded by one. Its physical-covector conversion is supplied by
`EnvelopeCutoff.physicalCovectorCutoff`.
Source: `app:ch_response:thm:response-literal-transfer`. -/
def internalEnvelopeCutoff (n : ℕ) (Λ : ℝ) (hΛ : 0 < Λ) : EnvelopeCutoff n Λ 1 2 := by
  let b : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
    ⟨Λ, 2 * Λ, hΛ, by linarith⟩
  exact {
    symbol := b
    smooth := b.contDiff
    bound_nonneg := zero_le_one
    bound := fun x ↦ by rw [abs_of_nonneg b.nonneg]; exact b.le_one
    one_on_ball := fun x hx ↦ b.one_of_mem_closedBall (by simpa [b] using hx)
    zero_outside := fun x hx ↦ b.zero_of_le_dist (by simpa [b] using hx) }

end JanetCartan.ResponseTransfer.Complement
