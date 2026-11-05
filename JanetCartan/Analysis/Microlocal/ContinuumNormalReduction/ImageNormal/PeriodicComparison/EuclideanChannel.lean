module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.PeriodicComparison.EuclideanChannel.Actions
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.PeriodicComparison.EuclideanChannel.Sobolev

/-!
# Bounded Euclidean image channel

The actual finite matrix construction for `app:ch_background:prop:bg-frame`,
Step 1, is `PeriodicComparison.euclideanChannel`. This same bounded real
operator retains `tsupport μ` on every input, realizes `channelSchwartz` and
`channelAdjointSchwartz` through its forward action and literal Hilbert
adjoint, and preserves Fourier H¹. The action theorems supply the two inputs
of `normal_schwartz_action_of_channel_actions`; the estimate below supplies
exactly `hB` of `normalCrossTerms_sobolev_one_bounds`.

All analytic inputs are proved from the smooth real coefficients and smooth
compactly supported masks. No growth bound on unmasked coefficients or
bounded realization of the first-order operator alone is assumed.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff
open JanetCartan.PeriodicLocalL2 JanetCartan.Pseudodifferential

namespace JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicComparison

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "R²" => EuclideanL2 d E

/-- The actual bounded real image channel preserves H¹, with the exact
complex-inclusion norm used by `normalCrossTerms_sobolev_one_bounds`
(`app:ch_background:prop:bg-frame`, Step 1). The complex channel estimate
transfers through the proved reality identity for the same `euclideanChannel`.
-/
theorem euclideanChannel_sobolev_one_bound
    (A : E → Fin d → Matrix (Fin d) (Fin d) ℝ)
    (Z : E → Matrix (Fin d) (Fin d) ℝ) (χ μ : E → ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hμ : ContDiff ℝ ∞ μ) (hμc : HasCompactSupport μ) :
    ∃ CB : ℝ, 0 ≤ CB ∧ ∀ f : R²,
      MemVectorFourierSobolev 1 (l2ComplexInclusion volume f) →
      MemVectorFourierSobolev 1 (l2ComplexInclusion volume
        (euclideanChannel A Z χ μ hA hZ hχ hχc hμ hμc f)) ∧
      vectorFourierSobolevNorm 1 (l2ComplexInclusion volume
        (euclideanChannel A Z χ μ hA hZ hχ hχc hμ hμc f)) ≤
          CB * vectorFourierSobolevNorm 1 (l2ComplexInclusion volume f) := by
  obtain ⟨CB, hCB, hB⟩ :=
    complexEuclideanChannel_sobolev_one_bound A Z χ μ hA hZ hχ hχc hμ hμc
  refine ⟨CB, hCB, fun f hf ↦ ?_⟩
  rw [euclideanChannel_complexInclusion]
  exact hB (l2ComplexInclusion volume f) hf

end JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicComparison
