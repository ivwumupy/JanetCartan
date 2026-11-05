module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.SourceNegative.LocalizedQuadratures
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Preserve the source geometry under the inverse's actual inner cutoff

The fixed inner bump changes only the source cutoff and its derivative profile.
The original phase, gradient band and phase constants are retained. The product
support lies in the intersection of the original cutoff and inner bump supports;
no new phase, source family or inverse is selected.

Consumer: the source input of the normalized correction's finite inverse
remainder (`app:ch_regular:eq:inverse-remainder`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric MeasureTheory
open scoped ContDiff
namespace JanetCartan.ResponseTransfer.SourceNegative

/-- Construct the fixed cutoff profile for the actual inner multiplication in
`correctedSource`. The original source geometry supplies the phase and all its
bounds on the product support. The profile precedes all varying phases and slow
scales, and no plateau relation between the cutoffs is needed
(`app:ch_response:eq:response-actual-solver-formula`,
`app:ch_regular:eq:inverse-remainder`). -/
theorem exists_innerCutoff_source_geometry_profiles
    {n : ℕ} {x : Euclidean n} (χ₂ : ContDiffBump x)
    (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ) :
    ∃ Xloc : ℕ → ℝ, (∀ j, 0 ≤ Xloc j) ∧
      ∀ (φ : Euclidean n → ℝ) (S : Set (Euclidean n))
        (c G L : ℝ) (P X : ℕ → ℝ),
        SourceGeometry χ φ S c G L P X →
          SourceGeometry ((χ₂ : Euclidean n → ℝ) * χ) φ
            (tsupport ((χ₂ : Euclidean n → ℝ) * χ)) c G L P Xloc := by
  let cut : Euclidean n → ℝ := (χ₂ : Euclidean n → ℝ) * χ
  have hcut : ContDiff ℝ ∞ cut := χ₂.contDiff.mul hχ
  have hc : HasCompactSupport cut := χ₂.hasCompactSupport.of_isClosed_subset
    (isClosed_tsupport _) tsupport_mul_subset_left
  choose Xloc hXloc hbound using fun j ↦ hc.exists_bound_iteratedFDeriv hcut j
  refine ⟨Xloc,hXloc,?_⟩
  intro φ S c G L P X geometry
  have hsub : tsupport cut ⊆ S := tsupport_mul_subset_right.trans geometry.support_subset
  exact {
    cutoff_smooth := hcut
    phase_smooth := geometry.phase_smooth
    compact := hc
    support_subset := Subset.rfl
    lower_pos := geometry.lower_pos
    lower_lt_upper := geometry.lower_lt_upper
    scale_one_le := geometry.scale_one_le
    phase_constants_nonneg := geometry.phase_constants_nonneg
    cutoff_constants_nonneg := hXloc
    gradient_lower := fun y hy ↦ geometry.gradient_lower y (hsub hy)
    gradient_upper := fun y hy ↦ geometry.gradient_upper y (hsub hy)
    phase_derivatives := fun y hy j hj ↦ geometry.phase_derivatives y (hsub hy) j hj
    cutoff_derivatives := fun y j ↦ (hbound j j le_rfl y).trans
      (le_mul_of_one_le_right (hXloc j) (one_le_pow₀ geometry.scale_one_le)) }

end JanetCartan.ResponseTransfer.SourceNegative
