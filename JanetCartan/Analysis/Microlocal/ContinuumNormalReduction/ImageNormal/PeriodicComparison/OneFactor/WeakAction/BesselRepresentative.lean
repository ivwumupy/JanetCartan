module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.PeriodicComparison.OneFactor.WeakAction.BesselRepresentative.Localized

/-!
# The smooth localized representative of the actual periodic Bessel lift

This constructs both inputs needed by
`periodicChannel_schwartz_action_of_localized_besselLift` from the original
real L² datum and its Schwartz representative. The H¹ lift is the actual
periodic Bessel inverse of the source-masked datum. The localized comparison
retains its explicit nonzero-lattice remainder and both original measures
(`app:ch_background:prop:bg-frame`, Step 1, image-normal paragraph).
-/

public noncomputable section

open MeasureTheory
open scoped ContDiff SchwartzMap
open JanetCartan.PeriodicLocalL2
open JanetCartan.Pseudodifferential.DifferentialChart

namespace JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicComparison

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- A smooth representative of the actual source-masked periodic H¹ Bessel
lift, together with its pointwise localized Euclidean comparison. This
constructs the `hlift` and `hcomparison` inputs of
`periodicChannel_schwartz_action_of_localized_besselLift`; neither identity
nor the existence of a smooth inverse representative is assumed
(`app:ch_background:prop:bg-frame`, Step 1, image-normal paragraph). -/
theorem exists_smooth_localized_periodicBesselLift (_hd : 0 < d)
    {r R : ℝ} (hr : r < 1 / 2) (hR₀ : 0 < R) (hrR : r < R) (hR : R < 1 / 2)
    (χ ρ : E → ℝ) (hχ : ContDiff ℝ ∞ χ) (hρ : ContDiff ℝ ∞ ρ)
    (hχs : tsupport χ ⊆ chartBox r) (hρs : tsupport ρ ⊆ chartBox R)
    (v : Fin d → 𝓢(E, ℂ)) (f : EuclideanL2 d E)
    (hf : l2ComplexInclusion volume f =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (fun j ↦ v j x)) :
    ∃ (w : Torus d → E) (hw : IsSmoothPeriodic w),
      ContinuumRow.periodicBesselLift
        (ContinuumRow.cutoffMultiplier (periodizedCutoff hr χ hχ hχs) (toTorus (𝕜 := ℝ) f)) =
        PeriodicSobolevSpace.ofSmooth 1 w hw ∧
      ∀ x j, (ρ x : ℂ) * (periodicLift w x j : ℂ) =
        (ρ x : ℂ) * imageBesselSchwartzCLM
          (SchwartzMap.smulLeftCLM ℂ (fun y ↦ (χ y : ℂ)) (v j)) x +
        ∫ y, (localizedImageBesselRemainder ρ χ x y : ℂ) * v j y := by
  obtain ⟨w, hw, hlift⟩ :=
    BesselRepresentative.exists_smooth_periodicBesselLift hr χ hχ hχs v f hf
  exact ⟨w, hw, hlift, BesselRepresentative.localized_comparison_of_smooth_lift
    hr hR₀ hrR hR χ ρ hχ hρ hχs hρs v f hf w hw hlift⟩

end JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicComparison
