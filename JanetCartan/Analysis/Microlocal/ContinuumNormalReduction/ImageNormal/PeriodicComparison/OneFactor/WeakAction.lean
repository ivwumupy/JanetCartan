module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.PeriodicComparison.OneFactor.WeakAction.KernelAction
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.PeriodicComparison.OneFactor.WeakAction.ChannelAction
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.PeriodicComparison.OneFactor.WeakAction.BesselRepresentative

/-!
# The differentiated Schwartz action of the actual periodic image channel

For `app:ch_background:prop:bg-frame`, Step 1, the actual periodic image
channel agrees with the Euclidean Schwartz channel plus the integral of the
one-factor remainder kernel. The smooth representative of the actual masked
periodic H¹ lift and its localized Bessel comparison are constructed from
the original real L² datum. Differentiation, plateau cancellation, the weak
coefficient operator and both measures are justified.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff SchwartzMap
open JanetCartan.PeriodicLocalL2
open JanetCartan.Pseudodifferential.DifferentialChart
open JanetCartan.ContinuumRow

namespace JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicComparison

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Independent downstream deduction for the actual image channel. The
`hlift` and `hcomparison` inputs belong to the smooth localized Bessel-lift
construction, before applying the coefficient operator. The parent must
instantiate them for its original real L² input and Schwartz representative
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem periodicChannel_schwartz_action_of_localized_besselLift
    {r R : ℝ} (hr : r < 1 / 2) (hrR : r < R) (hR : R < 1 / 2)
    (c : GeometricProfile.ReducedCoefficientIndex d → C(Torus d, ℝ))
    (χ μ ρ : E → ℝ) (hχ : ContDiff ℝ ∞ χ) (hμ : ContDiff ℝ ∞ μ)
    (hρ : ContDiff ℝ ∞ ρ)
    (hχs : tsupport χ ⊆ chartBox r) (hμs : tsupport μ ⊆ chartBox r)
    (hρs : tsupport ρ ⊆ chartBox R)
    (hplateau : ∀ x ∈ tsupport μ, ρ =ᶠ[nhds x] (fun _ ↦ 1))
    (A : E → Fin d → Matrix (Fin d) (Fin d) ℝ)
    (Z : E → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hcA : ∀ x ∈ tsupport μ, ∀ a i j,
      periodicLift (c (.inl (a, i, j))) =ᶠ[nhds x] (fun y ↦ A y a i j))
    (hcZ : ∀ x ∈ tsupport μ, ∀ i j,
      periodicLift (c (.inr (i, j))) =ᶠ[nhds x] (fun y ↦ Z y i j))
    (v : Fin d → 𝓢(E, ℂ)) (f : EuclideanL2 d E)
    (w : Torus d → E) (hw : IsSmoothPeriodic w)
    (hlift : periodicBesselLift
      (cutoffMultiplier (periodizedCutoff hr χ hχ hχs) (toTorus (𝕜 := ℝ) f)) =
      PeriodicSobolevSpace.ofSmooth 1 w hw)
    (hcomparison : ∀ x j, (ρ x : ℂ) * (periodicLift w x j : ℂ) =
      (ρ x : ℂ) * imageBesselSchwartzCLM
        (SchwartzMap.smulLeftCLM ℂ (fun y ↦ (χ y : ℂ)) (v j)) x +
      ∫ y, (localizedImageBesselRemainder ρ χ x y : ℂ) * v j y) :
    l2ComplexInclusion volume (periodicChannel hr c χ μ hχ hμ hχs hμs f) =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (fun i ↦ channelSchwartz A Z χ μ v i x +
        ∑ j, ∫ y, (oneFactorRemainderKernel ρ χ μ A Z i j (x, y) : ℂ) * v j y) := by
  have hμc : HasCompactSupport μ := hasCompactSupport_of_imageBessel_cube_support μ
    (fun x hx ↦ hμs (subset_tsupport μ hx))
  have hχR : ∀ x, χ x ≠ 0 → ∀ a, |x a| ≤ R :=
    fun x hx a ↦ (hχs (subset_tsupport χ hx) a).trans hrR.le
  filter_upwards [periodicChannel_of_smooth_besselLift hr c χ μ hχ hμ hχs hμs A Z
    (fun x hx a i j ↦ (hcA x hx a i j).self_of_nhds)
    (fun x hx i j ↦ (hcZ x hx i j).self_of_nhds) f w hw hlift] with x hx
  rw [hx]
  apply PiLp.ext
  intro i
  exact maskedCoefficientOperator_eq_channelSchwartz_add_remainder hR ρ χ μ hρ hχ hμ
    (fun y hy ↦ hρs (subset_tsupport ρ hy)) hχR hμc hplateau A Z hA hZ v
    (fun y j ↦ (periodicLift w y j : ℂ)) hcomparison x i

/-- The actual periodic channel acts on a real L² datum with Schwartz
representative as the Euclidean channel plus the explicit differentiated
lattice remainder (`app:ch_background:prop:bg-frame`, Step 1, image-normal
paragraph). The smooth localized Bessel lift is constructed here; only the
auxiliary plateau from `exists_oneFactorPlateau` and the local coefficient
agreements produced by ImageGeometry are supplied by the caller. The source
cutoff supplies compact support without an extra condition on `v`. -/
theorem periodicChannel_schwartz_action (hd : 0 < d)
    {r R : ℝ} (hr : r < 1 / 2) (hR₀ : 0 < R) (hrR : r < R) (hR : R < 1 / 2)
    (c : GeometricProfile.ReducedCoefficientIndex d → C(Torus d, ℝ))
    (_hc : ∀ k, IsSmoothPeriodic (c k))
    (χ μ ρ : E → ℝ) (hχ : ContDiff ℝ ∞ χ) (hμ : ContDiff ℝ ∞ μ)
    (hρ : ContDiff ℝ ∞ ρ)
    (hχs : tsupport χ ⊆ chartBox r) (hμs : tsupport μ ⊆ chartBox r)
    (hρs : tsupport ρ ⊆ chartBox R)
    (hplateau : ∀ x ∈ tsupport μ, ρ =ᶠ[nhds x] (fun _ ↦ 1))
    (A : E → Fin d → Matrix (Fin d) (Fin d) ℝ)
    (Z : E → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hcA : ∀ x ∈ tsupport μ, ∀ a i j,
      periodicLift (c (.inl (a, i, j))) =ᶠ[nhds x] (fun y ↦ A y a i j))
    (hcZ : ∀ x ∈ tsupport μ, ∀ i j,
      periodicLift (c (.inr (i, j))) =ᶠ[nhds x] (fun y ↦ Z y i j))
    (v : Fin d → 𝓢(E, ℂ)) (f : EuclideanL2 d E)
    (hf : l2ComplexInclusion volume f =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (fun j ↦ v j x)) :
    l2ComplexInclusion volume (periodicChannel hr c χ μ hχ hμ hχs hμs f) =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (fun i ↦ channelSchwartz A Z χ μ v i x +
        ∑ j, ∫ y, (oneFactorRemainderKernel ρ χ μ A Z i j (x, y) : ℂ) * v j y) := by
  obtain ⟨w, hw, hlift, hcomparison⟩ := exists_smooth_localized_periodicBesselLift
    hd hr hR₀ hrR hR χ ρ hχ hρ hχs hρs v f hf
  exact periodicChannel_schwartz_action_of_localized_besselLift hr hrR hR c χ μ ρ
    hχ hμ hρ hχs hμs hρs hplateau A Z hA hZ hcA hcZ v f w hw hlift hcomparison

end JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicComparison
