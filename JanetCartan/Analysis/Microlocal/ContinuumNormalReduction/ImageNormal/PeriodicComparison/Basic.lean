module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.NormalIdentity
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparisonEndpoint
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.CommutatorNormal.NormalSplit
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.ImageGeometry.Periodization.Basic

/-!
# Fixed data for the periodic image-channel comparison

The cutoffs in `app:ch_background:prop:bg-frame`, Step 1, use the existing
real periodization and the actual restriction/extension between torus volume
and Lebesgue measure. The Schwartz operators specify the two literal channel
actions needed by the Euclidean construction and the one-factor comparison.
No bounded differential operator on L² is assumed.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff SchwartzMap
open JanetCartan.PeriodicLocalL2
open JanetCartan.Pseudodifferential.DifferentialChart
open JanetCartan.ContinuumRow.ImageGeometry.Periodization

namespace JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicComparison

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "R²" => EuclideanL2 d E
local notation "S" => 𝓢(E, ℂ)

/-- The fixed real cutoff, periodized from its original chart box
(`app:ch_background:defn:bg-row`). -/
def periodizedCutoff {r : ℝ} (hr : r < 1 / 2) (χ : E → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hχs : tsupport χ ⊆ chartBox r) : C(Torus d, ℝ) :=
  ⟨realPeriodization χ, (isSmoothPeriodic_realPeriodization hr hχs hχ).1⟩

/-- The box-supported periodized cutoff is smooth on the actual torus
(`app:ch_background:defn:bg-row`). -/
theorem isSmoothPeriodic_periodizedCutoff {r : ℝ} (hr : r < 1 / 2) (χ : E → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hχs : tsupport χ ⊆ chartBox r) :
    IsSmoothPeriodic (periodizedCutoff hr χ hχ hχs) :=
  isSmoothPeriodic_realPeriodization hr hχs hχ

/-- The periodic cutoff agrees locally with every physical jet on the cell
(`app:ch_background:defn:bg-row`). -/
theorem periodizedCutoff_eventuallyEq {r : ℝ} (hr : r < 1 / 2) (χ : E → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hχs : tsupport χ ⊆ chartBox r)
    {x : E} (hx : x ∈ fundamentalCell d) :
    periodicLift (periodizedCutoff hr χ hχ hχs) =ᶠ[nhds x] χ :=
  realPeriodization_eventuallyEq hr hχs hx

/-- Pull back a torus operator using the literal cell maps, retaining the two
measures in `app:ch_background:prop:bg-frame`, Step 1. -/
def pullback (T : ContinuumRow.OutputL2 d →L[ℝ] ContinuumRow.OutputL2 d) :
    R² →L[ℝ] R² :=
  toEuclidean.toContinuousLinearMap ∘L T ∘L toTorus

/-- Pullback commutes with the literal real Hilbert adjoint
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem pullback_adjoint (T : ContinuumRow.OutputL2 d →L[ℝ] ContinuumRow.OutputL2 d) :
    (pullback T).adjoint = pullback T.adjoint := by
  simp only [pullback, ContinuousLinearMap.adjoint_comp, toEuclidean_adjoint,
    toTorus_adjoint, ContinuousLinearMap.comp_assoc]

/-- Pullback preserves the normal because restriction after extension is the
identity on the torus. No inverse identity on arbitrary Euclidean data is used
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem pullback_normal (T : ContinuumRow.OutputL2 d →L[ℝ] ContinuumRow.OutputL2 d) :
    pullback (T.comp T.adjoint) = (pullback T).comp (pullback T).adjoint := by
  rw [pullback_adjoint]
  ext1 f
  change toEuclidean (𝕜 := ℝ) (T (T.adjoint (toTorus (𝕜 := ℝ) f))) =
    toEuclidean (𝕜 := ℝ) (T (toTorus (𝕜 := ℝ)
      (toEuclidean (𝕜 := ℝ) (T.adjoint (toTorus (𝕜 := ℝ) f)))))
  rw [toTorus_toEuclidean]

/-- The actual periodic image channel on physical L², with the original
source and measurement cutoffs (`app:ch_background:defn:bg-row`). -/
def periodicChannel {r : ℝ} (hr : r < 1 / 2)
    (c : GeometricProfile.ReducedCoefficientIndex d → C(Torus d, ℝ))
    (χ μ : E → ℝ) (hχ : ContDiff ℝ ∞ χ) (hμ : ContDiff ℝ ∞ μ)
    (hχs : tsupport χ ⊆ chartBox r) (hμs : tsupport μ ⊆ chartBox r) :
    R² →L[ℝ] R² :=
  pullback (ContinuumRow.imageChannel c (periodizedCutoff hr μ hμ hμs)
    (periodizedCutoff hr χ hχ hχs))

/-- The actual pulled-back image channel retains the physical measurement
support (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem periodicChannel_support {r : ℝ} (hr : r < 1 / 2)
    (c : GeometricProfile.ReducedCoefficientIndex d → C(Torus d, ℝ))
    (χ μ : E → ℝ) (hχ : ContDiff ℝ ∞ χ) (hμ : ContDiff ℝ ∞ μ)
    (hχs : tsupport χ ⊆ chartBox r) (hμs : tsupport μ ⊆ chartBox r) (f : R²) :
    ∀ᵐ x ∂volume, x ∉ tsupport μ → periodicChannel hr c χ μ hχ hμ hχs hμs f x = 0 := by
  apply toEuclidean_supported (𝕜 := ℝ)
  filter_upwards [ContinuumRow.imageChannel_coeFn c (periodizedCutoff hr μ hμ hμs)
    (periodizedCutoff hr χ hχ hχs) (toTorus (𝕜 := ℝ) f)] with z hz
  intro hzs
  change ContinuumRow.imageChannel c (periodizedCutoff hr μ hμ hμs)
    (periodizedCutoff hr χ hχ hχs) (toTorus (𝕜 := ℝ) f) z = 0
  rw [hz]
  have hm : μ (AmplitudeBound.centeredTorusRepresentative z) = 0 :=
    image_eq_zero_of_notMem_tsupport hzs
  change μ (AmplitudeBound.centeredTorusRepresentative z) • _ = 0
  rw [hm, zero_smul]

/-- The literal Euclidean channel `μ P J χ` on Schwartz families. Its bounded
real realization is a separate construction required by this task
(`app:ch_background:prop:bg-frame`, Step 1). -/
def channelSchwartz (A : E → Fin d → Matrix (Fin d) (Fin d) ℝ)
    (Z : E → Matrix (Fin d) (Fin d) ℝ) (χ μ : E → ℝ) :
    (Fin d → S) →L[ℂ] (Fin d → S) :=
  (maskedCoefficientSchwartzCLM A Z μ).comp
    (ContinuousLinearMap.pi fun j ↦ imageBesselSchwartzCLM.comp
      ((SchwartzMap.smulLeftCLM ℂ (fun x ↦ (χ x : ℂ))).comp
        (ContinuousLinearMap.proj j)))

/-- The literal reversed channel `χ J P* μ` on Schwartz families, including
the divergence-form coefficient terms (`app:ch_background:prop:bg-frame`, Step 1). -/
def channelAdjointSchwartz (A : E → Fin d → Matrix (Fin d) (Fin d) ℝ)
    (Z : E → Matrix (Fin d) (Fin d) ℝ) (χ μ : E → ℝ) :
    (Fin d → S) →L[ℂ] (Fin d → S) :=
  (ContinuousLinearMap.pi fun j ↦
    (SchwartzMap.smulLeftCLM ℂ (fun x ↦ (χ x : ℂ))).comp
      (imageBesselSchwartzCLM.comp (ContinuousLinearMap.proj j))).comp
    (maskedCoefficientAdjointSchwartzCLM A Z μ)

/-- The two literal Schwartz channel factors give exactly the original
source-square normal; no source cutoff commutes across a Bessel multiplier
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem channelSchwartz_comp_adjoint (A : E → Fin d → Matrix (Fin d) (Fin d) ℝ)
    (Z : E → Matrix (Fin d) (Fin d) ℝ) (χ μ : E → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) :
    (channelSchwartz A Z χ μ).comp (channelAdjointSchwartz A Z χ μ) =
      coefficientSourceSquaredImageSchwartz A Z χ μ := by
  have ht := hχc.hasTemperateGrowth hχ
  have htc : (fun x ↦ (χ x : ℂ)).HasTemperateGrowth := by fun_prop
  have hts : (fun x ↦ ((χ x)^2 : ℂ)).HasTemperateGrowth := by fun_prop
  ext1 v
  change maskedCoefficientSchwartzCLM A Z μ _ = maskedCoefficientSchwartzCLM A Z μ _
  congr 1
  funext j
  apply congrArg imageBesselSchwartzCLM
  change (SchwartzMap.smulLeftCLM ℂ (fun x ↦ (χ x : ℂ)))
      ((SchwartzMap.smulLeftCLM ℂ (fun x ↦ (χ x : ℂ)))
        (imageBesselSchwartzCLM (maskedCoefficientAdjointSchwartzCLM A Z μ v j))) =
    (SchwartzMap.smulLeftCLM ℂ (fun x ↦ ((χ x)^2 : ℂ)))
      (imageBesselSchwartzCLM (maskedCoefficientAdjointSchwartzCLM A Z μ v j))
  ext x
  rw [SchwartzMap.smulLeftCLM_apply_apply htc,
    SchwartzMap.smulLeftCLM_apply_apply htc, SchwartzMap.smulLeftCLM_apply_apply hts]
  simp only [smul_eq_mul, pow_two, mul_assoc]

end JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicComparison
