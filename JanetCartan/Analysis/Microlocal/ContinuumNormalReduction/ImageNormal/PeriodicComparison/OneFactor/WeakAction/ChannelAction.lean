module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.PeriodicComparison.Cutoff
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.Image

/-!
# The weak image channel on a smooth Bessel representative

For `app:ch_background:prop:bg-frame`, Step 1, the actual H¹ reduced operator
has the physical coefficient formula on a smooth representative. The cell
maps retain torus volume and Lebesgue measure. The consumer must identify the
actual masked Bessel lift with that representative; this file supplies no
regularity assumption on the image channel itself.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff
open JanetCartan.PeriodicLocalL2
open JanetCartan.Pseudodifferential.DifferentialChart
open JanetCartan.ContinuumRow

namespace JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicComparison

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem partialDeriv_complex_periodicLift
    (w : Torus d → E) (hw : IsSmoothPeriodic w) (x : E) (a j : Fin d) :
    partialDeriv (fun y ↦ (periodicLift w y j : ℂ)) x a =
      (periodicCoordinateDeriv a w (torusQuotient x) j : ℂ) := by
  have hd := (Complex.ofRealCLM.comp
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d ↦ ℝ) j)).hasFDerivAt.comp x
      (hw.2.differentiable (by simp) x).hasFDerivAt
  change HasFDerivAt (fun y ↦ (periodicLift w y j : ℂ)) _ x at hd
  rw [partialDeriv, hd.fderiv]
  have he := congr_fun (periodicLift_coordinateDeriv hw.2 a) x
  change periodicCoordinateDeriv a w (torusQuotient x) = _ at he
  simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, PiLp.proj_apply, he]

private theorem coefficientOperator_complex_periodicLift
    (c : GeometricProfile.ReducedCoefficientIndex d → C(Torus d, ℝ))
    (A : E → Fin d → Matrix (Fin d) (Fin d) ℝ)
    (Z : E → Matrix (Fin d) (Fin d) ℝ)
    (w : Torus d → E) (hw : IsSmoothPeriodic w) (x : E)
    (hA : ∀ a i j, periodicLift (c (.inl (a, i, j))) x = A x a i j)
    (hZ : ∀ i j, periodicLift (c (.inr (i, j))) x = Z x i j) (i : Fin d) :
    coefficientOperator A Z (fun y j ↦ (periodicLift w y j : ℂ)) x i =
      (reducedPeriodicFormula c w (torusQuotient x) i : ℂ) := by
  simp only [coefficientOperator, reducedPeriodicFormula_apply, Complex.ofReal_add,
    Complex.ofReal_sum, Complex.ofReal_mul, partialDeriv_complex_periodicLift w hw x]
  change (∑ a, ∑ j, (A x a i j : ℂ) *
      (periodicCoordinateDeriv a w (torusQuotient x) j : ℂ)) +
      ∑ j, (Z x i j : ℂ) * (periodicLift w x j : ℂ) =
    (∑ a, ∑ j, ((periodicLift (c (.inl (a, i, j))) x : ℝ) : ℂ) *
      (periodicCoordinateDeriv a w (torusQuotient x) j : ℂ)) +
      ∑ j, ((periodicLift (c (.inr (i, j))) x : ℝ) : ℂ) * (periodicLift w x j : ℂ)
  simp only [hA, hZ]

/-- The actual weak coefficient operator agrees with the physical complex
coefficient expression under the original measurement mask. The arrays need
only agree on its support; their local agreement is produced by ImageGeometry
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem toEuclidean_masked_reducedWeakOperator_ofSmooth
    {r : ℝ} (hr : r < 1 / 2)
    (c : GeometricProfile.ReducedCoefficientIndex d → C(Torus d, ℝ))
    (μ : E → ℝ) (hμ : ContDiff ℝ ∞ μ) (hμs : tsupport μ ⊆ chartBox r)
    (A : E → Fin d → Matrix (Fin d) (Fin d) ℝ)
    (Z : E → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ x ∈ tsupport μ, ∀ a i j,
      periodicLift (c (.inl (a, i, j))) x = A x a i j)
    (hZ : ∀ x ∈ tsupport μ, ∀ i j,
      periodicLift (c (.inr (i, j))) x = Z x i j)
    (w : Torus d → E) (hw : IsSmoothPeriodic w) :
    l2ComplexInclusion volume (toEuclidean (𝕜 := ℝ)
      (cutoffMultiplier (periodizedCutoff hr μ hμ hμs)
        (reducedWeakOperator c (PeriodicSobolevSpace.ofSmooth 1 w hw)))) =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (fun i ↦ (μ x : ℂ) *
        coefficientOperator A Z (fun y j ↦ (periodicLift w y j : ℂ)) x i) := by
  let T := cutoffMultiplier (periodizedCutoff hr μ hμ hμs)
    (reducedWeakOperator c (PeriodicSobolevSpace.ofSmooth 1 w hw))
  have ht : T =ᵐ[volume] fun z ↦
      periodizedCutoff hr μ hμ hμs z • reducedPeriodicFormula c w z := by
    filter_upwards [cutoffMultiplier_coeFn (periodizedCutoff hr μ hμ hμs)
      (reducedWeakOperator c (PeriodicSobolevSpace.ofSmooth 1 w hw)),
      reducedWeakOperator_ofSmooth_ae c w hw] with z hz hwz
    exact hz.trans (congrArg (fun q : E ↦ periodizedCutoff hr μ hμ hμs z • q) hwz)
  have ht' := (ae_restrict_iff' measurableSet_halfOpenCell).mp
    (measurePreserving_quotient.quasiMeasurePreserving.ae_eq_comp ht)
  filter_upwards [euclideanComplexInclusion.coeFn_compLpL (toEuclidean (𝕜 := ℝ) T),
    toEuclidean_coe (𝕜 := ℝ) T, ht'] with x hx hy hz
  change l2ComplexInclusion volume (toEuclidean (𝕜 := ℝ) T) x = _ at hx ⊢
  rw [hx, hy]
  apply PiLp.ext
  intro i
  by_cases hc : x ∈ halfOpenCell d
  · rw [Set.indicator_of_mem hc]
    change (T (torusQuotient x) i : ℂ) = _
    simp only [Function.comp_apply] at hz
    rw [hz hc]
    have hm := (periodizedCutoff_eventuallyEq hr μ hμ hμs
      (halfOpenCell_subset_fundamentalCell hc)).self_of_nhds
    change periodizedCutoff hr μ hμ hμs (torusQuotient x) = μ x at hm
    simp only [PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul, hm]
    by_cases hm₀ : μ x = 0
    · simp [hm₀]
    · rw [coefficientOperator_complex_periodicLift c A Z w hw x
        (hA x (subset_tsupport μ hm₀)) (hZ x (subset_tsupport μ hm₀))]
  · rw [Set.indicator_of_notMem hc]
    have hm : μ x = 0 := image_eq_zero_of_notMem_tsupport
      (fun h ↦ hc (chartBox_subset_cell hr (hμs h)))
    simp [hm]

/-- Applying the preceding weak-operator identity to the actual Bessel lift
identifies the image channel on any proved smooth representative. The H¹
identification is an explicit construction obligation of the caller
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem periodicChannel_of_smooth_besselLift
    {r : ℝ} (hr : r < 1 / 2)
    (c : GeometricProfile.ReducedCoefficientIndex d → C(Torus d, ℝ))
    (χ μ : E → ℝ) (hχ : ContDiff ℝ ∞ χ) (hμ : ContDiff ℝ ∞ μ)
    (hχs : tsupport χ ⊆ chartBox r) (hμs : tsupport μ ⊆ chartBox r)
    (A : E → Fin d → Matrix (Fin d) (Fin d) ℝ)
    (Z : E → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ x ∈ tsupport μ, ∀ a i j,
      periodicLift (c (.inl (a, i, j))) x = A x a i j)
    (hZ : ∀ x ∈ tsupport μ, ∀ i j,
      periodicLift (c (.inr (i, j))) x = Z x i j)
    (f : EuclideanL2 d E) (w : Torus d → E) (hw : IsSmoothPeriodic w)
    (hlift : periodicBesselLift
      (cutoffMultiplier (periodizedCutoff hr χ hχ hχs) (toTorus (𝕜 := ℝ) f)) =
      PeriodicSobolevSpace.ofSmooth 1 w hw) :
    l2ComplexInclusion volume (periodicChannel hr c χ μ hχ hμ hχs hμs f) =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (fun i ↦ (μ x : ℂ) *
        coefficientOperator A Z (fun y j ↦ (periodicLift w y j : ℂ)) x i) := by
  change l2ComplexInclusion volume (toEuclidean (𝕜 := ℝ)
    (cutoffMultiplier (periodizedCutoff hr μ hμ hμs)
      (reducedWeakOperator c (periodicBesselLift
        (cutoffMultiplier (periodizedCutoff hr χ hχ hχs) (toTorus (𝕜 := ℝ) f)))))) =ᵐ[volume] _
  rw [hlift]
  exact toEuclidean_masked_reducedWeakOperator_ofSmooth hr c μ hμ hμs A Z hA hZ w hw

end JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicComparison
