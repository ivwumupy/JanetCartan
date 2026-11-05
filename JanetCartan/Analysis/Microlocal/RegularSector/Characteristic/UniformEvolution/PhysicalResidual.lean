module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformEvolution.SupportedOperators

/-!
# The estimated residual is the literal physical derivative

The producer's original-coordinate column identity is conjugated by the
same selected coordinate split. It identifies the third collared matrix
with `twoTimePhysicalApply` on the actual output plateau. Kernel congruence
then preserves the SAME bounded residual, its test action and reversed
triangle, including the full zeroth coefficient `B`.
Source: `app:ch_regular_base:eq:energy-complete-residual` in `paper-v2.tex`.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.UniformEvolution
open AmplitudeBounds ResidualCoordinates FourierIntegral EvolutionIntegral
open KernelIdentification UncutTestAction
open JanetCartan.CharacteristicTransport.CompleteResidual
variable {d q : ℕ}
local notation "E" => Euclidean (d+1)
local notation "T" => Characteristic.TwoTimePoint (Euclidean d)
local notation "Mat" => MetricTensor (d+1)

/-- The exact physical-column output of `ConicConstruction` implies equality
with the residual consumer's canonical matrix derivative. Smoothness comes
from the SAME supported correction (`energy-complete-residual`). -/
theorem retained_residual_eq_twoTimePhysicalApply
    (i : Fin (d+1)) (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (W₁ W₂ : T → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (κ : ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W₁)
    (hphysical : ∀ p : T, κ =ᶠ[𝓝 p.1] (fun _ ↦ 1) → ∀ j : Fin (d+1),
      (fun k ↦ W₂ p k j) =
        WKB.firstOrderApply (complexPencilCoefficient Q) (complexPencilZeroth B)
          (fun y k ↦ W₁ (physicalSlice (coordinateSplit i) p.2.1 p.2.2.2 y) k j)
          ((coordinateSplit i).symm (p.1, p.2.2.1)))
    (x : E) (hx : κ =ᶠ[𝓝 (x 0)] (fun _ ↦ 1)) (s : ℝ) (η : Euclidean d) :
    W₂ (x 0, (s, (spatialPart x, η))) =
      twoTimePhysicalApply (fun y a ↦ (coefficient i Q y a).map Complex.ofReal)
        (fun y ↦ (zeroth i B y).map Complex.ofReal)
        (curryCharacteristicMatrix W₁) (x 0) s (spatialPart x) η := by
  have hslice : ContDiff ℝ ∞ (fun y : E ↦ W₁ (y 0, (s, (spatialPart y, η)))) :=
    hW.comp (((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d+1))).contDiff).prodMk
      (contDiff_const.prodMk (spatialPartCLM.contDiff.prodMk contDiff_const)))
  ext k j
  have hf : DifferentiableAt ℝ
      (fun y a ↦ W₁ (physicalSlice (coordinateSplit i) s η y) a j)
      (physicalCoordinates i x) := by
    have hf' := hW.comp (contDiff_physicalSlice (coordinateSplit i) s η)
    exact differentiableAt_pi.mpr fun a ↦
      ((Matrix.entryLinearMap ℝ ℂ a j).toContinuousLinearMap.contDiff.comp hf').differentiable
        (by simp) _
  have he : (fun y a ↦ W₁ (y 0, (s, (spatialPart y, η))) a j) =
      (fun y a ↦ W₁ (physicalSlice (coordinateSplit i) s η y) a j) ∘ physicalCoordinates i := by
    funext y a
    rw [Function.comp_apply, physicalSlice_physicalCoordinates]
  have hc := twoTimePhysicalApply_column
    (fun y a ↦ (coefficient i Q y a).map Complex.ofReal)
    (fun y ↦ (zeroth i B y).map Complex.ofReal) (curryCharacteristicMatrix W₁)
    s η x (hslice.differentiable (by simp) x) j
  have hp := hphysical (x 0, (s, (spatialPart x, η))) hx j
  rw [← physicalCoordinates_apply] at hp
  have hconj := firstOrderApply_physicalCoordinates i Q B hf
  rw [← he] at hconj
  exact congrFun (hp.trans (hconj.symm.trans hc)) k

/-- Equality of amplitudes on the output mask preserves the literal elapsed
graph without assuming any operator estimate (`fixed-time-representation`). -/
theorem retained_elapsedGraph_amplitude_congr
    (Ψ : TwoTimePhase d) (W V : TwoTimeAmplitude d q) (χout χsource β : E → ℂ)
    (hWV : ∀ x, χout x ≠ 0 → ∀ s η, W (x 0) s (spatialPart x) η = V (x 0) s (spatialPart x) η)
    (r : ℝ) : elapsedGraph Ψ W χout χsource β r = elapsedGraph Ψ V χout χsource β r := by
  unfold elapsedGraph
  congr 1
  funext x y ξ
  by_cases hx : χout x = 0
  · simp [elapsedAmplitude, hx]
  · simp only [elapsedAmplitude, hWV x hx]

/-- The original uncut action respects the same output-mask equality,
including source-before-Fourier multiplication (`retarded-kernel`). -/
theorem retained_retardedPhysicalIntegral_amplitude_congr
    (Ψ : TwoTimePhase d) (W V : TwoTimeAmplitude d q) (χout χsource β : E → ℂ)
    (hWV : ∀ x, χout x ≠ 0 → ∀ s η, W (x 0) s (spatialPart x) η = V (x 0) s (spatialPart x) η)
    (hs : ContDiff ℝ ∞ χsource) (a : ℝ) (u : graphTestSpace (d+1) q) (x : E) :
    retardedPhysicalIntegral Ψ W χout χsource β hs a u x =
      retardedPhysicalIntegral Ψ V χout χsource β hs a u x := by
  by_cases hx : χout x = 0
  · simp [retardedPhysicalIntegral, hx]
  unfold retardedPhysicalIntegral
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  simp only [graphOperator, hWV x hx]

/-- The reversed triangle, with the conjugate transpose and multiplier,
also respects that exact amplitude equality (`energy-complete-residual`). -/
theorem retained_reverseRetardedFrequency_amplitude_congr
    (Ψ : TwoTimePhase d) (W V : TwoTimeAmplitude d q) (χout β : E → ℂ)
    (hWV : ∀ x, χout x ≠ 0 → ∀ s η, W (x 0) s (spatialPart x) η = V (x 0) s (spatialPart x) η)
    (u : E → Fin q → ℂ) (a b : ℝ) (ξ : E) :
    reverseRetardedFrequency Ψ W χout β u a b ξ =
      reverseRetardedFrequency Ψ V χout β u a b ξ := by
  have he (t s : ℝ) (y : Euclidean d) :
      reverseTimeFourierKernel Ψ W χout u ξ t s y =
        reverseTimeFourierKernel Ψ V χout u ξ t s y := by
    by_cases hx : χout (timeSpacePoint t y) = 0
    · simp [reverseTimeFourierKernel, hx]
    have hw := hWV (timeSpacePoint t y) hx s (spatialPart ξ)
    simp only [timeSpacePoint_time, spatialPart_timeSpacePoint] at hw
    simp only [reverseTimeFourierKernel, hw]
  unfold reverseRetardedFrequency
  simp_rw [he]

/-- Transfer the actual constructed residual to the literal `PW₁` on the
output plateau. This only rewrites its kernels; the operator and all signed
single-high bounds are the ones already constructed (`energy-complete-residual`). -/
theorem retained_signed_bounds_amplitude_congr
    (KQ : Set E) (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (Ψ : TwoTimePhase d) (W V : TwoTimeAmplitude d q) (χout χsource β : E → ℂ)
    (hWV : ∀ x, χout x ≠ 0 → ∀ s η, W (x 0) s (spatialPart x) η = V (x 0) s (spatialPart x) η)
    (hs : ContDiff ℝ ∞ χsource) (Δ a A₀ : ℝ) (A : ℕ → ℝ) (o : ℕ)
    (Op : SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q)
    (hOp : RetainedSignedRetardedBounds KQ Q B Δ a Ψ W χout χsource β hs o A₀ A Op) :
    RetainedSignedRetardedBounds KQ Q B Δ a Ψ V χout χsource β hs o A₀ A Op := by
  simpa only [RetainedSignedRetardedBounds, elapsedGraphIntegral,
    retained_elapsedGraph_amplitude_congr Ψ W V χout χsource β hWV,
    retained_retardedPhysicalIntegral_amplitude_congr Ψ W V χout χsource β hWV,
    retained_reverseRetardedFrequency_amplitude_congr Ψ W V χout β hWV] using hOp

end JanetCartan.RegularSector.Characteristic.UniformEvolution
