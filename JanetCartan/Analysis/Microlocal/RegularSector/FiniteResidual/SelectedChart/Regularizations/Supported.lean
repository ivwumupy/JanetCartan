module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.SelectedChart.Geometry
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformEvolution.PhysicalResidual

/-!
# Literal regularized kernels on the retained supported phase

Phase agreement is used only where the actual amplitude and output mask are
nonzero. The third collared amplitude is replaced by the full physical `PW₁`
only on that same carrier. Consumers: the forward and adjoint regularizations
in `app:ch_regular_base:eq:energy-complete-residual`.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FiniteResidual.SelectedChart
open Characteristic Characteristic.AmplitudeBounds Characteristic.ConicPhase
open Characteristic.EvolutionIntegral Characteristic.UniformEvolution
open FourierIntegral
variable {d q : ℕ}
local notation "E" => Euclidean (d+1)
local notation "T" => Characteristic.TwoTimePoint (Euclidean d)
local notation "Mat" => Matrix (Fin q) (Fin q) ℂ

/-- The forward and conjugate-transposed regularized kernels respect the
same supported phase and amplitude agreement. The right source multiplier
is retained inside `elapsedAmplitude` (`retarded-kernel`). -/
theorem cut_elapsed_kernels_congr_on_output
    (Ψ Ψ' : TwoTimePhase d) (W V : TwoTimeAmplitude d q)
    (χout χsource β θ : E → ℂ)
    (hWV : ∀ x, χout x ≠ 0 → ∀ s η,
      W (x 0) s (spatialPart x) η = V (x 0) s (spatialPart x) η)
    (hphase : ∀ x, χout x ≠ 0 → ∀ s η, W (x 0) s (spatialPart x) η ≠ 0 →
      Ψ' (x 0) s (spatialPart x) η = Ψ (x 0) s (spatialPart x) η)
    (r : ℝ) :
    graphTestOutput (elapsedPhase Ψ' r)
        (frequencyCutFullAmplitude θ (elapsedAmplitude V χout χsource β r)) =
      graphTestOutput (elapsedPhase Ψ r)
        (frequencyCutFullAmplitude θ (elapsedAmplitude W χout χsource β r)) ∧
    (∀ u : E → Fin q → ℂ, reverseGraphOperator (elapsedPhase Ψ' r)
        (frequencyCutFullAmplitude (fun ξ ↦ star (θ ξ))
          (fun x y ξ ↦ (elapsedAmplitude V χout χsource β r x y ξ).conjTranspose)) u =
      reverseGraphOperator (elapsedPhase Ψ r)
        (frequencyCutFullAmplitude (fun ξ ↦ star (θ ξ))
          (fun x y ξ ↦ (elapsedAmplitude W χout χsource β r x y ξ).conjTranspose)) u) := by
  have hA : elapsedAmplitude V χout χsource β r = elapsedAmplitude W χout χsource β r := by
    funext x y ξ
    by_cases hx : χout x = 0
    · simp [elapsedAmplitude, hx]
    · simp only [elapsedAmplitude, hWV x hx]
  have hp (x y ξ : E) (h : elapsedAmplitude W χout χsource β r x y ξ ≠ 0) :
      elapsedPhase Ψ' r x ξ = elapsedPhase Ψ r x ξ := by
    have hx : χout x ≠ 0 := fun hx ↦ h (by simp [elapsedAmplitude, hx])
    have hw : W (x 0) (x 0-r) (spatialPart x) (spatialPart ξ) ≠ 0 :=
      fun hw ↦ h (by simp [elapsedAmplitude, hw])
    exact congrArg (fun v : ℝ ↦ (x 0-r) * ξ 0 + v) (hphase x hx _ _ hw)
  rw [hA]
  refine ⟨graphTestOutput_phase_congr _ _ _ ?_, ?_⟩
  · intro x y ξ h
    exact hp x y ξ (fun hz ↦ h (by simp [frequencyCutFullAmplitude, hz]))
  · intro u
    apply reverseGraphOperator_phase_congr
    intro x y ξ h
    exact hp x y ξ (fun hz ↦ h (by simp [frequencyCutFullAmplitude, hz]))

/-- Every cutoff sees the SAME supported solver phase `G`, in both literal
kernels. These are exactly the phase germs retained by
`SelectedChartEvolutionAt` (`energy-complete-residual`). -/
theorem solver_cut_elapsed_kernels_supported
    (ℓ : Euclidean d →L[ℝ] ℝ) (C : OpenPartialHomeomorph T T)
    (W₀ W₁ : T → Mat) (G : T → ℝ)
    (hG : ∀ p ∈ tsupport W₀ ∪ tsupport W₁, G =ᶠ[𝓝 p] phase ℓ C)
    (χout χsource β θ : E → ℂ) (r : ℝ) :
    let W := curryCharacteristicMatrix W₀ + curryCharacteristicMatrix W₁
    let Ψ := fun t s y η ↦ G (t, (s, (y, η)))
    graphTestOutput (elapsedPhase Ψ r)
        (frequencyCutFullAmplitude θ (elapsedAmplitude W χout χsource β r)) =
      graphTestOutput (elapsedPhase (curriedPhase ℓ C) r)
        (frequencyCutFullAmplitude θ (elapsedAmplitude W χout χsource β r)) ∧
    (∀ u : E → Fin q → ℂ, reverseGraphOperator (elapsedPhase Ψ r)
        (frequencyCutFullAmplitude (fun ξ ↦ star (θ ξ))
          (fun x y ξ ↦ (elapsedAmplitude W χout χsource β r x y ξ).conjTranspose)) u =
      reverseGraphOperator (elapsedPhase (curriedPhase ℓ C) r)
        (frequencyCutFullAmplitude (fun ξ ↦ star (θ ξ))
          (fun x y ξ ↦ (elapsedAmplitude W χout χsource β r x y ξ).conjTranspose)) u) := by
  apply cut_elapsed_kernels_congr_on_output
  · intro x hx s η; rfl
  · intro x hx s η hw
    exact solver_phase_eq_on_support ℓ C W₀ W₁ G hG hw

/-- The output time plateau suffices to replace the third collared amplitude
by the full physical correction and the conic phase by `G`, in both regularized
kernels. `hphysical` is produced by `retained_residual_eq_twoTimePhysicalApply`
from the original column identity, including `B` (`energy-complete-residual`). -/
theorem residual_cut_elapsed_kernels_supported
    (ℓ : Euclidean d →L[ℝ] ℝ) (C : OpenPartialHomeomorph T T)
    (W₂ : T → Mat) (PW₁ : TwoTimeAmplitude d q) (G : T → ℝ) (κ : ℝ → ℝ)
    (hG : ∀ p : T, κ =ᶠ[𝓝 p.1] (fun _ ↦ 1) → W₂ p ≠ 0 →
      G =ᶠ[𝓝 p] phase ℓ C)
    (χout χsource β θ : E → ℂ)
    (hout : ∀ x, χout x ≠ 0 → κ =ᶠ[𝓝 (x 0)] (fun _ ↦ 1))
    (hphysical : ∀ x, κ =ᶠ[𝓝 (x 0)] (fun _ ↦ 1) → ∀ s η,
      W₂ (x 0, (s, (spatialPart x, η))) = PW₁ (x 0) s (spatialPart x) η)
    (r : ℝ) :
    let Ψ := fun t s y η ↦ G (t, (s, (y, η)))
    graphTestOutput (elapsedPhase Ψ r)
        (frequencyCutFullAmplitude θ (elapsedAmplitude PW₁ χout χsource β r)) =
      graphTestOutput (elapsedPhase (curriedPhase ℓ C) r)
        (frequencyCutFullAmplitude θ (elapsedAmplitude (curryCharacteristicMatrix W₂) χout χsource β r)) ∧
    (∀ u : E → Fin q → ℂ, reverseGraphOperator (elapsedPhase Ψ r)
        (frequencyCutFullAmplitude (fun ξ ↦ star (θ ξ))
          (fun x y ξ ↦ (elapsedAmplitude PW₁ χout χsource β r x y ξ).conjTranspose)) u =
      reverseGraphOperator (elapsedPhase (curriedPhase ℓ C) r)
        (frequencyCutFullAmplitude (fun ξ ↦ star (θ ξ))
          (fun x y ξ ↦ (elapsedAmplitude (curryCharacteristicMatrix W₂) χout χsource β r x y ξ).conjTranspose)) u) := by
  apply cut_elapsed_kernels_congr_on_output
  · intro x hx s η
    exact hphysical x (hout x hx) s η
  · intro x hx s η hw
    exact (hG _ (hout x hx) hw).eq_of_nhds

end JanetCartan.RegularSector.FiniteResidual.SelectedChart
