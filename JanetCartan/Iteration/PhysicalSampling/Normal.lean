module

public import JanetCartan.Iteration.PhysicalSampling.Kernel
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.RetainedNormal

/-!
# Exact full-output normal of the actual scalar kernel

The identification uses the same scalar kernel and its proved supported phase,
not a comparison with the measured stress row. It retains the normalized input
Jacobian and the whole-space physical output. Consumer: the scalar continuum
mean in `new:eq:amplitude-test`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalSampling

open ActualCarriers FrozenMenu CurrentFullPhase LeadingWave.FullModulation FullPhaseCharts
open Sampling Sampling.RawKernel Sampling.MeasuredAmplitude Sampling.MeanNormalBound
open Sampling.MeanNormalBound.NormalizedFullPhase Sampling.MeanNormalBound.CanonicalGap
open SamplingKernelBounds RawPrimary.MaskProfiles RawInputPartition PhysicalMean ContinuumRow
open NormalComparison ColoredNormalComparison

variable {m J p : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)
  (Q : {Q : Euclidean (m + 1) → Fin (m + 1) → MetricTensor (m + 1) //
    ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress (m + 1)) < T.family.threshold})
  (χ : ContDiffBump (0 : Euclidean (m + 1)))
  (a : Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))
  {ρ : ℝ} (hρ : 0 < ρ) {c C : ℝ} (hP : P.IsValid c C)
  (hcarrier : closedBall a.2.1 (2 * ρ) ⊆ parameterInterior (2 * P.radius))
  (angular : Euclidean (m + 1 - 1) → ℂ) (H : Euclidean (m + 1 - 1) → ℝ)
  (ha : ∀ θ, θ ≠ 0 → ContDiffAt ℝ ∞ angular θ)
  (hH : ContDiff ℝ ∞ H) (hH₀ : ∀ η, ‖η‖ ≤ 1 → H η = 0)
  (B : ℝ) (hB : 0 ≤ B) (hdB : ∀ η, ‖detectorMask angular H η‖ ≤ B)
  (τ : (Fin 3 → Fin (p + 1)) → ℝ) (hτ₀ : ∀ color, τ color ≠ 0)

local notation "D" => retainedScalarKernelData (J := J) T Q χ a hρ hP hcarrier
  angular H ha hH hH₀ B hB hdB τ hτ₀

/-- Exact scalar-kernel normal, with the SAME physical output and normalized
annular input. The canonical phase is required only where its proved scalar
amplitude is nonzero (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem retainedScalarKernelData_normal_eq_uniform
    (hphase : closedBall a (2 * ρ) ⊆ domain T)
    (hχ : Function.support (χ : Euclidean (m + 1) → ℝ) ⊆ closedBall a.1 (ρ / 2))
    (ψ : SeparatedSampling.Point → ℝ) {R Pψ : ℝ}
    (hψ : SeparatedSampling.PatchBounds ψ R Pψ) (hψc : Continuous ψ)
    (hψgraph : ∀ s v, ψ (carrierSamplingEquiv (s, v)) ≠ 0 →
      (carrierParameters (v, s), T.reference.spatialPatch (carrierParameters (v, s))) ∈
        closedBall a.2 (ρ / 4))
    (hψchart : ∀ s v, ψ (carrierSamplingEquiv (s, v)) ≠ 0 →
      carrierParameters (v, s) ∈ parameterInterior (3 * P.radius / 2))
    (j : Fin J) (color : Fin 3 → Fin (p + 1)) (v : Euclidean 2)
    (hscale : |τ color| * (2 : ℝ) ^ j.val ≤ measuredPhaseRadius T hP (ρ := ρ))
    {G : UniformNormalGeometry (m + 1) (m + 1)} {Cnormal : ℕ → ℝ}
    (Ndata : UniformNormalData G Cnormal)
    (hNphase : Ndata.phase = fun ε x u ↦
      normalizedFullPhase T Q v ε x (canonicalInputCoordinates T u))
    (hNamp : Ndata.amplitude = fun ε x u ↦
      (scalarNormalizedAmplitude T χ ψ angular H j.val (ε, v, x, u)).ofLp)
    (hε : (τ color) * (2 : ℝ) ^ j.val ∈ Icc 0 G.ε₀) :
    atomNormal (fullBandKernelOperator (D) (fun z ↦ (j, (color, z)))
      (continuous_const.prodMk (continuous_const.prodMk continuous_id)) ψ hψc j.val R v) =
      samplingOutputConjugation (m + 1)
        ((Ndata.uniformOscillatoryOperator ((2 : ℝ) ^ j.val)
          ((τ color) * (2 : ℝ) ^ j.val)).comp
          (Ndata.uniformOscillatoryOperator ((2 : ℝ) ^ j.val)
            ((τ color) * (2 : ℝ) ^ j.val)).adjoint) := by
  apply fullBandKernelOperator_normal_eq_uniform_of_supported_phase
    (D) (fun z ↦ (j, (color, z)))
    (continuous_const.prodMk (continuous_const.prodMk continuous_id))
    ψ hψc j.val R v Ndata hε
  · intro u _ x hn
    rw [hNphase]
    apply retainedScalarKernelData_phase_on_support T Q χ a hρ hP hcarrier
      angular H ha hH hH₀ B hB hdB τ hτ₀ hphase hχ ψ hψgraph hψchart
      j color v hscale u.1 u.2 x
    intro hz
    simp only [Prod.mk.eta] at hz
    apply hn
    rw [hNamp]
    change (scalarNormalizedAmplitude T χ ψ angular H j.val
      ((τ color) * (2 : ℝ) ^ j.val, v, x, fullInputCoordinates m u)).ofLp = 0
    rw [hz]
    rfl
  · intro u _ x i
    rw [hNamp]
    exact scalarAuxiliaryBandAmplitude_normalization T χ ψ angular H
      (fun q ↦ extendedRetainedCarrier T a.2.1 hρ (WithLp.toLp 2 q.2))
      (fun q ↦ τ q.1) j (color, carrierSamplingEquiv (u.1, v)) v x u.1 u.2 i
  · intro u hu x
    rw [hNamp]
    change (scalarNormalizedAmplitude T χ ψ angular H j.val
      ((τ color) * (2 : ℝ) ^ j.val, v, x, u)).ofLp = 0
    rw [scalarNormalizedAmplitude_eq_zero_off_fullInputDomain
      T χ ψ hψ angular H j.val v ((τ color) * (2 : ℝ) ^ j.val) u hu x]
    rfl

end JanetCartan.PhysicalSampling
