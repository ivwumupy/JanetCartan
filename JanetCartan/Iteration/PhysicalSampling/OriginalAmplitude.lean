module

public import JanetCartan.Iteration.PhysicalSampling.OriginalKernel

/-!
# Fixed original scalar amplitude bounds for the common event

The scalar row's fixed physical support, amplitude bound and original detector
bound are independent of the current phase, color rates and finite ceiling.
They instantiate the scalar side of
`exists_threshold_original_common_scalar_native_of_amplitude`, without any
chosen-witness amplitude comparison or measured-row inverse
(`new:eq:amplitude-test`, `app:ch_waves:thm:sampling`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalSampling
open ActualCarriers FrozenMenu CurrentFullPhase Sampling SamplingKernelBounds

variable {m J p : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)
  (Q : {Q : Euclidean (m + 1) → Fin (m + 1) → MetricTensor (m + 1) //
    ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress (m + 1)) < T.family.threshold})
  (χ : ContDiffBump (0 : Euclidean (m + 1)))
  (center : Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))
  {ρ : ℝ} (hρ : 0 < ρ) {c C : ℝ} (hP : P.IsValid c C)
  (hcarrier : closedBall center.2.1 (2 * ρ) ⊆ parameterInterior (2 * P.radius))
  {ηoriginal : Euclidean (m + 1 - 1)} {roriginal : ℝ}
  (hηoriginal : ηoriginal ≠ 0) (hroriginal : 0 < roriginal)
  (τ : (Fin 3 → Fin (p + 1)) → ℝ) (hτ₀ : ∀ color, τ color ≠ 0)

local notation "D" => originalScalarKernelData (J := J) T Q χ center hρ hP hcarrier
  hηoriginal hroriginal τ hτ₀

/-- Uniform fixed support, Fourier amplitude and literal original mask bounds
for the actual scalar kernel. No phase or rate bound is needed. -/
theorem originalScalarKernelData_uniform_bounds :
    (∀ q η x, x ∉ tsupport (χ : Euclidean (m + 1) → ℝ) →
      (D).amplitude ((q, η), x) = 0) ∧
    (∀ q η x, ‖(D).amplitude ((q, η), x)‖ ≤
      (2 * Real.pi) ^ (-((m + 1 : ℕ) : ℝ) / 2)) ∧
    (∀ η, ‖(D).mask η‖ ≤ 1) := by
  refine ⟨(D).amplitude_eq_zero, ?_, (D).mask_le⟩
  intro q η x
  apply ((D).amplitude_le q η x).trans_eq
  change (2 * Real.pi) ^ (-((m + 1 : ℕ) : ℝ) / 2) * 1 = _
  exact mul_one _

end JanetCartan.PhysicalSampling
