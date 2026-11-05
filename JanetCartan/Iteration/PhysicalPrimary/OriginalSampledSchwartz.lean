module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.UniformStep.SampledMetric
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# The unchanged real Schwartz sum of the final sampled wave family

The field in `main:eq:primary` is the sum itself, not a new spatial cutoff of
that sum. Once the actual final corrected waves are realized as Schwartz maps,
this construction retains their exact global values, self tensor, and signed
quadratic source. It neither chooses another sample nor assumes a response or
primary estimate. Producing the actual same-history corrected waves and their
sharp bounds remains the parent construction's obligation.
Consumer: the actual primary in `main:prop:current-waves` and the same-family
ledger in `RevisedStage.increment_estimates_of_physicalSobolev_profiles`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalPrimary
open UniformStep

variable {n N : ℕ} {ι : Type*} [Fintype ι]

/-- The literal finite real sum of the final Schwartz waves. There is no
additional output mask (`main:eq:primary`). -/
def uncutSampledPrimary (b : ℝ) (μ : ι → ℝ)
    (Z : ι → SchwartzMap (Euclidean n) (EuclideanSpace ℂ (Fin N))) :
    SchwartzMap (Euclidean n) (Euclidean N) :=
  (b * Real.sqrt 2) • ∑ i, Real.sqrt (μ i) • (Z i).postcompCLM euclideanRealPart

/-- Schwartz packaging does not change the original sampled primary at any
physical point (`main:eq:primary`). -/
theorem uncutSampledPrimary_coe (b : ℝ) (μ : ι → ℝ)
    (Z : ι → SchwartzMap (Euclidean n) (EuclideanSpace ℂ (Fin N))) :
    (uncutSampledPrimary b μ Z : Euclidean n → Euclidean N) =
      sampledPrimary b μ (fun i ↦ (Z i : Euclidean n → EuclideanSpace ℂ (Fin N))) := by
  funext x
  simp [uncutSampledPrimary, sampledPrimary, Finset.sum_apply]

/-- Global same-family self/off identity. The Hermitian tensor is that of the
literal derivatives of the final waves, not a previously prepared family
(`main:eq:self-off`). -/
theorem uncut_sampled_self_off (b : ℝ) (μ : ι → ℝ)
    (Z : ι → SchwartzMap (Euclidean n) (EuclideanSpace ℂ (Fin N)))
    (θ : ι → Euclidean n → ℝ) :
    inducedMetric (uncutSampledPrimary b μ Z) =
      b ^ 2 • CurrentMean.weightedHermitianTensor μ
        (fun x i ↦ sampledDerivative (fun i ↦ (Z i : Euclidean n → EuclideanSpace ℂ (Fin N))) i x) +
      ProductSum.offSelfSource b μ
        (sampledDerivative (fun i ↦ (Z i : Euclidean n → EuclideanSpace ℂ (Fin N))))
        (sampledDerivativeAmplitude (fun i ↦ (Z i : Euclidean n → EuclideanSpace ℂ (Fin N))) θ) := by
  rw [uncutSampledPrimary_coe,
    offSelfSource_sampledDerivative b μ (fun i ↦ (Z i).differentiable),
    weightedHermitian_sampledDerivativeAmplitude μ _ θ]
  abel

/-- The same real Schwartz primary has the complete signed quadratic source,
including doubled phases and cross-patch terms. No global analytic amplitude
factorization is assumed: the literal demodulated derivative supplies it
(`app:ch_pairs:lem:pairs-ledger`). -/
theorem uncut_sampled_signed_sum [DecidableEq ι] (b : ℝ) (μ : ι → ℝ)
    (hμ : ∀ i, 0 ≤ μ i)
    (Z : ι → SchwartzMap (Euclidean n) (EuclideanSpace ℂ (Fin N)))
    (θ : ι → Euclidean n → ℝ) :
    inducedMetric (uncutSampledPrimary b μ Z) -
      b ^ 2 • CurrentMean.weightedHermitianTensor μ
        (fun x i ↦ sampledDerivative (fun i ↦ (Z i : Euclidean n → EuclideanSpace ℂ (Fin N))) i x) =
      ProductSum.weightedSignedSum b μ
        (ProductSum.plusSource θ
          (sampledDerivativeAmplitude (fun i ↦ (Z i : Euclidean n → EuclideanSpace ℂ (Fin N))) θ))
        (ProductSum.minusSource θ
          (sampledDerivativeAmplitude (fun i ↦ (Z i : Euclidean n → EuclideanSpace ℂ (Fin N))) θ)) := by
  rw [uncutSampledPrimary_coe, weightedHermitian_sampledDerivativeAmplitude μ _ θ]
  exact sampledPrimary_offSelf_eq_signedSum b μ hμ
    (fun i ↦ (Z i).differentiable) θ _
    (sampledDerivative_eq_phase_smul_amplitude _ θ)

end JanetCartan.PhysicalPrimary
