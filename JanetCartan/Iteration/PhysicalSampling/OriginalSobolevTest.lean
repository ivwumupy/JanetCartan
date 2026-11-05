module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.PaperEstimates.RowApplication.Matrices.PhysicalSobolev
public import JanetCartan.Iteration.PhysicalSamplingShells.Realization

/-!
# The literal physical Sobolev amplitude inequality on the original native row

Apply the matrix amplitude theorem with the UNMODIFIED sampled scalar kernel.
Native pointwise integrability and the integral action hold on every original
L² input. The only bound consumed here is the actual same-prefix operator
norm, supplied by the one concentrated event in the original application.
No continuity or derivatives in the sample or frequency index are required.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open MeasureTheory FourierTransform
namespace JanetCartan.PhysicalSampling.OriginalSobolevTest
open PhysicalSamplingShells Sampling Sampling.Realization SeparatedSampling SamplingKernelBounds
open CanonicalRowComparison RawInputPartition AmplitudeBound AmplitudeBound.PaperEstimates
open Pseudodifferential FourierConventions

variable {A : Type*} [Fintype A] {n J p : ℕ} (hn : 1 ≤ n)
  (B : ℝ) (ψ : A → Point → ℝ) (w : ℝ → ℝ) (h : ℝ) (U : A → Lattice → Point)
  (D : A → BandKernelData (Fin J × ((Fin 3 → Fin (p + 1)) × Point)) n) (L : ℕ)
local notation "X" => (SampleIndex p B ψ w h U × RefinedIndex J) × Euclidean (n-1)
local notation "μ" => sampledShellMeasure (ι := SampleIndex p B ψ w h U) n J
local notation "E" => Euclidean n

/-- For EACH physical matrix amplitude, construct its actual original sampled
operator. Its norm charges only the fixed ranks, box and physical `H^ell` size,
not the number of bands or samples. In particular there is no premise about the
modified operator, its integral representation, or a bare single-row operator
(`new:eq:amplitude-test`, `app:ch_osc:lem:osc-amplitude`). -/
theorem native_physical_amplitude_test {Ctest : ℝ}
    (hT : ‖nativeScalarOperator hn B ψ w h U D L‖ ≤ Ctest)
    (nout nin : ℕ) (R : ℝ) (b : X → E → Matrix (Fin nout) (Fin nin) ℂ)
    (hb : ∀ i j, StronglyMeasurable (fun q : X × E ↦ b q.1 q.2 i j))
    (hc : ∀ i j u, Continuous (fun x ↦ b u x i j))
    (hs : ∀ i j u, SupportedInCenteredBox R (fun x ↦ b u x i j))
    (hm : ∀ i j u, MemLp (fun x ↦ b u x i j) 2 volume)
    (hphys : ∀ i j u, MemLp (fun ξ ↦ euclideanSobolevWeight (n / 2 + 1 : ℕ)
      ((2 * Real.pi) • ξ) • (𝓕 ((hm i j u).toLp (fun x ↦ b u x i j)) :
        Lp ℂ 2 (volume : Measure E)) ξ) 2 volume)
    (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ i j u, (eLpNorm (fun ξ ↦ euclideanSobolevWeight (n / 2 + 1 : ℕ)
      ((2 * Real.pi) • ξ) • (𝓕 ((hm i j u).toLp (fun x ↦ b u x i j)) :
        Lp ℂ 2 (volume : Measure E)) ξ) 2 volume).toReal ≤ M) :
    ∃ S : Lp (EuclideanSpace ℂ (Fin nin)) 2 μ →L[ℂ]
        Lp (EuclideanSpace ℂ (Fin nout)) 2 (volume : Measure E),
      ‖S‖ ≤ ((nout : ℝ) * (nin : ℝ) * rowAmplitudeConstant n R) * Ctest * M ∧
        ∀ f : Lp (EuclideanSpace ℂ (Fin nin)) 2 μ, S f =ᵐ[volume] fun x ↦ ∫ u,
          nativeScalarKernel hn B ψ w h U D L x u • WithLp.toLp 2 ((b u x).mulVec (f u).ofLp) ∂μ := by
  let T := nativeScalarOperator hn B ψ w h U D L
  let K := nativeScalarKernel hn B ψ w h U D L
  let S := physicalSobolevMatrixRowAmplitudeOperator R b hb hs hm hphys M hM hbound T
  have hfac : 0 ≤ (nout : ℝ) * (nin : ℝ) * rowAmplitudeConstant n R :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (rowAmplitudeConstant_nonneg n R)
  refine ⟨S, ?_, ?_⟩
  · have hnorm := norm_physicalSobolevMatrixRowAmplitudeOperator_le R b hb hs hm hphys M hM hbound T
    exact (by simpa only [S,Fintype.card_fin] using hnorm : ‖S‖ ≤
      ((nout : ℝ) * (nin : ℝ) * rowAmplitudeConstant n R) * ‖T‖ * M).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hT hfac) hM)
  · intro f
    exact physicalSobolevMatrixRowAmplitudeOperator_ae_kernel R b hb hc hs hm hphys M hM hbound
      T K (nativeScalarOperator_ae_integral hn B ψ w h U D L) f
      (Filter.Eventually.of_forall (integrable_nativeScalarKernel_smul hn B ψ w h U D L f))

end JanetCartan.PhysicalSampling.OriginalSobolevTest
