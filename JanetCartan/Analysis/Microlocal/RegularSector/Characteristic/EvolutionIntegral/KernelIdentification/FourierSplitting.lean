module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification.ElapsedKernels
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SourceMultiplier.SchwartzInput
public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.FrequencyCutoff.GraphConvergence

/-!
# Source Fourier splitting of the actual elapsed kernel

The full amplitude contains the output mask, source mask and conic multiplier.
The source mask is applied before the Fourier transform; the multiplier remains
inside the frequency integral. The Fourier transform is the existing physical
`sourceInputFourierTransform`, whose normalization leaves `(2π)⁻ⁿ` outside.
Source: `app:ch_regular_base:eq:fixed-time-representation`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification

open FourierIntegral FourierIntegral.LowBounds.FrequencyCutoff

variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)

/-- Complex source masking of the existing compact smooth test space. Its
Schwartz conversion is the input to the physical Fourier transform in
`app:ch_regular_base:eq:fixed-time-representation`. -/
def complexSourceMaskTest (χsource : E → ℂ) (hs : ContDiff ℝ ∞ χsource)
    (u : graphTestSpace (d + 1) q) : graphTestSpace (d + 1) q :=
  ⟨fun z ↦ χsource z • u.val z, hs.smul u.property.1, u.property.2.smul_left (f := χsource)⟩

/-- Splitting the temporal oscillation from the spatial phase with physical
covectors. Source: `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem exp_elapsedPhase (Ψ : TwoTimePhase d) (r : ℝ) (x ξ : E) :
    Complex.exp (Complex.I * (elapsedPhase Ψ r x ξ : ℂ)) =
      Complex.exp (Complex.I * (((x 0 - r) * ξ 0 : ℝ) : ℂ)) *
        Complex.exp (Complex.I * (Ψ (x 0) (x 0 - r) (spatialPart x) (spatialPart ξ) : ℂ)) := by
  rw [elapsedPhase, Complex.ofReal_add, mul_add, Complex.exp_add]

/-- The literal fixed-`r` source Fourier formula, including the compact
frequency regularization and both physical masks. The source mask remains
inside the transform, giving the order `Mχout U_r Bβ Mχsource`.
This is the source-Fourier part of
`app:ch_regular_base:eq:fixed-time-representation`; no test identification
or frequency integrability is assumed to evaluate the inner source integral. -/
theorem cut_elapsedGraph_eq_sourceFourierIntegral
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (χout χsource β θ : E → ℂ)
    (hs : ContDiff ℝ ∞ χsource) (r : ℝ) (u : graphTestSpace (d + 1) q) (x : E) :
    graphOperator (elapsedPhase Ψ r)
      (frequencyCutFullAmplitude θ (elapsedAmplitude b χout χsource β r))
      (fun z ↦ (u.val z).ofLp) x =
    χout x • (((2 * Real.pi) ^ (d + 1) : ℂ)⁻¹ • ∫ ξ,
      Complex.exp (Complex.I * (((x 0 - r) * ξ 0 : ℝ) : ℂ)) •
        (Complex.exp (Complex.I *
          (Ψ (x 0) (x 0 - r) (spatialPart x) (spatialPart ξ) : ℂ)) •
          (b (x 0) (x 0 - r) (spatialPart x) (spatialPart ξ)).mulVec
            ((θ ξ * β ξ) • sourceInputFourierTransform
              (graphTestToSchwartz (complexSourceMaskTest χsource hs u)) ξ))) := by
  let A : E → E → Matrix (Fin q) (Fin q) ℂ := fun x ξ ↦
    (θ ξ * β ξ) • b (x 0) (x 0 - r) (spatialPart x) (spatialPart ξ)
  have hA : frequencyCutFullAmplitude θ (elapsedAmplitude b χout χsource β r) =
      fun x z ξ ↦ χout x • (χsource z • A x ξ) := by
    funext x z ξ
    simp only [frequencyCutFullAmplitude, elapsedAmplitude, A, smul_smul]
    congr 1
    ring
  rw [hA, graphOperator_target_mul]
  have hsource : graphOperator (elapsedPhase Ψ r) (fun x z ξ ↦ χsource z • A x ξ)
      (fun z ↦ (u.val z).ofLp) =
      graphOperator (elapsedPhase Ψ r) (fun x _ ξ ↦ A x ξ)
        (graphTestToSchwartz (complexSourceMaskTest χsource hs u)) := by
    rw [← graphOperator_source_mul]
    rfl
  rw [hsource, graphOperator_eq_sourceFourierIntegral]
  congr 2
  apply integral_congr_ae
  filter_upwards [] with ξ
  rw [exp_elapsedPhase, mul_smul]
  simp only [A, Matrix.smul_mulVec, Matrix.mulVec_smul]

/-- The reverse full amplitude keeps the source mask outside and the conjugate
Fourier multiplier to the left of the adjoint evolution. This is the literal
frequency-cut kernel underlying `Mχsource* Bβ* E_b* Mχout*` in
`app:ch_regular_base:lem:retarded-kernel`. -/
theorem cut_reverse_elapsedGraph_masks
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (χout χsource β θ : E → ℂ)
    (r : ℝ) (u : E → Fin q → ℂ) (z : E) :
    reverseGraphOperator (elapsedPhase Ψ r)
      (frequencyCutFullAmplitude (fun ξ ↦ star (θ ξ))
        (fun x z ξ ↦ (elapsedAmplitude b χout χsource β r x z ξ).conjTranspose)) u z =
      star (χsource z) • (((2 * Real.pi) ^ (d + 1) : ℂ)⁻¹ •
        ∫ ξ, star (θ ξ * β ξ) • ∫ x,
          star (graphOscillation (elapsedPhase Ψ r) x z ξ) •
            (b (x 0) (x 0 - r) (spatialPart x) (spatialPart ξ)).conjTranspose.mulVec
              (star (χout x) • u x)) := by
  simp only [reverseGraphOperator, frequencyCutFullAmplitude, elapsedAmplitude,
    Matrix.conjTranspose_smul, Matrix.smul_mulVec, Matrix.mulVec_smul, star_mul]
  simp_rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with ξ
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [smul_smul]
  congr 1
  ring

end JanetCartan.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
