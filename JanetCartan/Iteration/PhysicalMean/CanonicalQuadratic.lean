module

public import JanetCartan.Iteration.PhysicalMean.CanonicalSource
public import JanetCartan.Iteration.PhysicalMean.QuadraticSobolev

/-!
# Literal canonical quadratic source and the full grouped physical tensor

The SAME original sampled adjoints and SAME current inverse feed the full raw
kernel. The resulting canonical polynomial is exactly the periodization of
`C Σν μν HB(Σβ Fνβ, Σβ Gνβ)`. The only identity premises are primitive raw
kernel and coefficient realizations, produced by the actual corrected-raw
factory; no polynomial identity or bound is assumed
(`new:eq:mean-operators`, `app:ch_mean_pairs:eq:block-bilinear`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

open MeasureTheory
open scoped Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalMean
open CurrentMean SmoothPeriodicFamily CanonicalChange PhysicalForwardMean RawInputRealization ContinuumRow

variable {n N : ℕ} {ν β : Type*} [Fintype ν] [Fintype β]
    (radius : ν × β → ℝ) (weight : ν → ℝ)
    (φ : ((ν × β) × Euclidean (n-1)) → Euclidean n → ℝ)
    (m : ((ν × β) × Euclidean (n-1)) → ℝ)
    (amp : Fin N → Fin n → ((ν × β) × Euclidean (n-1)) → Euclidean n → ℂ)
    (C : Euclidean n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n)
    (Cp : Torus n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n) (hCp : IsSmoothPeriodic Cp)
    (hCeq : ∀ z, Cp z = C (AmplitudeBound.centeredTorusRepresentative z))
    (A : ∀ i : ν, Input n (fun j ↦ radius (i,j)) →L[ℝ] OutputL2 n)
    (G : ∀ i : ν, Input n (fun j ↦ radius (i,j)) →ₗ[ℝ]
      SmoothPeriodicFamily n Unit (Matrix (Fin N) (Fin n) ℂ))
    (hG : ∀ i w z, (G i w).val z () = ∑ j : β,
      (∫ η, ((fun a c ↦ physicalForwardKernel (fun η ↦ φ ((i,j),η)) (fun η ↦ m ((i,j),η))
        (fun η y ↦ amp a c ((i,j),η) y) (AmplitudeBound.centeredTorusRepresentative z) η*w j η) :
          Matrix (Fin N) (Fin n) ℂ) ∂annularMeasure n (radius (i,j)) : Matrix (Fin N) (Fin n) ℂ))
    (Q₀ : OutputL2 n →L[ℝ] OutputL2 n)

/-- The literal annular inputs are the ORIGINAL individual sampled real
adjoints of the SAME current inverse, with no weights divided out. -/
def canonicalAnnularInputs (u : SmoothResidual n) :
    ∀ ij : ν × β, Lp ℂ 2 (annularMeasure n (radius ij)) :=
  fun ij ↦ ((A ij.1).adjoint (Q₀ (smoothResidualToL2 n u))) ij.2

include hCeq hG

/-- Exact function equality between the actual canonical quadratic source and
the full original grouped physical tensor. Both source arguments are retained,
so the same identity also applies to low residual differences. -/
theorem fixedSourceQuadratic_eq_groupedPeriodization (u v : SmoothResidual n) :
    (fun z ↦ (fixedSourceQuadratic weight Cp hCp A G Q₀ u v).val z ()) =
      UniformStep.Periodization.vectorPeriodization
        (groupedAnnularWeightedQuadratic radius φ m amp weight C
          (canonicalAnnularInputs radius A Q₀ u) (canonicalAnnularInputs radius A Q₀ v)) := by
  funext z
  change Cp z (∑ i, weight i • mixedHermitianTensor
      ((G i ((A i).adjoint (Q₀ (smoothResidualToL2 n u)))).val z ())
      ((G i ((A i).adjoint (Q₀ (smoothResidualToL2 n v)))).val z ())) = _
  rw [hCeq z]
  simp_rw [hG]
  rfl

/-- The actual canonical L² class has the literal grouped physical
periodization as its representative. This closes the smooth-function-to-L²
identity before any Sobolev norm comparison is made. -/
theorem fixedSourceQuadratic_toL2_ae_groupedPeriodization (u v : SmoothResidual n) :
    smoothResidualToL2 n (fixedSourceQuadratic weight Cp hCp A G Q₀ u v) =ᵐ[volume]
      UniformStep.Periodization.vectorPeriodization
        (groupedAnnularWeightedQuadratic radius φ m amp weight C
          (canonicalAnnularInputs radius A Q₀ u) (canonicalAnnularInputs radius A Q₀ v)) := by
  have he := componentL2_coe_ae () (fixedSourceQuadratic weight Cp hCp A G Q₀ u v)
  rw [fixedSourceQuadratic_eq_groupedPeriodization radius weight φ m amp C Cp hCp hCeq A G hG Q₀ u v] at he
  exact he

/-- The actual source seminorm is exactly the SAME-order Fourier Sobolev norm
of the full grouped tensor. No output norm equivalence loss is introduced. -/
theorem fixedSourceQuadratic_sobolev_eq_grouped (u v : SmoothResidual n) (s : ℕ) :
    residualSobolevSeminorm n s (fixedSourceQuadratic weight Cp hCp A G Q₀ u v) =
      periodicSobolevNorm s (UniformStep.Periodization.vectorPeriodization
        (groupedAnnularWeightedQuadratic radius φ m amp weight C
          (canonicalAnnularInputs radius A Q₀ u) (canonicalAnnularInputs radius A Q₀ v))) := by
  rw [residualSobolevSeminorm_eq_periodicSobolevNorm]
  have he := fixedSourceQuadratic_toL2_ae_groupedPeriodization radius weight φ m amp C Cp hCp hCeq A G hG Q₀ u v
  simp only [periodicSobolevNorm, periodicFourierCoeff_congr_ae he]

end JanetCartan.PhysicalMean
