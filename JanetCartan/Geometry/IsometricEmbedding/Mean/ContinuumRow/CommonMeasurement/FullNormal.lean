module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CommonMeasurement.Transfer

/-!
# Restriction of the supported producer's full reflected normal

Specialize the proved multiplier and transfer identities to the exact full
matrix amplitude returned by the supported carrier producer. The new bounded
physical operator is constructed by multiplication; its literal full-amplitude
action is proved from that of the existing PDO. This is a global L² identity,
not a principal-symbol or localized-normal assertion.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.CommonMeasurement
open AmplitudeBound Pseudodifferential PeriodicLocalL2 ContinuumNormal
  ContinuumNormalReduction TransportKernel CarrierNormalRealization
variable {n N : ℕ}

/-- The SAME constructed carrier's restricted global normal is the transfer
of a bounded physical realization of the full reflected amplitude with its
measurement coefficient multiplied by `β`. All analytic premises are the
original supported producer's conclusions; the new realization and normal
identity are proved here. Both positions, the original inverse chart and
spectator measure, `k = 2πξ`, and the single quadrature factor four are retained
(`app:ch_background:eq:bg-full-complex-amplitude`, `bg-real-symbol`). -/
theorem restricted_fullReflected_realization
    (hn : 0 < n) (R : ℝ)
    (a : TransportSymbol.Coefficients n N) (J : TransportSymbol.InputVariables n → ℝ)
    (u : TransportSymbol.Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (TransportSymbol.Variables n × Euclidean 2)) (S : Set (Euclidean 2))
    (hb : ContDiff ℝ ∞ (Function.uncurry (fullReflectedMatrixAmplitude a J u Ω S)))
    (hs : ∀ ξ i j, SupportedInCenteredBox R
      (fun z ↦ fullReflectedMatrixAmplitude a J u Ω S ξ z i j))
    (B : ℝ) (hB : ∀ i j, HasAmplitudeDerivativeBound
      (fun ξ z ↦ fullReflectedMatrixAmplitude a J u Ω S ξ z i j) (2 * (n + 1)) B)
    (χ : C(Torus n, ℝ)) (β : Euclidean n → ℝ)
    (hβ : ContDiff ℝ ∞ β) (hβs : HasCompactSupport β)
    (hχ : ∀ z, χ z = β (centeredTorusRepresentative z))
    (U : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hUnormal : carrierChannel U ∘L (carrierChannel U).adjoint =
      realOutputCompression (transferOperator
        (vectorTwoPositionL2Operator hn R (fullReflectedMatrixAmplitude a J u Ω S) hb hs B hB))) :
    let A := vectorTwoPositionL2Operator hn R (fullReflectedMatrixAmplitude a J u Ω S) hb hs B hB
    let Aχ := freezingVectorPhysicalMultiplier β hβ.continuous hβs ∘L A ∘L
      freezingVectorPhysicalMultiplier β hβ.continuous hβs
    (carrierChannel (restrictCarrier χ U) ∘L (carrierChannel (restrictCarrier χ U)).adjoint =
      realOutputCompression (transferOperator Aχ)) ∧
    ∀ (f : Euclidean n → EuclideanSpace ℂ (Fin n)) (hf : MemLp f 2 volume),
      ContDiff ℝ ∞ f → HasCompactSupport f →
      Aχ (hf.toLp f) =ᵐ[volume] fun x ↦ WithLp.toLp 2
        (matrixFullAmplitudeOperator
          (fun x y ξ ↦ fullReflectedMatrixAmplitude (restrictCoefficients a β) J u Ω S ξ
            (pairedPosition x y)) (fun y j ↦ f y j) x) := by
  dsimp only
  refine ⟨restrictCarrier_global_normal χ β hβ.continuous hβs hχ U _ hUnormal, ?_⟩
  intro f hf hfc hfs
  rw [fullReflectedMatrixAmplitude_restrictCoefficients]
  exact physicalSandwich_ae_matrixFullAmplitudeOperator hn R
    (fullReflectedMatrixAmplitude a J u Ω S) hb hs B hB β hβ hβs f hf hfc hfs

end JanetCartan.ContinuumRow.CommonMeasurement
