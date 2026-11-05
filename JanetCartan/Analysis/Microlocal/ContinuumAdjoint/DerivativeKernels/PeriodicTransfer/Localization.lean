module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.PeriodicTransfer.Extension

/-!
# Localization of the literal carrier adjoint

For `app:ch_background:prop:bg-adjoint`, the representative formula of the
Euclidean adjoint identifies its periodic restriction and its compact source
extension. All integrals retain their original Haar and carrier measures.
The chart-point and measurement-cutoff identities are already used in the
producer `exists_literalCarrierAdjoint_chart_raw_bound`; here only the resulting
literal formula and its chart support are needed.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open JanetCartan.AmplitudeBound JanetCartan.PeriodicLocalL2

namespace JanetCartan.ContinuumAdjoint.DerivativeKernels
open ContinuumRow Pseudodifferential Pseudodifferential.DifferentialChart
variable {n N : ℕ}

/-- The original adjoint integral depends only on the datum on its chart,
up to Haar-null sets (`app:ch_background:prop:bg-adjoint`). -/
theorem carrierAdjointIntegral_congr_chart_ae (d : CarrierData n N)
    {v w : Torus n → EuclideanSpace ℂ (Fin n)}
    (h : ∀ᵐ x ∂volume, x ∈ d.outputChart → v x = w x) :
    carrierAdjointIntegral d v = carrierAdjointIntegral d w := by
  funext z
  apply integral_congr_ae
  filter_upwards [h] with x hx
  by_cases hchart : x ∈ d.outputChart
  · rw [hx hchart]
  · simp only [carrierKernel_eq_zero_outside d hchart, inner_zero_left]

/-- The periodic operator is the literal unit-cell lift followed by the given
Euclidean adjoint (`app:ch_background:prop:bg-adjoint`). -/
def periodicCarrierOperator
    (U : EuclideanL2 n (EuclideanSpace ℂ (Fin n)) →L[ℂ] CarrierL2 n) :
    PeriodicL2 n (EuclideanSpace ℂ (Fin n)) →L[ℂ] CarrierL2 n :=
  U.comp (toEuclidean (𝕜 := ℂ)).toContinuousLinearMap

/-- The periodic restriction represents the original Haar adjoint for every
periodic L² datum, without a smoothness assumption
(`app:ch_background:prop:bg-adjoint`). -/
theorem periodicCarrierOperator_ae (d : CarrierData n N)
    (U : EuclideanL2 n (EuclideanSpace ℂ (Fin n)) →L[ℂ] CarrierL2 n)
    (hU : ∀ f, U f =ᵐ[carrierMeasure n] carrierAdjointIntegral d
      (fun x ↦ f (centeredTorusRepresentative x)))
    (v : PeriodicL2 n (EuclideanSpace ℂ (Fin n))) :
    periodicCarrierOperator U v =ᵐ[carrierMeasure n] carrierAdjointIntegral d v := by
  have hv : (fun x ↦ toEuclidean (𝕜 := ℂ) v (centeredTorusRepresentative x)) =ᵐ[volume] v := by
    have h := (toTorus_coe (𝕜 := ℂ) (toEuclidean (𝕜 := ℂ) v)).symm
    rwa [toTorus_toEuclidean] at h
  have he := carrierAdjointIntegral_congr_chart_ae d (hv.mono (fun _ hx _ ↦ hx))
  exact (hU (toEuclidean (𝕜 := ℂ) v)).trans (Filter.Eventually.of_forall fun x ↦ congrFun he x)

/-- On smooth tests the periodic operator equals the same Euclidean adjoint
applied to compact extension. The buffered box contains the whole chart; hence
artificial cutoff derivatives introduce no change to the literal integral
(`app:ch_background:prop:bg-adjoint`). -/
theorem periodicCarrierOperator_eq_extension
    {r : ℝ} (ψ : SourceCutoff n r) (d : CarrierData n N)
    {K : Set (Euclidean n)} (hK : K ⊆ chartBox r)
    (hchart : d.outputChart = torusChart K)
    (U : EuclideanL2 n (EuclideanSpace ℂ (Fin n)) →L[ℂ] CarrierL2 n)
    (hU : ∀ f, U f =ᵐ[carrierMeasure n] carrierAdjointIntegral d
      (fun x ↦ f (centeredTorusRepresentative x)))
    {u : Torus n → EuclideanSpace ℂ (Fin n)} (hu : IsSmoothPeriodic u)
    (v : PeriodicL2 n (EuclideanSpace ℂ (Fin n))) (hv : v =ᵐ[volume] u) :
    periodicCarrierOperator U v = U (periodicVectorExtension ψ hu) := by
  have hext := measurePreserving_representative.quasiMeasurePreserving.ae_eq_comp
    (periodicVectorExtension_coe ψ hu).restrict
  have he : carrierAdjointIntegral d
      (fun x ↦ periodicVectorExtension ψ hu (centeredTorusRepresentative x)) =
        carrierAdjointIntegral d v := by
    apply carrierAdjointIntegral_congr_chart_ae
    filter_upwards [hext, hv] with x hx hvx hxc
    have hxK : centeredTorusRepresentative x ∈ K := by
      simpa only [hchart, torusChart, mem_preimage] using hxc
    have hp : ψ.toFun (centeredTorusRepresentative x) = 1 :=
      show centeredTorusRepresentative x ∈ {y | ψ.toFun y = 1} from
        interior_subset (ψ.plateau (hK hxK))
    change periodicVectorExtension ψ hu (centeredTorusRepresentative x) = v x
    dsimp only [Function.comp_apply] at hx
    rw [hx, hp, one_smul]
    simpa only [periodicLift, Function.comp_apply,
      torusQuotient_centeredTorusRepresentative] using hvx.symm
  apply Lp.ext
  exact (periodicCarrierOperator_ae d U hU v).trans
    ((hU (periodicVectorExtension ψ hu)).trans
      (Filter.Eventually.of_forall fun x ↦ congrFun he x)).symm

end JanetCartan.ContinuumAdjoint.DerivativeKernels
