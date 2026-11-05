module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.Kernel
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Literal adjoint pairing on integrable test inputs

Fubini proves the literal integral-adjoint identity in
`app:ch_background:eq:bg-realification` whenever the displayed integrals are
integrable. This does not assert convergence for arbitrary L² inputs or construct
the bounded extension: the unbounded-frequency oscillatory estimate is still needed.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.ContinuumRow

/-- Moving the first slot of the complex inner product through an integrable
vector kernel, used in `app:ch_background:eq:bg-realification`. -/
theorem integral_inner_left {α V : Type*} [MeasurableSpace α] (μ : Measure α)
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (v : α → V) (hv : Integrable v μ) (w : V) :
    inner ℂ (∫ x, v x ∂μ) w = ∫ x, inner ℂ (v x) w ∂μ := by
  rw [← inner_conj_symm, ← integral_inner hv, ← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with x
  exact inner_conj_symm _ _

/-- Fubini's literal carrier-adjoint pairing on test inputs
(`app:ch_background:eq:bg-T`, `app:ch_background:eq:bg-realification`).
The hypotheses state actual integrability, not a presumed adjoint identity. -/
theorem carrierTestIntegral_adjoint_pairing {n N : ℕ} (d : CarrierData n N)
    (f : CarrierVariable n → ℂ) (w : Torus n → EuclideanSpace ℂ (Fin n))
    (hsections : ∀ᵐ x ∂volume, Integrable (fun u ↦ f u • carrierKernel d x u)
      (carrierMeasure n))
    (hpair : Integrable (fun p : Torus n × CarrierVariable n ↦
      (starRingEnd ℂ) (f p.2) * inner ℂ (carrierKernel d p.1 p.2) (w p.1))
      (volume.prod (carrierMeasure n))) :
    (∫ x, inner ℂ (carrierTestIntegral d f x) (w x)) =
      ∫ u, (starRingEnd ℂ) (f u) * carrierAdjointIntegral d w u ∂carrierMeasure n := by
  calc
    (∫ x, inner ℂ (carrierTestIntegral d f x) (w x)) =
        ∫ x, ∫ u, (starRingEnd ℂ) (f u) * inner ℂ (carrierKernel d x u) (w x)
          ∂carrierMeasure n := by
      apply integral_congr_ae
      filter_upwards [hsections] with x hx
      rw [carrierTestIntegral, integral_inner_left _ _ hx]
      simp only [inner_smul_left]
    _ = ∫ u, ∫ x, (starRingEnd ℂ) (f u) * inner ℂ (carrierKernel d x u) (w x)
          ∂volume ∂carrierMeasure n := integral_integral_swap hpair
    _ = ∫ u, (starRingEnd ℂ) (f u) * carrierAdjointIntegral d w u ∂carrierMeasure n := by
      apply integral_congr_ae
      filter_upwards [] with u
      exact integral_const_mul _ _

end JanetCartan.ContinuumRow
