module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierExtension.Limit
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.TestAdjoint
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Support and literal adjoint of a carrier realization

Consequences of realization on the proved dense initial test domain, for
`app:ch_background:eq:bg-T` and `app:ch_background:prop:bg-frame`, Step 1.
Consumers are the continuum row and initial-variable adjoint constructions.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace JanetCartan.ContinuumRow

variable {n N : ℕ}

/-- Output support passes from literal tests to every initial L² input
(`app:ch_background:defn:bg-row`). No measurability of the chart is needed. -/
theorem carrierRealization_eq_zero_outside (d : CarrierData n N)
    (U : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hU : ∀ u : carrierInitialTestSpace n,
      U (carrierInitialTestToLp u) =ᵐ[volume] carrierTestIntegral d u.val)
    (f : CarrierL2 n) : ∀ᵐ x ∂volume, x ∉ d.outputChart → U f x = 0 := by
  obtain ⟨v, hv, hlim⟩ := mem_closure_iff_seq_limit.mp (denseRange_carrierInitialTestToLp f)
  have hs (k : ℕ) : ∀ᵐ x ∂volume, x ∉ d.outputChart → U (v k) x = 0 := by
    obtain ⟨u, hu⟩ := hv k
    rw [← hu]
    filter_upwards [hU u] with x hx houtside
    rw [hx, carrierTestIntegral_eq_zero_outside d u.val houtside]
  obtain ⟨ks, _, hks⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (U.continuous.tendsto f |>.comp hlim)).exists_seq_tendsto_ae
  filter_upwards [hks, ae_all_iff.mpr hs] with x hx hsx houtside
  exact tendsto_nhds_unique hx (tendsto_const_nhds.congr (fun k ↦ (hsx (ks k) houtside).symm))

/-- The Hilbert adjoint pairs with the literal kernel wherever Fubini is
justified (`app:ch_background:eq:bg-realification`). Only integrability of
actual sections and the actual scalar product kernel is required. -/
theorem carrierRealization_adjoint_pairing (d : CarrierData n N)
    (U : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hU : ∀ u : carrierInitialTestSpace n,
      U (carrierInitialTestToLp u) =ᵐ[volume] carrierTestIntegral d u.val)
    (u : carrierInitialTestSpace n) (w : ComplexOutputL2 n)
    (hsections : ∀ᵐ x ∂volume, Integrable (fun z ↦ u.val z • carrierKernel d x z)
      (carrierMeasure n))
    (hpair : Integrable (fun p : Torus n × CarrierVariable n ↦
      (starRingEnd ℂ) (u.val p.2) * inner ℂ (carrierKernel d p.1 p.2) (w p.1))
      (volume.prod (carrierMeasure n))) :
    inner ℂ (carrierInitialTestToLp u) (U.adjoint w) =
      ∫ z, (starRingEnd ℂ) (u.val z) * carrierAdjointIntegral d w z
        ∂carrierMeasure n := by
  rw [U.adjoint_inner_right, L2.inner_def]
  calc
    _ = ∫ x, inner ℂ (carrierTestIntegral d u.val x) (w x) := by
      apply integral_congr_ae
      filter_upwards [hU u] with x hx
      rw [hx]
    _ = _ := carrierTestIntegral_adjoint_pairing d u.val w hsections hpair

end JanetCartan.ContinuumRow
