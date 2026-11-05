module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.Spaces
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Keeping the spectator measure in the transport normal

The rearrangement `((s,v),η) ↔ (v,(s,η))` in
`app:ch_background:eq:bg-full-complex-amplitude` preserves the literal product
measure. It does not push forward the initial data by the physical transport.
This leaf supplies the Fubini step for `regularizedNormalEntry`.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.ContinuumRow.TransportKernel

/-- The variables transformed by the conic chart, at fixed spectator `v`
(`app:ch_background:eq:bg-Psi`). -/
abbrev SliceVariable (n : ℕ) := ℝ × Euclidean (n - 1)

/-- Canonical coordinates `(s,η)` for a positive output dimension. This is a
coordinate permutation, not the transport of initial data
(`app:ch_background:eq:bg-Psi`). -/
def sliceCoordinates (m : ℕ) : Euclidean (m + 1) ≃ᵐ SliceVariable (m + 1) :=
  (MeasurableEquiv.toLp 2 (Fin (m + 1) → ℝ)).symm.trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℝ) 0).trans
      ((MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.toLp 2 (Fin m → ℝ))))

/-- The canonical `(s,η)` coordinates preserve Lebesgue measure exactly,
so there is no extra coordinate Jacobian in
`app:ch_background:eq:bg-full-complex-amplitude`. -/
theorem sliceCoordinates_measurePreserving (m : ℕ) :
    MeasurePreserving (sliceCoordinates m) volume (volume.prod volume) :=
  ((MeasurePreserving.id volume).prod (PiLp.volume_preserving_toLp (Fin m))).comp
    ((volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℝ) 0).comp
      (PiLp.volume_preserving_ofLp (Fin (m + 1))))

/-- Literal regrouping of carrier variables, with no geometric transport
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
def spectatorEquiv (n : ℕ) : CarrierVariable n ≃ᵐ Euclidean 2 × SliceVariable n :=
  (MeasurableEquiv.prodComm.prodCongr (MeasurableEquiv.refl _)).trans
    MeasurableEquiv.prodAssoc

/-- The regrouping preserves exactly `((ds dv) dη)` as `dv (ds dη)`
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem spectatorEquiv_measurePreserving (n : ℕ) :
    MeasurePreserving (spectatorEquiv n) (carrierMeasure n)
      (volume.prod (volume.prod volume)) :=
  (measurePreserving_prodAssoc volume volume volume).comp
    (Measure.measurePreserving_swap.prod (MeasurePreserving.id volume))

/-- Absolute integrability transfers to the spectator ordering, as needed for
Fubini in `app:ch_background:eq:bg-full-complex-amplitude`. -/
theorem integrable_spectator_iff {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    (f : CarrierVariable n → F) :
    Integrable (fun p : Euclidean 2 × SliceVariable n ↦ f ((p.2.1, p.1), p.2.2))
      (volume.prod (volume.prod volume)) ↔ Integrable f (carrierMeasure n) :=
  ((spectatorEquiv_measurePreserving n).symm (spectatorEquiv n)).integrable_comp_emb
    (spectatorEquiv n).symm.measurableEmbedding

/-- Actual Fubini with the spectator outside the `(s,η)` integral. The sole
analytic hypothesis is absolute integrability on the original input measure
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem integral_carrier_eq_spectator {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : CarrierVariable n → F)
    (hf : Integrable f (carrierMeasure n)) :
    (∫ u, f u ∂carrierMeasure n) =
      ∫ v : Euclidean 2, ∫ t : SliceVariable n, f ((t.1, v), t.2)
        ∂(volume.prod volume) := by
  rw [← ((spectatorEquiv_measurePreserving n).symm
    (spectatorEquiv n)).integral_comp' f]
  exact integral_prod _ ((integrable_spectator_iff f).mpr hf)

end JanetCartan.ContinuumRow.TransportKernel
