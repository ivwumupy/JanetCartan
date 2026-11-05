module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalTailRealization.RawNormal
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputPartition

/-!
# Literal finite carrier squares on the canonical adjoint datum

The smooth wide-band masks from `RawInputPartition` are packaged on the
original carrier measure, and their finite sum is identified with the
rounded carrier square. The low support needed for this reassembly is proved
directly for the original adjoint integral from its high-frequency kernel.
The input's L² membership is an analytic domain input, not a representation
identity or a tail estimate.

Consumers are the reference-normal identification in `RawNormal` and
`RecurrenceTail.run_inductive_raw_tail_le`, for
`app:ch_waves:eq:sampling-prefix-normal` and `main:eq:linear-two-errors`.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ENNReal

namespace JanetCartan.CanonicalTailRealization
open ContinuumRow RawCutoffBounds RawInputPartition

variable {n N : ℕ}

/-- The original smooth wide-band mask as an L∞ coefficient on `dz dη`;
no sharp piece is truncated separately
(`app:ch_waves:eq:sampling-prefix-normal`). -/
def dyadicCarrierBandMask (n j : ℕ) : Lp ℝ ∞ (carrierMeasure n) :=
  carrierMask (carrierBand n j)
    ((measurable_radialBand n j).comp measurable_snd).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x ↦ bandProfile_mem (‖x.2‖ / dyadicScale j))

/-- The packaged mask has exactly the original wide-band representative
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem dyadicCarrierBandMask_coeFn (n j : ℕ) :
    dyadicCarrierBandMask n j =ᵐ[carrierMeasure n] carrierBand n j :=
  carrierMask_coeFn _ _ _

/-- The single wide-band square acts by the original smooth squared mask
on the literal carrier datum (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem carrierSquaredCutoff_dyadicBand_coeFn (j : ℕ) (u : CarrierL2 n) :
    carrierSquaredCutoff (dyadicCarrierBandMask n j) u =ᵐ[carrierMeasure n]
      fun x ↦ carrierBand n j x ^ 2 • u x := by
  refine (carrierSquaredCutoff_coeFn (dyadicCarrierBandMask n j) u).trans ?_
  filter_upwards [dyadicCarrierBandMask_coeFn n j] with x hx
  exact congrArg (fun t : ℝ ↦ t ^ 2 • u x) hx

/-- Reassembly of the actual finite raw input squares is equality of L²
classes. The given floor-one support is preserved; the carrier cutoff is
never substituted into either auxiliary component
(`app:ch_background:defn:bg-mixed`). -/
theorem carrierSquaredCutoff_rounded_eq_sum (K : ℝ) (u : CarrierL2 n)
    (hu : ∀ᵐ x ∂carrierMeasure n, ‖x.2‖ ≤ 1 → u x = 0) :
    carrierSquaredCutoff (roundedCarrierMask n K) u =
      ∑ j ∈ Finset.range (cutoffCount K), carrierSquaredCutoff (dyadicCarrierBandMask n j) u := by
  apply Lp.ext
  have hbands := Filter.eventually_all.mpr (fun j : Fin (cutoffCount K) ↦
    carrierSquaredCutoff_dyadicBand_coeFn j.val u)
  filter_upwards [carrierSquaredCutoff_coeFn (roundedCarrierMask n K) u,
    Lp.coeFn_finsetSum (Finset.range (cutoffCount K))
      (fun j ↦ carrierSquaredCutoff (dyadicCarrierBandMask n j) u),
    carrierPrefixMask_coeFn n (cutoffCount K), hbands, hu] with x hcut hsum hmask hbands hfloor
  rw [hcut, hsum, Finset.sum_apply]
  change (carrierPrefixMask n (cutoffCount K) x) ^ 2 • u x = _
  rw [hmask]
  have hsum' : (∑ j ∈ Finset.range (cutoffCount K),
      carrierSquaredCutoff (dyadicCarrierBandMask n j) u x) =
      (∑ j ∈ Finset.range (cutoffCount K), carrierBand n j x ^ 2) • u x := by
    rw [Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro j hj
    exact hbands ⟨j, Finset.mem_range.mp hj⟩
  rw [hsum']
  by_cases hx : ‖x.2‖ ≤ 1
  · simp only [hfloor hx, smul_zero]
  · exact congrArg (fun t : ℝ ↦ t • u x)
      (sum_scalarBand_sq_eq_prefix_sq (cutoffCount K) (le_of_not_ge hx)).symm

/-- The literal kernel's high cutoff forces low-frequency vanishing of
its adjoint integral, before any choice of an L² representative
(`app:ch_background:eq:bg-T`). -/
theorem carrierAdjointIntegral_eq_zero_of_highCutoff (d : CarrierData n N)
    (q : Torus n → EuclideanSpace ℂ (Fin n)) {x : CarrierVariable n}
    (hx : d.highCutoff ‖x.2‖ = 0) : carrierAdjointIntegral d q x = 0 := by
  simp only [carrierAdjointIntegral, carrierKernel_eq_zero_of_highCutoff d _ _ hx,
    inner_zero_left, integral_zero]

/-- The actual L² adjoint-integral datum retains its floor-one support.
Only membership is supplied; support is proved from the original kernel
(`app:ch_background:defn:bg-row`). -/
theorem adjointIntegral_toLp_floor (d : CarrierData n N)
    (hhigh : ∀ t, t ≤ 1 → d.highCutoff t = 0)
    (q : Torus n → EuclideanSpace ℂ (Fin n))
    (hq : MemLp (carrierAdjointIntegral d q) 2 (carrierMeasure n)) :
    ∀ᵐ x ∂carrierMeasure n, ‖x.2‖ ≤ 1 → hq.toLp (carrierAdjointIntegral d q) x = 0 := by
  filter_upwards [hq.coeFn_toLp] with x hx hlow
  exact hx.trans (carrierAdjointIntegral_eq_zero_of_highCutoff d q (hhigh _ hlow))

/-- The SAME actual adjoint-integral datum has exactly the literal finite
wide-band raw square. In particular the datum may use the fixed inverse
applied to the current residual, with no new choice for each cutoff
(`main:eq:linear-two-errors`). -/
theorem carrierSquaredCutoff_adjointIntegral_eq_sum (d : CarrierData n N)
    (hhigh : ∀ t, t ≤ 1 → d.highCutoff t = 0)
    (q : Torus n → EuclideanSpace ℂ (Fin n))
    (hq : MemLp (carrierAdjointIntegral d q) 2 (carrierMeasure n)) (K : ℝ) :
    carrierSquaredCutoff (roundedCarrierMask n K) (hq.toLp (carrierAdjointIntegral d q)) =
      ∑ j ∈ Finset.range (cutoffCount K), carrierSquaredCutoff (dyadicCarrierBandMask n j)
        (hq.toLp (carrierAdjointIntegral d q)) :=
  carrierSquaredCutoff_rounded_eq_sum K _ (adjointIntegral_toLp_floor d hhigh q hq)

end JanetCartan.CanonicalTailRealization
