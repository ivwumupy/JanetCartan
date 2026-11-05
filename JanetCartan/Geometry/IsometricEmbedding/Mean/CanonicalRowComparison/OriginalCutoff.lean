module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalTailRealization.CarrierBands

/-!
# The original continuum carrier at every retained cutoff

The floor-one support follows from the SAME literal continuum adjoint and
its high cutoff. The existing wide-band square partition therefore identifies
the finite sum of actual cut-carrier normals with the rounded raw square on
the original operator, before its original inverse is applied.

Consumer: `CanonicalRowComparison`'s transport-to-reference identification
in `app:ch_mean_pairs:eq:mean-normal-comparison`.
-/

@[expose] public noncomputable section
open MeasureTheory

namespace JanetCartan.CanonicalRowComparison
open ContinuumRow RawCutoffBounds RawInputPartition CanonicalTailRealization

/-- Retain the original band labels when writing a prefix under its fixed
ceiling (`app:ch_waves:eq:sampling-prefix-normal`). -/
private theorem sum_fin_prefix_eq_range {E : Type*} [AddCommMonoid E]
    {L bands : ℕ} (hL : L ≤ bands) (f : ℕ → E) :
    (∑ j ∈ Finset.univ.filter (fun j : Fin bands ↦ j.val < L), f j.val) =
      ∑ j ∈ Finset.range L, f j := by
  classical
  rw [Finset.sum_filter, Fin.sum_univ_eq_sum_range (fun j ↦ if j < L then f j else 0)]
  rw [← Finset.sum_filter]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨h.trans_le hL, h⟩⟩

/-- On the original raw adjoint, the rounded square is exactly the sum of
the unchanged smooth band squares. This derives the support condition from
the actual high-pass and literal-adjoint realization; it is not assumed of
the canonical datum (`app:ch_waves:eq:sampling-prefix-normal`,
`main:eq:linear-two-errors`). -/
theorem originalCarrier_adjoint_rounded_eq_sum
    {n N : ℕ} (d : CarrierData n N)
    (hhigh : ∀ t, t ≤ 1 → d.highCutoff t = 0)
    (U : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hU : ∀ q, U.adjoint q =ᵐ[carrierMeasure n] carrierAdjointIntegral d q)
    (K : ℝ) (q : OutputL2 n) :
    carrierSquaredCutoff (roundedCarrierMask n K) ((carrierChannel U).adjoint q) =
      ∑ j ∈ Finset.range (cutoffCount K),
        carrierSquaredCutoff (dyadicCarrierBandMask n j) ((carrierChannel U).adjoint q) := by
  let v := l2ComplexInclusion volume q
  have hm : MemLp (carrierAdjointIntegral d v) 2 (carrierMeasure n) :=
    (memLp_congr_ae (hU v)).mp (Lp.memLp _)
  have he : hm.toLp (carrierAdjointIntegral d v) = U.adjoint v :=
    Lp.ext (hm.coeFn_toLp.trans (hU v).symm)
  have hs := carrierSquaredCutoff_adjointIntegral_eq_sum d hhigh v hm K
  rw [he] at hs
  simp only [carrierChannel_adjoint_apply, map_smul, ← Finset.smul_sum]
  exact congrArg (fun w : CarrierL2 n ↦ (2 : ℝ) • w) hs

/-- The finite band normal equals the ORIGINAL carrier composed with the
rounded raw square and its original adjoint. The cutoff count is bounded by
the fixed pre-sampling ceiling, with no new row or inverse chosen at a prefix
(`app:ch_waves:eq:sampling-prefix-normal`, `app:ch_mean_pairs:defn:mean-canonical`). -/
theorem originalCarrier_band_normals_eq_rounded
    {n N bands : ℕ} (d : CarrierData n N)
    (hhigh : ∀ t, t ≤ 1 → d.highCutoff t = 0)
    (U : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hU : ∀ q, U.adjoint q =ᵐ[carrierMeasure n] carrierAdjointIntegral d q)
    (K : ℝ) (hL : cutoffCount K ≤ bands) :
    (∑ j ∈ Finset.univ.filter (fun j : Fin bands ↦ j.val < cutoffCount K),
      ((carrierChannel U).comp (carrierMultiplier (dyadicCarrierBandMask n j.val))).comp
        ((carrierChannel U).comp (carrierMultiplier (dyadicCarrierBandMask n j.val))).adjoint) =
      (carrierChannel U).comp ((carrierSquaredCutoff (roundedCarrierMask n K)).comp
        (carrierChannel U).adjoint) := by
  classical
  rw [sum_fin_prefix_eq_range hL (fun j ↦
    ((carrierChannel U).comp (carrierMultiplier (dyadicCarrierBandMask n j))).comp
      ((carrierChannel U).comp (carrierMultiplier (dyadicCarrierBandMask n j))).adjoint)]
  ext1 q
  simp only [sum_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_comp,
    carrierMultiplier_adjoint]
  change (∑ j ∈ Finset.range (cutoffCount K), carrierChannel U
    (carrierSquaredCutoff (dyadicCarrierBandMask n j) ((carrierChannel U).adjoint q))) = _
  rw [← map_sum, ← originalCarrier_adjoint_rounded_eq_sum d hhigh U hU K q]

end JanetCartan.CanonicalRowComparison
