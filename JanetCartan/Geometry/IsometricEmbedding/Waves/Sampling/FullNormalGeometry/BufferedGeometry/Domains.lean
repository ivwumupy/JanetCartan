module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.FullNormalGeometry.PhaseExtension

/-!
# Convex neighborhoods of the complete radial sampling support

The positive radial interval times the retained normalized input core has a
convex image in the literal sampling coordinates. Its entire compact support
fits inside the interior of the doubled core, with a positive input buffer.
The consumer is the domain part of `UniformNormalGeometry` and its original
phase-extension containment in `app:ch_waves:setup:oscillatory`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped ContDiff

namespace JanetCartan.Sampling.FullNormalGeometry
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ActualPhase ActualComparison ContinuumRow.CanonicalConic
open MeanNormalBound.CanonicalGap RawKernel
open ContinuumNormalReduction.ConicChart

variable {m : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- Exact identification of the complete support in the product coordinates
used by the actual inverse construction. Consumer: the radial C¹ and frozen
gap inputs to `app:ch_seed:prop:seed-phase-charts`. -/
theorem radialSamplingSupport_eq_preimage (z₀ : Euclidean 3)
    (ηb : Euclidean m) (r amin amax : ℝ) :
    radialSamplingSupport T z₀ ηb r amin amax =
      ((canonicalInputIsometry T).toContinuousLinearEquiv.trans
        (adaptedSliceCoordinates T).equiv) ⁻¹'
        ((fun q : ℝ × (ℝ × Euclidean m) ↦ radialScale q.1 q.2) ''
          (Icc amin amax ×ˢ dataBox (n := m + 1) z₀ ηb r)) := by
  ext u
  constructor
  · rintro ⟨⟨a, w⟩, ⟨ha, hw⟩, he⟩
    refine ⟨(a, (adaptedSliceCoordinates T).equiv w), ⟨ha, hw⟩, ?_⟩
    change radialScale a ((adaptedSliceCoordinates T).equiv w) =
      (adaptedSliceCoordinates T).equiv (canonicalInputCoordinates T u)
    rw [← he]
    simp only [radialInput, ContinuousLinearEquiv.apply_symm_apply]
  · rintro ⟨⟨a, w⟩, ⟨ha, hw⟩, he⟩
    refine ⟨(a, (adaptedSliceCoordinates T).equiv.symm w), ⟨ha, ?_⟩, ?_⟩
    · change (adaptedSliceCoordinates T).equiv
        ((adaptedSliceCoordinates T).equiv.symm w) ∈ dataBox (n := m + 1) z₀ ηb r
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using hw
    · apply (adaptedSliceCoordinates T).equiv.injective
      change radialScale a w = (adaptedSliceCoordinates T).equiv
        (canonicalInputCoordinates T u) at he
      simpa only [radialInput, ContinuousLinearEquiv.apply_symm_apply] using he

/-- The complete radial support is convex for a nonnegative prescribed radial
interval; the incidence coordinate is unchanged. This supplies the convex
domain needed by the global inverse construction, without cutting the kernel
into radial pieces (`app:ch_seed:prop:seed-phase-charts`). -/
theorem convex_radialSamplingSupport (z₀ : Euclidean 3) (ηb : Euclidean m)
    (r : ℝ) {amin amax : ℝ} (hamin : 0 ≤ amin) :
    Convex ℝ (radialSamplingSupport T z₀ ηb r amin amax) := by
  rw [radialSamplingSupport_eq_preimage]
  apply Convex.linear_preimage
  rintro _ ⟨⟨a, t, η⟩, ⟨ha, ht, hη⟩, rfl⟩
    _ ⟨⟨b, s, ξ⟩, ⟨hb, hs, hξ⟩, rfl⟩ α β hα hβ hab
  obtain ⟨θ, hθ, he⟩ := (convex_closedBall ηb r).exists_mem_add_smul_eq hη hξ
    (mul_nonneg hα (hamin.trans ha.1)) (mul_nonneg hβ (hamin.trans hb.1))
  refine ⟨(α * a + β * b, (α • t + β • s, θ)),
    ⟨(convex_Icc amin amax) ha hb hα hβ hab,
      (convex_closedBall (z₀ 0) r) ht hs hα hβ hab, hθ⟩, ?_⟩
  apply Prod.ext
  · rfl
  · simpa only [radialScale, Prod.smul_snd, Prod.snd_add, smul_smul] using he

private def radialProductEquiv (a : ℝ) (ha : a ≠ 0) :
    (ℝ × Euclidean m) ≃L[ℝ] (ℝ × Euclidean m) :=
  ContinuousLinearEquiv.equivOfInverse
    (radialLinearMap (E := Euclidean m) a) (radialLinearMap (E := Euclidean m) a⁻¹)
    (by intro w; ext <;> simp [radialScale, smul_smul, ha])
    (by intro w; ext <;> simp [radialScale, smul_smul, ha])

/-- Every point of the original compact support has a neighborhood inside
the doubled angular/incidence core, retaining the entire SAME radial interval.
This is full support coverage, not a single local inverse box
(`app:ch_waves:setup:oscillatory`). -/
theorem radialSamplingSupport_subset_interior_double (z₀ : Euclidean 3)
    (ηb : Euclidean m) {r amin amax : ℝ} (hr : 0 < r) (hamin : 0 < amin) :
    radialSamplingSupport T z₀ ηb r amin amax ⊆
      interior (radialSamplingSupport T z₀ ηb (2 * r) amin amax) := by
  rw [radialSamplingSupport_eq_preimage, radialSamplingSupport_eq_preimage]
  let c := (canonicalInputIsometry T).toContinuousLinearEquiv.trans
    (adaptedSliceCoordinates T).equiv
  rintro u ⟨⟨a, w⟩, ⟨ha, hw⟩, he⟩
  let R := radialProductEquiv (m := m) a (ne_of_gt (hamin.trans_le ha.1))
  have hopen : IsOpen (c ⁻¹' (R '' dataSet (n := m + 1) z₀ ηb (2 * r))) :=
    (R.toHomeomorph.isOpenMap _ ((isOpen_ball).prod isOpen_ball)).preimage c.continuous
  apply interior_mono (s := c ⁻¹' (R '' dataSet (n := m + 1) z₀ ηb (2 * r))) ?_
  · rw [hopen.interior_eq]
    exact ⟨w, (dataBox_geometry (n := m + 1) z₀ ηb hr).2.2.2 hw, he⟩
  · rintro p ⟨q, hq, hqp⟩
    exact ⟨(a, q), ⟨ha, ball_subset_closedBall hq.1, ball_subset_closedBall hq.2⟩, hqp⟩

/-- The entire compact radial support has a positive buffer inside an open
bounded convex domain whose closure stays in the doubled support. All choices
use only the frozen geometry and prescribed support labels
(`app:ch_osc:setup:osc-normal`). -/
theorem exists_radialSamplingDomain (z₀ : Euclidean 3) (ηb : Euclidean m)
    {r amin amax : ℝ} (hr : 0 < r) (hamin : 0 < amin) :
    ∃ D : Set (Euclidean (m + 1)), IsOpen D ∧ Convex ℝ D ∧
      IsCompact (closure D) ∧
      closure D ⊆ radialSamplingSupport T z₀ ηb (2 * r) amin amax ∧
      ∃ b > (0 : ℝ), cthickening b (radialSamplingSupport T z₀ ηb r amin amax) ⊆ D := by
  let K := radialSamplingSupport T z₀ ηb (2 * r) amin amax
  have hK := radialSamplingSupport_compact T z₀ ηb (2 * r) amin amax
  have hcl : closure (interior K) ⊆ K :=
    closure_minimal interior_subset hK.isClosed
  refine ⟨interior K, isOpen_interior,
    (convex_radialSamplingSupport T z₀ ηb (2 * r) hamin.le).interior,
    hK.of_isClosed_subset isClosed_closure hcl, hcl, ?_⟩
  exact (radialSamplingSupport_compact T z₀ ηb r amin amax).exists_cthickening_subset_open
    isOpen_interior (radialSamplingSupport_subset_interior_double T z₀ ηb hr hamin)

end JanetCartan.Sampling.FullNormalGeometry
