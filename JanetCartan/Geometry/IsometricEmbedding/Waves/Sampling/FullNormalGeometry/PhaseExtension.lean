module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.FullNormalGeometry.Support

/-!
# Open extension of the literal full sampling phase

The actual modulation constructor gives a two-sided epsilon neighborhood for
the SAME retained current phase. Its pullback below keeps the original
incidence, covector and spectator coordinates. No inverse or phase-jet bound
is assumed. The consumer is `UniformNormalData.phase_smooth` in the full
sampling construction (`app:ch_waves:setup:oscillatory`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff

namespace JanetCartan.Sampling.FullNormalGeometry
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ActualPhase ActualComparison ContinuumRow.CanonicalConic ContinuumRow.CanonicalCarrier
open MeanNormalBound.CanonicalGap RawKernel
open ContinuumNormalReduction.ConicChart

variable {m : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- The original coefficient and phase extension domain, expressed in the
literal sampling coordinates. There is no restriction to an inverse image
or a selected local input box (`app:ch_seed:eq:seed-quotient-integral`). -/
def fullPhaseExtensionDomain (v : Euclidean 2) (M : ℝ) :
    Set (Euclidean (m + 1) × Euclidean (m + 1)) :=
  ball 0 T.family.radius ×ˢ
    ((fun u ↦
      (carrierParameters (v, ((adaptedSliceCoordinates T).equiv
        (canonicalInputCoordinates T u)).1),
        ((adaptedSliceCoordinates T).equiv (canonicalInputCoordinates T u)).2)) ⁻¹'
      (parameterInterior (3 * P.radius / 2) ×ˢ ball (0 : Euclidean m) M))

/-- The extension is open in both original spatial variables, as required
by `UniformNormalData.isOpen_extensionDomain`
(`app:ch_osc:setup:osc-normal`). -/
theorem isOpen_fullPhaseExtensionDomain (v : Euclidean 2) (M : ℝ) :
    IsOpen (fullPhaseExtensionDomain T v M) := by
  apply isOpen_ball.prod
  apply ((isOpen_parameterInterior _).prod isOpen_ball).preimage
  change Continuous (fun u ↦
    (carrierParameters (v, ((adaptedSliceCoordinates T).equiv
      (canonicalInputIsometry T u)).1),
      ((adaptedSliceCoordinates T).equiv (canonicalInputIsometry T u)).2))
  fun_prop

/-- Actual joint phase smoothness through zero and past both endpoints of
the parameter interval. The epsilon radius is chosen before the current frame
and all spectators. Its producer is `ActualPhase.exists_smooth_modulation`
on the retained `T.currentChart`, not an independently chosen phase
(`app:ch_seed:eq:seed-quotient-integral`). -/
theorem exists_literalFullPhase_smooth {c C : ℝ} (hP : P.IsValid c C)
    {M : ℝ} (hM : 0 < M) :
    ∃ e > (0 : ℝ), ∀ Q, ∀ v : Euclidean 2,
      ContDiffOn ℝ ∞ (fun q : ℝ × (Euclidean (m + 1) × Euclidean (m + 1)) ↦
        normalizedFullPhase T Q v q.1 q.2.1 (canonicalInputCoordinates T q.2.2))
        (Ioo (-e) e ×ˢ fullPhaseExtensionDomain T v M) := by
  obtain ⟨e, he, hmod⟩ := exists_smooth_modulation T hP hM
  refine ⟨e, he, ?_⟩
  intro Q v
  let idx := fun q : ℝ × (Euclidean (m + 1) × Euclidean (m + 1)) ↦
    (((carrierParameters (v, ((adaptedSliceCoordinates T).equiv
      (canonicalInputIsometry T q.2.2)).1),
      ((adaptedSliceCoordinates T).equiv (canonicalInputIsometry T q.2.2)).2), q.1),
      physicalCoordinates T q.2.1)
  have hi : ContDiff ℝ ∞ idx := by
    dsimp only [idx]
    fun_prop
  apply (hmod Q).1.comp hi.contDiffOn
  intro q hq
  refine ⟨⟨hq.2.2, hq.1⟩, ?_⟩
  simpa only [idx, mem_ball, dist_zero_right, LinearIsometryEquiv.norm_map] using hq.2.1

/-- The entire radially enlarged core remains in the original coefficient
extension whenever its literal covector bound fits. This condition involves
only fixed support radii, not an analytic phase budget
(`app:ch_waves:setup:oscillatory`). -/
theorem radialSamplingSupport_subset_fullPhaseExtensionDomain
    {z₀ : Euclidean 3} {ηb : Euclidean m} {r amin amax M : ℝ}
    (hamin : 0 ≤ amin) (hM : amax * (‖ηb‖ + r) < M)
    {v : Euclidean 2}
    (hcarrier : ∀ t ∈ closedBall (z₀ 0) r,
      carrierParameters (v, t) ∈ parameterInterior (3 * P.radius / 2)) :
    ball 0 T.family.radius ×ˢ radialSamplingSupport T z₀ ηb r amin amax ⊆
      fullPhaseExtensionDomain T v M := by
  rintro ⟨x, u⟩ ⟨hx, hu⟩
  obtain ⟨⟨a, w⟩, ⟨ha, hw⟩, he⟩ := hu
  refine ⟨hx, ?_⟩
  change (carrierParameters (v, ((adaptedSliceCoordinates T).equiv
    (canonicalInputCoordinates T u)).1),
    ((adaptedSliceCoordinates T).equiv (canonicalInputCoordinates T u)).2) ∈
      parameterInterior (3 * P.radius / 2) ×ˢ ball (0 : Euclidean m) M
  rw [← he]
  simp only [radialInput, ContinuousLinearEquiv.apply_symm_apply, radialScale,
    mem_prod, mem_ball, dist_zero_right]
  have hw' : (adaptedSliceCoordinates T).equiv w ∈ dataBox (n := m + 1) z₀ ηb r := hw
  refine ⟨hcarrier _ hw'.1, ?_⟩
  have hnorm : ‖((adaptedSliceCoordinates T).equiv w).2‖ ≤ ‖ηb‖ + r := by
    have hh := norm_le_insert' ((adaptedSliceCoordinates T).equiv w).2 ηb
    have hd := mem_closedBall_iff_norm.mp hw'.2
    linarith
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hamin.trans ha.1)]
  exact (mul_le_mul ha.2 hnorm (norm_nonneg _) (hamin.trans (ha.1.trans ha.2))).trans_lt hM

end JanetCartan.Sampling.FullNormalGeometry
