module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.FullNormalGeometry.PhaseExtension
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.CanonicalInputGeometry
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseEstimates.QuotientJets.Integral

/-!
# Fixed substitutions for the full sampling phase

The incidence variable remains among the differentiated inputs. The compact
set of spectator/physical/input triples is chosen before the immersion. These
are the geometric inputs to the phase part of `UniformNormalData.input_jets`
in `app:ch_waves:setup:oscillatory`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.Sampling.FullNormalGeometry.PhaseJets
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualPhase
open ContinuumRow.CanonicalConic ContinuumRow.CanonicalCarrier RawKernel
open MeanNormalBound.CanonicalGap

variable {m : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- The SAME literal sampling input, including incidence, in the retained
adapted chart (`app:ch_seed:prop:seed-phase-charts`). -/
def inputCoordinates : Euclidean (m + 1) →L[ℝ] (ℝ × Euclidean (m + 1 - 1)) :=
  (adaptedSliceCoordinates T).equiv.toContinuousLinearMap.comp
    (canonicalInputIsometry T).toContinuousLinearEquiv.toContinuousLinearMap

/-- The substitution agrees with the published measurable input map
(`app:ch_waves:setup:oscillatory`). -/
theorem inputCoordinates_apply (u : Euclidean (m + 1)) :
    inputCoordinates T u =
      (adaptedSliceCoordinates T).equiv (canonicalInputCoordinates T u) := rfl

/-- All spectators are retained in the open extension domain. A compact
subset of this set supplies the geometric hypothesis of the jet endpoint
(`app:ch_seed:eq:seed-quotient-integral`). -/
def tripleDomain (M : ℝ) : Set (Euclidean 2 × (Euclidean (m + 1) × Euclidean (m + 1))) :=
  {q | q.2 ∈ fullPhaseExtensionDomain T q.1 M}

/-- Openness before the phase or immersion is chosen
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem isOpen_tripleDomain (M : ℝ) : IsOpen (tripleDomain T M) := by
  change IsOpen ((fun q : Euclidean 2 × (Euclidean (m + 1) × Euclidean (m + 1)) ↦
    (q.2.1, (carrierParameters (q.1, (inputCoordinates T q.2.2).1),
      (inputCoordinates T q.2.2).2))) ⁻¹'
        (ball 0 T.family.radius ×ˢ
          (parameterInterior (3 * P.radius / 2) ×ˢ ball (0 : Euclidean (m + 1 - 1)) M)))
  exact (isOpen_ball.prod ((isOpen_parameterInterior _).prod isOpen_ball)).preimage
    (by fun_prop)

/-- The literal shifted covector, with epsilon and incidence both free
(`app:ch_seed:eq:seed-quotient-integral`). -/
def shift (s : ℝ)
    (q : ℝ × (Euclidean 2 × (Euclidean (m + 1) × Euclidean (m + 1)))) :
    WithLp 2 (ℝ × Euclidean (m + 1 - 1)) × Euclidean (m + 1 - 1) :=
  (physicalCoordinates T q.2.2.1,
    T.reference.spatialPatch (carrierParameters (q.2.1, (inputCoordinates T q.2.2.2).1)) +
      (s * q.1) • (inputCoordinates T q.2.2.2).2)

/-- The fixed direction in the quotient integrand
(`app:ch_seed:eq:seed-quotient-integral`). -/
def direction
    (q : ℝ × (Euclidean 2 × (Euclidean (m + 1) × Euclidean (m + 1)))) : Euclidean (m + 1 - 1) :=
  (inputCoordinates T q.2.2.2).2

/-- The full literal phase, jointly in epsilon and every original coordinate.
This is the function whose restrictions give `UniformNormalData.input_jets`
(`app:ch_waves:setup:oscillatory`). -/
def literalJoint
    (Q : {Q : Euclidean (m + 1) → Fin (m + 1) → MetricTensor (m + 1) //
      ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress (m + 1)) < T.family.threshold})
    (q : ℝ × (Euclidean 2 × (Euclidean (m + 1) × Euclidean (m + 1)))) : ℝ :=
  normalizedFullPhase T Q q.2.1 q.1 q.2.2.1 (canonicalInputCoordinates T q.2.2.2)

/-- The published actual extension is smooth with the spectators also free,
on precisely the same geometric domain (`app:ch_seed:eq:seed-quotient-integral`). -/
theorem exists_literalJoint_smooth {c C : ℝ} (hP : P.IsValid c C)
    {M : ℝ} (hM : 0 < M) :
    ∃ e > (0 : ℝ), ∀ Q,
      ContDiffOn ℝ ∞ (literalJoint T Q) (Ioo (-e) e ×ˢ tripleDomain T M) := by
  obtain ⟨e, he, hmod⟩ := exists_smooth_modulation T hP hM
  refine ⟨e, he, fun Q ↦ ?_⟩
  apply (hmod Q).1.comp
    (f := fun q : ℝ × (Euclidean 2 × (Euclidean (m + 1) × Euclidean (m + 1))) ↦
      (((carrierParameters (q.2.1, (inputCoordinates T q.2.2.2).1),
        (inputCoordinates T q.2.2.2).2), q.1), physicalCoordinates T q.2.2.1))
    (by fun_prop)
  intro q hq
  refine ⟨⟨hq.2.2, hq.1⟩, ?_⟩
  simpa only [mem_ball, dist_zero_right, LinearIsometryEquiv.norm_map] using hq.2.1

/-- Smoothness of the actual substitution on the explicit full-input domain.
No phase budget is an input (`app:ch_seed:eq:seed-phase-tame`). -/
theorem shift_smooth {c C : ℝ} (hP : P.IsValid c C) (M : ℝ) :
    ContDiffOn ℝ ∞ (fun w : ℝ ×
      (ℝ × (Euclidean 2 × (Euclidean (m + 1) × Euclidean (m + 1)))) ↦
      shift T w.1 w.2) (univ ×ˢ (univ ×ˢ tripleDomain T M)) := by
  have hz : ContDiffOn ℝ ∞
      (fun w : ℝ × (ℝ × (Euclidean 2 × (Euclidean (m + 1) × Euclidean (m + 1)))) ↦
        T.reference.spatialPatch
          (carrierParameters (w.2.2.1, (inputCoordinates T w.2.2.2.2).1)))
      (univ ×ˢ (univ ×ˢ tripleDomain T M)) := by
    apply (T.reference.spatialPatch_smooth hP).comp (by fun_prop)
    intro w hw
    exact (middle_parameter_buffers hP).2 (fun i ↦ (hw.2.2.2.1 i).le)
  unfold shift
  exact ContDiffOn.prodMk (by fun_prop) (hz.add (by fun_prop))

/-- A two-sided epsilon cap keeps the actual shifts in the primitive phase
ball, uniformly in spectators and the full input
(`app:ch_seed:eq:seed-quotient-integral`). -/
theorem exists_shift_cap {c C : ℝ} (hP : P.IsValid c C) {M : ℝ} (hM : 0 < M) :
    ∃ e > (0 : ℝ), ∀ s ∈ Ioo (-1 : ℝ) 2,
      MapsTo (shift T s) (Ioo (-e) e ×ˢ tripleDomain T M)
        (ball (0, covectorCenter T) T.family.radius) := by
  obtain ⟨e, he, hb⟩ := exists_covector_shift_buffer T hP hM
  refine ⟨e, he, ?_⟩
  intro s hs q hq
  rw [mem_ball, Prod.dist_eq, max_lt_iff]
  refine ⟨?_, ?_⟩
  · simpa only [shift, mem_ball, dist_zero_right, LinearIsometryEquiv.norm_map] using hq.2.1
  · exact hb _ (fun i ↦ (hq.2.2.1 i).le) _
      (by exact (by simpa only [mem_ball, dist_zero_right, inputCoordinates_apply] using hq.2.2.2 :
        ‖(inputCoordinates T q.2.2.2).2‖ < M).le)
      _ (abs_lt.mpr hq.1).le s hs

/-- Compactness gives all fixed substitution jets before the immersion. The
incidence derivative is included; this is not a fixed-carrier slice bound
(`app:ch_waves:setup:oscillatory`). -/
theorem exists_shift_jet_bounds {c C : ℝ} (hP : P.IsValid c C) (M e : ℝ)
    {H : Set (Euclidean 2 × (Euclidean (m + 1) × Euclidean (m + 1)))}
    (hH : IsCompact H) (hHM : H ⊆ tripleDomain T M) :
    ∃ b : ℕ → ℝ, (∀ j, 0 ≤ b j) ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ q ∈ Icc (-e) e ×ˢ H, ∀ j,
        ‖iteratedFDeriv ℝ j (shift T s) q‖ ≤ b j := by
  have hb (j : ℕ) : ∃ b : ℝ, ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ q ∈ Icc (-e) e ×ˢ H, ‖iteratedFDeriv ℝ j (shift T s) q‖ ≤ b := by
    have hc : ContinuousOn (fun w : ℝ ×
        (ℝ × (Euclidean 2 × (Euclidean (m + 1) × Euclidean (m + 1)))) ↦
        iteratedFDeriv ℝ j (shift T w.1) w.2)
        (Icc (0 : ℝ) 1 ×ˢ (Icc (-e) e ×ˢ H)) := by
      intro w hw
      exact (NormalComparison.contDiffAt_segmentSpatialJet
        ((shift_smooth T hP M).contDiffAt
          ((isOpen_univ.prod (isOpen_univ.prod (isOpen_tripleDomain T M))).mem_nhds
            ⟨mem_univ _, mem_univ _, hHM hw.2.2⟩)) j).continuousAt.continuousWithinAt
    obtain ⟨b, hb⟩ := (isCompact_Icc.prod (isCompact_Icc.prod hH)).exists_bound_of_continuousOn hc
    exact ⟨b, fun s hs q hq ↦ hb (s, q) ⟨hs, hq⟩⟩
  choose b hb using hb
  exact ⟨fun j ↦ max 0 (b j), fun j ↦ le_max_left _ _,
    fun s hs q hq j ↦ (hb j s hs q hq).trans (le_max_right _ _)⟩

end JanetCartan.Sampling.FullNormalGeometry.PhaseJets
