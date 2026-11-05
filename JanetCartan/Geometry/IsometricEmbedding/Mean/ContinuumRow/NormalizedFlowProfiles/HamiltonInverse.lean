module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedFlowProfiles.CarrierInputs
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseEstimates.FiberBounds

/-!
# Jets of the literal retained Hamilton inverse

The canonical derivatives of the full phase recover both inverse time and
initial position. This supplies inverse-coordinate bounds for the existing
quantitative family, without choosing another inverse or assuming its bounds.
The actual normalized source frame then makes these estimates uniform in the
source scale (`app:lem:common-hamilton-phase`,
`app:ch_background:prop:bg-normalized`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumRow.NormalizedFlowProfiles
open HamiltonPhase ActualCarriers FrozenMenu CurrentFullPhase
open FullPhaseCharts.InverseEstimates ProjectedStressFrame

private def inverseCoordinateExtraction {n : ℕ} :
    ((Euclidean n × (ℝ × Euclidean (n - 1))) →L[ℝ] ℝ) →L[ℝ]
      ℝ × Euclidean (n - 1) :=
  (ContinuousLinearMap.apply ℝ ℝ (0, 1, 0)).prod
    ((InnerProductSpace.toDual ℝ (Euclidean (n - 1))).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((ContinuousLinearMap.compL ℝ (Euclidean (n - 1))
        (Euclidean n × (ℝ × Euclidean (n - 1))) ℝ).flip
          ((0 : Euclidean (n - 1) →L[ℝ] Euclidean n).prod
            ((0 : Euclidean (n - 1) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ _)))))

private theorem coordinates_eq_extracted {n : ℕ}
    {H : HomogeneousSymbol (Euclidean n)} {Φ : HamiltonFlow H (Euclidean (n - 1))}
    (C : ProjectionChart Φ) {q : Euclidean n × (ℝ × Euclidean (n - 1))}
    (hq : q ∈ C.target) :
    C.coordinates q = inverseCoordinateExtraction (fderiv ℝ (phase C.coordinates) q) := by
  rw [(C.hasFDerivAt_phase hq).fderiv]
  apply Prod.ext
  · simp [inverseCoordinateExtraction, phaseDifferential_apply]
  · apply (InnerProductSpace.toDual ℝ (Euclidean (n - 1))).injective
    ext v
    change ⟪(C.coordinates q).2, v⟫_ℝ =
      (InnerProductSpace.toDual ℝ (Euclidean (n - 1)))
        ((InnerProductSpace.toDual ℝ (Euclidean (n - 1))).symm _) v
    rw [LinearIsometryEquiv.apply_symm_apply]
    simp [phaseDifferential_apply]

/-- All orders of the SAME inverse Hamilton chart follow from the full phase
bound with one more derivative. The common target is the original closed
target ball, with the original doubled smooth buffer; no new inverse or
uniform inverse estimate is an input (`app:lem:common-hamilton-phase`). -/
theorem exists_current_coordinates_frame_bound {n : ℕ} {P : Patch n}
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU) :
    ∃ A : ℕ → ℝ, (∀ m, 0 < A m) ∧ ∀ Q m,
      cNorm (closedBall (T.data.adapted.embedding T.data.adapted.baseData.1,
        T.data.adapted.baseData.2) T.family.radius) m (T.currentChart Q).coordinates ≤
        A m * (1 + cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius)
          (m + 2) Q.1) := by
  let L := inverseCoordinateExtraction (n := n)
  refine ⟨fun m ↦ (1 + ‖L‖) * T.family.coefficient (m + 1),
    fun m ↦ mul_pos (by positivity) (T.family.coefficient_pos _), ?_⟩
  intro Q m
  let K := closedBall (T.data.adapted.embedding T.data.adapted.baseData.1,
    T.data.adapted.baseData.2) T.family.radius
  let W := ball (T.data.adapted.embedding T.data.adapted.baseData.1,
    T.data.adapted.baseData.2) (2 * T.family.radius)
  let S := phase (T.currentChart Q).coordinates
  have hKW : K ⊆ W := closedBall_subset_ball (by linarith [T.family.radius_pos])
  have hS : ContDiffOn ℝ ∞ S W := T.family.phase_smooth Q
  have hreg : ∀ q ∈ K, ContDiffAt ℝ m (fderiv ℝ S) q := fun q hq ↦
    ((hS.contDiffAt (isOpen_ball.mem_nhds (hKW hq))).fderiv_right
      (m := ∞) (by simp)).of_le (by simp)
  have he : cNorm K m (T.currentChart Q).coordinates = cNorm K m (L ∘ fderiv ℝ S) := by
    apply GeometricProfile.cNorm_eq_of_eventuallyEq
    intro q hq
    filter_upwards [isOpen_ball.mem_nhds (hKW hq)] with z hz
    exact coordinates_eq_extracted (T.family.chart Q) (T.family.target_contains Q hz)
  change cNorm K m (T.currentChart Q).coordinates ≤ _
  rw [he]
  calc
    _ ≤ ‖L‖ * cNorm K m (fderiv ℝ S) :=
      cNorm_postLinear_le_on (isCompact_closedBall _ _) m L hreg
    _ ≤ (1 + ‖L‖) * cNorm K (m + 1) S :=
      mul_le_mul (by linarith) (GeometricProfile.cNorm_fderiv_le K m S)
        (cNorm_nonneg ..) (by positivity)
    _ ≤ (1 + ‖L‖) * (T.family.coefficient (m + 1) *
        (1 + cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius)
          (m + 2) Q.1)) := by
      simpa only [Nat.add_assoc, Nat.reduceAdd] using
        mul_le_mul_of_nonneg_left (T.current_phase_bound Q (m + 1))
          (by positivity : 0 ≤ 1 + ‖L‖)
    _ = _ := by ring

/-- Uniform phase and inverse-chart jets for the actual normalized source
family, on the SAME retained common target. Constants precede the scale and
the admitted frame witness. Quantifying over every witness with the literal
source frame allows intersection with a separately chosen null-flow scale
interval without identifying independent existential choices
(`app:ch_background:prop:bg-normalized`, `app:lem:common-hamilton-phase`). -/
theorem exists_source_hamilton_inverse_profiles {n : ℕ} (H : FlatReference n)
    {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) (hbounded : Bornology.IsBounded U)
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U) :
    ∃ σ₀ : ℝ, 0 < σ₀ ∧ σ₀ ≤ 1 ∧ ∃ A : ℕ → ℝ, (∀ m, 0 < A m) ∧
      ∀ σ ∈ Ioc (0 : ℝ) σ₀, ∀ Q,
        Q.1 = projectedStress (sourceDilation H.map σ) → ∀ m,
        cNorm (closedBall (T.data.adapted.embedding T.data.adapted.baseData.1,
          T.data.adapted.baseData.2) T.family.radius) m
          (phase (T.currentChart Q).coordinates) +
        cNorm (closedBall (T.data.adapted.embedding T.data.adapted.baseData.1,
          T.data.adapted.baseData.2) T.family.radius) m (T.currentChart Q).coordinates ≤ A m := by
  classical
  obtain ⟨σ₀, hσ₀, hσ₁, hg, hb⟩ := exists_source_frame_profiles H hbounded
  choose B hB hbound using hb
  obtain ⟨D, hD, hd⟩ := exists_current_coordinates_frame_bound T
  refine ⟨σ₀, hσ₀, hσ₁,
    fun m ↦ T.family.coefficient m * (1 + B (m + 1)) + D m * (1 + B (m + 2)),
    fun m ↦ add_pos (mul_pos (T.family.coefficient_pos _) (by have := hB (m + 1); positivity))
      (mul_pos (hD m) (by have := hB (m + 2); positivity)), ?_⟩
  intro σ hσ Q heq m
  have hf (k : ℕ) : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius)
      k Q.1 ≤ B k := by
    rw [heq]
    exact (cNorm_mono_set_of_contDiffAt (hphysical.trans subset_closure)
      hbounded.isCompact_closure
      (fun x hx ↦ ((hg σ hσ).2.2 x hx).of_le (by simp))).trans (hbound k σ hσ).2
  exact add_le_add
    ((T.current_phase_bound Q m).trans (mul_le_mul_of_nonneg_left
      (add_le_add (le_refl 1) (hf (m + 1))) (T.family.coefficient_pos _).le))
    ((hd Q m).trans (mul_le_mul_of_nonneg_left
      (add_le_add (le_refl 1) (hf (m + 2))) (hD m).le))

end JanetCartan.ContinuumRow.NormalizedFlowProfiles
