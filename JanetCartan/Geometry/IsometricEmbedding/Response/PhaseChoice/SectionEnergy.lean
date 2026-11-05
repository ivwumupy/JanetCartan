module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.CarrierProperties
public import JanetCartan.Geometry.IsometricEmbedding.Response.Compatible.PhaseComparison

/-!
# The section-energy phase of the selected primary chart

For `app:ch_response:thm:response-compatible-choice`, use the very chart selected
by `exists_constructed_carrier_phases`. The energy chart and its section buffer
are constructed from that family's retained radii. No phase equality, inverse
gap, or choice of a second Hamilton family is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff InnerProductSpace Topology Matrix.Norms.Frobenius

namespace JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
open HamiltonPhase FrozenMenu FrozenPhaseReference

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- The positive section-energy phase is the literal full phase of the primary
chart (`app:ch_response:eq:response-energy-Cauchy`). -/
def sectionEnergyPhase
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (x : Euclidean n) (η : ℝ × Euclidean (n - 1)) : ℝ :=
  phase (T.currentChart Q).coordinates (x, η)

/-- The exact conjugate phase, including nonzero energy
(`app:ch_response:thm:response-compatible-choice`). -/
def conjugateSectionEnergyPhase
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold}) (x : Euclidean n)
    (η : ℝ × Euclidean (n - 1)) : ℝ := -T.sectionEnergyPhase Q x (-η)

/-- A common open energy and transverse-covector buffer, chosen before the
current frame, samples, and accuracy (`app:ch_response:thm:response-compatible-choice`). -/
def sectionEnergyDomain : Set (ℝ × Euclidean (n - 1)) :=
  ball T.data.adapted.baseData.2 (min T.family.radius (3 * T.family.sourceRadius))

/-- The canonical carrier of the actual primary phase
(`app:ch_response:eq:response-exact-phase`). -/
def primaryCanonical (z : Euclidean 3) : ℝ × Euclidean (n - 1) :=
  (0, T.reference.spatialPatch z)

/-- The entire doubled closed primary patch lies in the selected energy buffer
(`app:ch_response:thm:response-compatible-choice`). -/
theorem primaryCanonical_mem {z : Euclidean 3}
    (hz : z ∈ parameterCube (2 * P.radius)) :
    T.primaryCanonical z ∈ T.sectionEnergyDomain := T.patch_buffer z hz

/-- Both physical and canonical buffers lie in the exact current target
(`app:ch_response:thm:response-compatible-choice`). -/
theorem sectionEnergyDomain_subset_target (Q : _) {x : Euclidean n}
    (hx : x ∈ ball 0 T.physicalRadius) {η : ℝ × Euclidean (n - 1)}
    (hη : η ∈ T.sectionEnergyDomain) : (x, η) ∈ (T.currentChart Q).target := by
  change dist (x, η) (T.data.adapted.embedding T.data.adapted.baseData.1,
    T.data.adapted.baseData.2) < T.family.radius
  rw [Prod.dist_eq, max_lt_iff]
  refine ⟨?_, hη.trans_le (min_le_left _ _)⟩
  have hp := T.physicalRadius_pos
  have hm := min_le_left T.family.radius (3 * T.family.sourceRadius)
  have hr : T.physicalRadius < T.family.radius := by
    dsimp [physicalRadius] at hp ⊢
    linarith
  simpa only [AdaptedSection.baseData, map_zero] using hx.trans hr

/-- Every energy in the buffer has its actual time-zero section point in the
selected source. This strengthens the producer's zero-energy source inclusion
(`app:ch_response:eq:response-energy-Cauchy`). -/
theorem sectionEnergy_source (Q : _) {u : Euclidean (n - 1)}
    (hu : T.reference.sectionEmbedding u ∈ ball 0 T.physicalRadius)
    {η : ℝ × Euclidean (n - 1)} (hη : η ∈ T.sectionEnergyDomain) :
    (0, (u, η)) ∈ (T.currentChart Q).source := by
  have hlt : T.physicalRadius < 3 * T.family.sourceRadius := by
    have hh := min_le_right T.family.radius (3 * T.family.sourceRadius)
    have hp := T.physicalRadius_pos
    dsimp [physicalRadius] at hp ⊢
    linarith
  have hu' : ‖u‖ < T.physicalRadius := by
    simpa only [reference, mem_ball, dist_zero_right, LinearIsometry.norm_map] using hu
  have hb : (0, (u, η)) ∈ ball ((0 : ℝ), T.data.adapted.baseData)
      (3 * T.family.sourceRadius) := by
    rw [mem_ball, Prod.dist_eq, max_lt_iff, dist_self, Prod.dist_eq, max_lt_iff]
    exact ⟨by linarith [T.family.sourceRadius_pos],
      by simpa [AdaptedSection.baseData] using hu'.trans hlt,
      hη.trans_le (min_le_right _ _)⟩
  have hadm := T.family.source_admissible Q hb
  rw [currentChart, restrictChart_source_eq _ _ _ (T.family.source_eq Q)]
  refine ⟨hb, ?_⟩
  change ((T.family.flow Q).position (0, (u, η)), η) ∈ T.target
  rw [(T.family.flow Q).initial_position _ hadm.2, T.family.section_eq]
  exact T.sectionEnergyDomain_subset_target Q hu hη

/-- Exact Cauchy data at every energy in the fixed buffer, with the primary
section sign (`app:ch_response:eq:response-energy-Cauchy`). -/
theorem sectionEnergyPhase_section (Q : _) {u : Euclidean (n - 1)}
    (hu : T.reference.sectionEmbedding u ∈ ball 0 T.physicalRadius)
    {η : ℝ × Euclidean (n - 1)} (hη : η ∈ T.sectionEnergyDomain) :
    T.sectionEnergyPhase Q (T.reference.sectionEmbedding u) η = ⟪u, η.2⟫_ℝ := by
  have h := (T.currentChart Q).initial_value (T.sectionEnergy_source Q hu hη)
  rw [T.family.section_eq Q] at h
  exact h

/-- Full-energy eikonal for the literal normalized current determinant
(`app:ch_response:eq:response-energy-root`). -/
theorem sectionEnergyPhase_eikonal (Q : _) {x : Euclidean n}
    (hx : x ∈ ball 0 T.physicalRadius) {η : ℝ × Euclidean (n - 1)}
    (hη : η ∈ T.sectionEnergyDomain) :
    normalizedSymbol Q.1 (x, gradient (fun y ↦ T.sectionEnergyPhase Q y η) x) = η.1 :=
  (T.currentChart Q).eikonal (T.sectionEnergyDomain_subset_target Q hx hη)

/-- The chosen primary phase is exactly the zero-energy restriction on its
entire parameter domain (`app:ch_response:eq:response-exact-phase`). -/
theorem sectionEnergyPhase_primary (Q : _) (x : Euclidean n) (z : Euclidean 3) :
    T.sectionEnergyPhase Q x (T.primaryCanonical z) = T.carrier Q x z := rfl

/-- Exact phase equality retains the actual physical gradient
(`app:ch_response:eq:response-exact-phase`). -/
theorem sectionEnergyPhase_primary_gradient (Q : _) (x : Euclidean n) (z : Euclidean 3) :
    gradient (fun y ↦ T.sectionEnergyPhase Q y (T.primaryCanonical z)) x =
      T.carrierGradient Q x z := rfl

/-- The negative phase uses the same primary carrier with the opposite sign
(`app:ch_response:thm:response-compatible-choice`). -/
theorem conjugateSectionEnergyPhase_primary (Q : _) (x : Euclidean n) (z : Euclidean 3) :
    T.conjugateSectionEnergyPhase Q x (-T.primaryCanonical z) = -T.carrier Q x z := by
  simp only [conjugateSectionEnergyPhase, neg_neg, sectionEnergyPhase_primary]

/-- The physical gradient of the conjugate chart has exactly the opposite
sign at the reflected canonical covector
(`app:ch_response:thm:response-compatible-choice`). -/
theorem conjugateSectionEnergyPhase_gradient (Q : _) (x : Euclidean n)
    (η : ℝ × Euclidean (n - 1)) :
    gradient (fun y ↦ T.conjugateSectionEnergyPhase Q y η) x =
      -gradient (fun y ↦ T.sectionEnergyPhase Q y (-η)) x := by
  change gradient (-(fun y ↦ T.sectionEnergyPhase Q y (-η))) x = _
  simp only [gradient, fderiv_neg, map_neg]

/-- Exact gradient compatibility for the negative primary sign
(`app:ch_response:eq:response-exact-phase`). -/
theorem conjugateSectionEnergyPhase_primary_gradient (Q : _)
    (x : Euclidean n) (z : Euclidean 3) :
    gradient (fun y ↦ T.conjugateSectionEnergyPhase Q y (-T.primaryCanonical z)) x =
      -T.carrierGradient Q x z := by
  rw [T.conjugateSectionEnergyPhase_gradient, neg_neg,
    T.sectionEnergyPhase_primary_gradient]

/-- The reflected phase retains the same positive section sign at every
energy in its reflected buffer (`app:ch_response:eq:response-energy-Cauchy`). -/
theorem conjugateSectionEnergyPhase_section (Q : _) {u : Euclidean (n - 1)}
    (hu : T.reference.sectionEmbedding u ∈ ball 0 T.physicalRadius)
    {η : ℝ × Euclidean (n - 1)} (hη : -η ∈ T.sectionEnergyDomain) :
    T.conjugateSectionEnergyPhase Q (T.reference.sectionEmbedding u) η = ⟪u, η.2⟫_ℝ := by
  rw [conjugateSectionEnergyPhase, T.sectionEnergyPhase_section Q hu hη]
  simp

/-- Joint smoothness of the actual positive phase on the full energy buffer
(`app:ch_response:thm:response-compatible-choice`). -/
theorem sectionEnergyPhase_smooth (Q : _) :
    ContDiffOn ℝ ∞ (fun q : Euclidean n × (ℝ × Euclidean (n - 1)) ↦
      T.sectionEnergyPhase Q q.1 q.2)
      (ball 0 T.physicalRadius ×ˢ T.sectionEnergyDomain) := by
  exact (T.family.phase_smooth Q).mono (fun q hq ↦
    (ball_subset_ball (by linarith [T.family.radius_pos] :
      T.family.radius ≤ 2 * T.family.radius))
        (T.sectionEnergyDomain_subset_target Q hq.1 hq.2))

/-- The conjugate phase is jointly smooth on the reflected energy buffer
(`app:ch_response:thm:response-compatible-choice`). -/
theorem conjugateSectionEnergyPhase_smooth (Q : _) :
    ContDiffOn ℝ ∞ (fun q : Euclidean n × (ℝ × Euclidean (n - 1)) ↦
      T.conjugateSectionEnergyPhase Q q.1 q.2)
      (ball 0 T.physicalRadius ×ˢ (Neg.neg ⁻¹' T.sectionEnergyDomain)) :=
  ((T.sectionEnergyPhase_smooth Q).comp
    (contDiffOn_fst.prodMk contDiffOn_snd.neg) (fun _ h ↦ h)).neg

/-- The selected energy domain excludes zero. At zero canonical covector the
explicit phase vanishes identically, contradicting nonzero Hamilton momentum.
Thus pointedness is a conclusion of the constructed chart
(`app:ch_response:thm:response-compatible-choice`). -/
theorem zero_notMem_sectionEnergyDomain :
    (0 : ℝ × Euclidean (n - 1)) ∉ T.sectionEnergyDomain := by
  intro hzero
  have ht : ((0 : Euclidean n), (0 : ℝ × Euclidean (n - 1))) ∈
      T.reference.chart.target := by
    change dist ((0 : Euclidean n), (0 : ℝ × Euclidean (n - 1)))
      (T.data.adapted.embedding T.data.adapted.baseData.1,
        T.data.adapted.baseData.2) < T.family.radius
    rw [Prod.dist_eq, max_lt_iff]
    exact ⟨by simpa [AdaptedSection.baseData] using T.family.radius_pos,
      hzero.trans_le (min_le_left _ _)⟩
  have hg := carrierPhase_gradient_mem_domain T.reference.chart
    (fun _ : Unit ↦ (0 : Euclidean (n - 1))) (x := 0) (z := ()) ht
  have he : (fun y : Euclidean n ↦
      carrierPhase T.reference.chart (fun _ : Unit ↦ (0 : Euclidean (n - 1))) y ()) =
      fun _ ↦ (0 : ℝ) := by
    funext y
    simp [carrierPhase, phase]
  rw [he] at hg
  simp [reference, frozenSymbol, normalizedHomogeneousSymbol,
    normalizedSymbolDomain] at hg

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
