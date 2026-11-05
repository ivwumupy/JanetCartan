module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.SmoothBufferedChart
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.MixedHessian
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.SymbolRegularity

/-!
# Buffered local homogeneous Hamilton phases

Assemble the actual transverse flow, buffered inverse projection, and mixed
phase derivative for one symbol (`app:lem:common-hamilton-phase`). The source
has a quantitative buffer and the target has compact closure. Uniformity for
a symbol neighborhood and estimates at arbitrary derivative order are separate.
-/

@[expose] public noncomputable section
open Set Filter Metric
open scoped Topology ContDiff InnerProductSpace
namespace JanetCartan.HamiltonPhase
variable {E U : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ U]

/-- A transverse smooth Hamilton flow has a smooth inverse chart on a buffered
physical/canonical target. The entire preimage inside the outer source ball
lies in the middle ball (`app:lem:common-hamilton-phase`). -/
theorem HamiltonFlow.exists_smoothBufferedProjection
    {H : HomogeneousSymbol E} (Φ : HamiltonFlow H U)
    (j : U →ₗᵢ[ℝ] E) (hj : Φ.sectionMap = j.toContinuousLinearMap)
    (ν : E) (horth : ∀ u : U, ⟪ν, j u⟫_ℝ = 0)
    (hspan : ∀ x : E, ⟪ν, x⟫_ℝ = 0 → ∃ u : U, j u = x)
    {s₀ : InitialData U} (hs₀ : s₀ ∈ Φ.parameters)
    (hv : ⟪ν, H.hp (j s₀.1, Φ.momentum ((0 : ℝ), s₀))⟫_ℝ ≠ 0)
    (hc : ContDiffOn ℝ ∞ Φ.position (Φ.time ×ˢ Φ.parameters)) :
    ∃ (C : ProjectionChart Φ) (r δ : ℝ), 0 < r ∧ 0 < δ ∧
      (j s₀.1, s₀.2) ∈ C.target ∧ (0, s₀) ∈ C.source ∧
      IsCompact (closure C.target) ∧
      C.source = ball ((0 : ℝ), s₀) (3 * r) ∩ Φ.augmentedProjection ⁻¹' C.target ∧
      C.source ⊆ ball ((0 : ℝ), s₀) (2 * r) ∧
      closure (ball ((0 : ℝ), s₀) (3 * r)) ⊆ Φ.time ×ˢ Φ.parameters ∧
      cthickening δ (Φ.augmentedProjection '' closure (ball ((0 : ℝ), s₀) r)) ⊆ C.target ∧
      cthickening δ (closure C.target) ⊆ Φ.augmentedProjection '' ball ((0 : ℝ), s₀) (2 * r) ∧
      Φ.augmentedProjection ⁻¹' cthickening δ (closure C.target) ∩
        ball ((0 : ℝ), s₀) (3 * r) ⊆ ball ((0 : ℝ), s₀) (2 * r) ∧
      ContDiffOn ℝ ∞ C.coordinates C.target := by
  have hc₀ : ContDiffAt ℝ 1 Φ.position ((0 : ℝ), s₀) :=
    (hc.contDiffAt ((Φ.isOpen_time.prod Φ.isOpen_parameters).mem_nhds
      ⟨Φ.zero_mem_time, hs₀⟩)).of_le (by simp)
  obtain ⟨A, _, r, hr, _, _, _, _, _, hadm, hconv, hgap,
    ε, hε, δ, hδ, V, hV, hVc, hzV, hstable⟩ :=
    Φ.exists_bufferedProjection_domains j hj ν horth hspan hs₀ hv hc₀
  have hDadm : ball ((0 : ℝ), s₀) (3 * r) ⊆ Φ.time ×ˢ Φ.parameters :=
    subset_closure.trans hadm
  have hd : ∀ q ∈ ball ((0 : ℝ), s₀) (3 * r),
      DifferentiableAt ℝ Φ.augmentedProjection q :=
    fun q hq ↦ (Φ.hasFDerivAt_augmentedProjection (hDadm hq)).differentiableAt
  obtain ⟨_, _, _, hinner, htarget, hpre, _⟩ :=
    hstable Φ.augmentedProjection hd
      (fun _ _ ↦ by simpa only [sub_self, ContinuousLinearMap.opNorm_zero] using hε.le)
      (fun _ _ ↦ by simpa only [sub_self, norm_zero] using hε.le)
  have himage : V ⊆ Φ.augmentedProjection '' ball ((0 : ℝ), s₀) (3 * r) := by
    intro z hz
    exact (image_mono (ball_subset_ball (by linarith)))
      (htarget (self_subset_cthickening _ (subset_closure hz)))
  have hhalf : ∀ q ∈ ball ((0 : ℝ), s₀) (3 * r),
      ‖(A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U)).comp
        (fderiv ℝ Φ.augmentedProjection q) - ContinuousLinearMap.id ℝ (ℝ × InitialData U)‖
          ≤ 1 / 2 := by
    intro q hq
    have he : (A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U)).comp
        (fderiv ℝ Φ.augmentedProjection q - (A : _ →L[ℝ] _)) =
        (A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U)).comp
          (fderiv ℝ Φ.augmentedProjection q) - ContinuousLinearMap.id ℝ (ℝ × InitialData U) := by
      apply ContinuousLinearMap.ext
      intro v
      simp
    have hg := hgap q hq
    rw [he] at hg
    linarith
  obtain ⟨C, ht, hs, hC⟩ :=
    Φ.exists_smoothBufferedProjectionChart isOpen_ball hconv hV hDadm himage hc A hhalf
  have hs₀C : (0, s₀) ∈ C.source := by
    rw [hs]
    refine ⟨mem_ball_self (by positivity), ?_⟩
    simpa [HamiltonFlow.augmentedProjection, Φ.initial_position s₀ hs₀, hj] using hzV
  refine ⟨C, r, δ, hr, hδ, ht.symm ▸ hzV, hs₀C, ht.symm ▸ hVc, ?_, ?_,
    hadm, ht.symm ▸ hinner, ht.symm ▸ htarget, ht.symm ▸ hpre, ht.symm ▸ hC⟩
  · rw [ht]
    exact hs
  · intro q hq
    rw [hs] at hq
    exact hpre ⟨self_subset_cthickening _ (subset_closure hq.2), hq.1⟩

/-- Construct the buffered smooth phase and a nondegenerate mixed derivative
from transverse symbol data, with no supplied flow, inverse, or derivative gap
(`app:lem:common-hamilton-phase`, `app:ch_regular_base:eq:actual-eikonal`).

This is the local, single-symbol conclusion. The mixed derivative gap is on
an open neighborhood of the central target point; homogeneity retains the
actual source-membership condition. No common conic extension or symbol-family
estimates are asserted here. -/
theorem exists_bufferedHomogeneousHamiltonPhase
    (H : HomogeneousSymbol E) (hhom : H.ConicHomogeneous)
    (hH : ContDiffOn ℝ ∞ H.h H.domain)
    (j : U →ₗᵢ[ℝ] E) (ν : E) (hν : ‖ν‖ = 1)
    (horth : ∀ v : U, ⟪ν, j v⟫_ℝ = 0)
    (hspan : ∀ x : E, ⟪ν, x⟫_ℝ = 0 → ∃ u : U, j u = x)
    {s₀ : InitialData U} {τ₀ : ℝ}
    (hbase : transverseSectionState j ν (s₀, τ₀) ∈ H.domain)
    (henergy : H.h (transverseSectionState j ν (s₀, τ₀)) = s₀.2.1)
    (htrans : ⟪H.hp (transverseSectionState j ν (s₀, τ₀)), ν⟫_ℝ ≠ 0) :
    ∃ (Φ : HamiltonFlow H U) (C : ProjectionChart Φ) (r δ : ℝ),
      Φ.sectionMap = j.toContinuousLinearMap ∧ 0 < r ∧ 0 < δ ∧
      (j s₀.1, s₀.2) ∈ C.target ∧ (0, s₀) ∈ C.source ∧
      IsCompact (closure C.target) ∧
      C.source = ball ((0 : ℝ), s₀) (3 * r) ∩ Φ.augmentedProjection ⁻¹' C.target ∧
      C.source ⊆ ball ((0 : ℝ), s₀) (2 * r) ∧
      closure (ball ((0 : ℝ), s₀) (3 * r)) ⊆ Φ.time ×ˢ Φ.parameters ∧
      cthickening δ (Φ.augmentedProjection '' closure (ball ((0 : ℝ), s₀) r)) ⊆ C.target ∧
      cthickening δ (closure C.target) ⊆ Φ.augmentedProjection '' ball ((0 : ℝ), s₀) (2 * r) ∧
      Φ.augmentedProjection ⁻¹' cthickening δ (closure C.target) ∩
        ball ((0 : ℝ), s₀) (3 * r) ⊆ ball ((0 : ℝ), s₀) (2 * r) ∧
      ContDiffOn ℝ ∞ Φ.position (Φ.time ×ˢ Φ.parameters) ∧
      ContDiffOn ℝ ∞ Φ.momentum (Φ.time ×ˢ Φ.parameters) ∧
      ContDiffOn ℝ ∞ C.coordinates C.target ∧
      ContDiffOn ℝ ∞ (phase C.coordinates) C.target ∧
      (∀ z ∈ C.target,
        HasFDerivAt (phase C.coordinates)
          (phaseDifferential (Φ.momentum (chartLift C.coordinates z)) (C.coordinates z)) z ∧
        H.h (z.1, gradient (fun x ↦ phase C.coordinates (x, z.2)) z.1) = z.2.1 ∧
        HasFDerivAt (fun η ↦ phase C.coordinates (z.1, η))
          (canonicalCovector (C.coordinates z)) z.2) ∧
      (∀ u η, (0, (u, η)) ∈ C.source →
        phase C.coordinates (j u, η) = ⟪u, η.2⟫_ℝ) ∧
      (∀ x η (a : ℝ), 0 < a → (x, η) ∈ C.target →
        ((C.coordinates (x, η)).1, ((C.coordinates (x, η)).2, a • η)) ∈ C.source →
        phase C.coordinates (x, a • η) = a * phase C.coordinates (x, η)) ∧
      (∃ (A : (ℝ × U) ≃L[ℝ] E) (W : Set (E × (ℝ × U))),
        (A : (ℝ × U) →L[ℝ] E) = C.mixedMomentumDerivative (j s₀.1, s₀.2) ∧
        IsOpen W ∧ (j s₀.1, s₀.2) ∈ W ∧ W ⊆ C.target ∧
        ∀ w ∈ W, ‖(A.symm : E →L[ℝ] (ℝ × U)).comp (C.mixedMomentumDerivative w) -
          ContinuousLinearMap.id ℝ (ℝ × U)‖ ≤ (1 / 4 : ℝ)) := by
  obtain ⟨Φ, _, _, _, hsΦ, hj, hp₀, hx, hξ, hscale⟩ :=
    exists_transverseHamiltonFlow H hhom hH
      (H.contDiffOn_vectorField (by simpa using hH)) j ν hν horth hbase henergy htrans
  have hv : ⟪ν, H.hp (j s₀.1, Φ.momentum (0, s₀))⟫_ℝ ≠ 0 := by
    rw [hp₀, real_inner_comm]
    exact htrans
  obtain ⟨C, r, δ, hr, hδ, hz, hs, hcompact, hsource, hsourcebuffer, hadm,
    hinner, htarget, hpre, hC⟩ := Φ.exists_smoothBufferedProjection j hj ν horth hspan hsΦ hv hx
  refine ⟨Φ, C, r, δ, hj, hr, hδ, hz, hs, hcompact, hsource, hsourcebuffer, hadm,
    hinner, htarget, hpre, hx, hξ, hC, ?_, ?_, ?_, ?_,
    C.exists_mixedMomentumDerivative_neighborhood hξ hC hz⟩
  · exact (contDiff_snd.fst.contDiffOn.mul hC.fst).add
      (hC.snd.inner ℝ contDiff_snd.snd.contDiffOn)
  · intro z hz
    refine ⟨C.hasFDerivAt_phase hz, C.eikonal hz, ?_⟩
    have ha := C.source_admissible _ (C.maps_to_source z hz)
    exact Φ.hasFDerivAt_phase_parameter (C.hasFDerivAt_coordinates z hz) ha.1 ha.2
      (Filter.eventuallyEq_of_mem (C.isOpen_target.mem_nhds hz)
        (fun w hw ↦ C.right_inverse w hw))
  · intro u η hs
    simpa [hj] using C.initial_value hs
  · intro x η a ha hz has
    have hsrc := C.source_admissible _ (C.maps_to_source _ hz)
    have hscaled := C.source_admissible _ has
    exact C.homogeneous hz has (hscale _ hsrc.2 a ha hscaled.2 _ hsrc.1).1

end JanetCartan.HamiltonPhase
