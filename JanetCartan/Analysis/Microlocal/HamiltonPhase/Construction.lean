module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.Transversality
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.SectionData
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.Scaling

/-!
# Constructing the local homogeneous Hamilton phase

For `app:lem:common-hamilton-phase`, assemble the transverse implicit energy root,
Picard–Lindelöf flow, transverse projection isomorphism, and smooth local inverse.
Neither an initial momentum root nor an inverse chart nor a flow scaling law is
assumed. The resulting phase satisfies the full differential, eikonal, section,
and positive homogeneity identities on its actual chart.

This is a local construction for one symbol. Common buffers for a neighborhood
of symbols, the mixed-Hessian gap, and uniform derivative bounds require further
quantitative arguments.
-/

open Set Filter
open scoped Topology ContDiff InnerProductSpace
@[expose] public noncomputable section
namespace JanetCartan.HamiltonPhase
variable {E U : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

/-- Construct a smooth two-sided Hamilton flow directly from a transverse
symbol and section. Its covector scaling follows from the implicit root and
ODE uniqueness (`app:lem:common-hamilton-phase`). -/
theorem exists_transverseHamiltonFlow
    (H : HomogeneousSymbol E) (hhom : H.ConicHomogeneous)
    (hH : ContDiffOn ℝ ∞ H.h H.domain)
    (hfield : ContDiffOn ℝ ∞ H.vectorField H.domain)
    (j : U →ₗᵢ[ℝ] E) (ν : E) (hν : ‖ν‖ = 1)
    (horth : ∀ v : U, ⟪ν, j v⟫_ℝ = 0)
    {s₀ : InitialData U} {τ₀ : ℝ}
    (hbase : transverseSectionState j ν (s₀, τ₀) ∈ H.domain)
    (henergy : H.h (transverseSectionState j ν (s₀, τ₀)) = s₀.2.1)
    (htrans : ⟪H.hp (transverseSectionState j ν (s₀, τ₀)), ν⟫_ℝ ≠ 0) :
    ∃ Φ : HamiltonFlow H U, ∃ ε > (0 : ℝ),
      Φ.time = Ioo (-ε) ε ∧ s₀ ∈ Φ.parameters ∧
      Φ.sectionMap = j.toContinuousLinearMap ∧
      Φ.momentum (0, s₀) = τ₀ • ν + j s₀.2.2 ∧
      ContDiffOn ℝ ∞ Φ.position (Φ.time ×ˢ Φ.parameters) ∧
      ContDiffOn ℝ ∞ Φ.momentum (Φ.time ×ˢ Φ.parameters) ∧
      ∀ s ∈ Φ.parameters, ∀ r : ℝ, 0 < r → scaleSectionData r s ∈ Φ.parameters →
        ∀ t ∈ Φ.time,
          Φ.position (t, scaleSectionData r s) = Φ.position (t, s) ∧
          Φ.momentum (t, scaleSectionData r s) = r • Φ.momentum (t, s) := by
  obtain ⟨P, g, hP, _, hsP, hg₀, _, hp, hdata, hscale⟩ :=
    exists_transverseSectionData H hH j ν hν horth hbase henergy htrans
  obtain ⟨Φ, ε, hε, htime, hsΦ, hsub, hj, hx, hξ, hinit⟩ :=
    exists_localHamiltonFlow (⊤ : ℕ∞) (by simp) H hfield j.toContinuousLinearMap hP
      (sectionRootMomentum j ν g) hp (fun s hs ↦ (hdata s hs).1)
      (fun s hs ↦ (hdata s hs).2.1) (fun s hs ↦ (hdata s hs).2.2.2) hsP
  refine ⟨Φ, ε, hε, htime, hsΦ, hj, ?_, hx, hξ, ?_⟩
  · rw [hinit s₀ hsΦ]
    simp [sectionRootMomentum, hg₀]
  · intro s hs r hr hrs t ht
    have hsc : Φ.momentum (0, scaleSectionData r s) = r • Φ.momentum (0, s) := by
      rw [hinit _ hrs, hinit _ hs]
      exact (hscale s (hsub hs) r hr (hsub hrs)).2
    exact ⟨Φ.position_smul hhom (hfield.of_le (by simp)) hr hs hrs hsc ht,
      Φ.momentum_smul hhom (hfield.of_le (by simp)) hr hs hrs hsc ht⟩

/-- Construct a smooth local phase from a transverse degree-one symbol, with
`dS = ξ · dx + t de + u′ · dη′`, the eikonal equation, the canonical-coordinate
identity, and the section value (`app:lem:common-hamilton-phase`,
`app:ch_regular_base:eq:actual-eikonal`).

The geometric hypothesis `hspan` says that `j` parametrizes the entire initial
hyperplane. Homogeneity holds whenever the scaled lift belongs to the actual
chart source; no extension outside this local inverse domain is asserted. -/
theorem exists_localHomogeneousHamiltonPhase
    (H : HomogeneousSymbol E) (hhom : H.ConicHomogeneous)
    (hH : ContDiffOn ℝ ∞ H.h H.domain)
    (hfield : ContDiffOn ℝ ∞ H.vectorField H.domain)
    (j : U →ₗᵢ[ℝ] E) (ν : E) (hν : ‖ν‖ = 1)
    (horth : ∀ v : U, ⟪ν, j v⟫_ℝ = 0)
    (hspan : ∀ x : E, ⟪ν, x⟫_ℝ = 0 → ∃ u : U, j u = x)
    {s₀ : InitialData U} {τ₀ : ℝ}
    (hbase : transverseSectionState j ν (s₀, τ₀) ∈ H.domain)
    (henergy : H.h (transverseSectionState j ν (s₀, τ₀)) = s₀.2.1)
    (htrans : ⟪H.hp (transverseSectionState j ν (s₀, τ₀)), ν⟫_ℝ ≠ 0) :
    ∃ (Φ : HamiltonFlow H U) (C : ProjectionChart Φ),
      Φ.sectionMap = j.toContinuousLinearMap ∧
      (0, s₀) ∈ C.source ∧ (j s₀.1, s₀.2) ∈ C.target ∧
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
      (∀ x η (r : ℝ), 0 < r → (x, η) ∈ C.target →
        ((C.coordinates (x, η)).1, ((C.coordinates (x, η)).2, r • η)) ∈ C.source →
        phase C.coordinates (x, r • η) = r * phase C.coordinates (x, η)) := by
  obtain ⟨Φ, ε, hε, htime, hsΦ, hj, hp₀, hx, hξ, hscale⟩ :=
    exists_transverseHamiltonFlow H hhom hH hfield j ν hν horth hbase henergy htrans
  have hv : ⟪ν, H.hp (j s₀.1, Φ.momentum (0, s₀))⟫_ℝ ≠ 0 := by
    rw [hp₀, real_inner_comm]
    exact htrans
  obtain ⟨A, hA⟩ := Φ.exists_initialAugmentedProjectionEquiv j hj ν horth hspan hsΦ hv
  have haug : ContDiffOn ℝ ∞ Φ.augmentedProjection (Φ.time ×ˢ Φ.parameters) :=
    hx.prodMk contDiff_snd.snd.contDiffOn
  obtain ⟨C, hsC, hzC, hC⟩ :=
    Φ.exists_smoothLocalProjectionChart ⟨Φ.zero_mem_time, hsΦ⟩ haug A hA
  have hz : (j s₀.1, s₀.2) ∈ C.target := by
    simpa [HamiltonFlow.augmentedProjection, Φ.initial_position s₀ hsΦ, hj] using hzC
  refine ⟨Φ, C, hj, hsC, hz, hx, hξ, hC, ?_, ?_, ?_, ?_⟩
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
  · intro x η r hr hz hrs
    have ha := C.source_admissible _ (C.maps_to_source _ hz)
    have hra := C.source_admissible _ hrs
    exact C.homogeneous hz hrs (hscale _ ha.2 r hr hra.2 _ ha.1).1

end JanetCartan.HamiltonPhase
