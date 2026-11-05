module

public import JanetCartan.Analysis.Microlocal.ProtectedFlow.SourceFlows

/-!
# Physical buffers for the retained canonical Hamilton flows

The auxiliary state flows used to construct common tubes are identified with
any retained canonical flow of the same symbol, by actual ODE uniqueness.
No range inside the protection ball is assumed of the retained flow. Only
its original time-strip admissibility is needed. This closes the physical
containment step once the selected rectangles have the prescribed time width
(`app:ch_regular:thm:no-return`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ProtectedFlow
open HamiltonPhase ActualCarriers ActualCarriers.FrozenPhaseReference

private theorem hamilton_curves_eqOn_of_initial_eq {n : ℕ}
    {H : HomogeneousSymbol (Euclidean n)} (hH : ContDiffOn ℝ ∞ H.h H.domain)
    {u v : ℝ → Euclidean n × Euclidean n} {τ : ℝ} (hτ : 0 < τ)
    (hu : ∀ t ∈ Icc (-τ) τ, HasDerivAt u (H.vectorField (u t)) t)
    (hv : ∀ t ∈ Icc (-τ) τ, HasDerivAt v (H.vectorField (v t)) t)
    (humem : ∀ t ∈ Icc (-τ) τ, u t ∈ H.domain)
    (hvmem : ∀ t ∈ Icc (-τ) τ, v t ∈ H.domain)
    (hinit : u 0 = v 0) : EqOn u v (Icc (-τ) τ) := by
  let K := u '' Icc (-τ) τ ∪ v '' Icc (-τ) τ
  have huc : ContinuousOn u (Icc (-τ) τ) := fun t ht ↦ (hu t ht).continuousAt.continuousWithinAt
  have hvc : ContinuousOn v (Icc (-τ) τ) := fun t ht ↦ (hv t ht).continuousAt.continuousWithinAt
  have hK : IsCompact K := (isCompact_Icc.image_of_continuousOn huc).union
    (isCompact_Icc.image_of_continuousOn hvc)
  have hKD : K ⊆ H.domain := by
    rintro z (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact humem t ht
    · exact hvmem t ht
  have hfield : ContDiffOn ℝ 1 H.vectorField H.domain :=
    H.contDiffOn_vectorField (hH.of_le (by simp))
  have hloc : LocallyLipschitzOn K H.vectorField := by
    intro z hz
    obtain ⟨L, S, hS, hLS⟩ :=
      (hfield.contDiffAt (H.isOpen_domain.mem_nhds (hKD hz))).exists_lipschitzOnWith
    exact ⟨L, S, mem_nhdsWithin_of_mem_nhds hS, hLS⟩
  obtain ⟨L, hL⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hK hloc
  exact ODE_solution_unique_of_mem_Icc (s := fun _ ↦ K) (fun _ _ ↦ hL)
    (show (0 : ℝ) ∈ Ioo (-τ) τ from ⟨by linarith, hτ⟩) huc
    (fun t ht ↦ hu t (Ioo_subset_Icc_self ht))
    (fun t ht ↦ Or.inl ⟨t, Ioo_subset_Icc_self ht, rfl⟩) hvc
    (fun t ht ↦ hv t (Ioo_subset_Icc_self ht))
    (fun t ht ↦ Or.inr ⟨t, Ioo_subset_Icc_self ht, rfl⟩) hinit

/-- ODE uniqueness identifies a retained canonical Hamilton flow with the
constructed source flow on the entire shifted interval, in either orientation.
The retained flow's physical range is a conclusion of this identification,
not a hypothesis (`app:ch_regular:thm:no-return`). -/
theorem retainedFlow_state_eq_sourceFlow {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {H : HomogeneousSymbol (Euclidean n)} (hH : ContDiffOn ℝ ∞ H.h H.domain)
    (Φ : HamiltonFlow H V)
    {z₀ q : Euclidean n × Euclidean n} {R a T τ t₀ : ℝ}
    {Ψ : (Euclidean n × Euclidean n) × ℝ → Euclidean n × Euclidean n}
    (hΨ : ODE.IsSmoothFlowOn H.vectorField z₀ R a T Ψ)
    (hτ : 0 < τ) (hτT : τ < T) (hRD : closedBall z₀ R ⊆ H.domain)
    (hq : q ∈ closedBall z₀ a) {s : InitialData V} (hs : s ∈ Φ.parameters)
    (htime : ∀ t ∈ Icc (-τ) τ, t₀ + t ∈ Φ.time)
    (hinit : (Φ.position (t₀, s), Φ.momentum (t₀, s)) = q) :
    ∀ t ∈ Icc (-τ) τ,
      (Φ.position (t₀ + t, s), Φ.momentum (t₀ + t, s)) = Ψ (q, t) := by
  have htT {t : ℝ} (ht : t ∈ Icc (-τ) τ) : t ∈ Ioo (-T) T := by
    constructor <;> linarith [ht.1, ht.2]
  apply hamilton_curves_eqOn_of_initial_eq hH hτ
  · intro t ht
    exact (HasDerivAt.comp_const_add t₀ t
      (Φ.position_hasDerivAt (htime t ht) hs)).prodMk
        (HasDerivAt.comp_const_add t₀ t (Φ.momentum_hasDerivAt (htime t ht) hs))
  · intro t ht
    exact hΨ.hasDerivAt hq (htT ht)
  · intro t ht
    exact Φ.state_mem _ (htime t ht) s hs
  · intro t ht
    exact hRD (hΨ.range q hq t (Ioo_subset_Icc_self (htT ht)))
  · simpa only [add_zero, hΨ.initial q hq] using hinit

/-- Common positive time and physical buffers for *every retained* Hamilton
flow whose initial state lies in the full compact source product. The
constant is chosen before the current frame and before the retained flow.
All intermediate points, both time orientations and the whole actual closed
source support are covered (`app:ch_regular:thm:no-return`).

The only interval condition is admissibility in the retained flow's original
time strip. The actual factor construction must choose rectangles of this
fixed width inside that strip; physical containment is proved here. -/
theorem exists_extended_frame_retained_flow_tubes {n : ℕ}
    (p : BallExtension.Parameters (Euclidean n))
    {r : ℝ} (hr : 0 < r) {Ω : Set (Euclidean n)} (hΩ : IsCompact Ω)
    (hΩzero : ∀ ξ ∈ Ω, ξ ≠ 0) :
    ∃ τ δ ε : ℝ, 0 < τ ∧ 0 < δ ∧ 0 < ε ∧
      ∀ (Q : Euclidean n → Fin n → MetricTensor n)
        (hQ : ∀ x ∈ closedBall p.center p.radius, ContDiffAt ℝ ∞ Q x),
        cNorm (closedBall p.center p.radius) 6 (Q - fun _ ↦ cubeStress n) < δ →
        let H := normalizedHomogeneousSymbol isOpen_univ (affineFrameExtension p Q)
          (contDiff_affineFrameExtension p
            (fun x hx ↦ (hQ x hx).contDiffWithinAt)).contDiffOn;
        ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
          (Φ : HamiltonFlow H V) (s : InitialData V) (t₀ : ℝ),
          s ∈ Φ.parameters →
          (Φ.position (t₀, s), Φ.momentum (t₀, s)) ∈ closedBall 0 r ×ˢ Ω →
          (∀ t ∈ Icc (-τ) τ, t₀ + t ∈ Φ.time) →
          ∀ t ∈ Icc (-τ) τ,
            closedBall (Φ.position (t₀ + t, s)) ε ⊆ ball 0 (2 * r) := by
  obtain ⟨s, R, a, T, τ, δ, ε, hτ, hδ, hε, hpos, _hcover, hrange, hflows⟩ :=
    exists_extended_frame_source_flows p hr hΩ hΩzero
  refine ⟨τ, δ, ε, hτ, hδ, hε, ?_⟩
  intro Q hQ hsmall
  let hE := contDiff_affineFrameExtension p (fun x hx ↦ (hQ x hx).contDiffWithinAt)
  let H := normalizedHomogeneousSymbol isOpen_univ (affineFrameExtension p Q) hE.contDiffOn
  obtain ⟨Ψ, hΨ, hsource⟩ := hflows Q hQ hsmall
  dsimp only
  intro V _ _ Φ u t₀ hu hinit htime t ht
  let q := (Φ.position (t₀, u), Φ.momentum (t₀, u))
  obtain ⟨i, hqi, _hzero, hbuffer⟩ := hsource q hinit
  have he := retainedFlow_state_eq_sourceFlow
    (contDiffOn_normalizedSymbol isOpen_univ hE.contDiffOn) Φ (hΨ i)
    hτ (hpos i).2.2 (fun _ h ↦ (hrange i h).2) hqi hu htime rfl t ht
  rw [show Φ.position (t₀ + t, u) = (Ψ i (q, t)).1 from congrArg Prod.fst he]
  exact (hbuffer t ht).1

end JanetCartan.ProtectedFlow
