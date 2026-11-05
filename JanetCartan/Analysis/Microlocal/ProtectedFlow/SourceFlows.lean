module

public import JanetCartan.Analysis.Microlocal.ProtectedFlow.ComparisonPropagation
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.PhaseAssembly.Buffers

/-!
# Actual two-sided flows of the complete source product

For `app:ch_regular:thm:no-return`, construct a finite covering family of actual
Hamilton flows from primitive closeness of the same fixed frame extension.
The complete time intervals and their physical buffers precede the frame.
Every point of the source product, including its boundary, is covered.
These flows are for the literal normalized determinant; identification with
retained canonical factor flows uses ODE uniqueness.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ProtectedFlow
open HamiltonPhase ActualCarriers ActualCarriers.FrozenPhaseReference

/-- A constructed state flow gives a complete characteristic segment, retaining
all intermediate points and allowing either endpoint orientation. Consumed by
`exists_extended_frame_source_flows` (`app:ch_regular:thm:no-return`). -/
theorem smoothFlow_completeCharacteristicSegment {n : ℕ}
    {H : HomogeneousSymbol (Euclidean n)} {z₀ : Euclidean n × Euclidean n}
    {R a T τ : ℝ} {Ψ : (Euclidean n × Euclidean n) × ℝ → Euclidean n × Euclidean n}
    (hΨ : ODE.IsSmoothFlowOn H.vectorField z₀ R a T Ψ)
    (hτ : 0 < τ) (hτT : τ < T)
    {W : Set (Euclidean n)}
    (hRW : closedBall z₀ R ⊆ (W ×ˢ univ) ∩ H.domain)
    {q : Euclidean n × Euclidean n} (hq : q ∈ closedBall z₀ a)
    (hchar : H.h q = 0) {t : ℝ} (ht : t ∈ Icc (-τ) τ) :
    CompleteCharacteristicSegment H W q (Ψ (q, t)) := by
  have htime {u : ℝ} (hu : u ∈ Icc (-τ) τ) : u ∈ Ioo (-T) T := by
    constructor <;> linarith [hu.1, hu.2]
  refine ⟨hchar, (fun u ↦ (Ψ (q, u)).1), (fun u ↦ (Ψ (q, u)).2),
    -τ, τ, 0, t, ⟨by linarith, hτ.le⟩, ht, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · intro u hu
    exact (hΨ.hasDerivAt hq (htime hu)).fst
  · intro u hu
    exact (hΨ.hasDerivAt hq (htime hu)).snd
  · intro u hu
    exact (hRW (hΨ.range q hq u (Ioo_subset_Icc_self (htime hu)))).1.1
  · intro u hu
    exact (hRW (hΨ.range q hq u (Ioo_subset_Icc_self (htime hu)))).2
  · exact (hΨ.initial q hq).symm

/-- Construct actual buffered flow tubes covering every point of the complete
compact source product, from the same affine extension and primitive frame
`C⁶` closeness. One positive time and physical buffer work uniformly in the
frame and both orientations. The state flows satisfy the actual Hamilton ODE;
no flow, tube-containment or source-coverage assumption is used
(`app:ch_regular:thm:no-return`, finite-factor physical tubes). -/
theorem exists_extended_frame_source_flows {n : ℕ}
    (p : BallExtension.Parameters (Euclidean n))
    {r : ℝ} (hr : 0 < r) {Ω : Set (Euclidean n)} (hΩ : IsCompact Ω)
    (hΩzero : ∀ ξ ∈ Ω, ξ ≠ 0) :
    ∃ (s : Finset (closedBall (0 : Euclidean n) r ×ˢ Ω))
      (R a T : s → ℝ) (τ δ ε : ℝ),
      0 < τ ∧ 0 < δ ∧ 0 < ε ∧
      (∀ i, 0 < R i ∧ 0 < a i ∧ τ < T i) ∧
      (∀ q ∈ closedBall 0 r ×ˢ Ω, ∃ i : s, q ∈ closedBall i.1.1 (a i)) ∧
      (∀ i, closedBall i.1.1 (R i) ⊆
        (ball 0 (2 * r) ×ˢ univ) ∩ (frozenSymbol n).domain) ∧
      ∀ (Q : Euclidean n → Fin n → MetricTensor n)
        (hQ : ∀ x ∈ closedBall p.center p.radius, ContDiffAt ℝ ∞ Q x),
        cNorm (closedBall p.center p.radius) 6 (Q - fun _ ↦ cubeStress n) < δ →
        let H := normalizedHomogeneousSymbol isOpen_univ (affineFrameExtension p Q)
          (contDiff_affineFrameExtension p
            (fun x hx ↦ (hQ x hx).contDiffWithinAt)).contDiffOn;
        ∃ Ψ : s → (Euclidean n × Euclidean n) × ℝ → Euclidean n × Euclidean n,
          (∀ i, ODE.IsSmoothFlowOn H.vectorField i.1.1 (R i) (a i) (T i) (Ψ i)) ∧
          ∀ q ∈ closedBall 0 r ×ˢ Ω, ∃ i : s,
            q ∈ closedBall i.1.1 (a i) ∧ Ψ i (q, 0) = q ∧
            ∀ t ∈ Icc (-τ) τ,
              closedBall (Ψ i (q, t)).1 ε ⊆ ball 0 (2 * r) ∧
              (Ψ i (q, t)) ∈ H.domain ∧
              (H.h q = 0 → CompleteCharacteristicSegment H (ball 0 (2 * r))
                q (Ψ i (q, t))) := by
  classical
  let S := closedBall (0 : Euclidean n) r ×ˢ Ω
  let V : Set (Euclidean n × Euclidean n) :=
    (ball 0 (3 * r / 2) ×ˢ univ) ∩ (frozenSymbol n).domain
  have hV : IsOpen V := (isOpen_ball.prod isOpen_univ).inter (frozenSymbol n).isOpen_domain
  have hSV : S ⊆ V := by
    intro z hz
    exact ⟨⟨closedBall_subset_ball (by linarith) hz.1, mem_univ _⟩,
      (mem_frozenSymbol_domain z).mpr (hΩzero z.2 hz.2)⟩
  have hballs (z : S) : ∃ ρ > (0 : ℝ), closedBall z.1 ρ ⊆ V :=
    nhds_basis_closedBall.mem_iff.mp (hV.mem_nhds (hSV z.2))
  choose ρ hρ hρV using hballs
  have hρD (z : S) : closedBall z.1 (ρ z) ⊆ (frozenSymbol n).domain :=
    fun _ h ↦ (hρV z h).2
  have hlocal (z : S) := exists_common_symbol_flows (frozenSymbol n)
    (frozenSymbol n).isOpen_domain Subset.rfl (hρ z) (hρD z) (frozenSymbol_smooth n)
  choose a ha T hT C hC d hd Ψ₀ hΨ₀ hflows using hlocal
  have hframe (z : S) := exists_extended_symbol_comparison_radius p
    (isCompact_closedBall z.1 (ρ z))
    (fun q hq ↦ (mem_frozenSymbol_domain q).mp (hρD z hq)) 3 (hd z)
  choose e he hecomp using hframe
  have hS : IsCompact S := (isCompact_closedBall _ _).prod hΩ
  obtain ⟨s, hs⟩ := hS.elim_finite_subcover (fun z : S ↦ ball z.1 (a z))
    (fun _ ↦ isOpen_ball) (by
      intro z hz
      exact mem_iUnion.mpr ⟨⟨z, hz⟩, mem_ball_self (ha ⟨z, hz⟩)⟩)
  have hcover : ∀ q ∈ S, ∃ i : s, q ∈ closedBall i.1.1 (a i.1) := by
    intro q hq
    obtain ⟨i, hi, hqi⟩ := mem_iUnion₂.mp (hs hq)
    exact ⟨⟨i, hi⟩, ball_subset_closedBall hqi⟩
  obtain ⟨τ, δ, _, hτ, _, hδ, _, hmin⟩ := exists_common_phase_buffers
    (fun i : s ↦ T i.1 / 2) (fun i : s ↦ e i.1) (fun _ ↦ (1 : ℝ))
    (fun i ↦ half_pos (hT i.1)) (fun i ↦ he i.1)
  have hτT (i : s) : τ < T i.1 := by linarith [(hmin i).1]
  have hrange (i : s) : closedBall i.1.1 (ρ i.1) ⊆
      (ball 0 (2 * r) ×ˢ univ) ∩ (frozenSymbol n).domain := by
    intro q hq
    have hh := hρV i.1 hq
    exact ⟨⟨ball_subset_ball (by linarith) hh.1.1, mem_univ _⟩, hh.2⟩
  refine ⟨s, fun i ↦ ρ i.1, fun i ↦ a i.1, fun i ↦ T i.1, τ, δ, r / 4,
    hτ, hδ, by positivity, fun i ↦ ⟨hρ i.1, ha i.1, hτT i⟩,
    hcover, hrange, ?_⟩
  intro Q hQ hsmall
  let hE := contDiff_affineFrameExtension p (fun x hx ↦ (hQ x hx).contDiffWithinAt)
  let H := normalizedHomogeneousSymbol isOpen_univ (affineFrameExtension p Q) hE.contDiffOn
  have hH : ContDiffOn ℝ ∞ H.h (frozenSymbol n).domain :=
    contDiffOn_normalizedSymbol isOpen_univ hE.contDiffOn
  have hclose (i : s) : cNorm (closedBall i.1.1 (ρ i.1)) 3
      (fun z ↦ H.h z - (frozenSymbol n).h z) ≤ d i.1 :=
    (hecomp i.1 Q hQ (((cNorm_mono_order (by decide : 3 ≤ 6)).trans_lt hsmall).trans_le
      (hmin i).2.1)).le
  choose Ψ hΨ hcompare using fun i : s ↦ hflows i.1 H Subset.rfl hH (hclose i)
  refine ⟨Ψ, hΨ, ?_⟩
  intro q hq
  obtain ⟨i, hqi⟩ := hcover q hq
  refine ⟨i, hqi, (hΨ i).initial q hqi, ?_⟩
  intro t ht
  have htT : t ∈ Icc (-T i.1) (T i.1) := by
    constructor <;> linarith [ht.1, ht.2, hτT i]
  have hstate := (hΨ i).range q hqi t htT
  have hphysical := (hρV i.1 hstate).1.1
  refine ⟨?_, (hρV i.1 hstate).2, fun hchar ↦
    smoothFlow_completeCharacteristicSegment (hΨ i) hτ (hτT i) (hrange i) hqi hchar ht⟩
  intro x hx
  rw [mem_closedBall] at hx
  rw [mem_ball] at hphysical ⊢
  calc
    dist x 0 ≤ dist x (Ψ i (q, t)).1 + dist (Ψ i (q, t)).1 0 := dist_triangle _ _ _
    _ < 2 * r := by linarith

end JanetCartan.ProtectedFlow
