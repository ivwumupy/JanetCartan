module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.PrimitiveRealization.Geometry

/-!
# Frozen shell on the retained inner masks

The outer inverse radii and inner mask radii remain independent. The local
joint producer consumes this transfer before selecting its finite cover.
Sources: `app:ch_background:eq:bg-full-complex-amplitude`, `new:lem:scaling`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.RetainedFrozen.UnitRealization
open FrozenModel ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic ContinuumNormalReduction TransportSymbol
variable {n : ℕ}

variable {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)} {r a r' a' : ℝ}
    {c C : ℝ} (hP : P.IsValid c C)
    (hηb : ηb ≠ 0) (hr : 0 < r) (ha : 0 < a) (har : 6 * a ≤ 3 * r)
    (hcarrier : closedBall (spectatorCenter z₀) (3 * r) ×ˢ closedBall (z₀ 0) (3 * r) ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2))

    (ha' : 0 < a') (hrr : r' ≤ r) (haa : a' ≤ a)

include hP hηb hr ha har hcarrier ha' hrr haa

/-- The origin projection sends the frozen transported original support,
including closure points, into the original transported mask support.
This closes the support comparison used by the frozen constructor (`bg-Psi`,
`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem originOutput_mem_closure_retainedMaskImage {p : Variables n × Euclidean 2}
    (hp : p ∈ closure (augmentedTransportGradient (normalizedTransportPosition T Q 0) ''
      conicMaskSupport z₀ ηb r' a')) :
    originOutput p ∈ closure (augmentedTransportGradient (transportPosition T Q) ''
      conicMaskSupport z₀ ηb r' a') := by
  apply originOutput_smooth.continuous.continuousAt.continuousWithinAt.mem_closure hp
  rintro _ ⟨q, hq, rfl⟩
  have hq₀ := originInput_mem_conicMaskSupport ha'.le hq
  have hqdom : q ∈ frozenInputDomain z₀ ηb r (6 * a) :=
    conicMaskSupport_subset hηb hr ha (by linarith)
      (conicMaskSupport_mono z₀ ηb hrr haa hq₀)
  refine ⟨originInput q, hq₀, ?_⟩
  simp only [originOutput, augmentedTransportGradient, originInput]
  rw [frozenForward_eq_origin T Q hP hr har hcarrier hqdom]
  rfl

/-- Transfer a proved supported shell for the original map to the frozen
map, retaining the same masks. The extra inequality is only containment of
the physical mask in the output ball; the parent chooses the small mask after
the common output radius. This is a geometric deduction, not a construction
of that radius or an operator bound (`app:ch_background:eq:bg-Psi`). -/
theorem retainedFrozenMaskImage_supported_shell
    {k : Euclidean n} {ℓ τ : ℝ} (hsmall : 4 * a' ≤ τ)
    (hshell : ∀ q : Variables n × Euclidean 2, ‖q.1.2.2‖ = ℓ →
      q ∈ closure (augmentedTransportGradient (transportPosition T Q) ''
        conicMaskSupport z₀ ηb r' a') →
      q ∈ closedBall ((0, 0, k), spectatorCenter z₀) τ)
    {p : Variables n × Euclidean 2} (hnorm : ‖p.1.2.2‖ = ℓ)
    (hp : p ∈ closure (augmentedTransportGradient (normalizedTransportPosition T Q 0) ''
      conicMaskSupport z₀ ηb r' a')) :
    p ∈ closedBall ((0, 0, k), spectatorCenter z₀) τ := by
  have hs := hshell (originOutput p) hnorm
    (originOutput_mem_closure_retainedMaskImage T Q hP hηb hr ha har hcarrier ha' hrr haa hp)
  have hx := conicMaskImage_position_support (normalizedTransportPosition T Q 0) z₀ ηb r' a' hp
  rw [mem_closedBall, Prod.dist_eq, Prod.dist_eq, Prod.dist_eq] at hs ⊢
  simp only [originOutput, dist_self, max_le_iff] at hs ⊢
  exact ⟨⟨(mem_closedBall.mp hx.1).trans hsmall,
    (mem_closedBall.mp hx.2).trans hsmall, hs.1.2.2⟩, hs.2⟩

end JanetCartan.ContinuumNormal.RetainedFrozen.UnitRealization
