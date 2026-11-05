module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.Inverse
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.PuncturedSupport

/-!
# Original-mask support for the frozen carrier construction

The frozen map erases physical positions only in its frequency component.
Its original compact-mask image therefore projects into the original conic
image, including at closure points. This proves the punctured support buffer
required by `exists_carrierL2Extension_supported_globalNormal_of_primitiveNorms`
for the SAME frozen inverse and domain. No whole-domain shell containment is
used (`new:lem:scaling`, `app:ch_background:eq:bg-full-complex-amplitude`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.FrozenModel
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow ContinuumRow.CanonicalCarrier ContinuumRow.CanonicalConic
open ContinuumNormalReduction TransportSymbol

variable {n : ℕ}

/-- Setting the two positions to zero preserves the original compact masks.
This does not change carrier labels or radial/angular frequency (`bg-row`). -/
theorem originInput_mem_conicMaskSupport {z₀ : Euclidean 3}
    {ηb : Euclidean (n - 1)} {r a : ℝ} (ha : 0 ≤ a) {p : InputVariables n}
    (hp : p ∈ conicMaskSupport z₀ ηb r a) :
    originInput p ∈ conicMaskSupport z₀ ηb r a :=
  ⟨⟨mem_closedBall_self (by positivity), mem_closedBall_self (by positivity)⟩, hp.2⟩

/-- The closed transported mask retains its original two physical supports,
for the literal augmented map (`app:ch_background:defn:bg-row`). -/
theorem conicMaskImage_position_support
    (Y : Euclidean n × CarrierParameter → Euclidean (n - 1))
    (z₀ : Euclidean 3) (ηb : Euclidean (n - 1)) (r a : ℝ)
    {p : Variables n × Euclidean 2}
    (hp : p ∈ closure (augmentedTransportGradient Y '' conicMaskSupport z₀ ηb r a)) :
    p.1.1 ∈ closedBall 0 (4 * a) ∧ p.1.2.1 ∈ closedBall 0 (4 * a) := by
  have hc : IsClosed {q : Variables n × Euclidean 2 |
      q.1.1 ∈ closedBall 0 (4 * a) ∧ q.1.2.1 ∈ closedBall 0 (4 * a)} :=
    (isClosed_closedBall.preimage continuous_fst.fst).inter
      (isClosed_closedBall.preimage continuous_fst.snd.fst)
  apply closure_minimal (t := {q : Variables n × Euclidean 2 |
    q.1.1 ∈ closedBall 0 (4 * a) ∧ q.1.2.1 ∈ closedBall 0 (4 * a)}) ?_ hc hp
  rintro _ ⟨q, hq, rfl⟩
  exact hq.1

variable {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)} {r a : ℝ}
    {c C : ℝ} (hP : P.IsValid c C)
    (hηb : ηb ≠ 0) (hr : 0 < r) (ha : 0 < a) (har : 6 * a ≤ 3 * r)
    (hcarrier : closedBall (spectatorCenter z₀) (3 * r) ×ˢ closedBall (z₀ 0) (3 * r) ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2))

include hP hηb hr ha har hcarrier

/-- The origin projection sends the frozen transported original support,
including closure points, into the original transported mask support.
This closes the support comparison used by the frozen constructor (`bg-Psi`,
`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem originOutput_mem_closure_frozenMaskImage {p : Variables n × Euclidean 2}
    (hp : p ∈ closure (augmentedTransportGradient (normalizedTransportPosition T Q 0) ''
      conicMaskSupport z₀ ηb r a)) :
    originOutput p ∈ closure (augmentedTransportGradient (transportPosition T Q) ''
      conicMaskSupport z₀ ηb r a) := by
  apply originOutput_smooth.continuous.continuousAt.continuousWithinAt.mem_closure hp
  rintro _ ⟨q, hq, rfl⟩
  have hq₀ := originInput_mem_conicMaskSupport ha.le hq
  have hqdom : q ∈ frozenInputDomain z₀ ηb r (6 * a) :=
    conicMaskSupport_subset hηb hr ha (by linarith) hq₀
  refine ⟨originInput q, hq₀, ?_⟩
  simp only [originOutput, augmentedTransportGradient, originInput]
  rw [frozenForward_eq_origin T Q hP hr har hcarrier hqdom]
  rfl

/-- Punctured closure of the original frozen mask lies in the SAME frozen
symbol domain. All support information is inherited from the actual masks;
the analytic hypotheses are the retained chart outputs of
`exists_frozen_conic_inputs` (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem frozenConicMaskImage_punctured_buffer
    (hf : ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
      (physicalParameterSet z₀ (6 * a) ×ˢ dataSet z₀ ηb (3 * r)))
    (htrans : ∀ p ∈ physicalParameterSet z₀ (6 * a),
      ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r),
        ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖) :
    closure (augmentedTransportGradient (normalizedTransportPosition T Q 0) ''
      conicMaskSupport z₀ ηb r a) ∩ {p | p.1.2.2 ≠ 0} ⊆
      frozenSymbolDomain T Q z₀ ηb r (6 * a) := by
  rintro p ⟨hp, hne⟩
  exact conicMaskImage_punctured_buffer T Q hηb hr ha (by linarith) htrans hf
    ⟨originOutput_mem_closure_frozenMaskImage T Q hP hηb hr ha har hcarrier hp, hne⟩

/-- Transfer a proved supported shell for the original map to the frozen
map, retaining the same masks. The extra inequality is only containment of
the physical mask in the output ball; the parent chooses the small mask after
the common output radius. This is a geometric deduction, not a construction
of that radius or an operator bound (`app:ch_background:eq:bg-Psi`). -/
theorem frozenConicMaskImage_supported_shell
    {k : Euclidean n} {ℓ τ : ℝ} (hsmall : 4 * a ≤ τ)
    (hshell : ∀ q : Variables n × Euclidean 2, ‖q.1.2.2‖ = ℓ →
      q ∈ closure (augmentedTransportGradient (transportPosition T Q) ''
        conicMaskSupport z₀ ηb r a) →
      q ∈ closedBall ((0, 0, k), spectatorCenter z₀) τ)
    {p : Variables n × Euclidean 2} (hnorm : ‖p.1.2.2‖ = ℓ)
    (hp : p ∈ closure (augmentedTransportGradient (normalizedTransportPosition T Q 0) ''
      conicMaskSupport z₀ ηb r a)) :
    p ∈ closedBall ((0, 0, k), spectatorCenter z₀) τ := by
  have hs := hshell (originOutput p) hnorm
    (originOutput_mem_closure_frozenMaskImage T Q hP hηb hr ha har hcarrier hp)
  have hx := conicMaskImage_position_support (normalizedTransportPosition T Q 0) z₀ ηb r a hp
  rw [mem_closedBall, Prod.dist_eq, Prod.dist_eq, Prod.dist_eq] at hs ⊢
  simp only [originOutput, dist_self, max_le_iff] at hs ⊢
  exact ⟨⟨(mem_closedBall.mp hx.1).trans hsmall,
    (mem_closedBall.mp hx.2).trans hsmall, hs.1.2.2⟩, hs.2⟩

end JanetCartan.ContinuumNormal.FrozenModel
