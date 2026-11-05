module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.FrozenPhaseReference.Neighborhood

/-!
# Affine identities for the retained frozen Hamilton flow

The Hamilton ODE, rather than a prescribed phase formula, supplies momentum
conservation and the positive-sign affine identity of
`app:lem:common-hamilton-phase`. These are consumed by the local frozen
reference construction in `app:ch_seed:prop:seed-actual-menu`, Step 1.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff InnerProductSpace

namespace JanetCartan.ActualCarriers.FrozenPhaseReference
open HamiltonPhase

/-- The adapted orthogonal coordinates reconstruct every physical covector
(`app:ch_seed:prop:seed-actual-menu`, Step 1). -/
theorem AdaptedSection.covector_decomposition {n : ℕ} {ξ : Euclidean n}
    (a : AdaptedSection ξ) (p : Euclidean n) :
    ⟪a.normal, p⟫_ℝ • a.normal + a.embedding (a.embedding.toContinuousLinearMap.adjoint p) = p := by
  obtain ⟨u, hu⟩ := a.spanning (p - ⟪a.normal, p⟫_ℝ • a.normal) (by
    simp [inner_sub_right, inner_smul_right, a.normal_unit])
  have hadj : a.embedding.toContinuousLinearMap.adjoint p = u := by
    apply ext_inner_right ℝ
    intro v
    rw [ContinuousLinearMap.adjoint_inner_left]
    change ⟪p, a.embedding v⟫_ℝ = ⟪u, v⟫_ℝ
    rw [← a.embedding.inner_map_map u v, hu]
    simp [inner_sub_left, inner_smul_left, a.orthogonal]
  rw [hadj, hu]
  abel

/-- The canonical base datum is the state `(0, ξ)`
(`app:lem:common-hamilton-phase`). -/
theorem AdaptedSection.baseState_eq {n : ℕ} {ξ : Euclidean n}
    (a : AdaptedSection ξ) :
    transverseSectionState a.embedding a.normal (a.baseData, ⟪a.normal, ξ⟫_ℝ) = (0, ξ) := by
  simp [transverseSectionState, AdaptedSection.baseData, a.covector_decomposition]

/-- The actual frozen Hamilton ODE conserves the full momentum, for both
positive and negative time (`app:lem:common-hamilton-phase`). -/
theorem frozenFlow_momentum_eq_initial {n : ℕ}
    (Φ : HamiltonFlow (frozenSymbol n) (Euclidean (n - 1)))
    {t : ℝ} (ht : t ∈ Φ.time) {s : InitialData (Euclidean (n - 1))}
    (hs : s ∈ Φ.parameters) : Φ.momentum (t, s) = Φ.momentum (0, s) := by
  apply ext_inner_right ℝ
  intro v
  apply conserved_of_hasDerivAt_zero Φ.isOpen_time Φ.isPreconnected_time Φ.zero_mem_time
    (t := t) (f := fun r ↦ ⟪Φ.momentum (r, s), v⟫_ℝ) _ ht
  intro r hr
  have hd := (Φ.momentum_hasDerivAt hr hs).inner ℝ (hasDerivAt_const r v)
  simpa [frozenSymbol_hx_eq_zero (Φ.state_mem r hr s hs)] using hd

/-- Euler's identity integrates to the positive-sign full-energy phase
formula along the frozen flow (`app:lem:common-hamilton-phase`). -/
theorem frozenFlow_affine_pairing {n : ℕ}
    (Φ : HamiltonFlow (frozenSymbol n) (Euclidean (n - 1)))
    {t : ℝ} (ht : t ∈ Φ.time) {s : InitialData (Euclidean (n - 1))}
    (hs : s ∈ Φ.parameters) :
    ⟪Φ.momentum (0, s), Φ.position (t, s)⟫_ℝ = s.2.1 * t + ⟪s.1, s.2.2⟫_ℝ := by
  have hc := conserved_of_hasDerivAt_zero Φ.isOpen_time Φ.isPreconnected_time
    Φ.zero_mem_time (f := fun r ↦ ⟪Φ.momentum (0, s), Φ.position (r, s)⟫_ℝ - s.2.1 * r)
    (fun r hr ↦ ?_) ht
  · simpa [Φ.initial_position s hs, Φ.initial_momentum s hs s.1, real_inner_comm, add_comm]
      using (sub_eq_iff_eq_add.mp hc)
  have hd := ((hasDerivAt_const r (Φ.momentum (0, s))).inner ℝ
    (Φ.position_hasDerivAt hr hs)).sub ((hasDerivAt_id r).const_mul s.2.1)
  have he : ⟪Φ.momentum (0, s),
      (frozenSymbol n).hp (Φ.position (r, s), Φ.momentum (r, s))⟫_ℝ = s.2.1 := by
    rw [← frozenFlow_momentum_eq_initial Φ hr hs]
    exact ((frozenSymbol n).euler (Φ.state_mem r hr s hs)).trans (Φ.energy hr hs)
  convert! hd using 1
  simp [he]

end JanetCartan.ActualCarriers.FrozenPhaseReference
