module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.FrozenPhaseReference.NeighborhoodConstruction.FlowIdentities

/-!
# Canonical momentum of the retained frozen chart

The only extra input is injectivity of the energy/tangential-momentum map on
the fixed state ball. The scalar-root buffer construction must supply this
input before these deductions give a local reference
(`app:lem:common-hamilton-phase`, `app:ch_seed:prop:seed-actual-menu`, Step 1).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff InnerProductSpace

namespace JanetCartan.ActualCarriers.FrozenPhaseReference
open HamiltonPhase

variable {n : ℕ} {ξ : Euclidean n} {a : AdaptedSection ξ}
  {D : Set (Euclidean n × Euclidean n)} {R : ℝ}
  (F : FrozenHamiltonFamily a.embedding a.normal a.baseData ⟪a.normal, ξ⟫_ℝ D R)

/-- Every canonical covector occurring in the target also admits the initial
datum with zero tangential position. This uses the retained source buffers
(`app:lem:common-hamilton-phase`). -/
theorem FrozenHamiltonFamily.canonicalDatum_mem {q : Euclidean n × (ℝ × Euclidean (n - 1))}
    (hq : q ∈ F.chart.target) : (0, q.2) ∈ F.flow.parameters := by
  have hb := F.reference_control.source_subset (F.chart.maps_to_source q hq)
  have hdist : dist q.2 a.baseData.2 < 2 * F.sourceRadius := by
    rw [mem_ball, Prod.dist_eq, max_lt_iff] at hb
    have hh := hb.2
    rw [Prod.dist_eq, max_lt_iff] at hh
    exact hh.2
  have hsmall : ((0 : ℝ), ((0 : Euclidean (n - 1)), q.2)) ∈
      ball ((0 : ℝ), a.baseData) (3 * F.sourceRadius) := by
    have hr := F.sourceRadius_pos
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    refine ⟨by simpa using (by linarith : 0 < 3 * F.sourceRadius), ?_⟩
    rw [Prod.dist_eq, max_lt_iff]
    refine ⟨?_, hdist.trans (by linarith : 2 * F.sourceRadius < 3 * F.sourceRadius)⟩
    simpa [AdaptedSection.baseData] using (by linarith : 0 < 3 * F.sourceRadius)
  exact (F.reference_control.source_admissible (subset_closure hsmall)).2

/-- The retained fixed state ball bounds each initial momentum around `ξ`
(`app:lem:common-hamilton-phase`). -/
theorem FrozenHamiltonFamily.initialMomentum_mem {s : InitialData (Euclidean (n - 1))}
    (hs : s ∈ F.flow.parameters) : F.flow.momentum (0, s) ∈ closedBall ξ R := by
  have h := F.reference_control.state_mem (0, s) ⟨F.flow.zero_mem_time, hs⟩
  rw [a.baseState_eq] at h
  rw [mem_closedBall, Prod.dist_eq, max_le_iff] at h
  exact h.2

/-- The tangential part of the actual initial momentum is the prescribed
canonical covector (`app:lem:common-hamilton-phase`). -/
theorem FrozenHamiltonFamily.initialMomentum_adjoint {s : InitialData (Euclidean (n - 1))}
    (hs : s ∈ F.flow.parameters) :
    a.embedding.toContinuousLinearMap.adjoint (F.flow.momentum (0, s)) = s.2.2 := by
  apply ext_inner_right ℝ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_left, ← F.reference_control.section_eq]
  exact F.flow.initial_momentum s hs v

/-- Initial energy can be evaluated at physical position zero because the
frozen symbol is independent of position (`app:lem:common-hamilton-phase`). -/
theorem FrozenHamiltonFamily.initialMomentum_energy {s : InitialData (Euclidean (n - 1))}
    (hs : s ∈ F.flow.parameters) :
    (frozenSymbol n).h (0, F.flow.momentum (0, s)) = s.2.1 := by
  simpa only [frozenSymbol_h] using F.flow.initial_energy s hs

/-- The reference covector is obtained by evaluating the same retained flow
at time zero and tangential position zero (`app:ch_seed:prop:seed-actual-menu`). -/
def FrozenHamiltonFamily.canonicalMomentum (η : ℝ × Euclidean (n - 1)) : Euclidean n :=
  F.flow.momentum (0, (0, η))

/-- Scalar-root uniqueness removes the initial tangential-position dependence
of the frozen momentum (`app:lem:common-hamilton-phase`). -/
theorem FrozenHamiltonFamily.initialMomentum_eq_canonical
    (hinj : Set.InjOn (fun p : Euclidean n ↦
      ((frozenSymbol n).h (0, p), a.embedding.toContinuousLinearMap.adjoint p))
      (closedBall ξ R)) {s : InitialData (Euclidean (n - 1))}
    (hs : s ∈ F.flow.parameters) (hzero : (0, s.2) ∈ F.flow.parameters) :
    F.flow.momentum (0, s) = F.canonicalMomentum s.2 := by
  apply hinj (F.initialMomentum_mem hs) (F.initialMomentum_mem hzero)
  exact Prod.ext ((F.initialMomentum_energy hs).trans (F.initialMomentum_energy hzero).symm)
    ((F.initialMomentum_adjoint hs).trans (F.initialMomentum_adjoint hzero).symm)

/-- The positive-sign affine phase identity holds on the entire retained
target, including nonzero energy (`app:lem:common-hamilton-phase`). -/
theorem FrozenHamiltonFamily.phase_eq_canonicalMomentum
    (hinj : Set.InjOn (fun p : Euclidean n ↦
      ((frozenSymbol n).h (0, p), a.embedding.toContinuousLinearMap.adjoint p))
      (closedBall ξ R)) {q : Euclidean n × (ℝ × Euclidean (n - 1))}
    (hq : q ∈ F.chart.target) :
    phase F.chart.coordinates q = ⟪F.canonicalMomentum q.2, q.1⟫_ℝ := by
  have ha := F.chart.source_admissible _ (F.chart.maps_to_source q hq)
  have hp := F.initialMomentum_eq_canonical hinj ha.2 (F.canonicalDatum_mem hq)
  have he := frozenFlow_affine_pairing F.flow ha.1 ha.2
  rw [hp, F.chart.right_inverse q hq] at he
  exact he.symm

/-- Root uniqueness identifies the actual canonical momentum with each
characteristic covector in the state ball, provided its canonical datum is
admissible (`app:ch_seed:prop:seed-actual-menu`, Step 1). -/
theorem FrozenHamiltonFamily.canonicalMomentum_eq_of_characteristic
    (hinj : Set.InjOn (fun p : Euclidean n ↦
      ((frozenSymbol n).h (0, p), a.embedding.toContinuousLinearMap.adjoint p))
      (closedBall ξ R)) {p : Euclidean n} (hp : p ∈ closedBall ξ R)
    (hchar : cubeDeterminant p = 0)
    (hparam : (0, (0, a.embedding.toContinuousLinearMap.adjoint p)) ∈ F.flow.parameters) :
    F.canonicalMomentum (0, a.embedding.toContinuousLinearMap.adjoint p) = p := by
  apply hinj (F.initialMomentum_mem hparam) hp
  refine Prod.ext ?_ (F.initialMomentum_adjoint hparam)
  dsimp only
  rw [F.initialMomentum_energy hparam, frozenSymbol_h, hchar, mul_zero]

end JanetCartan.ActualCarriers.FrozenPhaseReference
