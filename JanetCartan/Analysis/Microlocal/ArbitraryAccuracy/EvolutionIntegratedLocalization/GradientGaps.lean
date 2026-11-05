module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.Stationarity
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.Localizers.Gaps
public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.PackedPhase

/-!
# Compact buffered gaps for the actual elapsed phase

For `app:ch_regular:lem:finite-chain`, the interior buffer protects only
zero-characteristic flow segments, while the boundary buffer protects the
full diagonal. Compactness gives a positive full-gradient gap and a uniform
tangential gap in a fixed collar. The continuity inputs concern the actual
first derivatives on the indicated compact family, not a global phase
extension. The parent supplies that family and the buffered proof masks.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology

namespace JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization

open RegularSector.Characteristic
open RegularSector.Characteristic.EvolutionIntegral
open FiniteChain.Graph

variable {d : ℕ}

/-- The oriented zero-characteristic relation of the actual elapsed flow.
For the literal adjoint the original source is the output. This relation
does not include arbitrary-energy graphs (`app:ch_regular:lem:finite-chain`). -/
def zeroEnergyFlowRelation (backward : Bool) (h : RootState (Euclidean d) → ℝ)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)) (r : ℝ)
    (source target : Euclidean (d + 1) × Euclidean (d + 1)) : Prop :=
  if backward then rootSuspension h target = 0 ∧
    source = rootSuspensionState h 0 (Φ (spacetimeRootState target, r))
  else rootSuspension h source = 0 ∧
    target = rootSuspensionState h 0 (Φ (spacetimeRootState source, r))

/-- Every full critical point lies on the correct oriented zero-energy
relation, in the original physical coordinates
(`app:ch_regular:eq:joint-stationary`). -/
theorem zeroEnergyFlowRelation_of_stationary
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    (hC : (C : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) = twoTimeProjection Φ)
    (backward : Bool) (x y : Euclidean (d + 1)) (r : ℝ)
    (p : JointVariables (Euclidean (d + 1)))
    (hq : elapsedChartPoint r p.1.1 p.2.1 ∈ C.target)
    (hclock : (twoTimeState Φ (C.symm (elapsedChartPoint r p.1.1 p.2.1))).1 = p.1.1 0)
    (hphase : HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C (elapsedChartPoint r p.1.1 p.2.1))
      (elapsedChartPoint r p.1.1 p.2.1))
    (hzero : fderiv ℝ (jointElapsedPhase backward (chartPhase C) x y) (r, p) = 0) :
    zeroEnergyFlowRelation backward h Φ r (y, p.2.2.1) (x, p.2.2.2) := by
  cases backward
  · obtain ⟨hf, he, _⟩ := forward_interior_stationary_flow hC x y r p hq hclock hphase hzero
    exact ⟨he, hf⟩
  · obtain ⟨hf, he, _⟩ := reverse_interior_stationary_flow hC x y r p hq hclock hphase hzero
    exact ⟨he, hf⟩

/-- A buffered zero-characteristic image excludes zeros of the full joint
derivative. The hypothesis protects precisely the stationary interior
relation, including closed input shoulders and the output complement
(`app:ch_regular:eq:chain-tail`). The parent constructs these geometric masks. -/
theorem fderiv_jointElapsedPhase_ne_zero_of_buffer
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    (hC : (C : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) = twoTimeProjection Φ)
    (backward : Bool) {mi mo : LocalizerSymbol (d + 1)}
    {R : Set (Euclidean (d + 1) × Euclidean (d + 1))} (r : ℝ)
    (hbuffer : ∀ a ∈ tsupport mi, ∀ b ∈ R, zeroEnergyFlowRelation backward h Φ r a b →
      b ∈ interior {q | mo q = 1})
    (x y : Euclidean (d + 1)) (p : JointVariables (Euclidean (d + 1)))
    (hq : elapsedChartPoint r p.1.1 p.2.1 ∈ C.target)
    (hclock : (twoTimeState Φ (C.symm (elapsedChartPoint r p.1.1 p.2.1))).1 = p.1.1 0)
    (hphase : HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C (elapsedChartPoint r p.1.1 p.2.1))
      (elapsedChartPoint r p.1.1 p.2.1))
    (hin : (y, p.2.2.1) ∈ tsupport mi) (hR : (x, p.2.2.2) ∈ R)
    (hout : (x, p.2.2.2) ∈ tsupport (fun q ↦ 1 - mo q)) :
    fderiv ℝ (jointElapsedPhase backward (chartPhase C) x y) (r, p) ≠ 0 := by
  intro hzero
  exact notMem_complement_tsupport_of_mem_plateau
    (hbuffer _ hin _ hR
      (zeroEnergyFlowRelation_of_stationary hC backward x y r p hq hclock hphase hzero)) hout

/-- The diagonal buffer excludes tangential stationary points at the genuine
boundary. No characteristic energy restriction is made there
(`app:ch_regular:lem:finite-chain`). -/
theorem fderiv_jointElapsedPhase_boundary_ne_zero_of_buffer
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    (hC : (C : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) = twoTimeProjection Φ)
    (backward : Bool) {mi mo : LocalizerSymbol (d + 1)}
    (hbuffer : tsupport mi ⊆ interior {q | mo q = 1})
    (x y : Euclidean (d + 1)) (p : JointVariables (Euclidean (d + 1)))
    (hq : elapsedChartPoint 0 p.1.1 p.2.1 ∈ C.target)
    (hi : Φ ((C.symm (elapsedChartPoint 0 p.1.1 p.2.1)).2, 0) =
      (C.symm (elapsedChartPoint 0 p.1.1 p.2.1)).2)
    (hphase : HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C (elapsedChartPoint 0 p.1.1 p.2.1))
      (elapsedChartPoint 0 p.1.1 p.2.1))
    (hin : (y, p.2.2.1) ∈ tsupport mi)
    (hout : (x, p.2.2.2) ∈ tsupport (fun q ↦ 1 - mo q)) :
    fderiv ℝ (fun w ↦ jointElapsedPhase backward (chartPhase C) x y (0, w)) p ≠ 0 := by
  intro hzero
  obtain ⟨hx, hξ⟩ := boundary_stationary_diagonal hC backward x y p hq hi hphase hzero
  rw [hx, hξ] at hout
  exact notMem_complement_tsupport_of_mem_plateau (hbuffer hin) hout

private theorem exists_positive_collar {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) (G : X × ℝ → ℝ)
    (hcont : ∀ t ∈ K, ContinuousAt G (t, 0)) (hpos : ∀ t ∈ K, 0 < G (t, 0)) :
    ∃ ε > 0, ∃ δ > 0, ∀ t ∈ K, ∀ r : ℝ, |r| ≤ ε → δ ≤ G (t, r) := by
  have hc : ContinuousOn (fun t ↦ G (t, 0)) K := by
    intro t ht
    have he : ContinuousAt (fun s : X ↦ (s, (0 : ℝ))) t :=
      (continuous_id.prodMk continuous_const).continuousAt
    exact ((hcont t ht).comp (f := fun s : X ↦ (s, (0 : ℝ))) he).continuousWithinAt
  obtain ⟨δ, hδ, hgap⟩ := CompatibleResponse.exists_uniform_positive_bound hK hc hpos
  have hsub : K ×ˢ ({0} : Set ℝ) ⊆ interior {w | δ / 2 < G w} := by
    rintro ⟨t, r⟩ ⟨ht, hr⟩
    have hr0 : r = 0 := mem_singleton_iff.mp hr
    subst r
    apply mem_interior_iff_mem_nhds.mpr
    exact (hcont t ht).preimage_mem_nhds (Ioi_mem_nhds (by linarith [hgap t ht]))
  obtain ⟨U, V, _, hV, hKU, h0V, hUV⟩ :=
    generalized_tube_lemma hK isCompact_singleton isOpen_interior hsub
  have hz : (0 : ℝ) ∈ V := h0V (mem_singleton 0)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hz)
  refine ⟨ε / 2, half_pos hε, δ / 2, half_pos hδ, ?_⟩
  intro t ht r hr
  have hrV : r ∈ V := hball (by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using
      hr.trans_lt (half_lt_self hε))
  have hm : (t, r) ∈ interior {w | δ / 2 < G w} := hUV ⟨hKU ht, hrV⟩
  exact (interior_subset (s := {w : X × ℝ | δ / 2 < G w}) hm).le

/-- A compact family of the actual boundary derivatives gives a tangential
squared-gradient gap in a fixed collar. Continuity is required only at the
boundary points of that family; the positive collar is constructed, not
assumed. The preceding boundary-buffer theorem supplies `hboundary`
(`app:ch_regular:lem:finite-chain`). -/
theorem exists_jointElapsedPhase_boundary_collar_gap
    {X ι : Type*} [TopologicalSpace X] [Fintype ι]
    {K : Set X} (hK : IsCompact K)
    (e : Module.Basis ι ℝ (JointVariables (Euclidean (d + 1))))
    (backward : Bool) (Ψ : X → TwoTimePhase d) (x y : X → Euclidean (d + 1))
    (p : X → JointVariables (Euclidean (d + 1)))
    (hcont : ∀ t ∈ K, ContinuousAt (fun tr : X × ℝ ↦
      fderiv ℝ (fun w ↦ jointElapsedPhase backward (Ψ tr.1) (x tr.1) (y tr.1)
        (tr.2, w)) (p tr.1)) (t, 0))
    (hboundary : ∀ t ∈ K,
      fderiv ℝ (fun w ↦ jointElapsedPhase backward (Ψ t) (x t) (y t) (0, w)) (p t) ≠ 0) :
    ∃ ε > 0, ∃ δ > 0, ∀ t ∈ K, ∀ r : ℝ, |r| ≤ ε →
      δ ≤ Localization.phaseGradientSquare e
        (fun w ↦ jointElapsedPhase backward (Ψ t) (x t) (y t) (r, w)) (p t) := by
  apply exists_positive_collar hK
    (fun tr : X × ℝ ↦ Localization.phaseGradientSquare e
      (fun w ↦ jointElapsedPhase backward (Ψ tr.1) (x tr.1) (y tr.1) (tr.2, w)) (p tr.1))
  · intro t ht
    unfold Localization.phaseGradientSquare
    exact tendsto_finsetSum _ (fun i _ ↦ ((hcont t ht).clm_apply continuousAt_const).pow 2)
  · intro t ht
    exact (FiniteChain.Retarded.phaseGradientSquare_basis_pos_iff _ _ _).mpr (hboundary t ht)

/-- The full-gradient gap is uniform on the entire compact interior family.
The previous zero-energy buffer theorem supplies `hinterior`; continuity
comes from the supported two-time first derivatives. The constant is chosen
before frequency and integration order (`app:ch_regular:eq:chain-tail`). -/
theorem exists_jointElapsedPhase_interior_gap
    {X ι : Type*} [TopologicalSpace X] [Fintype ι]
    {K : Set X} (hK : IsCompact K)
    (e : Module.Basis ι ℝ (ℝ × JointVariables (Euclidean (d + 1))))
    (backward : Bool) (Ψ : X → TwoTimePhase d) (x y : X → Euclidean (d + 1))
    (p : X → ℝ × JointVariables (Euclidean (d + 1)))
    (hcont : ContinuousOn (fun t ↦
      fderiv ℝ (jointElapsedPhase backward (Ψ t) (x t) (y t)) (p t)) K)
    (hinterior : ∀ t ∈ K,
      fderiv ℝ (jointElapsedPhase backward (Ψ t) (x t) (y t)) (p t) ≠ 0) :
    ∃ δ > 0, ∀ t ∈ K, δ ≤ Localization.phaseGradientSquare e
      (jointElapsedPhase backward (Ψ t) (x t) (y t)) (p t) := by
  apply CompatibleResponse.exists_uniform_positive_bound hK
  · unfold Localization.phaseGradientSquare
    exact continuousOn_finsetSum _ (fun i _ ↦ (hcont.clm_apply continuousOn_const).pow 2)
  · intro t ht
    exact (FiniteChain.Retarded.phaseGradientSquare_basis_pos_iff _ _ _).mpr (hinterior t ht)

/-- The two actual gradient gaps assembled directly from compact buffered
separation. The parent supplies the compact coefficient/chart family and
the diagonal and zero-characteristic image buffers; `EvolutionRelation`
supplies the chart differential and flow identities. No gap or successful
kernel estimate is a premise. Both orientations use the literal joint phase
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_buffered_jointElapsedPhase_gradient_gaps
    {X ι κ : Type*} [TopologicalSpace X] [Fintype ι] [Fintype κ]
    {K : Set X} (hK : IsCompact K)
    (eT : Module.Basis ι ℝ (JointVariables (Euclidean (d + 1))))
    (eI : Module.Basis κ ℝ (ℝ × JointVariables (Euclidean (d + 1))))
    (h : X → RootState (Euclidean d) → ℝ)
    (Φ : X → RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (C : X → OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (backward : Bool) (x y : X → Euclidean (d + 1)) (r : X → ℝ)
    (p : X → JointVariables (Euclidean (d + 1)))
    (hC : ∀ t ∈ K, (C t : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) =
      twoTimeProjection (Φ t))
    (hqB : ∀ t ∈ K, elapsedChartPoint 0 (p t).1.1 (p t).2.1 ∈ (C t).target)
    (hi : ∀ t ∈ K, Φ t (((C t).symm (elapsedChartPoint 0 (p t).1.1 (p t).2.1)).2, 0) =
      ((C t).symm (elapsedChartPoint 0 (p t).1.1 (p t).2.1)).2)
    (hphaseB : ∀ t ∈ K, HasFDerivAt (twoTimePhase (C t))
      (twoTimePhaseDifferential (h t) (Φ t) (C t) (elapsedChartPoint 0 (p t).1.1 (p t).2.1))
      (elapsedChartPoint 0 (p t).1.1 (p t).2.1))
    (hqI : ∀ t ∈ K, elapsedChartPoint (r t) (p t).1.1 (p t).2.1 ∈ (C t).target)
    (hclock : ∀ t ∈ K,
      (twoTimeState (Φ t) ((C t).symm (elapsedChartPoint (r t) (p t).1.1 (p t).2.1))).1 =
        (p t).1.1 0)
    (hphaseI : ∀ t ∈ K, HasFDerivAt (twoTimePhase (C t))
      (twoTimePhaseDifferential (h t) (Φ t) (C t)
        (elapsedChartPoint (r t) (p t).1.1 (p t).2.1))
      (elapsedChartPoint (r t) (p t).1.1 (p t).2.1))
    {mi mo : LocalizerSymbol (d + 1)}
    {R : Set (Euclidean (d + 1) × Euclidean (d + 1))}
    (hdiag : tsupport mi ⊆ interior {q | mo q = 1})
    (hflow : ∀ t ∈ K, ∀ a ∈ tsupport mi, ∀ b ∈ R,
      zeroEnergyFlowRelation backward (h t) (Φ t) (r t) a b → b ∈ interior {q | mo q = 1})
    (hin : ∀ t ∈ K, (y t, (p t).2.2.1) ∈ tsupport mi)
    (hR : ∀ t ∈ K, (x t, (p t).2.2.2) ∈ R)
    (hout : ∀ t ∈ K, (x t, (p t).2.2.2) ∈ tsupport (fun q ↦ 1 - mo q))
    (hcontB : ∀ t ∈ K, ContinuousAt (fun tr : X × ℝ ↦
      fderiv ℝ (fun w ↦ jointElapsedPhase backward (chartPhase (C tr.1)) (x tr.1) (y tr.1)
        (tr.2, w)) (p tr.1)) (t, 0))
    (hcontI : ContinuousOn (fun t ↦
      fderiv ℝ (jointElapsedPhase backward (chartPhase (C t)) (x t) (y t)) (r t, p t)) K) :
    ∃ ε > 0, ∃ δT > 0, ∃ δI > 0, ∀ t ∈ K,
      (∀ s : ℝ, |s| ≤ ε → δT ≤ Localization.phaseGradientSquare eT
        (fun w ↦ jointElapsedPhase backward (chartPhase (C t)) (x t) (y t) (s, w)) (p t)) ∧
      δI ≤ Localization.phaseGradientSquare eI
        (jointElapsedPhase backward (chartPhase (C t)) (x t) (y t)) (r t, p t) := by
  obtain ⟨ε, hε, δT, hδT, hT⟩ := exists_jointElapsedPhase_boundary_collar_gap
    hK eT backward (fun t ↦ chartPhase (C t)) x y p hcontB (fun t ht ↦
      fderiv_jointElapsedPhase_boundary_ne_zero_of_buffer (hC t ht) backward hdiag
        (x t) (y t) (p t) (hqB t ht) (hi t ht) (hphaseB t ht) (hin t ht) (hout t ht))
  obtain ⟨δI, hδI, hI⟩ := exists_jointElapsedPhase_interior_gap
    hK eI backward (fun t ↦ chartPhase (C t)) x y (fun t ↦ (r t, p t)) hcontI (fun t ht ↦
      fderiv_jointElapsedPhase_ne_zero_of_buffer (hC t ht) backward (r t) (hflow t ht)
        (x t) (y t) (p t) (hqI t ht) (hclock t ht) (hphaseI t ht)
        (hin t ht) (hR t ht) (hout t ht))
  exact ⟨ε, hε, δT, hδT, δI, hδI, fun t ht ↦ ⟨hT t ht, hI t ht⟩⟩

end JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
