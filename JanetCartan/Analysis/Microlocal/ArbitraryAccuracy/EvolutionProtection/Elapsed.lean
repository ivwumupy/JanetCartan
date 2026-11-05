module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionRelation
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionProtection.Segments

/-!
# The actual elapsed stationary relation gives complete direct root segments

The interior branch uses the proved source-energy equation of the two-time
phase. The boundary branch uses its full diagonal identity. Neither branch is
identified with the old fixed-transverse retarded operator. Whole root-domain
and physical-domain conditions remain explicit, in both elapsed orientations.
Consumer: complete-chain localization in `app:ch_regular:lem:finite-chain`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set
open scoped ContDiff Topology InnerProductSpace

namespace JanetCartan.ArbitraryAccuracy
open RegularSector.Characteristic
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.KernelIdentification

variable {n d : ℕ}

/-- Convert the literal time/space coordinates of the elapsed phase back to
the retained physical coordinates. Its use on both bases and covectors is
canonical only with the pairing identity below
(`app:ch_regular:lem:finite-chain`). -/
def adaptedPhysicalPhaseState (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (z : Euclidean (d + 1) × Euclidean (d + 1)) : Euclidean n × Euclidean n :=
  (e.symm (z.1 0, spatialPart z.1), e.symm (z.2 0, spatialPart z.2))

/-- The exact coordinate pairing required to transport the elapsed canonical
relation. The sector producer must establish `hpair` for its chosen adapted
coordinates; invertibility alone is insufficient
(`app:ch_regular:lem:finite-chain`). -/
theorem adaptedPhysicalPhaseState_pairing
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (hpair : ∀ u v : ℝ × Euclidean d,
      ⟪e.symm u, e.symm v⟫_ℝ = u.1 * v.1 + ⟪u.2, v.2⟫_ℝ)
    (z : Euclidean (d + 1) × Euclidean (d + 1)) :
    ⟪(adaptedPhysicalPhaseState e z).1, (adaptedPhysicalPhaseState e z).2⟫_ℝ =
      ⟪z.1, z.2⟫_ℝ := by
  rw [inner_eq_time_add_spatial]
  exact hpair _ _

/-- Orthogonal physical coordinates discharge the precise pairing premise.
This is applicable when the sector's retained coordinate inverse is the
literal time/space recombination followed by its orthogonal change of frame
(`app:ch_regular:thm:no-return`). -/
theorem adapted_pairing_of_orthogonal_recombination
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (A : Euclidean (d + 1) ≃ₗᵢ[ℝ] Euclidean n)
    (he : ∀ u : ℝ × Euclidean d, e.symm u = A (timeSpacePoint u.1 u.2))
    (u v : ℝ × Euclidean d) :
    ⟪e.symm u, e.symm v⟫_ℝ = u.1 * v.1 + ⟪u.2, v.2⟫_ℝ := by
  rw [he, he, A.inner_map_map, inner_eq_time_add_spatial]
  simp

/-- The zero-energy suspension has exactly the physical pencil root state
(`app:ch_regular:lem:finite-chain`). -/
@[simp] theorem adaptedPhysicalPhaseState_rootSuspensionState
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (h : RootState (Euclidean d) → ℝ) (w : RootState (Euclidean d)) :
    adaptedPhysicalPhaseState e (rootSuspensionState h 0 w) = physicalPencilRootState e h w := by
  simp [adaptedPhysicalPhaseState, rootSuspensionState, physicalPencilRootState]

/-- The physical velocity used in the pencil comparison is exactly the
pushforward of the already derived Hamilton field of `τ-h`. This identifies
the fields themselves, not just their position components
(`app:ch_regular:thm:no-return`). -/
@[simp] theorem adaptedPhysicalPhaseState_rootSuspensionField
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (h : RootState (Euclidean d) → ℝ) (w : RootState (Euclidean d)) :
    adaptedPhysicalPhaseState e (rootSuspensionField h (rootSuspensionState h 0 w)) =
      physicalPencilRootVelocity e h w := by
  simp [adaptedPhysicalPhaseState, rootSuspensionField, physicalPencilRootVelocity]

/-- A zero source-energy point is the root lift of its own spatial state
(`app:ch_regular:lem:finite-chain`). -/
theorem adaptedPhysicalPhaseState_eq_root_of_zero_energy
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (h : RootState (Euclidean d) → ℝ) (z : Euclidean (d + 1) × Euclidean (d + 1))
    (hz : rootSuspension h z = 0) :
    adaptedPhysicalPhaseState e z = physicalPencilRootState e h (spacetimeRootState z) := by
  have ht : z.2 0 = h (spacetimeRootState z) := sub_eq_zero.mp hz
  simp only [adaptedPhysicalPhaseState, physicalPencilRootState, spacetimeRootState] at *
  rw [ht]

/-- Reversing a complete root segment retains its entire curve and both
domain conditions (`app:ch_regular:lem:finite-chain`, adjoint orientation). -/
theorem CompletePencilRootSegment.symm
    {e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d)}
    {h : RootState (Euclidean d) → ℝ} {D : Set (RootState (Euclidean d))}
    {W : Set (Euclidean n)} {z w : Euclidean n × Euclidean n}
    (hseg : CompletePencilRootSegment e h D W z w) :
    CompletePencilRootSegment e h D W w z := by
  obtain ⟨Z, a, b, t₀, t₁, ht₀, ht₁, hZ, hZD, hZW, hz, hw⟩ := hseg
  exact ⟨Z, a, b, t₁, t₀, ht₁, ht₀, hZ, hZD, hZW, hw, hz⟩

/-- Interior elapsed stationarity produces a whole zero-energy direct root
segment of the actual two-time flow. The interval is `[min 0 r,max 0 r]`, so
negative elapsed times and reversed relations require no positivity convention.
The root ODE and clock come from the local two-time flow constructor; its
whole-domain restrictions are retained explicitly
(`app:ch_regular:lem:finite-chain`). -/
theorem elapsed_stationary_completePencilRootSegment
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    {h : RootState (Euclidean d) → ℝ} {D : Set (RootState (Euclidean d))}
    {W : Set (Euclidean n)}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    (hC : (C : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) = twoTimeProjection Φ)
    {r : ℝ} {z ξ x ζ : Euclidean (d + 1)}
    (hq : elapsedChartPoint r x ξ ∈ C.target)
    (hclock : (twoTimeState Φ (C.symm (elapsedChartPoint r x ξ))).1 = x 0)
    (hphase : HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C (elapsedChartPoint r x ξ)) (elapsedChartPoint r x ξ))
    (hrel : FiniteChain.Graph.ForwardRelation (elapsedPhase (chartPhase C) r) z ξ x ζ)
    (hstationary : deriv (fun u ↦ elapsedPhase (chartPhase C) u x ξ) r = 0)
    (hi : Φ (spacetimeRootState (z, ξ), 0) = spacetimeRootState (z, ξ))
    (hode : ∀ t ∈ Icc (min 0 r) (max 0 r),
      HasDerivAt (fun u ↦ Φ (spacetimeRootState (z, ξ), u))
        (rootHamiltonField h (Φ (spacetimeRootState (z, ξ), t))) t)
    (hdom : ∀ t ∈ Icc (min 0 r) (max 0 r), Φ (spacetimeRootState (z, ξ), t) ∈ D)
    (hphysical : ∀ t ∈ Icc (min 0 r) (max 0 r),
      (physicalPencilRootState e h (Φ (spacetimeRootState (z, ξ), t))).1 ∈ W) :
    CompletePencilRootSegment e h D W
      (adaptedPhysicalPhaseState e (z, ξ)) (adaptedPhysicalPhaseState e (x, ζ)) := by
  have henergy := elapsed_graph_interior_stationary_energy hphase hrel hstationary
  have hflow := (forwardRelation_elapsedChartPhase_flow hC hq hclock hphase hrel).1
  rw [henergy] at hflow
  refine ⟨fun u ↦ Φ (spacetimeRootState (z, ξ), u), min 0 r, max 0 r, 0, r,
    ⟨min_le_left _ _, le_max_left _ _⟩, ⟨min_le_right _ _, le_max_right _ _⟩,
    hode, hdom, hphysical, ?_, ?_⟩
  · dsimp only
    rw [hi]
    exact adaptedPhysicalPhaseState_eq_root_of_zero_energy e h _ henergy
  · rw [hflow, adaptedPhysicalPhaseState_rootSuspensionState]

/-- The zero-elapsed boundary branch remains the FULL diagonal in physical
coordinates, including its covector. Its proof uses the actual inverse chart
and root-flow initial condition (`app:ch_regular:lem:finite-chain`). -/
theorem elapsed_boundary_physical_diagonal
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    (hC : (C : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) = twoTimeProjection Φ)
    {z ξ x ζ : Euclidean (d + 1)} (hq : elapsedChartPoint 0 x ξ ∈ C.target)
    (hi : Φ ((C.symm (elapsedChartPoint 0 x ξ)).2, 0) = (C.symm (elapsedChartPoint 0 x ξ)).2)
    (hphase : HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C (elapsedChartPoint 0 x ξ)) (elapsedChartPoint 0 x ξ))
    (hrel : FiniteChain.Graph.ForwardRelation (elapsedPhase (chartPhase C) 0) z ξ x ζ) :
    adaptedPhysicalPhaseState e (z, ξ) = adaptedPhysicalPhaseState e (x, ζ) := by
  obtain ⟨rfl, rfl⟩ := elapsed_graph_zero_diagonal hC hq hi hphase hrel
  rfl

end JanetCartan.ArbitraryAccuracy
