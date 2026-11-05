module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ConicPhase.Differential
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ConicPhase.AngularGeometry
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ConicPhase.ContinuousExtension

/-!
# Supported agreement, diagonal data and both conic time identities

These deductions use the SAME chart, flow and root from
`exists_buffered_physical_pencil_kernel`. The root scaling premise is exactly
that produced by `exists_pencilRoot_domain`; the sector constructor must retain
it through that same witness. No extended eikonal equation is assumed.
Source: `app:ch_regular_base:lem:characteristic-kernel` and
`app:ch_regular_base:lem:retarded-kernel` in `paper-v2.tex`.
-/

@[expose] public noncomputable section
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace
namespace JanetCartan.RegularSector.Characteristic.ConicPhase
open FourierIntegral EvolutionIntegral
variable {d m : ℕ}

/-- The actual elapsed cone normalizes into the original closed buffer
(`app:ch_regular_base:eq:fixed-time-representation`). -/
theorem elapsed_mem_domain_closedBuffer (ℓ : Euclidean d →L[ℝ] ℝ)
    {z : RootState (Euclidean d)} {ε r : ℝ} (hε : 0 < ε) (hr : r ∈ Icc 0 ε)
    {x : Euclidean (d + 1)} (hx : x ∈ elapsedPhysicalBox z ε)
    {η : Euclidean d} (hη : η ∈ angularCone ℓ z.2.2 ε) :
    (x 0, (x 0 - r, (spatialPart x, η))) ∈ domain ℓ (closedBall (z.1, z) (2 * ε)) :=
  ⟨hη.1, elapsedPoint_mem_twoTime_buffer hε hr hx hη.2⟩

/-- On the original local overlap the continuation retains the full joint
germ, not just its value (`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem phase_eventuallyEq_on_buffered_overlap (ℓ : Euclidean d →L[ℝ] ℝ)
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    {z : RootState (Euclidean d)} {ε r : ℝ} (hε : 0 < ε)
    (hbuffer : closedBall (z.1, z) (2 * ε) ⊆ C.target)
    (hdiff : ∀ q ∈ C.target,
      HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C q) q)
    (hr : r ∈ Icc 0 ε) {x : Euclidean (d + 1)} (hx : x ∈ elapsedPhysicalBox z ε)
    {η : Euclidean d} (hη : η ∈ angularCone ℓ z.2.2 ε)
    (hlocal : η ∈ ball z.2.2 (2 * ε)) :
    phase ℓ C =ᶠ[𝓝 (x 0, (x 0 - r, (spatialPart x, η)))] twoTimePhase C :=
  phase_eventuallyEq_on_overlap ℓ hdiff isOpen_ball isOpen_ball (convex_ball _ _)
    ((localPatch_bufferedBase_subset z ε).trans hbuffer)
    ⟨⟨elapsed_mem_bufferedBase hε hr hx, hlocal⟩,
      elapsed_mem_domain_bufferedBase ℓ hε hr hx hη⟩

/-- The local source diagonal gives the diagonal on every positive ray.
The radius comparison is ensured by the final assembly's fixed shrinking,
not an additional analytic premise (`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem phase_diagonal_on_buffer (ℓ : Euclidean d →L[ℝ] ℝ)
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    {z : RootState (Euclidean d)} {ε δ : ℝ} (hεδ : ε ≤ δ)
    (hdiag : ∀ w ∈ ball z.1 δ ×ˢ ball z.2 δ,
      twoTimePhase C (w.1, w) = ⟪w.2.1, w.2.2⟫_ℝ)
    {x : Euclidean (d + 1)} (hx : x ∈ elapsedPhysicalBox z ε)
    {η : Euclidean d} (hη : η ∈ angularCone ℓ z.2.2 ε) :
    phase ℓ C (x 0, (x 0, (spatialPart x, η))) = ⟪spatialPart x, η⟫_ℝ := by
  apply phase_diagonal ℓ C hη.1.ne'
  apply hdiag
  refine ⟨ball_subset_ball hεδ hx.1, ?_⟩
  simpa only [mem_ball, Prod.dist_eq, max_lt_iff] using
    And.intro (ball_subset_ball hεδ hx.2) (ball_subset_ball hεδ hη.2)

/-- Both eikonal identities throughout the actual elapsed cone. All domain
memberships are derived from the original transport buffer and diagonal.
The sole extra root premise is the exact positive-scaling conclusion of
`PencilRoot.exists_pencilRoot_domain`, for this SAME `D,h`.
Consumer: the characteristic branch in `app:ch_regular_base:lem:retarded-kernel`. -/
theorem phase_eikonal_on_buffer (ℓ : Euclidean d →L[ℝ] ℝ)
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    {D : Set (RootState (Euclidean d))} {I : Set ℝ} {U : Set (Euclidean d × Euclidean d)}
    {z : RootState (Euclidean d)} {ε r : ℝ} (hε : 0 < ε)
    (hbuffer : closedBall (z.1, z) (2 * ε) ⊆ C.target ∩ C.symm ⁻¹' (I ×ˢ (I ×ˢ U)))
    (hC : (C : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) = twoTimeProjection Φ)
    (hstate : ∀ q ∈ C.target, twoTimeState Φ (C.symm q) ∈ D ∧
      (twoTimeState Φ (C.symm q)).1 = q.1)
    (hdiff : ∀ q ∈ C.target,
      HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C q) q)
    (hdiag : ∀ w ∈ I ×ˢ U, (w.1, w) ∈ C.target ∧ twoTimeState Φ (C.symm (w.1, w)) = w)
    (hroot : ∀ w ∈ D, ∀ a : ℝ, 0 < a →
      (w.1, (w.2.1, a • w.2.2)) ∈ D ∧ h (w.1, (w.2.1, a • w.2.2)) = a * h w)
    (hr : r ∈ Icc 0 ε) {x : Euclidean (d + 1)} (hx : x ∈ elapsedPhysicalBox z ε)
    {η : Euclidean d} (hη : η ∈ angularCone ℓ z.2.2 ε) :
    deriv (fun t ↦ phase ℓ C (t, (x 0 - r, (spatialPart x, η)))) (x 0) =
      h (x 0, (spatialPart x,
        gradient (fun y ↦ phase ℓ C (x 0, (x 0 - r, (y, η)))) (spatialPart x))) ∧
    -deriv (fun s ↦ phase ℓ C (x 0, (s, (spatialPart x, η)))) (x 0 - r) =
      h (x 0 - r, (gradient (fun θ ↦ phase ℓ C (x 0, (x 0 - r, (spatialPart x, θ)))) η, η)) := by
  have hm := hbuffer (elapsed_mem_domain_closedBuffer ℓ hε hr hx hη).2
  have hs := root_states_mem_of_transport_buffer hC hstate hdiag hm.1 hm.2.2
  exact phase_eikonal_identities ℓ (hdiff _ hm.1) hroot hs.1 hs.2 hη.1

/-- The actual physical and angular mask supports suffice for equality of
the auxiliary graph and the same conic graph. The normalized-support
premise is discharged geometrically. Both masks and Fourier conventions
remain literal (`app:ch_regular_base:eq:fixed-time-representation`). -/
theorem elapsedGraph_eq_on_buffered_masks (ℓ : Euclidean d →L[ℝ] ℝ)
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    {z : RootState (Euclidean d)} {ε r : ℝ} (hε : 0 < ε)
    {G : TwoTimePoint (Euclidean d) → ℝ}
    (he : ∀ q ∈ domain ℓ (closedBall (z.1, z) (2 * ε)), G =ᶠ[𝓝 q] phase ℓ C)
    (b : TwoTimeAmplitude d m) (χout χsource β : Euclidean (d + 1) → ℂ)
    (hr : r ∈ Icc 0 ε)
    (hχ : Function.support χout ⊆ elapsedPhysicalBox z ε)
    (hβ : Function.support β ⊆ spatialPart ⁻¹' angularCone ℓ z.2.2 ε) :
    elapsedGraph (fun t s y η ↦ G (t, (s, (y, η)))) b χout χsource β r =
      elapsedGraph (curriedPhase ℓ C) b χout χsource β r :=
  elapsedGraph_eq_of_conic_extension_on_masks ℓ C he b χout χsource β r
    (fun _ _ hx hξ ↦ elapsed_mem_domain_closedBuffer ℓ hε hr (hχ hx) (hβ hξ))

end JanetCartan.RegularSector.Characteristic.ConicPhase
