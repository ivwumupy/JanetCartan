module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ConicPhase.AngularGeometry.Temporal

/-!
# Fixed angular margins and actual conic elapsed geometry

The exact local primitive from `exists_buffered_physical_pencil_kernel`
produces a linear section, open convex cone, inner margins, supported phase
geometry, whole-cone averaged-gradient injectivity, determinant gaps, and
finite uniform mixed inverse and temporal shear bounds. All objects are the
same continued phase `phase ℓ C`; no conic analytic bound is an input.

The constants here are for one fixed local phase. Uniform coefficient-family
estimates and the parent conic phase's eikonal and jet assembly are separate
obligations. Source: `app:ch_regular_base:lem:characteristic-kernel` and
`app:ch_regular_base:lem:retarded-kernel` in `paper-v2.tex`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.ConicPhase
open FourierIntegral EvolutionIntegral NormalComparison WholeImageGeometry
variable {d : ℕ}

/-- A fixed inner physical box has its closure in the outer elapsed box.
Consumer: the closed support input of the whole-image graph construction
in `app:ch_regular_base:lem:retarded-kernel`. -/
theorem closure_elapsedPhysicalBox_half_subset {z : RootState (Euclidean d)} {ε : ℝ}
    (hε : 0 < ε) : closure (elapsedPhysicalBox z (ε / 2)) ⊆ elapsedPhysicalBox z ε := by
  let K : Set (Euclidean (d + 1)) :=
    {x | x 0 ∈ closedBall z.1 (ε / 2) ∧ spatialPart x ∈ closedBall z.2.1 (ε / 2)}
  have hK : IsClosed K :=
    (isClosed_closedBall.preimage (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1))).continuous).inter
      (isClosed_closedBall.preimage spatialPartCLM.continuous)
  have hsub : elapsedPhysicalBox z (ε / 2) ⊆ K :=
    fun _ hx ↦ ⟨ball_subset_closedBall hx.1, ball_subset_closedBall hx.2⟩
  intro x hx
  have hm := closure_minimal hsub hK hx
  exact ⟨closedBall_subset_ball (by linarith) hm.1, closedBall_subset_ball (by linarith) hm.2⟩

/-- The inner lifted cone with any fixed positive spatial collar has its
closure inside the outer lifted cone. This is the exact frequency margin
used by `exists_fullGraphFamily_of_wholeImage_phase` in
`app:ch_regular_base:lem:retarded-kernel`. -/
theorem closure_lifted_angularCone_collar_subset (ℓ : Euclidean d →L[ℝ] ℝ)
    {η₀ : Euclidean d} {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) :
    closure (spatialPart ⁻¹' (angularCone ℓ η₀ (ε / 2) ∩ {η | c < ‖η‖})) ⊆
      spatialPart ⁻¹' angularCone ℓ η₀ ε :=
  (spatialPartCLM.continuous.closure_preimage_subset _).trans
    (preimage_mono (closure_angularCone_collar_subset (by linarith) hc))

/-- Assemble all geometric inputs of the conic elapsed graph from precisely
the original buffered primitive. The section and constants precede all
elapsed times, physical points, spatial rays, and temporal frequencies.
The producer of every local analytic premise is the SAME witness of
`exists_buffered_physical_pencil_kernel`; the parent must retain that witness
when assembling the eikonal and normalized jet conclusions.
Source: `app:ch_regular_base:lem:characteristic-kernel` and
`app:ch_regular_base:lem:retarded-kernel`. -/
theorem exists_angular_elapsed_geometry
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    {z : RootState (Euclidean d)} {ε : ℝ} (hε : 0 < ε) (hsmall : 2 * ε < ‖z.2.2‖)
    (hbuffer : closedBall (z.1, z) (2 * ε) ⊆ C.target)
    (hs : ContDiffOn ℝ ∞ (twoTimePhase C) C.target)
    (hdiff : ∀ q ∈ C.target,
      HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C q) q)
    (hnear : ∀ q ∈ closedBall (z.1, z) (2 * ε), ‖twoTimePhaseMixed C q - 1‖ ≤ 1 / 2) :
    ∃ ℓ : Euclidean d →L[ℝ] ℝ, ℓ z.2.2 = 1 ∧
      z.2.2 ∈ angularCone ℓ z.2.2 (ε / 2) ∧
      IsOpen (angularCone ℓ z.2.2 ε) ∧ Convex ℝ (angularCone ℓ z.2.2 ε) ∧
      (0 : Euclidean d) ∉ angularCone ℓ z.2.2 ε ∧
      closure (angularCone ℓ z.2.2 (ε / 2)) \ {0} ⊆ angularCone ℓ z.2.2 ε ∧
      ∃ κ > 0, ∃ M > 0, ∃ L > 0,
        (∀ r ∈ Icc 0 ε, ∀ Y : Set (Euclidean (d + 1)),
          SupportedPhaseRegularity (elapsedPhase (curriedPhase ℓ C) r)
            ((elapsedPhysicalBox z ε ×ˢ Y) ×ˢ (spatialPart ⁻¹' angularCone ℓ z.2.2 ε)) ∧
          SupportedPhaseHomogeneity (elapsedPhase (curriedPhase ℓ C) r)
            ((elapsedPhysicalBox z ε ×ˢ Y) ×ˢ (spatialPart ⁻¹' angularCone ℓ z.2.2 ε)) ∧
          SupportedMixedInvertibility (elapsedPhase (curriedPhase ℓ C) r)
            ((elapsedPhysicalBox z ε ×ˢ Y) ×ˢ (spatialPart ⁻¹' angularCone ℓ z.2.2 ε))) ∧
        ∀ r ∈ Icc 0 ε, ∀ x ∈ elapsedPhysicalBox z ε,
          (∀ η ∈ angularCone ℓ z.2.2 ε,
            ‖fun j : Fin d ↦ partialDeriv
              (elapsedTimeDerivative (curriedPhase ℓ C) r (x 0, spatialPart x)) η j‖ ≤ L) ∧
          (∀ ξ : Euclidean (d + 1), spatialPart ξ ∈ angularCone ℓ z.2.2 ε →
            IsUnit (mixedPhaseMatrix (elapsedPhase (curriedPhase ℓ C) r) x ξ).det ∧
            κ ≤ |(mixedPhaseMatrix (elapsedPhase (curriedPhase ℓ C) r) x ξ).det| ∧
            ‖(mixedPhaseMatrix (elapsedPhase (curriedPhase ℓ C) r) x ξ)⁻¹‖ ≤ M) ∧
          ∀ y ∈ elapsedPhysicalBox z ε,
            InjOn (averagedGradient (elapsedPhase (curriedPhase ℓ C) r) x y)
              (spatialPart ⁻¹' angularCone ℓ z.2.2 ε) ∧
            ∀ ξ : Euclidean (d + 1), spatialPart ξ ∈ angularCone ℓ z.2.2 ε →
              κ ≤ |(averagedJacobian (elapsedPhase (curriedPhase ℓ C) r) x y ξ).det| := by
  obtain ⟨ℓ, hℓ, hz, hD, hcD, h0, hmargin⟩ := exists_angular_margins hε hsmall
  obtain ⟨κm, hκm, M, hM, hm⟩ := exists_conic_elapsed_mixed_bounds ℓ hε hbuffer hs hdiff hnear
  obtain ⟨κa, hκa, ha⟩ := exists_conic_elapsed_averaged_geometry d
  obtain ⟨L, hL, ht⟩ := exists_conic_elapsedTimeMixed_bound ℓ hε hbuffer hs hdiff
  refine ⟨ℓ, hℓ, hz, hD, hcD, h0, hmargin,
    min κm κa, lt_min hκm hκa, M, hM, L, hL, ?_, ?_⟩
  · intro r hr Y
    have hrh := elapsed_supported_regularity_homogeneity ℓ hε hbuffer hs hr Y
    exact ⟨hrh.1, hrh.2, elapsed_supportedMixedInvertibility ℓ hε hbuffer hs hdiff hnear hr Y⟩
  · intro r hr x hx
    refine ⟨ht r hr x hx, ?_, ?_⟩
    · intro ξ hξ
      obtain ⟨hu, hd, hi⟩ := hm r hr x hx ξ hξ
      exact ⟨hu, (min_le_left κm κa).trans hd, hi⟩
    · intro y hy
      have hg := ha ℓ h Φ C z ε hε hbuffer hs hdiff hnear r hr x hx y hy
      exact ⟨hg.1, fun ξ hξ ↦ (min_le_right κm κa).trans (hg.2 ξ hξ)⟩

end JanetCartan.RegularSector.Characteristic.ConicPhase
