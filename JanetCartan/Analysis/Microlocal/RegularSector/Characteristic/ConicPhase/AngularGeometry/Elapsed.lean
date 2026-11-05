module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ConicPhase.AngularGeometry.Mixed
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.PhaseMixedBounds

/-!
# Elapsed geometry on the whole angular cone

Instantiate the existing supported and whole-image geometry with the actual
continued phase. The entire spacetime mixed matrix is unchanged by radial
normalization; hence the finite local inverse bound, whose temporal shear was
bounded on compact representatives, controls every positive radial scale.
Source: `app:ch_regular_base:lem:retarded-kernel`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.ConicPhase
open FourierIntegral EvolutionIntegral NormalComparison WholeImageGeometry
variable {d : ℕ}

/-- The original closed buffer supplies joint regularity throughout the
elapsed slab and whole spatial cone (`app:ch_regular_base:lem:retarded-kernel`). -/
theorem contDiffAt_curriedPhase_elapsed (ℓ : Euclidean d →L[ℝ] ℝ)
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    {z : RootState (Euclidean d)} {ε r : ℝ} (hε : 0 < ε)
    (hbuffer : closedBall (z.1, z) (2 * ε) ⊆ C.target)
    (hs : ContDiffOn ℝ ∞ (twoTimePhase C) C.target)
    (hr : r ∈ Icc 0 ε) {x : Euclidean (d + 1)} (hx : x ∈ elapsedPhysicalBox z ε)
    {η : Euclidean d} (hη : η ∈ angularCone ℓ z.2.2 ε) :
    ContDiffAt ℝ ∞
      (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
        curriedPhase ℓ C p.1.1 p.1.2 p.2.1 p.2.2)
      ((x 0, x 0 - r), (spatialPart x, η)) :=
  contDiffAt_curriedPhase ℓ hs (q := (x 0, (x 0 - r, (spatialPart x, η))))
    ⟨hη.1, hbuffer (elapsedPoint_mem_twoTime_buffer hε hr hx hη.2)⟩

/-- Supported regularity and exact homogeneity of the actual conic elapsed
phase, on the entire lifted spatial cone, for any source-position support.
Source: `app:ch_regular_base:lem:retarded-kernel`. -/
theorem elapsed_supported_regularity_homogeneity (ℓ : Euclidean d →L[ℝ] ℝ)
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    {z : RootState (Euclidean d)} {ε r : ℝ} (hε : 0 < ε)
    (hbuffer : closedBall (z.1, z) (2 * ε) ⊆ C.target)
    (hs : ContDiffOn ℝ ∞ (twoTimePhase C) C.target)
    (hr : r ∈ Icc 0 ε) (Y : Set (Euclidean (d + 1))) :
    SupportedPhaseRegularity (elapsedPhase (curriedPhase ℓ C) r)
      ((elapsedPhysicalBox z ε ×ˢ Y) ×ˢ (spatialPart ⁻¹' angularCone ℓ z.2.2 ε)) ∧
    SupportedPhaseHomogeneity (elapsedPhase (curriedPhase ℓ C) r)
      ((elapsedPhysicalBox z ε ×ˢ Y) ×ˢ (spatialPart ⁻¹' angularCone ℓ z.2.2 ε)) := by
  refine ⟨elapsedPhase_supportedPhaseRegularity _ r
    (fun _ hx _ hη ↦ contDiffAt_curriedPhase_elapsed ℓ hε hbuffer hs hr hx hη), ?_⟩
  exact elapsedPhase_supportedPhaseHomogeneity _ r (isOpen_elapsedPhysicalBox z ε)
    (fun x _ η _ _ ha ↦ extend_smul ℓ (twoTimePhase C) (x 0, (x 0 - r, (spatialPart x, η))) ha)

/-- The actual spatial half-gap gives the supported invertibility premise
on the full cone (`app:ch_regular_base:lem:retarded-kernel`). -/
theorem elapsed_supportedMixedInvertibility (ℓ : Euclidean d →L[ℝ] ℝ)
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    {z : RootState (Euclidean d)} {ε r : ℝ} (hε : 0 < ε)
    (hbuffer : closedBall (z.1, z) (2 * ε) ⊆ C.target)
    (hs : ContDiffOn ℝ ∞ (twoTimePhase C) C.target)
    (hdiff : ∀ q ∈ C.target,
      HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C q) q)
    (hnear : ∀ q ∈ closedBall (z.1, z) (2 * ε), ‖twoTimePhaseMixed C q - 1‖ ≤ 1 / 2)
    (hr : r ∈ Icc 0 ε) (Y : Set (Euclidean (d + 1))) :
    SupportedMixedInvertibility (elapsedPhase (curriedPhase ℓ C) r)
      ((elapsedPhysicalBox z ε ×ˢ Y) ×ˢ (spatialPart ⁻¹' angularCone ℓ z.2.2 ε)) :=
  elapsedPhase_supportedMixedInvertibility _ r (isOpen_angularCone ℓ z.2.2 ε)
    (fun _ hx _ hη ↦ contDiffAt_curriedPhase_elapsed ℓ hε hbuffer hs hr hx hη)
    (fun _ hx _ hη ↦ norm_mixedPhaseMatrix_phase_sub_one_le ℓ hε hbuffer hs hdiff hnear hr hx hη)

/-- Whole-cone averaged-gradient injectivity and a dimension-only positive
determinant gap. The constant precedes the phase, section, and buffer.
Source: `app:ch_regular_base:lem:retarded-kernel`. -/
theorem exists_conic_elapsed_averaged_geometry (d : ℕ) :
    ∃ κ > 0, ∀ (ℓ : Euclidean d →L[ℝ] ℝ)
      (h : RootState (Euclidean d) → ℝ)
      (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
      (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
      (z : RootState (Euclidean d)) (ε : ℝ), 0 < ε →
      closedBall (z.1, z) (2 * ε) ⊆ C.target →
      ContDiffOn ℝ ∞ (twoTimePhase C) C.target →
      (∀ q ∈ C.target, HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C q) q) →
      (∀ q ∈ closedBall (z.1, z) (2 * ε), ‖twoTimePhaseMixed C q - 1‖ ≤ 1 / 2) →
      ∀ r ∈ Icc 0 ε, ∀ x ∈ elapsedPhysicalBox z ε, ∀ y ∈ elapsedPhysicalBox z ε,
        InjOn (averagedGradient (elapsedPhase (curriedPhase ℓ C) r) x y)
          (spatialPart ⁻¹' angularCone ℓ z.2.2 ε) ∧
        ∀ ξ : Euclidean (d + 1), spatialPart ξ ∈ angularCone ℓ z.2.2 ε →
          κ ≤ |(averagedJacobian (elapsedPhase (curriedPhase ℓ C) r) x y ξ).det| := by
  obtain ⟨κ, hκ, hg⟩ := exists_elapsedPhase_averaged_geometry d
  refine ⟨κ, hκ, ?_⟩
  intro ℓ h Φ C z ε hε hbuffer hs hdiff hnear
  apply hg (curriedPhase ℓ C) ε (elapsedPhysicalBox z ε) (angularCone ℓ z.2.2 ε)
    (isOpen_elapsedPhysicalBox z ε) (isOpen_angularCone ℓ z.2.2 ε)
    (convex_elapsedPhysicalBox z ε) (convex_angularCone ℓ z.2.2 ε)
  · exact fun _ hr _ hx _ hη ↦ contDiffAt_curriedPhase_elapsed ℓ hε hbuffer hs hr hx hη
  · exact fun _ hr _ hx _ hη ↦
      norm_mixedPhaseMatrix_phase_sub_one_le ℓ hε hbuffer hs hdiff hnear hr hx hη

/-- The entire elapsed mixed matrix, including the temporal shear, equals
the original matrix at the normalized spacetime covector. This transports
the compact representative bounds without any assumption on conic shear.
Source: `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem mixedPhaseMatrix_elapsed_eq_normalize (ℓ : Euclidean d →L[ℝ] ℝ)
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    {z : RootState (Euclidean d)} {ε r : ℝ} (hε : 0 < ε)
    (hbuffer : closedBall (z.1, z) (2 * ε) ⊆ C.target)
    (hs : ContDiffOn ℝ ∞ (twoTimePhase C) C.target)
    (hdiff : ∀ q ∈ C.target,
      HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C q) q)
    (hr : r ∈ Icc 0 ε) {x ξ : Euclidean (d + 1)} (hx : x ∈ elapsedPhysicalBox z ε)
    (hξ : spatialPart ξ ∈ angularCone ℓ z.2.2 ε) :
    mixedPhaseMatrix (elapsedPhase (curriedPhase ℓ C) r) x ξ =
      mixedPhaseMatrix (elapsedPhase (curriedTwoTimePhase C) r) x
        ((ℓ (spatialPart ξ))⁻¹ • ξ) := by
  have hD : IsOpen (spatialPart ⁻¹' angularCone ℓ z.2.2 ε) :=
    (isOpen_angularCone ℓ z.2.2 ε).preimage spatialPartCLM.continuous
  have hcone : ∀ a : ℝ, 0 < a → ∀ ζ : Euclidean (d + 1),
      spatialPart ζ ∈ angularCone ℓ z.2.2 ε →
      spatialPart (a • ζ) ∈ angularCone ℓ z.2.2 ε := by
    intro a ha ζ hζ
    rw [show spatialPart (a • ζ) = a • spatialPart ζ from spatialPartCLM.map_smul a ζ]
    exact smul_mem_angularCone hζ ha
  have hS := elapsedPhase_contDiffOn (curriedPhase ℓ C) r
    (fun _ hx _ hη ↦ contDiffAt_curriedPhase_elapsed ℓ hε hbuffer hs hr hx hη)
  have he := PrimitiveProfiles.mixedPhaseMatrix_dilation_eq_on
    (isOpen_elapsedPhysicalBox z ε) hD hcone hS
    (fun a ha y _ ζ _ ↦ elapsedPhase_smul (curriedPhase ℓ C) r a y ζ
      (extend_smul ℓ (twoTimePhase C) (y 0, (y 0 - r, (spatialPart y, spatialPart ζ))) ha))
    (inv_pos.mpr hξ.1) hx hξ
  rw [← he]
  apply SupportedSobolev.mixedPhaseMatrix_eq_of_eventuallyEq
  have hp := phase_eventuallyEq_at_normalize ℓ hdiff isOpen_ball isOpen_ball (convex_ball _ _)
    ((localPatch_bufferedBase_subset z ε).trans hbuffer)
    (elapsed_mem_domain_bufferedBase ℓ hε hr hx hξ)
  have hc : Continuous (fun p : Euclidean (d + 1) × Euclidean (d + 1) ↦
      (p.1 0, (p.1 0 - r, (spatialPart p.1, spatialPart p.2)))) := by
    have ht0 : Continuous (fun p : Euclidean (d + 1) × Euclidean (d + 1) ↦ p.1 0) :=
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1))).continuous.comp continuous_fst
    exact ht0.prodMk ((ht0.sub continuous_const).prodMk
      ((spatialPartCLM.continuous.comp continuous_fst).prodMk
        (spatialPartCLM.continuous.comp continuous_snd)))
  have ht : Tendsto (fun p : Euclidean (d + 1) × Euclidean (d + 1) ↦
      (p.1 0, (p.1 0 - r, (spatialPart p.1, spatialPart p.2))))
      (𝓝 (x, (ℓ (spatialPart ξ))⁻¹ • ξ))
      (𝓝 (normalize ℓ (x 0, (x 0 - r, (spatialPart x, spatialPart ξ))))) := by
    simpa only [normalize, show spatialPart ((ℓ (spatialPart ξ))⁻¹ • ξ) =
      (ℓ (spatialPart ξ))⁻¹ • spatialPart ξ from spatialPartCLM.map_smul _ _] using
      hc.tendsto (x, (ℓ (spatialPart ξ))⁻¹ • ξ)
  filter_upwards [hp.comp_tendsto ht] with p hp
  exact congrArg (fun a : ℝ ↦ (p.1 0 - r) * p.2 0 + a) hp

/-- Actual finite uniform mixed inverse bounds for every positive radial
scale and every temporal frequency. `PhaseMixedBounds` derives the temporal
shear bound on compact representatives from joint smoothness; the preceding
matrix identity transfers that bound. No conic inverse bound is assumed.
Constants concern the one fixed phase, not a coefficient family.
Source: `app:ch_regular_base:lem:retarded-kernel`. -/
theorem exists_conic_elapsed_mixed_bounds (ℓ : Euclidean d →L[ℝ] ℝ)
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    {z : RootState (Euclidean d)} {ε : ℝ} (hε : 0 < ε)
    (hbuffer : closedBall (z.1, z) (2 * ε) ⊆ C.target)
    (hs : ContDiffOn ℝ ∞ (twoTimePhase C) C.target)
    (hdiff : ∀ q ∈ C.target,
      HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C q) q)
    (hnear : ∀ q ∈ closedBall (z.1, z) (2 * ε), ‖twoTimePhaseMixed C q - 1‖ ≤ 1 / 2) :
    ∃ κ > 0, ∃ B > 0, ∀ r ∈ Icc 0 ε, ∀ x ∈ elapsedPhysicalBox z ε,
      ∀ ξ : Euclidean (d + 1), spatialPart ξ ∈ angularCone ℓ z.2.2 ε →
        IsUnit (mixedPhaseMatrix (elapsedPhase (curriedPhase ℓ C) r) x ξ).det ∧
        κ ≤ |(mixedPhaseMatrix (elapsedPhase (curriedPhase ℓ C) r) x ξ).det| ∧
        ‖(mixedPhaseMatrix (elapsedPhase (curriedPhase ℓ C) r) x ξ)⁻¹‖ ≤ B := by
  obtain ⟨κ, hκ, B, hB, hb⟩ :=
    exists_curriedTwoTimePhase_elapsed_mixed_bounds C hε hbuffer hs hnear
  refine ⟨κ, hκ, B, hB, ?_⟩
  intro r hr x hx ξ hξ
  rw [mixedPhaseMatrix_elapsed_eq_normalize ℓ hε hbuffer hs hdiff hr hx hξ]
  exact hb r hr x hx _ (by
    simpa only [show spatialPart ((ℓ (spatialPart ξ))⁻¹ • ξ) =
      (ℓ (spatialPart ξ))⁻¹ • spatialPart ξ from spatialPartCLM.map_smul _ _] using hξ.2)

end JanetCartan.RegularSector.Characteristic.ConicPhase
