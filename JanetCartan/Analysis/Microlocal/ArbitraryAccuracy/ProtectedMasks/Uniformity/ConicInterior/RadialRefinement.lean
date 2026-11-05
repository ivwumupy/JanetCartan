module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.ConicInterior.RadialCharts
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ConicPhase.Assembly.CompactJets
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ConicPhase.Assembly.Transport

/-!
# A finite radial refinement chosen before the coefficient field

Compactness is used only for the fixed radial frequency carrier. Every
frequency has an inverse-dilated representative in the original local overlap;
the full frequency need not lie in the original chart target.

Consumer: the expanded finite family for `app:ch_regular:lem:finite-chain`.
This is a proof cover and does not partition or replace any operator.
-/

@[expose] public noncomputable section

open Set Metric Filter
open scoped Topology

namespace JanetCartan.ArbitraryAccuracy.ProtectedMasks.ConicInterior

open RegularSector.Characteristic ConicPhase EvolutionIntegral

variable {d : ℕ}

/-- A finite menu of positive radii covers the ENTIRE fixed radial band.
The menu depends only on the fixed section, angular buffer and radial
endpoints, and is therefore chosen before `Q` and accuracy.
Consumer: radial copies of the original chart in
`app:ch_regular:lem:finite-chain`. -/
theorem exists_radialSectionBand_refinement
    (ℓ : Euclidean d →L[ℝ] ℝ) (η₀ : Euclidean d)
    {γ a b : ℝ} (hγ : 0 < γ) (ha : 0 < a) :
    ∃ Λ : Finset ℝ, (∀ c ∈ Λ, c ∈ Icc a b) ∧
      ∀ η ∈ radialSectionBand ℓ η₀ (γ / 2) a b,
        ∃ c ∈ Λ, c⁻¹ • η ∈ ball η₀ γ := by
  classical
  let O : ℝ → Set (Euclidean d) := fun c ↦ (fun η ↦ c⁻¹ • η) ⁻¹' ball η₀ γ
  have hO (c : ℝ) : IsOpen (O c) := isOpen_ball.preimage (continuous_const_smul _)
  have hcover : radialSectionBand ℓ η₀ (γ / 2) a b ⊆ ⋃ c ∈ Icc a b, O c := by
    rintro η ⟨⟨c, θ⟩, ⟨hc, hθ, _⟩, rfl⟩
    refine mem_iUnion.mpr ⟨c, mem_iUnion.mpr ⟨hc, ?_⟩⟩
    change c⁻¹ • (c • θ) ∈ ball η₀ γ
    rw [inv_smul_smul₀ (ha.trans_le hc.1).ne']
    exact closedBall_subset_ball (by linarith) hθ
  obtain ⟨Λ, hΛ, hfin, hcover⟩ :=
    (isCompact_radialSectionBand ℓ η₀ (γ / 2) a b).elim_finite_subcover_image
      (fun c _ ↦ hO c) hcover
  refine ⟨hfin.toFinset, fun c hc ↦ hΛ (hfin.mem_toFinset.mp hc), ?_⟩
  intro η hη
  obtain ⟨c, hc, hlocal⟩ := mem_iUnion₂.mp (hcover hη)
  exact ⟨c, hfin.mem_toFinset.mpr hc, hlocal⟩

/-- A chosen radial cell puts the inverse-dilated elapsed point in the
original chart and identifies its transported phase germ with the SAME conic
phase. The closed physical half-buffers and full original elapsed interval
are retained. The original buffer and differential are produced by
`UniformGeometry.exists_uniform_fieldRoot_conicGeometry`
(`app:ch_regular:eq:joint-stationary`). -/
theorem radialChart_elapsedPoint_target_and_germ
    (ℓ : Euclidean d →L[ℝ] ℝ)
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    {z : RootState (Euclidean d)} {γ a b c r : ℝ}
    (hγ : 0 < γ) (ha : 0 < a) (hc : 0 < c)
    (hbuffer : closedBall (z.1, z) (2 * γ) ⊆ C.target)
    (hdiff : ∀ q ∈ C.target,
      HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C q) q)
    (hr : r ∈ Icc 0 γ) (x : Euclidean (d + 1)) (η : Euclidean d)
    (ht : x 0 ∈ closedBall z.1 (γ / 2))
    (hy : spatialPart x ∈ closedBall z.2.1 (γ / 2))
    (hη : η ∈ radialSectionBand ℓ z.2.2 (γ / 2) a b)
    (hcell : c⁻¹ • η ∈ ball z.2.2 γ) :
    (x 0, (x 0 - r, (spatialPart x, η))) ∈ (radialChart c hc.ne' C).target ∧
      phase ℓ C =ᶠ[𝓝 ((twoTimeRadialEquiv c hc.ne').symm
        (x 0, (x 0 - r, (spatialPart x, η))))] twoTimePhase C ∧
      phase ℓ C =ᶠ[𝓝 (x 0, (x 0 - r, (spatialPart x, η)))]
        twoTimePhase (radialChart c hc.ne' C) := by
  have hx : x ∈ elapsedPhysicalBox z γ :=
    ⟨closedBall_subset_ball (by linarith) ht, closedBall_subset_ball (by linarith) hy⟩
  have hηn := radialSectionBand_normalizes ha hη
  have hcone : η ∈ angularCone ℓ z.2.2 γ :=
    ⟨hηn.1, closedBall_subset_ball (by linarith) hηn.2⟩
  have hscaled := smul_mem_angularCone hcone (inv_pos.mpr hc)
  have hcell' : c⁻¹ • η ∈ ball z.2.2 (2 * γ) :=
    ball_subset_ball (by linarith) hcell
  have hlocal : (x 0, (x 0 - r, (spatialPart x, c⁻¹ • η))) ∈
      localPatch (bufferedBase z γ) (ball z.2.2 (2 * γ)) :=
    ⟨elapsed_mem_bufferedBase hγ hr hx, hcell'⟩
  have hgerm := phase_eventuallyEq_on_buffered_overlap ℓ hγ hbuffer hdiff hr hx hscaled hcell'
  exact ⟨hbuffer (localPatch_bufferedBase_subset z γ hlocal), hgerm,
    conicPhase_eventuallyEq_radialChart ℓ hc C _ hgerm⟩

end JanetCartan.ArbitraryAccuracy.ProtectedMasks.ConicInterior
