module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.CommonCharts.SeedCovector
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.CurrentFullPhase.FrameComponents
/-!
# Admitting an actual flat seed to the fixed Hamilton family

The producer for the primitive frame threshold of
`exists_retained_seed_common_conic_charts` (`new:lem:scaling`,
`app:ch_background:prop:bg-frame`). The original physical domain is retained.
Its boundedness lets the source contraction cover it together with the closed
frame-norm ball. The existing componentwise dilation estimates are converted
to the SAME joint frame norm used by the Hamilton family.

The chosen positive seed scale precedes the subsequent family scale, density
and history. Its origin frame is proved to equal the cube frame exactly.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
open ProjectedStressFrame ActualCarriers CurrentFullPhase
variable {n : ℕ} {P : FrozenMenu.Patch n} {U₀ : Set (Euclidean n)} {hU₀ : IsOpen U₀}
    (T : PatchQuantitativeFamily P U₀ hU₀)
/-- A genuine source contraction satisfies any prescribed positive primitive
frame threshold on the retained norm domain, while staying smooth on the
original bounded physical domain. The literal origin identity is also proved.
Consumer: `exists_dilated_flat_seed_common_conic_charts`, for
`app:ch_background:prop:bg-frame` and `new:lem:scaling`. -/
theorem exists_dilated_flat_seed_frame (G : FlatReference n) (hbounded : Bornology.IsBounded U₀)
    {δ cap : ℝ} (hδ : 0 < δ) (hcap : 0 < cap) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < cap ∧ ρ ≤ 1 ∧
      ContDiffOn ℝ ∞ (projectedStress (sourceDilation G.map ρ)) U₀ ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (projectedStress (sourceDilation G.map ρ) - fun _ ↦ cubeStress n) < δ ∧
      projectedStress (sourceDilation G.map ρ) 0 = cubeStress n := by
  let K := closedBall (0 : Euclidean n) T.data.localReference.stateRadius
  have hK : IsCompact K := isCompact_closedBall _ _
  have hL : IsCompact (K ∪ closure U₀) := hK.union hbounded.isCompact_closure
  obtain ⟨B, hB, hLB, σ₀, hσ₀, hσ₁, _, hgeom, hb⟩ :=
    exists_projectedStress_dilation_bounds G hL
  have hKB : K ⊆ B := fun x hx ↦ hLB (Or.inl hx)
  have hUB : U₀ ⊆ B := fun x hx ↦ hLB (Or.inr (subset_closure hx))
  obtain ⟨C, hC, hbound⟩ := hb 6
  let ρ := min σ₀ (min (cap / 2) (δ / (4 * 7 * C)))
  have hρ : 0 < ρ := lt_min hσ₀ (lt_min (half_pos hcap) (by positivity))
  have hρσ : ρ ≤ σ₀ := min_le_left _ _
  have hρcap : ρ < cap :=
    ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (half_lt_self hcap)
  obtain ⟨_, _, hsmooth⟩ := hgeom ρ ⟨hρ, hρσ⟩
  have hs : ContDiffOn ℝ ∞ (projectedStress (sourceDilation G.map ρ)) B :=
    contDiffOn_pi.mpr hsmooth
  refine ⟨ρ, hρ, hρcap, hρσ.trans hσ₁, hs.mono hUB, ?_, ?_⟩
  · apply frame_cNorm_lt_of_componentwise hK
      (fun x hx ↦ ((hs.sub contDiffOn_const).contDiffAt (hB.mem_nhds (hKB hx))).of_le
        (by simp)) hδ
    intro i
    have hmono := cNorm_mono_set_of_contDiffAt
      (f := fun x ↦ projectedStress (sourceDilation G.map ρ) x i - cubeStress n i) (show K ⊆ K ∪ closure U₀ from subset_union_left)
      hL (fun x hx ↦ (((hsmooth i).sub contDiffOn_const).contDiffAt
        (hB.mem_nhds (hLB hx))).of_le (by simp : (6 : ℕ∞ω) ≤ ∞))
    apply (hmono.trans (hbound ρ ⟨hρ, hρσ⟩ i)).trans_lt
    have hh : ρ ≤ δ / (4 * 7 * C) := (min_le_right _ _).trans (min_le_right _ _)
    have hh' := (le_div_iff₀ (show 0 < 4 * 7 * C by positivity)).mp hh
    norm_num
    nlinarith
  · funext i
    rw [projectedStress_sourceDilation hρ G.contDiff 0]
    · simpa only [smul_zero] using projectedStress_flatReference_zero G i
    · simpa only [smul_zero] using G.fullNormalRank 0
        (mem_ball_self (G.domain.coreRadius_pos.trans G.domain.coreRadius_lt_chartRadius))
end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
