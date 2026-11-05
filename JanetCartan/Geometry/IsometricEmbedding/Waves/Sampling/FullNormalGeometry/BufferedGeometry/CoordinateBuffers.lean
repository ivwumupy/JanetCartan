module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.FullNormalGeometry.BufferedGeometry.Domains
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.FullNormalGeometry.BufferedGeometry.InverseStability

/-!
# Buffered inverse domains in the literal sampling coordinates

Transfer the common product-coordinate image buffers through the SAME retained
physical coordinates. The output coordinate map decreases distances, so one
positive buffer works for both physical image inclusions. The consumer is the
actual radial geometry of `app:ch_seed:prop:seed-phase-charts`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff NNReal

namespace JanetCartan.Sampling.FullNormalGeometry
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ActualPhase ActualComparison ContinuumRow.CanonicalConic RawKernel
open ContinuumRow.CanonicalCarrier

variable {m : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

private theorem adaptedSliceCoordinates_dist_le (x y : Euclidean (m + 1)) :
    dist ((adaptedSliceCoordinates T).equiv x) ((adaptedSliceCoordinates T).equiv y) ≤
      dist x y := by
  rw [dist_eq_norm, ← map_sub, dist_eq_norm]
  rw [← (physicalCoordinates T).norm_map (x - y)]
  exact max_le (WithLp.norm_fst_le ℝ _) (WithLp.norm_snd_le ℝ _)

private theorem adaptedSliceCoordinates_cthickening {b : ℝ} (hb : 0 ≤ b)
    (S : Set (Euclidean (m + 1))) :
    cthickening b S ⊆ (adaptedSliceCoordinates T).equiv ⁻¹'
      cthickening b ((adaptedSliceCoordinates T).equiv '' S) := by
  intro x hx
  rw [cthickening_eq_biUnion_closedBall S hb] at hx
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp hx
  have hy' : (adaptedSliceCoordinates T).equiv y ∈
      closure ((adaptedSliceCoordinates T).equiv '' S) :=
    mem_closure_image (adaptedSliceCoordinates T).equiv.continuous.continuousAt hy
  have hxy' : (adaptedSliceCoordinates T).equiv x ∈
      closedBall ((adaptedSliceCoordinates T).equiv y) b :=
    (adaptedSliceCoordinates_dist_le T x y).trans hxy
  have hh := closedBall_subset_cthickening hy' b hxy'
  simpa only [mem_preimage, cthickening_closure] using hh

/-- Transfer the arbitrary-gap inverse construction to the literal sampling
input, keeping the entire specified compact `K`. The analytic inputs are supplied
by `exists_radial_frozen_derivative_gap` and `exists_actual_radial_chart_comparison`;
this deduction chooses no replacement phase (`app:lem:buffered-inverse-stability`,
`app:ch_seed:prop:seed-phase-charts`). -/
theorem common_buffered_inverse_domains_in_literal_coordinates
    {K D : Set (Euclidean (m + 1))} (hK : IsCompact K) (hD : IsOpen D)
    (hKD : K ⊆ D) (hconv : Convex ℝ D)
    (G : (ℝ × Euclidean m) ≃L[ℝ] (ℝ × Euclidean m)) {q : ℝ≥0} (hq : q < 1)
    {f₀ : (ℝ × Euclidean m) → (ℝ × Euclidean m)}
    (hf₀ : ∀ u ∈ D, DifferentiableAt ℝ f₀
      ((adaptedSliceCoordinates T).equiv (canonicalInputCoordinates T u)))
    (hgap₀ : ∀ u ∈ D,
      ‖G.symm.toContinuousLinearMap.comp (fderiv ℝ f₀
        ((adaptedSliceCoordinates T).equiv (canonicalInputCoordinates T u))) -
        ContinuousLinearMap.id ℝ (ℝ × Euclidean m)‖ ≤ q) :
    ∃ τ > (0 : ℝ), ∃ b > (0 : ℝ), ∃ V : Set (Euclidean (m + 1)),
      IsOpen V ∧ IsCompact (closure V) ∧
      ∀ f : (ℝ × Euclidean m) → (ℝ × Euclidean m),
        (∀ u ∈ D, DifferentiableAt ℝ f
          ((adaptedSliceCoordinates T).equiv (canonicalInputCoordinates T u))) →
        (∀ u ∈ D, ‖fderiv ℝ f ((adaptedSliceCoordinates T).equiv
          (canonicalInputCoordinates T u)) - fderiv ℝ f₀
          ((adaptedSliceCoordinates T).equiv (canonicalInputCoordinates T u))‖ ≤ τ) →
        (∀ u ∈ K, ‖f ((adaptedSliceCoordinates T).equiv (canonicalInputCoordinates T u)) -
          f₀ ((adaptedSliceCoordinates T).equiv (canonicalInputCoordinates T u))‖ ≤ τ) →
        let g := fun u ↦ (adaptedSliceCoordinates T).equiv.symm
          (f ((adaptedSliceCoordinates T).equiv (canonicalInputCoordinates T u)))
        InjOn g D ∧ cthickening b (g '' K) ⊆ V ∧
          cthickening b (closure V) ⊆ g '' D := by
  let ι := (canonicalInputIsometry T).toContinuousLinearEquiv.trans
    (adaptedSliceCoordinates T).equiv
  let o := (adaptedSliceCoordinates T).equiv
  obtain ⟨τ, hτ, b, hb, W, hW, hcW, hall⟩ :=
    common_buffered_inverse_domains_of_gap_lt_one
      (hK.image ι.continuous) (ι.toHomeomorph.isOpenMap D hD)
      (image_mono hKD) (Subset.refl _) (hconv.linear_image ι.toLinearMap)
      G hq (by rintro _ ⟨u, hu, rfl⟩; exact hf₀ u hu)
      (by rintro _ ⟨u, hu, rfl⟩; exact hgap₀ u hu)
  let V := o ⁻¹' W
  have hcl : closure V = o ⁻¹' closure W := o.toHomeomorph.preimage_closure W |>.symm
  refine ⟨τ, hτ, b, hb, V, hW.preimage o.continuous, ?_, ?_⟩
  · rw [hcl]
    exact o.toHomeomorph.isCompact_preimage.mpr hcW
  intro f hf hd hv
  obtain ⟨hinj, himage, hchart⟩ := hall f
    (by rintro _ ⟨u, hu, rfl⟩; exact hf u hu)
    (by rintro _ ⟨u, hu, rfl⟩; exact hd u hu)
    (by rintro _ ⟨u, hu, rfl⟩; exact hv u hu)
  let g := fun u ↦ o.symm (f (ι u))
  have him (S : Set (Euclidean (m + 1))) : o '' (g '' S) = f '' (ι '' S) := by
    ext w
    simp only [mem_image, g]
    constructor
    · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨ι u, ⟨u, hu, rfl⟩, (o.apply_symm_apply _).symm⟩
    · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨o.symm (f (ι u)), ⟨u, hu, rfl⟩, o.apply_symm_apply _⟩
  refine ⟨?_, ?_, ?_⟩
  · intro u hu w hw he
    apply ι.injective
    apply hinj (mem_image_of_mem _ hu) (mem_image_of_mem _ hw)
    exact o.symm.injective he
  · intro w hw
    have hh := adaptedSliceCoordinates_cthickening T hb.le (g '' K) hw
    change o w ∈ cthickening b (o '' (g '' K)) at hh
    rw [him] at hh
    exact himage hh
  · intro w hw
    have hh := adaptedSliceCoordinates_cthickening T hb.le (closure V) hw
    change o w ∈ cthickening b (o '' closure V) at hh
    have he : o '' closure V = closure W := by
      rw [hcl]
      exact o.surjective.image_preimage _
    rw [he] at hh
    obtain ⟨_, ⟨u, hu, rfl⟩, heq⟩ := hchart hh
    refine ⟨u, hu, ?_⟩
    change o.symm (f (ι u)) = w
    change f (ι u) = o w at heq
    rw [heq, o.symm_apply_apply]

end JanetCartan.Sampling.FullNormalGeometry
