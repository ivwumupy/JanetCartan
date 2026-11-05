module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.ActualConstruction.ImageComparison

/-!
# Same-mask physical image-adjoint variation

Unlike the carrier Fourier integral operator, the image channel is genuinely
operator-norm continuous in its actual reduced coefficient array. The existing
finite-immersion-jet neighborhood produces the same array difference even for
the supplied original cutoff. Consumer: the image slot of the strong augmented
adjoint comparison for `app:ch_background:prop:bg-normalized`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff
namespace JanetCartan.PhysicalInverseContinuity
open ContinuumRow GeometricProfile AmplitudeBound ContinuumNormal ContinuumNormal.ActualConstruction

/-- At the fixed datum, the actual image-adjoint difference is small in an
order-eight neighborhood of the same retained immersion and original image
array. This does not compare the moving carrier Fourier integral rows. -/
theorem exists_retained_image_adjoint_tolerance {n : ℕ} (G : FlatReference n)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) (hR : R < G.domain.chartRadius)
    {χ : Euclidean n → ℝ} (hs : tsupport χ ⊆ ball 0 r)
    (hχrange : ∀ x, χ x ∈ Icc (0 : ℝ) 1)
    (d : ReducedCoefficientIndex n → C(Torus n, ℝ))
    (hd : ∀ j z, d j z = χ (centeredTorusRepresentative z) *
      geometricReducedCoefficients G.map (centeredTorusRepresentative z) j)
    (χmeas χsrc : C(Torus n, ℝ)) (w : OutputL2 n) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ F : Euclidean n → Euclidean (embeddingDimension n),
      ContDiff ℝ ∞ F → cNorm (closedBall 0 R) 8 (F - G.map) < δ →
      ∀ c : ReducedCoefficientIndex n → C(Torus n, ℝ),
        (∀ j z, c j z = χ (centeredTorusRepresentative z) *
          geometricReducedCoefficients F (centeredTorusRepresentative z) j) →
        ‖(imageChannel c χmeas χsrc).adjoint w - (imageChannel d χmeas χsrc).adjoint w‖ ≤ ε := by
  have hcont : Continuous (fun c : ReducedCoefficientIndex n → C(Torus n, ℝ) ↦
      (imageChannel c χmeas χsrc).adjoint w) :=
    (ContinuousLinearMap.adjoint.continuous.comp (lipschitzWith_imageChannel χmeas χsrc).continuous).clm_apply
      continuous_const
  obtain ⟨η, hη, hclose⟩ := (Metric.continuousAt_iff
    (f := fun c : ReducedCoefficientIndex n → C(Torus n, ℝ) ↦ (imageChannel c χmeas χsrc).adjoint w)
    (a := d)).mp hcont.continuousAt ε hε
  obtain ⟨δ, hδ, hcompare⟩ := exists_retained_imageNormal_immersion_threshold G hr hrR hR
    hs hχrange d hd χmeas χsrc hη
  refine ⟨δ, hδ, ?_⟩
  intro F hF hsmall c hc
  have harray := (hcompare F hF hsmall c hc).1
  have h := hclose (by simpa only [dist_eq_norm] using harray)
  simpa only [dist_eq_norm] using h.le

end JanetCartan.PhysicalInverseContinuity
