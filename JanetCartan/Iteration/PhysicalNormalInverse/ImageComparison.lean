module

public import JanetCartan.Iteration.PhysicalGeometry.Neighborhood
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.ActualConstruction.ImageComparison

/-!
# Same-cutoff image comparison along physical Schwartz histories

Apply the actual physical C8 neighborhood to the existing literal cutoff
coefficient identities of `app:ch_background:prop:bg-frame`.  Only the compactly
localized image coefficients live on the auxiliary torus.  The current map is
`RevisedGlobal.finiteMap G.map u`, and no global increment is periodized.

Consumer: `PhysicalNormalInverse.exists_initialScale_for_realized_retained_history_coercivity`.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff

namespace JanetCartan.PhysicalNormalInverse

open ContinuumRow GeometricProfile AmplitudeBound ContinuumNormal.ActualConstruction

/-- A single initial-frequency threshold controls both the same-cutoff image
coefficients and their actual image normal for every admissible physical prefix.
The reference array and both operator masks are the supplied original ones;
only the history smallness is discharged here. -/
theorem exists_initialScale_for_retained_image_normal_comparison
    {n : ℕ} (G : FlatReference n) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hR : R < G.domain.chartRadius)
    {χ : Euclidean n → ℝ} (hs : tsupport χ ⊆ ball 0 r)
    (hχrange : ∀ x, χ x ∈ Icc (0 : ℝ) 1)
    (d : ReducedCoefficientIndex n → C(Torus n, ℝ))
    (hd : ∀ j z, d j z = χ (centeredTorusRepresentative z) *
      geometricReducedCoefficients G.map (centeredTorusRepresentative z) j)
    (χmeas χsrc : C(Torus n, ℝ)) {ε : ℝ} (hε : 0 < ε)
    {B : ℝ} (hB : 1 ≤ B) {rStar kMin : ℕ} (hStar : 8 ≤ rStar)
    (horder : RevisedScales.displacementLoss n +
      bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < (kMin : ℝ)) :
    ∃ S : ℝ, 2 ≤ S ∧ ∀ R₀, S ≤ R₀ →
      ∀ (j : ℕ) (u : Fin j → SchwartzMap (Euclidean n) (Euclidean (embeddingDimension n)))
        (ell : Fin j → ℕ), RevisedGlobal.IsAdmissibleHistory B R₀ kMin u ell →
      ∀ c : ReducedCoefficientIndex n → C(Torus n, ℝ),
        (∀ a z, c a z = χ (centeredTorusRepresentative z) *
          geometricReducedCoefficients (RevisedGlobal.finiteMap G.map u)
            (centeredTorusRepresentative z) a) →
        ‖c - d‖ < ε ∧
        ‖NormalPerturbation.normal (imageChannel c χmeas χsrc) -
          NormalPerturbation.normal (imageChannel d χmeas χsrc)‖ < ε := by
  obtain ⟨δ, hδ, hcomparison⟩ := exists_retained_imageNormal_immersion_threshold
    G hr hrR hR hs hχrange d hd χmeas χsrc hε
  obtain ⟨S, hS, hnear⟩ := PhysicalGeometry.exists_initialScale_for_c8_neighborhood
    G.map R hB hStar horder hδ
  refine ⟨S, hS, ?_⟩
  intro R₀ hR₀ j u ell hu c hc
  have hF : ContDiff ℝ ∞ (RevisedGlobal.finiteMap G.map u) :=
    G.contDiff.add (ContDiff.sum (fun i _ ↦ (u i).smooth'))
  exact hcomparison (RevisedGlobal.finiteMap G.map u) hF
    (hnear R₀ hR₀ j u ell hu) c hc

end JanetCartan.PhysicalNormalInverse
