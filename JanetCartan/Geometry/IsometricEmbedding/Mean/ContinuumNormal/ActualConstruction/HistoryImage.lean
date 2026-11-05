module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.ActualConstruction.ImageComparison
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.HistoryGeometry

/-!
# Image-normal comparison for every admissible history

Apply the actual C8 history neighborhood to the retained coefficient extension
and image normal. The supplied reference array, coefficient cutoff and both
operator masks stay fixed. One frequency threshold precedes every stage and
finite history, with the original displacement and frequency exponents.

Consumer: the image contribution in the same-row history coercivity and
`ContinuumInverse` (`app:ch_background:prop:bg-frame`,
`app:ch_background:eq:bg-global-bound`).
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff
namespace JanetCartan.ContinuumNormal.ActualConstruction
open ContinuumRow GeometricProfile AmplitudeBound

/-- Every admissible history satisfies the retained image coefficient and
normal comparison with one threshold before the history. The coefficient
cutoff, reference array and measurement/source masks are the supplied ones.
This discharges the image closeness input of the actual history coercivity
application using the original `main:eq:displacement-budget` and unchanged
scale exponents (`app:ch_background:prop:bg-frame`,
`app:ch_background:eq:bg-global-bound`). -/
theorem exists_initialScale_for_retained_image_normal_comparison
    {n : ℕ} (G : FlatReference n) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hR : R < G.domain.chartRadius)
    {χ : Euclidean n → ℝ} (hs : tsupport χ ⊆ ball 0 r)
    (hχrange : ∀ x, χ x ∈ Icc (0 : ℝ) 1)
    (d : ReducedCoefficientIndex n → C(Torus n, ℝ))
    (hd : ∀ j z, d j z = χ (centeredTorusRepresentative z) *
      geometricReducedCoefficients G.map (centeredTorusRepresentative z) j)
    (χmeas χsrc : C(Torus n, ℝ)) {ε : ℝ} (hε : 0 < ε)
    {kMin : ℕ}
    (horder : displacementLoss n + bandExponent * (8 + (n : ℝ) / 2) + 2 < kMin) :
    ∃ S : ℝ, 2 ≤ S ∧ ∀ R₀, S ≤ R₀ →
      ∀ (j : ℕ) (u : Fin j → Torus n → Euclidean (embeddingDimension n))
        (ell : Fin j → ℕ), IsAdmissibleHistory R₀ kMin u ell →
      ∀ c : ReducedCoefficientIndex n → C(Torus n, ℝ),
        (∀ a z, c a z = χ (centeredTorusRepresentative z) *
          geometricReducedCoefficients (finiteHistoryMap G.map u) (centeredTorusRepresentative z) a) →
        ‖c - d‖ < ε ∧
        ‖NormalPerturbation.normal (imageChannel c χmeas χsrc) -
          NormalPerturbation.normal (imageChannel d χmeas χsrc)‖ < ε := by
  obtain ⟨δ, hδ, hcomparison⟩ := exists_retained_imageNormal_immersion_threshold
    G hr hrR hR hs hχrange d hd χmeas χsrc hε
  obtain ⟨S, hS, hnear⟩ := HistoryGeometry.exists_initialScale_for_c8_neighborhood
    G.map R horder hδ
  refine ⟨S, hS, ?_⟩
  intro R₀ hR₀ j u ell hu c hc
  exact hcomparison (finiteHistoryMap G.map u) (hu.contDiff_finiteHistoryMap G.contDiff)
    (hnear R₀ hR₀ j u ell hu) c hc

end JanetCartan.ContinuumNormal.ActualConstruction
