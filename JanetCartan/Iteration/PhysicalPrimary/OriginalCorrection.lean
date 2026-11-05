module

public import JanetCartan.Iteration.PhysicalPrimary.SourceCorrection

/-!
# The correction of the same retained physical cell

The original producer supplies this SAME `c/E/A/H/B` tuple and the fixed
comparison-cover certificates. Every scalar equation and every moving-domain
certificate below is projected from its SAME `RetainedLeadingData`; no new
leading witness is selected. The positive column gap is definitionally the
fixed `c`, before the history. The physical geometric constructor supplies the
correction budget uniformly before every history.
Consumer: the original full-strain and reduced Fourier source in
`app:ch_response:eq:response-graded-source`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalPrimary
open ActualCarriers FrozenMenu CurrentFullPhase ProjectedStressFrame
open NullTransport ActualFlow FlowAmplitude RawPrimary LeadingWave.FullModulation

/-- Close all moving-domain, scalar-transport and correction-budget inputs on
one retained leading tuple. The fixed hypotheses are precisely the original
comparison cover and its positive radii; the current data is the original
leading output, not an assumed correction estimate. The same fixed `c` is the
quantitative null-column gap (`app:ch_waves:eq:primary-algebraic-correction`). -/
theorem exists_history_leading_correction_profiles {n : ℕ} (G : FlatReference n)
    {rGeom RGeom : ℝ} (hrGeom : 0 < rGeom) (hrR : rGeom < RGeom)
    (hRGeom : RGeom < G.domain.chartRadius)
    {P : Patch n} (T : PatchQuantitativeFamily P (ball 0 RGeom) isOpen_ball)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ closedBall 0 rGeom)
    (centers : Finset (parameterCube P.radius)) (row col : centers → Fin n)
    (ρ R τ Rc τc Mc rcomp δcomp σ : centers → ℝ)
    (Ωc : centers → Set (Euclidean n × Euclidean 3)) (ρc Bc gc Bfull : centers → ℝ)
    (Mscalar m c : ℝ) (hc : 0 < c) (E : ℕ → ℝ) (A H B : centers → ℕ → ℝ)
    (cell : centers) (hρ : 0 < ρ cell) (hR : 0 < R cell) (hτ : 0 < τ cell) (hσ : 0 < σ cell)
    (hworking : let a := ((0 : Euclidean n),(cell.1.1,T.reference.spatialPatch cell.1.1))
      closedBall a (2*σ cell) ⊆
        (coordinates (adaptedCoordinates T.data.adapted)).symm ''
          (Icc (-τ cell/2) (τ cell/2) ×ˢ
            closedBall ((0 : Euclidean (n-1)),(cell.1.1,T.reference.spatialPatch cell.1.1)) (R cell/64)))
    (hcoeff : let a := ((0 : Euclidean n),(cell.1.1,T.reference.spatialPatch cell.1.1))
      closedBall a (2*σ cell) ⊆ closedBall a (ρ cell))
    {Bband : ℝ} (hBband : 1 ≤ Bband) {rStar kMin : ℕ} (hStar : 14 ≤ rStar)
    (horder : RevisedScales.displacementLoss n +
      bandExponent * ((rStar : ℝ)+(n : ℝ)/2)+2 < (kMin : ℝ)) :
    ∃ threshold : ℝ, 2 ≤ threshold ∧ ∃ Γ : ℕ → ℝ, (∀ k, 0 < Γ k) ∧
      ∀ R₀, threshold ≤ R₀ →
      ∀ (stage : ℕ) (u : Fin stage → SchwartzMap (Euclidean n) (Euclidean (embeddingDimension n)))
        (ell : Fin stage → ℕ), RevisedGlobal.IsAdmissibleHistory Bband R₀ kMin u ell →
      let F := RevisedGlobal.finiteMap G.map u
      ∀ (hF : ContDiffOn ℝ ∞ F (ball 0 RGeom))
        (hi : IsImmersionOn F (ball 0 RGeom)) (hrank : HasFullNormalRankOn F (ball 0 RGeom))
        (hdata : RetainedLeadingData T (K := closedBall (0 : Euclidean n) rGeom)
          centers row col ρ R τ Rc τc Mc rcomp δcomp σ Ωc ρc Bc gc Bfull Mscalar m c E A H B F hF hi hrank),
      let Q := LeadingData.Q T centers row col ρ R τ Rc τc Mc rcomp δcomp σ Ωc ρc Bc gc Bfull
        Mscalar m c E A H B F hF hi hrank hdata
      let Φ := LeadingCell.Φ T centers row col ρ R τ Rc τc Mc rcomp δcomp σ Ωc ρc Bc gc Bfull
        Mscalar m c E A H B F hF hi hrank hdata cell
      let Y := LeadingCell.Y T centers row col ρ R τ Rc τc Mc rcomp δcomp σ Ωc ρc Bc gc Bfull
        Mscalar m c E A H B F hF hi hrank hdata cell
      let C := LeadingCell.C T centers row col ρ R τ Rc τc Mc rcomp δcomp σ Ωc ρc Bc gc Bfull
        Mscalar m c E A H B F hF hi hrank hdata cell
      let D := LeadingCell.D T centers row col ρ R τ Rc τc Mc rcomp δcomp σ Ωc ρc Bc gc Bfull
        Mscalar m c E A H B F hF hi hrank hdata cell
      let center := ((0 : Euclidean n),(cell.1.1,T.reference.spatialPatch cell.1.1))
      let Kr := closedBall ((0 : Euclidean (n-1)),cell.1.1) (R cell/8)
      ∀ initial : Euclidean (n-1) × Euclidean 3 → ℝ,
      ContDiffOn ℝ ∞ initial (ball ((0 : Euclidean (n-1)),cell.1.1) (R cell/4)) →
      cNorm Kr 14 initial ≤ Mscalar →
      (∀ p ∈ ball ((0 : Euclidean (n-1)),cell.1.1) (R cell/8), m ≤ initial p) →
      ContDiffOn ℝ ∞ (fullCorrectionCovector T Q F (row cell) (col cell) Φ Y initial) (C ⁻¹' D) ∧
        ∀ k, cNorm (closedBall center (2*σ cell)) k
          (fullCorrectionCovector T Q F (row cell) (col cell) Φ Y initial) ≤
            Γ k*(1+cNorm (closedBall (0 : Euclidean n) rGeom) (k+14) F+cNorm Kr (k+14) initial) := by
  obtain ⟨threshold,hthreshold,Γ,hΓ,hcorrection⟩ := exists_history_retained_correction_bounds
    G hrGeom hrR hRGeom T hball cell.1.1 (row cell) (col cell) hρ hR hτ hσ
    Mscalar (B cell) hc hworking hcoeff hBband hStar horder
  refine ⟨threshold,hthreshold,Γ,hΓ,?_⟩
  intro R₀ hR₀ stage u ell hu F hF hi hrank hdata Q Φ Y C D center Kr initial hinit h14 hlower
  obtain ⟨_hF₀,_hi₀,_hrank₀,hcorrect⟩ := hcorrection R₀ hR₀ stage u ell hu
  have hα := LeadingCell.scalar_regular T centers row col ρ R τ Rc τc Mc rcomp δcomp σ
    Ωc ρc Bc gc Bfull Mscalar m c E A H B F hF hi hrank hdata cell initial hinit h14 hlower
  have hnonzero := LeadingCell.scalar_nonzero T centers row col ρ R τ Rc τc Mc rcomp δcomp σ
    Ωc ρc Bc gc Bfull Mscalar m c E A H B F hF hi hrank hdata cell initial hinit h14 hlower
  have htransport := LeadingCell.scalar_transport T centers row col ρ R τ Rc τc Mc rcomp δcomp σ
    Ωc ρc Bc gc Bfull Mscalar m c E A H B F hF hi hrank hdata cell initial hinit h14 hlower
  have hscalar := LeadingCell.scalar_bound T centers row col ρ R τ Rc τc Mc rcomp δcomp σ
    Ωc ρc Bc gc Bfull Mscalar m c E A H B F hF hi hrank hdata cell initial hinit h14 hlower
  have hdom := LeadingCell.fact0 T centers row col ρ R τ Rc τc Mc rcomp δcomp σ
    Ωc ρc Bc gc Bfull Mscalar m c E A H B F hF hi hrank hdata cell
  have hphysical := LeadingCell.fact1 T centers row col ρ R τ Rc τc Mc rcomp δcomp σ
    Ωc ρc Bc gc Bfull Mscalar m c E A H B F hF hi hrank hdata cell
  have hD := LeadingCell.fact15 T centers row col ρ R τ Rc τc Mc rcomp δcomp σ
    Ωc ρc Bc gc Bfull Mscalar m c E A H B F hF hi hrank hdata cell
  have hcover := LeadingCell.fact16 T centers row col ρ R τ Rc τc Mc rcomp δcomp σ
    Ωc ρc Bc gc Bfull Mscalar m c E A H B F hF hi hrank hdata cell
  have hphys := LeadingCell.fact18 T centers row col ρ R τ Rc τc Mc rcomp δcomp σ
    Ωc ρc Bc gc Bfull Mscalar m c E A H B F hF hi hrank hdata cell
  have hgap := LeadingCell.fact34 T centers row col ρ R τ Rc τc Mc rcomp δcomp σ
    Ωc ρc Bc gc Bfull Mscalar m c E A H B F hF hi hrank hdata cell
  exact hcorrect Q.2.2 hdom hphysical D Φ Y hD hcover hphys
    (fun w hw ↦ (hgap w hw).1) initial h14 hα hnonzero htransport hscalar

end JanetCartan.PhysicalPrimary
