module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedRowGeometry.OriginalSourceLabels
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedRowGeometry.OriginalSourceDensity

/-!
# Original density comparison on the constructed retained source cells

Choose one region preserving every zero-position incidence point and the
original output cylinder, and prove the source density comparison for every
coefficient product in that region. The current and limiting density labels
are kept in the original scalar ball by the retained seed forward estimate.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedRowGeometry
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open ContinuumRow CanonicalCarrier PositiveReference PositiveReference.FlowConstruction
open NormalizedBackground.SourceGeometry ContinuumNormalReduction.TransportSymbol WideDensity

/-- Construct one original-label region and instantiate the source density
comparison there. The forward C¹ bound is the original retained flow bound;
no density, amplitude, inverse or operator convergence is a premise. The
same chosen region supplies the label ranges, seed smoothness, zero Cauchy
value, parameter identity and density estimates for every contained full
coefficient product. The source matching in the conclusion is the literal
ODE identity proved by
`exists_retained_chart_source_primitive_convergence_on_outputCylinder`.
Consumers: the joint retained row and its weighted full amplitude
(`app:ch_background:defn:bg-row`, `app:ch_background:prop:bg-normalized`,
`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem exists_original_source_density_region
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (zCell : Euclidean 3) {L Rc B τ Mc : ℝ}
    (hL : 0 < L) (hRc : 0 < Rc) (hτ : 0 < τ) (hMc : 0 < Mc)
    (hτRc : τ ≤ Rc / 16)
    {Ω Kc : Set (Euclidean n × Euclidean 3)}
    (hbuffer : MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
      (closedBall (0, ((0 : Euclidean (n - 1)), zCell)) Rc) Kc)
    {E : Set (Euclidean n × CarrierParameter)} (hE : IsOpen E)
    (hlabel : ∀ p ∈ E,
      (densityCoordinates T p).2 ∈ closedBall ((0 : Euclidean (n - 1)), zCell) (L / 64))
    (houtput : MapsTo (densityCoordinates T) E
      (outputCylinder ((0 : Euclidean (n - 1)), zCell) Rc τ)) :
    ∃ E' : Set (Euclidean n × CarrierParameter), IsOpen E' ∧ E' ⊆ E ∧
      (∀ z : CarrierParameter, ((0 : Euclidean n), z) ∈ E' ↔
        ((0 : Euclidean n), z) ∈ E) ∧
      MapsTo (densityCoordinates T) E'
        (outputCylinder ((0 : Euclidean (n - 1)), zCell) Rc τ) ∧
      ∀ (F : Euclidean n → Euclidean N) (row col : Fin n)
        (c : Chart T Ω Kc ((0 : Euclidean (n - 1)), zCell) Rc B τ row col F),
        cNorm (Icc (-τ) τ ×ˢ closedBall ((0 : Euclidean (n - 1)), zCell) (Rc / 8))
          1 c.forward ≤ Mc →
        MapsTo (densityCoordinates T) E' c.D ∧
        MapsTo (fun p : Euclidean n × CarrierParameter ↦ (p.1, parameter p.2)) E' Kc ∧
        ContDiffOn ℝ ∞ (densityFootpoint T c.inverse) E' ∧
        MapsTo (densityFootpoint T c.inverse) E'
          (ball ((0 : Euclidean (n - 1)), zCell) (L / 16)) ∧
        (∀ σ ∈ Ioc (0 : ℝ) 1,
          MapsTo (densityFootpoint T (sourceTransportFlow c.inverse σ)) E'
            (ball ((0 : Euclidean (n - 1)), zCell) (L / 16))) ∧
        ∀ (R : ℝ), 0 < R → ∀ V : Set CarrierParameter, IsOpen V →
          ball (0 : Euclidean n) R ×ˢ V ⊆ E' →
        ∀ (S : Set (Euclidean n × CarrierParameter)), IsCompact S →
          S ⊆ ball 0 R ×ˢ V → ∀ (K : Set (InputVariables n)), IsCompact K →
          (∀ side, MapsTo (densityEndpoint side) K S) →
        ∀ m : ℕ, ∃ A > (0 : ℝ), ∀ ε > (0 : ℝ),
          ∃ s > (0 : ℝ), s ≤ 1 ∧ ∀ σ ∈ Ioc (0 : ℝ) s,
          ∀ Yσ : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3,
          EqOn (densityFootpoint T Yσ)
            (densityFootpoint T (sourceTransportFlow c.inverse σ)) (ball 0 R ×ˢ V) →
          ∀ (d₀ : ℕ), m + 1 ≤ d₀ →
          ∀ (v : Euclidean (n - 1) × Euclidean 3 → ℝ),
          (∀ q ∈ closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8), ContDiffAt ℝ ∞ v q) →
          cNorm (closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8)) d₀ v ≤ 1 →
          cNorm K m (canonicalDensityPair T v Yσ) ≤ A ∧
          cNorm K m (sourceDensityPairLimit T v c.inverse) ≤ A ∧
          cNorm K m (canonicalDensityPair T v Yσ - sourceDensityPairLimit T v c.inverse) < ε := by
  obtain ⟨E', hE', hsub, hzero, houtput', hcharts⟩ :=
    exists_original_source_label_region (N := N) T zCell hL hRc hτ hMc hτRc
      (Ω := Ω) (B := B) hbuffer hE hlabel houtput
  refine ⟨E', hE', hsub, hzero, houtput', ?_⟩
  intro F row col c hforward
  obtain ⟨hD, hcoeff, hsmooth, hrange, hsource⟩ := hcharts F row col c hforward
  refine ⟨hD, hcoeff, hsmooth, hrange, hsource, ?_⟩
  intro R hR V hV hproduct S hS hSV K hK hKS m
  have hY := hsmooth.mono hproduct
  have hYzero (z) (hz : z ∈ V) : (densityFootpoint T c.inverse (0, z)).1 = 0 := by
    have hp := hproduct (show ((0 : Euclidean n), z) ∈ ball 0 R ×ˢ V from
      ⟨mem_ball_self hR, hz⟩)
    have hh := (outputCylinder_spec hRc hτ).2 (houtput' hp)
    have hlabel₀ : ((0 : Euclidean (n - 1)), parameter z) ∈
        ball ((0 : Euclidean (n - 1)), zCell) (Rc / 8) := by
      apply ball_subset_ball (show Rc / 32 ≤ Rc / 8 by linarith)
      simpa [densityCoordinates, coordinates_apply] using hh.2
    have he := c.inverse_forward _ hlabel₀ 0 ⟨neg_neg_of_pos hτ, hτ⟩
    rw [c.initial _ hlabel₀] at he
    simpa [densityFootpoint, densityCoordinates, coordinates_apply] using congrArg Prod.fst he
  have hparam (p) (hp : p ∈ ball (0 : Euclidean n) R ×ˢ V) :
      (densityFootpoint T c.inverse p).2 = parameter p.2 :=
    c.inverse_parameter _ (hD (hproduct hp))
  obtain ⟨A, hA, hsmall⟩ := exists_retained_source_densityPair_comparison T hR hV hY hYzero
    hparam hS hSV hK hKS hL zero_lt_one
    (fun σ hσ ↦ (hsource σ hσ).mono_left (hSV.trans hproduct)) m
  refine ⟨A, hA, ?_⟩
  intro ε hε
  obtain ⟨s, hs, hs1, _, hcompare⟩ := hsmall ε hε
  exact ⟨s, hs, hs1, hcompare⟩

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedRowGeometry
