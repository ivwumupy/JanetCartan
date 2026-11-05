module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedRowGeometry.OriginalSourceDensityConstruction
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedRowGeometry.OutputCylinder
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.FlowConstruction.ForwardBounds

/-!
# Uniform original-density geometry before choosing incidence masks

The original full-modulation working ball gives the scalar label buffer.
The exact carrier existence time and primitive direction bound give one
forward constant for every retained chart. Their time restriction preserves
all zero-position carrier points before the finite incidence selection.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedRowGeometry
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open ContinuumRow CanonicalCarrier LeadingPrimitive PositiveReference PositiveReference.FlowConstruction
open NormalizedBackground.SourceGeometry ContinuumNormalReduction.TransportSymbol WideDensity

/-- Construct the original scalar-domain geometry from the SAME carrier and
full-modulation buffers exported by `ChartCenters.CarrierData`. The label
range and forward bound are proved, with no new flow, inverse or density bound
as a premise. All zero-position incidence points survive, including those
distinct from the scalar cell center; this restriction precedes mask selection.
The source limit remains the divided-footpoint density, and all positive
source contractions use the original density ball. Consumers:
`exists_initialScale_for_selected_retained_history_normal_comparison`,
`exists_retained_joint_geometry_cover` and the retained low-budget row.
Sources: `app:ch_waves:eq:joint-tame`, `app:ch_background:eq:bg-Psi`,
`app:ch_background:prop:bg-normalized`, `app:ch_background:eq:bg-full-complex-amplitude`. -/
theorem exists_uniform_original_density_geometry_before_masks
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (zCell : Euclidean 3) {L Rc B τ σ τfull rcomp δcomp : ℝ}
    (hL : 0 < L) (hRc : 0 < Rc) (hB : 0 ≤ B)
    (hτeq : τ = existenceTime Rc (liftedLowBound T B) / 4)
    {Ω Kc : Set (Euclidean n × Euclidean 3)}
    (hΩ : IsOpen Ω) (hKc : IsCompact Kc) (hKΩ : Kc ⊆ Ω)
    (hbuffer : MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
      (closedBall (0, ((0 : Euclidean (n - 1)), zCell)) Rc) Kc)
    (hσ : 0 < σ)
    (hworking : closedBall ((0 : Euclidean n), (zCell, T.reference.spatialPatch zCell)) (2 * σ) ⊆
      (coordinates (adaptedCoordinates T.data.adapted)).symm ''
        (Icc (-τfull / 2) (τfull / 2) ×ˢ
          closedBall ((0 : Euclidean (n - 1)), (zCell, T.reference.spatialPatch zCell)) (L / 64)))
    {E : Set (Euclidean n × CarrierParameter)} (hE : IsOpen E)
    (hgraph : MapsTo (carrierGraph T) E
      (ball ((0 : Euclidean n), (zCell, T.reference.spatialPatch zCell)) σ))
    (hcomp : MapsTo (densityCoordinates T) E
      (Ioo (-δcomp) δcomp ×ˢ ball ((0 : Euclidean (n - 1)), zCell) rcomp))
    (hrcomp : 0 < rcomp) (hrc : 8 * rcomp ≤ Rc / 32) :
    ∃ Mc > (0 : ℝ),
      (∀ (F : Euclidean n → Euclidean N) (row col : Fin n)
        (c : Chart T Ω Kc ((0 : Euclidean (n - 1)), zCell) Rc B τ row col F),
        cNorm (Icc (-τ) τ ×ˢ closedBall ((0 : Euclidean (n - 1)), zCell) (Rc / 8))
          1 c.forward ≤ Mc) ∧
    ∃ E' : Set (Euclidean n × CarrierParameter), IsOpen E' ∧ E' ⊆ E ∧
      (∀ z : CarrierParameter, ((0 : Euclidean n), z) ∈ E' ↔
        ((0 : Euclidean n), z) ∈ E) ∧
      MapsTo (densityCoordinates T) E'
        (outputCylinder ((0 : Euclidean (n - 1)), zCell) Rc τ) ∧
      (∀ p ∈ E', (densityCoordinates T p).2 ∈
        closedBall ((0 : Euclidean (n - 1)), zCell) (L / 64)) ∧
      (∀ p ∈ E', |(densityCoordinates T p).1| < L / (64 * Mc)) ∧
      ∀ (F : Euclidean n → Euclidean N) (row col : Fin n)
        (c : Chart T Ω Kc ((0 : Euclidean (n - 1)), zCell) Rc B τ row col F),
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
  have hτ : 0 < τ := by
    rw [hτeq]
    exact div_pos (existenceTime_pos hRc (liftedLowBound_nonneg T hB)) (by norm_num)
  have hτRc : τ ≤ Rc / 16 := by
    have ht := (existenceTime_le hRc (liftedLowBound_nonneg T hB)).1
    rw [hτeq]
    linarith
  obtain ⟨Mc, hMc, hforward⟩ := exists_retained_chart_forward_bound (N := N)
    hΩ hKc hKΩ hRc hB hτeq hbuffer
  obtain ⟨Eout, hEout, hsubout, hzeroout, houtput⟩ :=
    exists_original_outputCylinder_region T zCell hτ hrcomp hrc hE hcomp
  have hlabels := densityCoordinates_mem_original_cylinder T zCell hσ hgraph hworking
  let Et := Eout ∩ (fun p ↦ (densityCoordinates T p).1) ⁻¹'
    Ioo (-(L / (64 * Mc))) (L / (64 * Mc))
  have hEt : IsOpen Et := hEout.inter
    (isOpen_Ioo.preimage (densityCoordinates T).continuous.fst)
  have ht : 0 < L / (64 * Mc) := div_pos hL (by positivity)
  have hzero (z : CarrierParameter) : ((0 : Euclidean n), z) ∈ Et ↔
      ((0 : Euclidean n), z) ∈ E := by
    constructor
    · intro hz
      exact (hzeroout z).mp hz.1
    · intro hz
      refine ⟨(hzeroout z).mpr hz, ?_⟩
      change (adaptedCoordinates T.data.adapted (0 : Euclidean n)).1 ∈
        Ioo (-(L / (64 * Mc))) (L / (64 * Mc))
      simpa only [map_zero, Prod.fst_zero, mem_Ioo, neg_lt_zero] using And.intro ht ht
  obtain ⟨E', hE', hsub, hzero', houtput', hcharts⟩ :=
    exists_original_source_density_region (N := N) T zCell hL hRc hτ hMc hτRc
      (Ω := Ω) (B := B) hbuffer hEt
      (fun p hp ↦ (hlabels (hsubout hp.1)).2) (houtput.mono_left inter_subset_left)
  refine ⟨Mc, hMc, hforward, E', hE', hsub.trans (inter_subset_left.trans hsubout),
    (fun z ↦ (hzero' z).trans (hzero z)), houtput',
    (fun p hp ↦ (hlabels (hsubout (hsub hp).1)).2),
    (fun p hp ↦ abs_lt.mpr (hsub hp).2), ?_⟩
  intro F row col c
  exact hcharts F row col c (hforward F row col c)

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedRowGeometry
