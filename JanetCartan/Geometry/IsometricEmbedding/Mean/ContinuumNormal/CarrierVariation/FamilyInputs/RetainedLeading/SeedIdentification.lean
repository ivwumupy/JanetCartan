module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading.SourceMatching
public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SeedScalarMatching

/-!
# The prescribed seed scalar on the same retained maps

The actual seed transport equation and Cauchy value identify its scalar with
the literal retained-flow formula. This is the relative identification needed
when the normalized mean and the leading family use the same selected minor.
It never identifies different minors. The source identity retains an arbitrary
initial multiplier at the ACTUAL current ODE inverse, as required by the wider
density class in `app:ch_background:prop:bg-frame`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open PositiveReference PositiveReference.FlowConstruction HamiltonPhase ProjectedStressFrame
open NormalizedBackground NormalizedBackground.SourceGeometry SourceMatching
open ContinuumRow CanonicalCarrier

/-- Apply scalar uniqueness to the supplied retained chart and a prescribed
seed scalar. Every flow and coefficient premise is supplied by the chart;
only the scalar's actual PDE and initial data remain, as exported by the
normalized-seed producer (`app:ch_background:eq:bg-Nsigma`). -/
theorem retained_chart_scalar_eq_of_transport
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    {T : PatchQuantitativeFamily P U hU}
    {Ω K : Set (Euclidean n × Euclidean 3)}
    {p₀ : Euclidean (n - 1) × Euclidean 3} {Rc B τ : ℝ} {row col : Fin n}
    {F : Euclidean n → Euclidean N}
    (c : Chart T Ω K p₀ Rc B τ row col F) (hτ : 0 < τ)
    {α : Euclidean n × Euclidean 3 → ℝ} {a : ℝ}
    (hα : ContDiffOn ℝ ∞ α (coordinates (adaptedCoordinates T.data.adapted) ⁻¹' c.D))
    (hpde : ∀ w ∈ coordinates (adaptedCoordinates T.data.adapted) ⁻¹' c.D,
      fderiv ℝ (fun x ↦ α (x, w.2)) w.1 (carrierTransportDirection T c.Q row col w) +
        carrierTransportPotential T c.Q F row col w * α w = 0)
    (hinit : ∀ p ∈ ball p₀ (Rc / 8), α (T.data.adapted.embedding p.1, p.2) = a) :
    EqOn (c.scalar (fun _ ↦ a)) α
      (coordinates (adaptedCoordinates T.data.adapted) ⁻¹' c.D) := by
  let C := coordinates (Z := Euclidean 3) (adaptedCoordinates T.data.adapted)
  have hphys : C ⁻¹' c.D ⊆ Ω := by
    intro w hw
    have hh := c.domain_coefficients hw
    change C.symm (C w) ∈ Ω at hh
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hh
  exact carrierScalarAmplitude_eq_of_transport T c.Q F row col
    isOpen_Ioo ordConnected_Ioo isOpen_ball c.domain_open ⟨by linarith, hτ⟩ hα
    (c.potential_smooth.mono hphys)
    (fun w hw ↦ (c.null_spec w (hphys hw)).2.2.2.2) hpde hinit
    c.forward_smooth c.forward_range c.initial c.inverse_range c.forward_inverse c.ode

/-- Match the literal current scalar with the SAME prescribed seed scalar,
using its PDE and initial value rather than an assumed scalar-gauge identity.
The scaled current domain is proved to lie in the original seed domain by
flow uniqueness and the forward range. An arbitrary initial multiplier remains
at the actual current ODE footpoint; in particular this applies to
`Real.sqrt (1 + v)` with the original density interval and budget unchanged.
Consumer: the source weighted-density assembly (`app:ch_background:eq:bg-Nsigma`,
`app:ch_background:prop:bg-normalized`). -/
theorem retained_charts_source_dilation_prescribed_scalar
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    {Ω : Set (Euclidean n × Euclidean 3)} (hΩ : IsOpen Ω)
    {z₀ : Euclidean 3} {ρ Rc B τ : ℝ} {row col : Fin n}
    (hKΩ : closedBall ((0 : Euclidean n), z₀) ρ ⊆ Ω)
    (hpatch : Ω ⊆ ball 0 T.physicalRadius ×ˢ parameterCube (2 * P.radius))
    (hRc : 0 < Rc) (hτ : 0 < τ) (hτR : τ ≤ Rc / 16)
    (hbuffer : MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
      (closedBall (0, ((0 : Euclidean (n - 1)), z₀)) Rc)
      (closedBall ((0 : Euclidean n), z₀) ρ))
    {F : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F)
    (hrank : HasFullNormalRankOn F U)
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (c₀ : Chart T Ω (closedBall ((0 : Euclidean n), z₀) ρ)
      ((0 : Euclidean (n - 1)), z₀) Rc B τ row col F)
    (htrans : ∀ q ∈ closedBall (0, T.data.center) T.data.localReference.stateRadius,
      ⟪(normalizedHomogeneousSymbol hU c₀.Q.1 c₀.Q.2.1).hp q, T.data.adapted.normal⟫_ℝ ≠ 0)
    (hflat : ∀ x ∈ U, inducedMetric F x = 1)
    {α : Euclidean n × Euclidean 3 → ℝ}
    (hα : ContDiffOn ℝ ∞ α (coordinates (adaptedCoordinates T.data.adapted) ⁻¹' c₀.D))
    (hpde : ∀ w ∈ coordinates (adaptedCoordinates T.data.adapted) ⁻¹' c₀.D,
      fderiv ℝ (fun x ↦ α (x, w.2)) w.1 (carrierTransportDirection T c₀.Q row col w) +
        carrierTransportPotential T c₀.Q F row col w * α w = 0)
    (hinit : ∀ p ∈ ball ((0 : Euclidean (n - 1)), z₀) (Rc / 8),
      α (T.data.adapted.embedding p.1, p.2) = 1)
    {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (cσ : Chart T Ω (closedBall ((0 : Euclidean n), z₀) ρ)
      ((0 : Euclidean (n - 1)), z₀) Rc B τ row col (sourceDilation F σ)) :
    let C := coordinates (Z := Euclidean 3) (adaptedCoordinates T.data.adapted)
    MapsTo (fun w : Euclidean n × Euclidean 3 ↦ (σ • w.1, w.2))
      (C ⁻¹' cσ.D) (C ⁻¹' c₀.D) ∧
    EqOn (cσ.scalar (fun _ ↦ σ)) (sourceAmplitude α σ) (C ⁻¹' cσ.D) ∧
    ∀ weight : Euclidean (n - 1) × Euclidean 3 → ℝ,
      EqOn (cσ.scalar (fun q ↦ σ * weight q))
        (fun w ↦ sourceAmplitude α σ w * weight (cσ.inverse (C w))) (C ⁻¹' cσ.D) := by
  let C := coordinates (Z := Euclidean 3) (adaptedCoordinates T.data.adapted)
  obtain ⟨hflow, _, hscalar, _, _⟩ := retained_charts_source_dilation T hΩ hKΩ hpatch
    hRc hτ hτR hbuffer hF hrank hphysical c₀ htrans hflat hσ hσ1 cσ
  have hseed := retained_chart_scalar_eq_of_transport c₀ hτ hα hpde hinit
  have hmaps : MapsTo (fun w : Euclidean n × Euclidean 3 ↦ (σ • w.1, w.2))
      (C ⁻¹' cσ.D) (C ⁻¹' c₀.D) := by
    intro w hw
    have hp := cσ.inverse_range hw
    have ht : σ * (C w).1 ∈ Ioo (-τ) τ := by
      apply abs_lt.mp
      rw [abs_mul, abs_of_pos hσ]
      exact (mul_le_of_le_one_left (abs_nonneg _) hσ1).trans_lt (abs_lt.mpr hp.1)
    have hl : transportLabelDilation σ (cσ.inverse (C w)) ∈
        ball ((0 : Euclidean (n - 1)), z₀) (Rc / 8) := by
      have hb := hp.2
      simp only [transportLabelDilation, mem_ball, Prod.dist_eq, max_lt_iff,
        dist_zero_right] at hb ⊢
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hσ]
      exact ⟨(mul_le_of_le_one_left (norm_nonneg _) hσ1).trans_lt hb.1, hb.2⟩
    have he := congrArg (transportLabelDilation σ) (hflow hp)
    rw [cσ.forward_inverse _ hw] at he
    simp only [sourceTransportFlow, transportLabelDilation_inv hσ.ne'] at he
    have hh := c₀.forward_range (show (σ * (C w).1,
        transportLabelDilation σ (cσ.inverse (C w))) ∈ Ioo (-τ) τ ×ˢ
        ball ((0 : Euclidean (n - 1)), z₀) (Rc / 8) from ⟨ht, hl⟩)
    change (σ * (C w).1, c₀.forward (σ * (C w).1,
      transportLabelDilation σ (cσ.inverse (C w)))) ∈ c₀.D at hh
    change transportLabelDilation σ (C w).2 =
      c₀.forward (σ * (C w).1, transportLabelDilation σ (cσ.inverse (C w))) at he
    rw [← he] at hh
    change C (σ • w.1, w.2) ∈ c₀.D
    simpa only [C, coordinates_source_dilation, transportCoordinateDilation] using hh
  have hs : EqOn (cσ.scalar (fun _ ↦ σ)) (sourceAmplitude α σ) (C ⁻¹' cσ.D) := by
    intro w hw
    exact (hscalar hw).trans (congrArg (fun b : ℝ ↦ σ • b) (hseed (hmaps hw)))
  refine ⟨hmaps, hs, ?_⟩
  intro weight w hw
  dsimp only
  rw [← hs hw]
  simp only [Chart.scalar, carrierScalarAmplitude, transportFromFootpoint,
    characteristicTransport, scalarTransport]
  ring

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading
