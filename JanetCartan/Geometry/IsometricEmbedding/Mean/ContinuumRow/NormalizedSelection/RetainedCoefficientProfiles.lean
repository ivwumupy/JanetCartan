module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedSelection.RetainedCharts
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedCarrierProfiles.SeedCoefficients
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.MatchedCoefficients

/-!
# Uniform coefficients of the actual retained source carriers

Instantiate the normalized coefficient producer on the original seed chart.
The seed scalar's smoothness follows from its actual transport construction.
Source uniqueness then transfers every coefficient budget to any supplied
contracted chart with the same minor and domains. The original masks and
physical measurement are used in both coefficient arrays.

Consumer: the high profiles of the full reflected amplitude on the same
finite row (`app:ch_background:eq:bg-full-complex-amplitude`,
`app:ch_background:prop:bg-normalized`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open Set Metric Filter
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumRow.NormalizedSelection

open ActualCarriers FrozenMenu CurrentFullPhase CanonicalCarrier
open ContinuumNormal.FrozenModel ContinuumNormal.CarrierVariation.FamilyInputs
open PositiveReference PositiveReference.FlowConstruction RetainedLeading
open NullTransport ActualFlow FlowAmplitude HamiltonPhase
open ContinuumNormalReduction.TransportSymbol

/-- Equality on the original open coefficient region preserves all finite
norms on its compact carrier (`app:ch_background:eq:bg-mixed-input`). -/
private theorem primitiveControls_of_eqOn {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {D : PrimitiveNormChart E} {p : ℕ} {M B H : ℝ} {f g : E → F}
    (h : D.Controls p M B H f) (heq : EqOn g f D.region) : D.Controls p M B H g := by
  have hnorm (m : ℕ) : cNorm D.carrier m g = cNorm D.carrier m f := by
    apply GeometricProfile.cNorm_eq_of_eventuallyEq _ m
    intro x hx
    exact Filter.eventuallyEq_of_mem (D.isOpen_region.mem_nhds (D.ball_subset hx))
      (fun _ hy ↦ heq hy)
  exact ⟨h.smooth.congr (fun _ hx ↦ heq hx), (hnorm 1).trans_le h.low,
    by rw [hnorm]; exact h.high⟩

/-- All five actual carrier coefficients have uniform bounds at every
order on one source interval. Constants precede `σ` and the contracted chart;
the original seed and source charts are connected by ODE uniqueness. The
seed null amplitude's smoothness is proved from `Chart.scalar_spec`, not
assumed. No operator, normal-amplitude or inverse estimate is an input.

The product lies in the original carrier cylinder; its center need not be
the incidence root. The initial scalar here is exactly `σ`. Variable initial
densities retain their separate original-domain one-high estimate
(`app:ch_background:eq:bg-Nsigma`, `app:ch_background:prop:bg-normalized`). -/
theorem exists_retained_chart_source_coefficient_profiles
    {n N : ℕ} {P : Patch n} {c C : ℝ} (hP : P.IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    {Ω : Set (Euclidean n × Euclidean 3)} (hΩ : IsOpen Ω)
    {zCell : Euclidean 3} {ρ Rc Bflow τ : ℝ} {row col : Fin n}
    (hKΩ : closedBall ((0 : Euclidean n), zCell) ρ ⊆ Ω)
    (hΩpatch : Ω ⊆ (U ∩ ball 0 T.physicalRadius) ×ˢ
      parameterInterior (3 * P.radius / 2))
    (hRc : 0 < Rc) (hτ : 0 < τ) (hτR : τ ≤ Rc / 16)
    (hbuffer : MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
      (closedBall (0, ((0 : Euclidean (n - 1)), zCell)) Rc)
      (closedBall ((0 : Euclidean n), zCell) ρ))
    {F : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F)
    (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (seed : Chart T Ω (closedBall ((0 : Euclidean n), zCell) ρ)
      ((0 : Euclidean (n - 1)), zCell) Rc Bflow τ row col F)
    (htrans : ∀ q ∈ closedBall (0, T.data.center) T.data.localReference.stateRadius,
      ⟪(normalizedHomogeneousSymbol hU seed.Q.1 seed.Q.2.1).hp q,
        T.data.adapted.normal⟫_ℝ ≠ 0)
    (hflat : ∀ x ∈ U, inducedMetric F x = 1)
    {R : ℝ} (hR : 0 < R) (hRT : R ≤ T.physicalRadius)
    (hRU : ball (0 : Euclidean n) R ⊆ U)
    {V : Set CarrierParameter} (hV : IsOpen V)
    (hVP : V ⊆ parameter ⁻¹' parameterInterior (3 * P.radius / 2))
    (hcoordinates : MapsTo (densityCoordinates T) (ball (0 : Euclidean n) R ×ˢ V)
      (Ioo (-τ) τ ×ˢ ball ((0 : Euclidean (n - 1)), zCell) (Rc / 32)))
    (D : CoefficientNormCharts n) (hD : D.field.region ⊆ ball (0 : Euclidean n) R ×ˢ V)
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)
    (ha : ContDiffOn ℝ ∞ (fun p ↦ angular p.1 p.2) D.angular.region)
    (hh : ContDiffOn ℝ ∞ high D.high.region) :
    ∃ M > (0 : ℝ), ∃ B : ℕ → ℝ, (∀ p, 1 ≤ B p) ∧
      ∀ σ ∈ Ioc (0 : ℝ) 1,
      ∀ current : Chart T Ω (closedBall ((0 : Euclidean n), zCell) ρ)
        ((0 : Euclidean (n - 1)), zCell) Rc Bflow τ row col (sourceDilation F σ),
      ∀ p, D.Controls p M (B p) 1
        (TransportKernel.coefficientsOfCarrier
          (data T current.Q (sourceDilation F σ) row col current.forward current.inverse
            (fun _ ↦ σ) hr hcell angular high) (FixedCutoffs.physical hr 1)) := by
  have hmaps : MapsTo (fun p : Euclidean n × CarrierParameter ↦ (p.1, parameter p.2))
      (ball 0 R ×ˢ V) ((coordinates (adaptedCoordinates T.data.adapted)) ⁻¹' seed.D) :=
    fun _ hp ↦ seed.small_subset (hcoordinates hp)
  obtain ⟨_, hb, _, _, _, _, _, _⟩ :=
    seed.scalar_spec hτ (fun _ ↦ 1) contDiffOn_const (fun _ _ ↦ zero_lt_one)
  have hb' := hb.comp
    (contDiff_fst.prodMk (parameter.contDiff.comp contDiff_snd)).contDiffOn hmaps
  obtain ⟨M, hM, B, hB, hcontrols⟩ :=
    NormalizedCarrierProfiles.exists_normalizedCarrierData_all_order_controls
      T seed.Q F row col seed.forward seed.inverse (fun _ ↦ 1) hr hcell angular high
      (FixedCutoffs.physical hr 1) hP seed.frame_eq hF.contDiffOn hi hrank hR hRT hRU
      hV hVP hb' D hD (FixedCutoffs.physical hr 1).contDiff.contDiffOn ha hh
  refine ⟨M, hM, B, hB, ?_⟩
  intro σ hσ current p
  have hpatch : Ω ⊆ ball 0 T.physicalRadius ×ˢ parameterCube (2 * P.radius) := by
    intro w hw
    exact ⟨(hΩpatch hw).1.2, fun i ↦ ((hΩpatch hw).2 i).le.trans (by linarith [hP.1])⟩
  obtain ⟨_, _, _, hnull, _⟩ := retained_charts_source_dilation T hΩ hKΩ hpatch
    hRc hτ hτR hbuffer hF hrank hphysical seed htrans hflat hσ.1 hσ.2 current
  have hfields (w) (hw : w ∈ D.field.region) :=
    coefficientsOfCarrier_current_eq_normalized hP T seed.Q current.Q hF hrank hphysical
      seed.frame_eq htrans hσ.1 hσ.2 current.frame_eq row col seed.forward seed.inverse
      current.forward current.inverse hr hcell angular high
      (ball_subset_ball hRT (hD hw).1)
      (fun i ↦ (hVP (hD hw).2 i).trans (by linarith [hP.1]))
      (hnull (current.small_subset (hcoordinates (hD hw))))
  have hc := hcontrols σ ⟨hσ.1.le, hσ.2⟩ p
  exact ⟨hc.measurement, hc.angular, hc.high,
    primitiveControls_of_eqOn hc.normal (fun _ hw ↦ (hfields _ hw).1),
    primitiveControls_of_eqOn hc.reduced (fun _ hw ↦ (hfields _ hw).2)⟩

end JanetCartan.ContinuumRow.NormalizedSelection
