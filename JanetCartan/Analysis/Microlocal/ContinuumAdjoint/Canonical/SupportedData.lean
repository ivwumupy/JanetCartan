module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.PhaseExtension
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.Footpoint
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.Assembly.TransportComponents

/-!
# Supported extensions represent the original canonical carrier

The global phase and scalar-transport endpoint must act on the original
kernel in `app:ch_background:eq:bg-T`. The data below retain its chart,
measurement, angular and radial masks, stress frame, covector and measures.
Only the transported position and scalar-factorized normal are extended.
Agreement on the complete supported chart implies exact equality of the
kernels, test integrals, every radial regularization and adjoint integrals.

The consumer is the canonical instantiation of
`exists_scalarTransportCarrierAdjoint_periodic_raw_bound`. No boundedness
or Sobolev estimate is assumed or proved by these locality identities.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint.Canonical
open ContinuumRow DerivativeKernels PhaseExtension
open ActualCarriers FrozenMenu CurrentFullPhase

variable {n N : ℕ}

/-- The data used by the global scalar-transport adjoint calculation. The
normal is constructed from the original scalar, flow and geometric normal;
the remaining kernel fields are retained (`app:ch_background:eq:bg-T`). -/
def scalarTransportData (d : CarrierData n N)
    (Y : Euclidean n × CarrierParameter → Euclidean (n - 1))
    (r : CarrierVariable n → ℝ) (flow : AdjointJetPoint n → ℝ)
    (ν : AdjointJetPoint n → Euclidean N) : CarrierData n N :=
  { d with
    transportedPosition := fun x z ↦ Y (x, z)
    normalField := fun x z ↦ (r (z, Y (x, z)) * flow (z, x)) • ν (z, x) }

/-- The endpoint's scalar formula follows from the constructed function data.
Local agreement with the actual transported normal is proved separately,
before using this data for the original kernel
(`app:ch_background:prop:bg-adjoint`). -/
theorem scalarTransportData_normalField (d : CarrierData n N)
    (Y : Euclidean n × CarrierParameter → Euclidean (n - 1))
    (r : CarrierVariable n → ℝ) (flow : AdjointJetPoint n → ℝ)
    (ν : AdjointJetPoint n → Euclidean N) (x : Euclidean n) (z : CarrierParameter) :
    (scalarTransportData d Y r flow ν).normalField x z =
      (r (z, (scalarTransportData d Y r flow ν).transportedPosition x z) *
        flow (z, x)) • ν (z, x) := rfl

/-- The phase passed to the raw endpoint is exactly the extended Hamilton
phase, with its physical radian frequency
(`app:ch_background:eq:bg-derivative-trade`). -/
theorem carrierChartPhase_scalarTransportData (d : CarrierData n N)
    (Y : Euclidean n × CarrierParameter → Euclidean (n - 1))
    (r : CarrierVariable n → ℝ) (flow : AdjointJetPoint n → ℝ)
    (ν : AdjointJetPoint n → Euclidean N) :
    carrierChartPhase (scalarTransportData d Y r flow ν) = phase Y := rfl

/-- The geometric component still uses the original detector and stress
contraction; replacing the phase does not change it
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem carrierChartGeometryComponent_scalarTransportData (d : CarrierData n N)
    (Y : Euclidean n × CarrierParameter → Euclidean (n - 1))
    (r : CarrierVariable n → ℝ) (flow : AdjointJetPoint n → ℝ)
    (ν : AdjointJetPoint n → Euclidean N) (χ : Euclidean n → ℝ) (j : Fin n) :
    carrierChartGeometryComponent (scalarTransportData d Y r flow ν) χ ν j =
      carrierChartGeometryComponent d χ ν j := rfl

/-- A supported replacement preserves the literal kernel. The only agreement
premises concern function values where both original masks are nonzero;
there is no operator or regularity premise (`app:ch_background:eq:bg-T`). -/
theorem carrierKernel_scalarTransportData_eq (d : CarrierData n N)
    (Y : Euclidean n × CarrierParameter → Euclidean (n - 1))
    (r : CarrierVariable n → ℝ) (flow : AdjointJetPoint n → ℝ)
    (ν : AdjointJetPoint n → Euclidean N)
    (hlocal : ∀ x ∈ d.outputChart, d.measurementCutoff x ≠ 0 →
      ∀ z θ, d.angularCutoff z θ ≠ 0 →
        Y (d.chartPoint x, z) = d.transportedPosition (d.chartPoint x) z ∧
        (r (z, Y (d.chartPoint x, z)) * flow (z, d.chartPoint x)) •
          ν (z, d.chartPoint x) = d.normalField (d.chartPoint x) z) :
    carrierKernel (scalarTransportData d Y r flow ν) = carrierKernel d := by
  classical
  funext x u
  by_cases hx : x ∈ d.outputChart
  · by_cases hm : d.measurementCutoff x = 0
    · simp [carrierKernel, scalarTransportData, carrierAmplitude, hx, hm]
    · by_cases ha : d.angularCutoff u.1 (‖u.2‖⁻¹ • u.2) = 0
      · simp [carrierKernel, scalarTransportData, carrierAmplitude, hx, ha]
      · obtain ⟨hY, hν⟩ := hlocal x hx hm u.1 (‖u.2‖⁻¹ • u.2) ha
        simp only [carrierKernel, scalarTransportData, indicator_of_mem hx,
          ContinuumRow.carrierPhase, carrierAmplitude, reducedCovector]
        rw [hν, hY]
  · simp [carrierKernel, scalarTransportData, hx]

/-- Equality of supported kernels preserves the original Lebesgue source
integral without a coordinate change (`app:ch_background:eq:bg-T`). -/
theorem carrierTestIntegral_congr_kernel {d₁ d₂ : CarrierData n N}
    (h : carrierKernel d₁ = carrierKernel d₂) :
    carrierTestIntegral d₁ = carrierTestIntegral d₂ := by
  funext f x
  simp only [carrierTestIntegral, h]

/-- The same kernel agreement holds for every finite source mask, hence for
the actual radial regularizations (`app:ch_background:prop:bg-frame`). -/
theorem regularizedCarrierIntegral_congr_kernel {d₁ d₂ : CarrierData n N}
    (h : carrierKernel d₁ = carrierKernel d₂) :
    regularizedCarrierIntegral d₁ = regularizedCarrierIntegral d₂ := by
  funext m f x
  exact congrFun (congrFun (carrierTestIntegral_congr_kernel h) _) x

/-- The literal adjoint retains both complex quadratures and the original
Haar integral under a supported extension (`app:ch_background:prop:bg-adjoint`). -/
theorem carrierAdjointIntegral_congr_kernel {d₁ d₂ : CarrierData n N}
    (h : carrierKernel d₁ = carrierKernel d₂) :
    carrierAdjointIntegral d₁ = carrierAdjointIntegral d₂ := by
  funext v u
  simp only [carrierAdjointIntegral, h]

variable {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y₀ : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {a b : ℝ} (ha : 0 < a) (hcell : 4 * a < 1 / 2)
    (z₀ : Euclidean 3) (θ₀ : Euclidean (n - 1)) (hb : 0 < b) (high : ℝ → ℝ)

/-- The fixed canonical angular mask and output chart reduce all kernel
agreement obligations to the complete closed supported chart. This is the
same chart on which `exists_projected_supported_phase_inputs` agrees with
the original Hamilton derivative (`app:ch_background:prop:bg-adjoint`). -/
theorem canonical_scalarTransportData_kernel_eq
    (Y : Euclidean n × CarrierParameter → Euclidean (n - 1))
    (r : CarrierVariable n → ℝ) (flow : AdjointJetPoint n → ℝ)
    (ν : AdjointJetPoint n → Euclidean N)
    (hY : EqOn Y (CanonicalCarrier.transportPosition T Q) (supportedChart z₀ a))
    (hν : ∀ p ∈ supportedChart (n := n) z₀ a,
      (r (p.2, Y p) * flow (p.2, p.1)) • ν (p.2, p.1) =
        CanonicalCarrier.normalField T Q F row col Φ Y₀ initial p.1 p.2) :
    let d := CanonicalCarrier.data T Q F row col Φ Y₀ initial ha hcell
      (CanonicalConic.angularMask z₀ θ₀ ha hb) high
    carrierKernel (scalarTransportData d Y r flow ν) = carrierKernel d := by
  dsimp only
  apply carrierKernel_scalarTransportData_eq
  intro x hx _ z θ hθ
  obtain ⟨hz, hv, _⟩ := CanonicalConic.angularMask_nonzero z₀ θ₀ ha hb hθ
  have hp : (AmplitudeBound.centeredTorusRepresentative x, z) ∈
      supportedChart (n := n) z₀ a :=
    ⟨hx, ball_subset_closedBall hz, ball_subset_closedBall hv⟩
  exact ⟨hY hp, hν _ hp⟩

section ActualFlow
open NullTransport ActualFlow FlowAmplitude

/-- Instantiate supported kernel agreement with the SAME actual flow and its
Hamilton conservation law. The flow hypotheses are the retained conclusions
of `NullTransport.exists_projected_local_positive_amplitude`, and symmetry
comes from `projected_frame_symmetry`. Only the fixed geometric containment
of the complete supported chart in that tube is additionally needed.
There is no scalar-composition or adjoint-estimate premise
(`app:ch_background:prop:bg-adjoint`, `app:ch_waves:thm:leading`). -/
theorem canonical_scalarTransportData_kernel_eq_of_flow
    {c C₁ : ℝ} (hP : P.IsValid c C₁)
    {K : Set (Euclidean n)} (hKU : K ⊆ U)
    (hsymm : ∀ x ∈ U, ∀ i, (Q.1 x i).IsSymm)
    {τ : ℝ} (hτ : 0 < τ)
    {L : Set (Euclidean (n - 1) × Euclidean 3)}
    {D : Set (ℝ × (Euclidean (n - 1) × Euclidean 3))}
    (hgeom : (coordinates (adaptedCoordinates T.data.adapted)) ⁻¹' D ⊆
      (ball 0 T.physicalRadius ∩ interior K) ×ˢ parameterInterior (3 * P.radius / 2))
    (hΦD : MapsTo (fun q ↦ (q.1, Φ q)) (Ioo (-τ) τ ×ˢ L) D)
    (hYD : MapsTo (fun q ↦ (q.1, Y₀ q)) D (Ioo (-τ) τ ×ˢ L))
    (hinit : ∀ p ∈ L, Φ (0, p) = p)
    (hinv : ∀ q ∈ D, Φ (q.1, Y₀ q) = q.2)
    (hcarrier : ∀ p ∈ L, ∀ t ∈ Ioo (-τ) τ, (Φ (t, p)).2 = p.2)
    (hYcarrier : ∀ q ∈ D, (Y₀ q).2 = q.2.2)
    (hode : ∀ p ∈ L, ∀ t ∈ Ioo (-τ) τ, HasDerivAt (fun s ↦ Φ (s, p))
      ((adaptedCoordinates T.data.adapted
        (carrierTransportDirection T Q row col
          ((coordinates (adaptedCoordinates T.data.adapted)).symm (t, Φ (t, p))))).2, 0) t)
    (hnull : ∀ w ∈ (coordinates (adaptedCoordinates T.data.adapted)) ⁻¹' D,
      carrierNullvector T Q col w ≠ 0 ∧ carrierConullvector T Q row w ≠ 0 ∧
      carrierConullvector T Q row w ᵥ*
        reducedSymbol (Q.1 w.1) (T.carrierGradient Q w.1 w.2) = 0 ∧
      carrierAdaptedDenominator T Q row col w ≠ 0)
    (hsupport : MapsTo (fun p : Euclidean n × CarrierParameter ↦
        coordinates (adaptedCoordinates T.data.adapted) (p.1, CanonicalCarrier.parameter p.2))
      (supportedChart z₀ a) D)
    (Y : Euclidean n × CarrierParameter → Euclidean (n - 1))
    (hY : EqOn Y (CanonicalCarrier.transportPosition T Q) (supportedChart z₀ a)) :
    let d := CanonicalCarrier.data T Q F row col Φ Y₀ initial ha hcell
      (CanonicalConic.angularMask z₀ θ₀ ha hb) high
    carrierKernel (scalarTransportData d Y (initialScalar initial)
      (flowFactor T Q F row col Φ Y₀) (geometricNormal T Q F col)) = carrierKernel d := by
  apply canonical_scalarTransportData_kernel_eq
    T Q F row col Φ Y₀ initial ha hcell z₀ θ₀ hb high Y
    (initialScalar initial) (flowFactor T Q F row col Φ Y₀)
    (geometricNormal T Q F col) hY
  intro p hp
  rw [hY hp]
  exact (normalField_eq_initialScalar_transportPosition T Q row col hP hKU hsymm hτ
    Φ Y₀ hgeom hΦD hYD hinit hinv hcarrier hYcarrier hode hnull F initial
    (hsupport hp)).symm

end ActualFlow

end JanetCartan.ContinuumAdjoint.Canonical
