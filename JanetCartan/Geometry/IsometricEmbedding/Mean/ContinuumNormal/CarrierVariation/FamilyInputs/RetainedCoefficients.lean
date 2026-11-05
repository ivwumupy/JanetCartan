module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SeedPhase
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.NormalizedCoefficients

/-!
# Primitive coefficient norms for the literal normalized carrier

The coefficient fields here are extracted by `coefficientsOfCarrier` from
`normalizedCarrierData`, with the actual canonical completion, selected null
column and scalar transport. They are identified with the shared normalized
source coefficients before taking finite norms. The primitive seed null
amplitude smoothness is an output of `carrierScalarAmplitude_spec` and
`exists_finite_flat_seed_unit_transports`; selecting these on the same admitted
seed and matching the scaled flows remain the source-family assembly's work.

Consumer: the `CoefficientNormCharts` inputs of full-amplitude comparison,
`app:ch_background:prop:bg-normalized`, `app:ch_osc:prop:osc-normal`, Step 4'.
The scalar formula still uses the ODE inverse, not the Hamilton transport.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 800000
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
open ActualCarriers FrozenMenu CurrentFullPhase ContinuumRow CanonicalCarrier FrozenModel
open NormalizedBackground NormalizedBackground.SourceGeometry NullTransport
open ContinuumNormalReduction.TransportSymbol

private theorem tendsto_coefficientNorms_of_eqOn
    {n N : ℕ} (a b : ℝ → Coefficients n N) (D : CoefficientNormCharts n) (m : ℕ)
    {I : Set ℝ} (hI : IsOpen I) (h0 : (0 : ℝ) ∈ I)
    {W : Set (Euclidean n × CarrierParameter)} (hW : IsOpen W) (hDW : D.field.carrier ⊆ W)
    (heq : ∀ σ ∈ I, ∀ p ∈ W,
      (a σ).normal p = (b σ).normal p ∧ (a σ).reduced p = (b σ).reduced p)
    (hn : Tendsto (fun σ ↦ cNorm D.field.carrier m ((b σ).normal - (b 0).normal)) (𝓝 0) (𝓝 0))
    (hq : Tendsto (fun σ ↦ cNorm D.field.carrier m ((b σ).reduced - (b 0).reduced)) (𝓝 0) (𝓝 0)) :
    Tendsto (fun σ ↦ cNorm D.field.carrier m ((a σ).normal - (a 0).normal)) (𝓝 0) (𝓝 0) ∧
    Tendsto (fun σ ↦ cNorm D.field.carrier m ((a σ).reduced - (a 0).reduced)) (𝓝 0) (𝓝 0) := by
  have hnorm (σ : ℝ) (hσ : σ ∈ I) :
      cNorm D.field.carrier m ((a σ).normal - (a 0).normal) =
        cNorm D.field.carrier m ((b σ).normal - (b 0).normal) ∧
      cNorm D.field.carrier m ((a σ).reduced - (a 0).reduced) =
        cNorm D.field.carrier m ((b σ).reduced - (b 0).reduced) := by
    constructor
    · refine GeometricProfile.cNorm_eq_of_eventuallyEq
        (f := (a σ).normal - (a 0).normal) (g := (b σ).normal - (b 0).normal) ?_ m
      intro p hp
      filter_upwards [hW.mem_nhds (hDW hp)] with q hq
      simpa only [Pi.sub_apply] using congrArg₂ (· - ·) (heq σ hσ q hq).1 (heq 0 h0 q hq).1
    · refine GeometricProfile.cNorm_eq_of_eventuallyEq
        (f := (a σ).reduced - (a 0).reduced) (g := (b σ).reduced - (b 0).reduced) ?_ m
      intro p hp
      filter_upwards [hW.mem_nhds (hDW hp)] with q hq
      simpa only [Pi.sub_apply] using congrArg₂ (· - ·) (heq σ hσ q hq).2 (heq 0 h0 q hq).2
  have hne : (fun σ ↦ cNorm D.field.carrier m ((b σ).normal - (b 0).normal)) =ᶠ[𝓝 0]
      (fun σ ↦ cNorm D.field.carrier m ((a σ).normal - (a 0).normal)) := by
    filter_upwards [hI.mem_nhds h0] with σ hσ
    exact (hnorm σ hσ).1.symm
  have hqe : (fun σ ↦ cNorm D.field.carrier m ((b σ).reduced - (b 0).reduced)) =ᶠ[𝓝 0]
      (fun σ ↦ cNorm D.field.carrier m ((a σ).reduced - (a 0).reduced)) := by
    filter_upwards [hI.mem_nhds h0] with σ hσ
    exact (hnorm σ hσ).2.symm
  exact ⟨Filter.Tendsto.congr' hne hn, Filter.Tendsto.congr' hqe hq⟩

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q₀ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)
    (measurement : Euclidean n → ℝ)

/-- Identification of the two nonconstant primitive coefficients of the
literal normalized carrier, including at scale zero. The normal is the
canonical normal of the actual scalar/null-column amplitude. The detector
uses the same seed stress and phase gradient. Consumer: the finite coefficient
norm limit below (`app:ch_background:eq:bg-Nsigma`). -/
theorem coefficientsOfCarrier_normalizedCarrierData_eq_source
    {c C : ℝ} (hP : P.IsValid c C)
    (hseed : Q₀.1 = ProjectedStressFrame.projectedStress F)
    {σ : ℝ} {p : Euclidean n × CarrierParameter}
    (hx : σ • p.1 ∈ ball (0 : Euclidean n) T.physicalRadius)
    (hz : parameter p.2 ∈ parameterInterior (2 * P.radius)) :
    let a := TransportKernel.coefficientsOfCarrier
      (normalizedCarrierData T Q₀ F row col Φ Y initial hr hcell angular high σ) measurement
    let b := normalizedSourceCoefficients F
      (fun q ↦ T.carrierGradient Q₀ q.1 (parameter q.2))
      (fun q ↦ carrierScalarAmplitude T Q₀ F row col Φ Y initial (q.1, parameter q.2) •
        carrierNullvector T Q₀ col (q.1, parameter q.2))
      measurement (fun q ↦ angular q.1 q.2) high σ
    a.normal p = b.normal p ∧ a.reduced p = b.reduced p := by
  constructor
  · rfl
  · funext i
    change (∑ j, ∑ k, Q₀.1 (σ • p.1) i j k *
      (normalizedCovector T Q₀ σ p.1 p.2 j * normalizedCovector T Q₀ σ p.1 p.2 k)) = _
    rw [normalizedCovector_eq_retainedCarrierGradient T Q₀ hP hx hz, hseed]
    change (∑ j, ∑ k, ProjectedStressFrame.projectedStress F (σ • p.1) i j k *
      (T.carrierGradient Q₀ (σ • p.1) (parameter p.2) j *
        T.carrierGradient Q₀ (σ • p.1) (parameter p.2) k)) =
      ∑ j, ∑ k, T.carrierGradient Q₀ (σ • p.1) (parameter p.2) j *
        ProjectedStressFrame.projectedStress F (σ • p.1) i j k *
          T.carrierGradient Q₀ (σ • p.1) (parameter p.2) k
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring

/-- Finite primitive convergence on exactly the prescribed coefficient norm
chart, for the literal normalized carrier. Only smoothness of the actual seed
null amplitude is an analytic transport input; the scalar ODE construction
supplies it through `carrierScalarAmplitude_spec`. Canonical normal and reduced
detector regularity and convergence are proved here. All masks remain fixed.
The common-seed assembly must instantiate the seed amplitude input rather than
identify two independent choices of source scale. Source:
`app:ch_background:prop:bg-normalized`, `app:ch_osc:prop:osc-normal`, Step 4'. -/
theorem tendsto_normalizedCarrierData_coefficients_sub_cNorm
    {c C : ℝ} (hP : P.IsValid c C)
    (hseed : Q₀.1 = ProjectedStressFrame.projectedStress F)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    {R : ℝ} (hR : 0 < R) (hRT : R ≤ T.physicalRadius)
    (hRU : ball (0 : Euclidean n) R ⊆ U)
    {V : Set CarrierParameter} (hV : IsOpen V)
    (hVP : V ⊆ parameter ⁻¹' parameterInterior (3 * P.radius / 2))
    (hb : ContDiffOn ℝ ∞
      (fun q : Euclidean n × CarrierParameter ↦
        carrierScalarAmplitude T Q₀ F row col Φ Y initial (q.1, parameter q.2) •
          carrierNullvector T Q₀ col (q.1, parameter q.2)) (ball 0 R ×ˢ V))
    (D : CoefficientNormCharts n) (hDV : MapsTo Prod.snd D.field.carrier V) (m : ℕ) :
    let a := fun σ ↦ TransportKernel.coefficientsOfCarrier
      (normalizedCarrierData T Q₀ F row col Φ Y initial hr hcell angular high σ) measurement
    Tendsto (fun σ ↦ cNorm D.field.carrier m ((a σ).normal - (a 0).normal)) (𝓝 0) (𝓝 0) ∧
    Tendsto (fun σ ↦ cNorm D.field.carrier m ((a σ).reduced - (a 0).reduced)) (𝓝 0) (𝓝 0) := by
  let a := fun σ ↦ TransportKernel.coefficientsOfCarrier
    (normalizedCarrierData T Q₀ F row col Φ Y initial hr hcell angular high σ) measurement
  let b := normalizedSourceCoefficients F
    (fun q ↦ T.carrierGradient Q₀ q.1 (parameter q.2))
    (fun q ↦ carrierScalarAmplitude T Q₀ F row col Φ Y initial (q.1, parameter q.2) •
      carrierNullvector T Q₀ col (q.1, parameter q.2))
    measurement (fun q ↦ angular q.1 q.2) high
  have hD : IsCompact D.field.carrier := isCompact_closedBall _ _
  obtain ⟨B, hB, hDB, e, he, hseg⟩ := exists_source_phase_buffer isOpen_ball
    (mem_ball_self hR) (hD.image continuous_fst)
  have hmaps : ∀ σ ∈ Ioo (-2 * e) (2 * e), MapsTo (fun x ↦ σ • x) B (ball 0 R) := by
    intro σ hσ x hx
    simpa using hseg σ hσ x hx 1 ⟨by norm_num, by norm_num⟩
  have hVP' : ∀ z ∈ V, parameter z ∈ parameterInterior (2 * P.radius) :=
    fun z hz i ↦ (hVP hz i).trans (by linarith [hP.1])
  have hξ : ContDiffOn ℝ ∞ (fun q : Euclidean n × CarrierParameter ↦
      T.carrierGradient Q₀ q.1 (parameter q.2)) (ball 0 R ×ˢ V) := by
    have harg : ContDiffOn ℝ ∞
        (fun q : Euclidean n × CarrierParameter ↦ (q.1, parameter q.2)) (ball 0 R ×ˢ V) :=
      contDiffOn_fst.prodMk (parameter.contDiff.comp_contDiffOn contDiffOn_snd)
    simpa only [Function.comp_def] using (T.carrierGradient_smooth hP Q₀).comp harg
      (fun q hq ↦ ⟨ball_subset_ball hRT hq.1, hVP' q.2 hq.2⟩)
  have hzero : (0 : ℝ) ∈ Ioo (-2 * e) (2 * e) := ⟨by linarith, by linarith⟩
  obtain ⟨hn, hq⟩ := tendsto_normalizedSourceCoefficients_sub_cNorm
    isOpen_ball hB hV isOpen_Ioo (hF.mono hRU)
    (fun x hx ↦ hi x (hRU hx)) (fun x hx ↦ hrank x (hRU hx))
    hξ hb hmaps D (fun p hp ↦ ⟨hDB ⟨p, hp, rfl⟩, hDV hp⟩)
    measurement (fun q ↦ angular q.1 q.2) high hzero m
  have heq (σ : ℝ) (hσ : σ ∈ Ioo (-2 * e) (2 * e)) (p : Euclidean n × CarrierParameter)
      (hp : p ∈ B ×ˢ V) :
      (a σ).normal p = (b σ).normal p ∧ (a σ).reduced p = (b σ).reduced p :=
    coefficientsOfCarrier_normalizedCarrierData_eq_source T Q₀ F row col Φ Y initial
      hr hcell angular high measurement hP hseed (σ := σ) (p := p)
      (ball_subset_ball hRT (hmaps σ hσ hp.1)) (hVP' p.2 hp.2)
  have hh := tendsto_coefficientNorms_of_eqOn a b D m isOpen_Ioo hzero
    (hB.prod hV) (fun p hp ↦ ⟨hDB ⟨p, hp, rfl⟩, hDV hp⟩) heq hn hq
  exact hh

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
