module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.NormalizedNormalLimit.FrozenSourceMatching
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.PrimitiveRealization.Kernel
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.Frequency

/-!
# Original seed kernel from one admitted positive source

The existing frozen substitution charts use only the phase at physical zero.
Transfer those charts to the original seed while keeping its literal normal,
reduced coefficient and density data. The positive source supplies geometric
bounds only; neither the reference map nor its scalar data is replaced.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric MeasureTheory
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.NormalizedNormalLimit
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic FrozenModel RetainedFrozen NullTransport
open ContinuumNormalReduction TransportSymbol TransportKernel CarrierNormalRealization
open CarrierVariation.FamilyInputs NormalizedBackground.SourceGeometry

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q₀ Qσ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    {F : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F)
    (hrank : HasFullNormalRankOn F U)
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (hseed : Q₀.1 = ProjectedStressFrame.projectedStress F)
    (htrans : ∀ z ∈ closedBall (0, T.data.center) T.data.localReference.stateRadius,
      ⟪(normalizedHomogeneousSymbol hU Q₀.1 Q₀.2.1).hp z, T.data.adapted.normal⟫_ℝ ≠ 0)
    {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hscaled : Qσ.1 = ProjectedStressFrame.projectedStress (sourceDilation F σ))
include hF hrank hphysical hseed htrans hσ hσ1 hscaled

variable {c C : ℝ} (hP : P.IsValid c C)
    {zRoot : Euclidean 3} {ηb : Euclidean (n - 1)} {r a : ℝ}
    (hηb : ηb ≠ 0) (hr : 0 < r)
    (hgeometry : RetainedSpectralGeometry T Qσ zRoot ηb r a)

include hP hηb hr hgeometry

/-- The original seed inverse has the physical-frequency comparison supplied
by an admitted positive source. Exact domain and canonical-inverse matching
keep the original cone and zero extensions. Consumer: the genuine zero-density
carrier realization (`app:ch_background:eq:bg-Nsigma`, `bg-Psi`, `bg-frame`). -/
theorem exists_seed_frozen_frequency_comparison_of_source :
    ∃ Cfreq > (0 : ℝ), ∀ p ∈ frozenSymbolDomain T Q₀ zRoot ηb r (6 * a),
      ‖p.1.2.2‖ ≤ Cfreq * ‖(frozenSymbolInverse T Q₀ zRoot ηb r (6 * a) p).2‖ := by
  have hinv := frozenSymbolInverse_eq_of_source_dilation T Q₀ Qσ hF hrank hphysical hseed htrans
    hσ hσ1 hscaled hP hηb hr hgeometry
  obtain ⟨har, hcarrier, G, β, cJ, V, L, _hcJ, _hV, _hLV, hf, hInv, hcone, hslice⟩ := hgeometry
  have hdom := frozenSymbolDomain_eq_of_source_dilation T Q₀ Qσ hF hrank hphysical hseed htrans
    hσ hσ1 hscaled hP (ηb := ηb) hr har hcarrier
  refine ⟨frozenFrequencyBound T G, frozenFrequencyBound_pos T G, ?_⟩
  intro p hp
  rw [← hdom] at hp
  rw [← hinv]
  exact frozenInverse_frequency_comparison T G Qσ hηb hr hf hInv hcone hslice hp

/-- Instantiate the original seed's literal unit kernel and symbol inputs
using the retained geometry of ONE admitted positive source. The normal and
reduced coefficients remain those of the original seed; only the substitution
chart is reused. Hamilton matching proves the phase identity, and equality of
the literal Jacobians on the inverse range includes their zero-frequency
values off the image. No seed-smallness or kernel identity is assumed.
Consumer: `SourceDensityLimitRealization.exists_source_zero_density_limit_realization`
on the same normalized family (`app:ch_background:prop:bg-normalized`,
`bg-Nsigma`, `bg-full-complex-amplitude`, `bg-real-symbol`). -/
theorem exists_seed_frozen_kernel_inputs_of_source
    (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    {r' a' : ℝ} (hr' : 0 < r') (ha' : 0 < a')
    (hrr : r' ≤ r) (haa : a' ≤ a) (har' : a' ≤ r') (hcell : 4 * a' < 1 / 2) :
    let angular := angularMask zRoot (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1
    let e₀ := normalizedCarrierData T Q₀ F row col Φ Y (fun _ ↦ 1)
      ha' hcell angular FixedCutoffs.highFrequency 0
    ∃ charts : ∀ (R : ℝ), 1 ≤ R → ∀ x, x ∈ e₀.outputChart → ∀ y, y ∈ e₀.outputChart →
        ChartInputs e₀ (radialCarrierMask FixedCutoffs.radialRegularization R) x y,
    ∃ symbols : ∀ R hR x hx y hy, SymbolInputs (charts R hR x hx y hy),
      ∀ R hR x hx y hy,
        (symbols R hR x hx y hy).coefficients = regularizedCoefficients
          (coefficientsOfCarrier e₀ (FixedCutoffs.physical ha' 1)) FixedCutoffs.radialRegularization R ∧
        (symbols R hR x hx y hy).jacobian = transportAbsoluteJacobian (adaptedSliceCoordinates T)
          (normalizedTransportPosition T Q₀ 0) ∧
        (symbols R hR x hx y hy).inverse = frozenSymbolInverse T Q₀ zRoot ηb r (6 * a) ∧
        (symbols R hR x hx y hy).domain = frozenSymbolDomain T Q₀ zRoot ηb r (6 * a) ∧
        (symbols R hR x hx y hy).spectatorSupport = closedBall (spectatorCenter zRoot) (a' / 2) ∧
        (symbols R hR x hx y hy).inputDomain = frozenInputDomain zRoot ηb r (6 * a) ∧
        (symbols R hR x hx y hy).inputSupport = bandInputSupport zRoot ηb r' a' R := by
  classical
  intro angular e₀
  have hn : 0 < n := by have := row.isLt; omega
  have hinv := frozenSymbolInverse_eq_of_source_dilation T Q₀ Qσ hF hrank hphysical hseed htrans
    hσ hσ1 hscaled hP hηb hr hgeometry
  obtain ⟨har, hcarrier, G, β, cJ, V, L, hcJ, hV, hLV, hf, hInv, hcone, _hslice⟩ := hgeometry
  have hdom := frozenSymbolDomain_eq_of_source_dilation T Q₀ Qσ hF hrank hphysical hseed htrans
    hσ hσ1 hscaled hP (ηb := ηb) hr har hcarrier
  obtain ⟨haug, _hdiff, hJac⟩ := source_frozen_transport_geometry_eq T Q₀ Qσ
    hF hrank hphysical hseed htrans hσ hσ1 hscaled hP (ηb := ηb) hr har hcarrier
  let J₀ := transportAbsoluteJacobian (adaptedSliceCoordinates T) (normalizedTransportPosition T Q₀ 0)
  have hJacInverse (p : Variables n × Euclidean 2) :
      J₀ (inverseCoordinates (frozenSymbolInverse T Qσ zRoot ηb r (6 * a)) p) =
      transportAbsoluteJacobian (adaptedSliceCoordinates T) (normalizedTransportPosition T Qσ 0)
        (inverseCoordinates (frozenSymbolInverse T Qσ zRoot ηb r (6 * a)) p) := by
    by_cases hp : p ∈ frozenSymbolDomain T Qσ zRoot ηb r (6 * a)
    · exact (hJac (frozenSymbolInverse_maps T Qσ hηb hr hInv hcone hp)).symm
    · have he := frozenSymbolInverse_zero_outside T Qσ hp
      have hzero : (inverseCoordinates (frozenSymbolInverse T Qσ zRoot ηb r (6 * a)) p).2.2 = 0 := by
        simp only [inverseCoordinates, he, Prod.snd_zero]
      exact (frozenKernelJacobian_zero_frequency T Q₀ hn _ hzero).trans
        (frozenKernelJacobian_zero_frequency T Qσ hn _ hzero).symm
  let charts := fun (R : ℝ) (_hR : 1 ≤ R) (x : Torus n) (_hx : x ∈ e₀.outputChart)
      (y : Torus n) (_hy : y ∈ e₀.outputChart) ↦
    (show ChartInputs e₀ (radialCarrierMask FixedCutoffs.radialRegularization R) x y from
    { frozenRefinedKernelChartInputs T Qσ F row col Φ Y hηb hr hr' ha' hrr haa har' hcell
        hP har hcarrier hf hInv hcone hV hLV hcJ R x y with
      support := by
        intro v t ht i j
        exact frozenNormalDensityEntry_zero_outside T Q₀ F row col Φ Y
          hηb hr' ha' hcell hrr haa har' _ x y _ ht i j
      phase_identity := by
        intro v t ht
        have he := frozenKernel_input_phase_identity T Q₀ hP hr har hcarrier ht
        have hgrad := congrArg (fun p : Variables n × Euclidean 2 ↦ p.1.2.2) (haug ht)
        exact he.trans (congrArg (fun ξ ↦ inner ℝ
          ((e₀).chartPoint x - (e₀).chartPoint y) ξ) hgrad.symm)
      density_measurable := fun i j ↦ frozenNormalDensityEntry_measurable T Q₀ F row col Φ Y
        hηb hr' ha' hcell hP hr har hcarrier hrr haa har' R x y i j })
  let symbols := fun (R : ℝ) (hR : 1 ≤ R) (x : Torus n) (hx : x ∈ e₀.outputChart)
      (y : Torus n) (hy : y ∈ e₀.outputChart) ↦
    (show SymbolInputs (charts R hR x hx y hy) from
    { frozenRefinedKernelSymbolInputs T Qσ F row col Φ Y hηb hr hr' ha' hrr haa har' hcell
        hP har hcarrier hf hInv hcone hV hLV hcJ (by linarith : 0 < R) x y with
      jacobian := J₀
      jacobian_eq := by
        intro v k
        exact (hJacInverse _).trans
          ((frozenRefinedKernelSymbolInputs T Qσ F row col Φ Y hηb hr hr' ha' hrr haa har' hcell
            hP har hcarrier hf hInv hcone hV hLV hcJ (by linarith : 0 < R) x y).jacobian_eq v k)
      regularity := by
        have hreg := frozenRefined_regularizedCoefficients_regularity T Qσ F row col Φ Y
          hηb hr' ha' hcell hP hr har hcarrier hf hInv hcone hcJ R
        exact { (frozenRefined_coefficients_regularity_one T Q₀ F row col Φ Y
          hηb hr' ha' hcell hP hr har hcarrier).regularized FixedCutoffs.radialRegularization_smooth R with
          jacobian := hreg.jacobian.congr (fun p hp ↦ (hJac hp).symm)
          jacobian_ne_zero := fun p hp ↦ (hJac hp).symm.trans_ne (hreg.jacobian_ne_zero p hp) } })
  exact ⟨charts, symbols, fun _ _ _ _ _ _ ↦ ⟨rfl, rfl, hinv, hdom, rfl, rfl, rfl⟩⟩

end JanetCartan.ContinuumNormal.NormalizedNormalLimit
