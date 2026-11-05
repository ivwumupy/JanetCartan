module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.RetainedLowBudget.PrimitiveBaseline
public import JanetCartan.Geometry.IsometricEmbedding.Mean.RetainedJointGeometry
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.CarrierNormalRealization.SupportedShell.PrimitiveBudget
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.SupportedInputs

/-!
# The commutator baseline on supplied retained geometry

Unlike an existential local row constructor, this result applies to the radii,
masks and coefficient charts already retained by the common finite selection.
Its geometric hypotheses are projections of
`RetainedJointGeometry.exists_retained_joint_comparison_geometry`, at the
original frequency section of radius `1 / 4`. The normal input is supplied by
`Mean.RetainedAssembly.HistoryLowBudget.exists_retained_history_low_bounds`.
No new carrier, mask, minor, flow or source domain is selected.

Consumer: the common-row application of `exists_augmentedNormal_tame_commutators`
and `exists_uniform_augmentedNormal_elliptic_estimates`.
Sources: `app:ch_background:eq:bg-full-complex-amplitude`,
`app:ch_background:eq:bg-commutator`, `app:ch_background:prop:bg-inverse`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumCommutator.RetainedLowBudget
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open NullTransport ActualFlow FlowAmplitude LeadingWave.FullModulation ProjectedStressFrame
open ContinuumRow LeadingPrimitive CanonicalCarrier CanonicalConic TransportKernel CarrierNormalRealization
open ContinuumNormalReduction.TransportSymbol ContinuumNormal.RetainedFrozen
open Pseudodifferential AmplitudeBound

/-- Apply the supported-shell amplitude theorem to a supplied retained geometry.
The full-normal bound is the only analytic input beyond the original finite-low
map budget, smoothness and carrier/full-flow compatibility. All five primitive
coefficient bounds and the order `μ+3` Hamilton position bound are proved by
`exists_retained_primitive_low_controls`. In particular the output constant
precedes the map, flows, minor and scalar, and no amplitude bound is assumed.

The geometric inputs are exactly the current branch of the joint comparison
geometry; the same spectral geometry supplies primitive regularity on the
original outer inverse domain. This is a pointwise deduction for the common
row, not another choice of local or finite carriers
(`app:ch_background:eq:bg-commutator`). -/
theorem exists_reflected_baseline_on_retained_geometry {n N : ℕ} {P : Patch n}
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {c C : ℝ} (hP : P.IsValid c C)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (D : CoefficientNormCharts n)
    {Jfull : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
    (hJfull : IsCompact Jfull) (hgraph : MapsTo (carrierGraph T) D.field.carrier Jfull)
    (E : Set (Euclidean n × CarrierParameter)) (hDE : D.field.region ⊆ E)
    (hfield : E ⊆ (U ∩ ball (0 : Euclidean n) T.physicalRadius) ×ˢ
      (parameter ⁻¹' parameterInterior (2 * P.radius)))
    (hphase : E ⊆ ball (0 : Euclidean n) T.family.radius ×ˢ
      (parameter ⁻¹' parameterInterior (3 * P.radius / 2)))
    (adet : Euclidean n × Euclidean 3) {ρdet : ℝ} (hρdet : 0 < ρdet)
    (hxdet : MapsTo Prod.fst (closedBall adet ρdet)
      (closedBall (0 : Euclidean n) T.data.localReference.stateRadius))
    (hdet : closedBall adet ρdet ⊆
      ball (0 : Euclidean n) T.physicalRadius ×ˢ parameterInterior (2 * P.radius))
    (hmaps : MapsTo (fun p : Euclidean n × CarrierParameter ↦ (p.1, parameter p.2))
      D.field.carrier (closedBall adet ρdet))
    (z₀ : Euclidean 3) {ηb : Euclidean (n - 1)} (hηb : ηb ≠ 0)
    {r a r' a' : ℝ} (hr : 0 < r) (hr' : 0 < r') (ha' : 0 < a')
    (hcell : 4 * a' < 1 / 2) (houter : coefficientDomain z₀ r (6 * a) ⊆ E)
    (p₀ : InputVariables n) (q₀ : Variables n × Euclidean 2)
    {ρ τ : ℝ} (hρ : 0 < ρ) (hτ : 0 < τ)
    {W Bi : Set (InputVariables n)} (hW : IsOpen W)
    (hKiW : closedBall p₀ ρ ⊆ W) (hBi : IsCompact Bi) (hWBi : W ⊆ Bi)
    (hBiDom : Bi ⊆ symbolInputDomain z₀ ηb r (6 * a))
    (hfoot : ∀ p ∈ closedBall p₀ ρ, D.Contains p)
    {It : Set ℝ} (hIt : IsOpen It) (hIIt : Icc (0 : ℝ) 1 ⊆ It)
    (hsegT : ∀ t ∈ It, MapsTo (transportSegmentInput n t) W D.field.region)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, MapsTo (transportSegmentInput n t) W D.field.carrier)
    (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2)
    {ε gap δgeometry : ℝ} (hε : 0 < ε) (hgap : 0 < gap) (hδgeometry : 0 < δgeometry)
    (hfreq : ∀ p ∈ Bi, ε ≤ ‖p.2.2‖)
    (hgeometry : ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
      (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
      ∀ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress n) < δgeometry →
      let Q := ⟨projectedStress F,
        contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
      RetainedSpectralGeometry T Q z₀ ηb r a ∧
      closedBall q₀ (2 * τ) ⊆ symbolDomain T Q z₀ ηb r (6 * a) ∧
      MapsTo (inverseCoordinates (symbolInverse T Q z₀ ηb r (6 * a)))
        (closedBall q₀ (2 * τ)) (closedBall p₀ ρ) ∧
      (∀ p ∈ closedBall p₀ ρ, ‖A.symm.toContinuousLinearMap.comp
        (fderiv ℝ (augmentedTransportGradient (transportPosition T Q)) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
      (∀ p ∈ Bi, gap ≤ transportAbsoluteJacobian (adaptedSliceCoordinates T)
        (transportPosition T Q) p) ∧
      (closure (augmentedTransportGradient (transportPosition T Q) ''
        conicMaskSupport z₀ ηb r' a') ∩ {p | p.1.2.2 ≠ 0} ⊆
          symbolDomain T Q z₀ ηb r (6 * a)) ∧
      (∀ x : Variables n, ‖x.2.2‖ = 1 / 4 → ∀ v : Euclidean 2,
        (x, v) ∈ closure (augmentedTransportGradient (transportPosition T Q) ''
          conicMaskSupport z₀ ηb r' a') → (x, v) ∈ closedBall q₀ τ) ∧
      (∀ p ∈ symbolDomain T Q z₀ ηb r (6 * a),
        ‖(symbolInverse T Q z₀ ηb r (6 * a) p).2‖ ≤ 2 * ‖p.1.2.2‖)) :
    ∃ δ > (0 : ℝ), ∀ {MF Bnormal κmet κ : ℝ},
      0 ≤ MF → 0 ≤ Bnormal → 0 < κmet → 0 < κ →
    ∃ Cbaseline > (0 : ℝ),
    ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
      (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
      cNorm K (2 * (n + 1) + 14) F ≤ MF →
      (∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ K, ∀ w ∈ normalSpace F x, κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      ∀ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress n) < δ →
      let Q := ⟨projectedStress F,
        contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
      ∀ (row col : Fin n)
        (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
          Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
        (φ y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
        (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
        (O : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1))))
        (Vcomp : Set (ℝ × (Euclidean (n - 1) × Euclidean 3))),
      IsOpen O → MapsTo Prod.fst O U → O ⊆ domain T → Jfull ⊆ O →
      MapsTo (carrierGraph T) E O →
      MapsTo (fun p : Euclidean n × CarrierParameter ↦
        coordinates (adaptedCoordinates T.data.adapted) (p.1, parameter p.2)) E Vcomp →
      ContDiffOn ℝ ∞ (fun w ↦ scalarAmplitude T Q F row col Φ Y initial w •
        nullvector T Q col w) O →
      (∀ q ∈ Vcomp, let w := (coordinates (adaptedCoordinates T.data.adapted)).symm q
        scalarAmplitude T Q F row col Φ Y initial
          (w.1, (w.2, T.reference.spatialPatch w.2)) =
            carrierScalarAmplitude T Q F row col φ y initial w) →
      cNorm Jfull (2 * (n + 1) + 1) (fullNormal T Q F row col Φ Y initial) ≤ Bnormal →
      let e := data T Q F row col φ y initial ha' hcell
        (angularMask z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1)
        FixedCutoffs.highFrequency
      let d := coefficientsOfCarrier e (FixedCutoffs.physical ha' 1)
      ContDiff ℝ ∞ (Function.uncurry (fullReflectedMatrixAmplitude d (symbolJacobian T Q)
        (symbolInverse T Q z₀ ηb r (6 * a)) (symbolDomain T Q z₀ ηb r (6 * a))
        (closedBall (spectatorCenter z₀) (a' / 2)))) ∧
      ∀ i j, HasAmplitudeDerivativeBound (fun ξ z ↦ fullReflectedMatrixAmplitude d
        (symbolJacobian T Q) (symbolInverse T Q z₀ ηb r (6 * a))
        (symbolDomain T Q z₀ ηb r (6 * a)) (closedBall (spectatorCenter z₀) (a' / 2)) ξ z i j)
        (2 * (n + 1) + 1) Cbaseline := by
  let angular := angularMask z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1
  obtain ⟨δbase, hδbase, hcontrols⟩ := exists_retained_primitive_low_controls T (N := N)
    hP hK hKU hball D hJfull hgraph (hDE.trans hfield) (hDE.trans hphase)
    adet hρdet hxdet hdet hmaps ha' hcell angular (angularMask_smooth ..)
  refine ⟨min δbase δgeometry, lt_min hδbase hδgeometry, ?_⟩
  intro MF Bnormal κmet κ hMF hBnormal hκmet hκ
  obtain ⟨M, hM, B, hB, hcontrols⟩ := hcontrols MF Bnormal κmet κ hMF hBnormal hκmet hκ
  obtain ⟨Cbaseline, hCbaseline, hbudget⟩ :=
    exists_fullReflectedMatrixAmplitude_supported_bounds_of_primitiveNorms (N := N)
      (adaptedSliceCoordinates T) p₀ q₀ hρ hτ hW hKiW hBi hWBi
      (O := ball q₀ (2 * τ)) isOpen_ball (closedBall_subset_ball (by linarith))
      D.field.isOpen_region (isCompact_closedBall _ _) D.field.ball_subset
      hIt hIIt hsegT hseg A hM.le hM.le hB hgap hε (zero_le_one.trans hB)
      (fun p hp ↦ hfreq p (hWBi (hKiW hp))) D hfoot
      (Cupper := 2) (ℓ := 1 / 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (S := closedBall (spectatorCenter z₀) (a' / 2)) (isCompact_closedBall _ _)
      (2 * (n + 1) + 1) (by omega) FixedCutoffs.highFrequency_smooth
      (fun _ ht ↦ FixedCutoffs.highFrequency_zero ht)
      (fun _ ht ↦ FixedCutoffs.highFrequency_one ht)
  refine ⟨Cbaseline, hCbaseline, ?_⟩
  intro F hF hi hrank hFM hmet hnormal hlow hclose
  let Q := (⟨projectedStress F, contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩ :
    {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
  dsimp only
  intro row col Φ Y φ y initial O Vcomp hO hOU hOdom hJO hgraphO hcompE hnull hcomp hfull
  obtain ⟨hY, hYlow, hcoeff, hYhigh⟩ := hcontrols Q F rfl hF hi hrank hFM hmet hnormal
    (hclose.trans_le (min_le_left _ _)) row col Φ Y φ y initial O Vcomp
    hO hOU hOdom hJO (fun _ hp ↦ hgraphO (hDE hp))
    (fun _ hp ↦ hcompE (hDE hp)) hnull hcomp hfull
  obtain ⟨hspectral, houtput, hrange, hgapA, hJacLow, hpunctured, hshell, hupper⟩ :=
    hgeometry F hF hi hrank hlow (hclose.trans_le (min_le_right _ _))
  obtain ⟨_har, _hcarrier, G, β, cJ, V, L, hcJ, hV, hLV, hf, hInv, htrans, _hslice⟩ := hspectral
  have hnormalEq p (hp : p ∈ E) :=
    normalField_eq_fullNormal_on_graph T Q F row col Φ Y φ y initial hcomp (hcompE hp)
  have hν : ContDiffOn ℝ ∞ (Function.uncurry (normalField T Q F row col φ y initial)) E :=
    ((fullNormal_smooth T Q F row col Φ Y initial hO hOU hOdom hF hi hrank hnull).comp
      ((carrierGraph_smooth T hP).mono (fun p hp ↦ ⟨mem_univ _, (hfield hp).2⟩))
      hgraphO).congr (fun p hp ↦ hnormalEq p hp)
  have hdetreg (i : Fin n) : ContDiffOn ℝ ∞
      (fun p : Euclidean n × CarrierParameter ↦
        quadratic (Q.1 p.1) (T.carrierGradient Q p.1 (parameter p.2)) i) E :=
    contDiffOn_pi.mp (PiLp.contDiff_ofLp.comp_contDiffOn
      ((quadratic_canonical_smooth T hP Q).mono hfield)) i
  let e := data T Q F row col φ y initial ha' hcell angular FixedCutoffs.highFrequency
  let d := coefficientsOfCarrier e (FixedCutoffs.physical ha' 1)
  have hreg := refined_coefficients_regularity T Q F row col φ y initial
    hηb hr' ha' hcell (hν.mono houter) (fun i ↦ (hdetreg i).mono houter)
    hr hf hInv htrans hcJ
  have hΩ := symbolDomain_open T Q hηb hr hInv htrans hV hLV
  have hR : IsOpen {p : Variables n | p.2.2 ≠ 0} :=
    isOpen_compl_singleton.preimage continuous_snd.snd
  obtain ⟨hb, hAb, _⟩ := hbudget d (transportPosition T Q)
    (symbolInverse T Q z₀ ηb r (6 * a)) (symbolJacobian T Q)
    (symbolDomain T Q z₀ ηb r (6 * a)) (symbolInputDomain z₀ ηb r (6 * a))
    (conicMaskSupport z₀ ηb r' a') {p | ‖p.2.2‖ = 1 / 4} {p | p.2.2 ≠ 0} 1
    hY hYlow hΩ (ball_subset_closedBall.trans houtput)
    (symbolInverse_smooth T Q hηb hr hInv htrans hLV)
    (hrange.mono (closedBall_subset_closedBall (by linarith)) Subset.rfl)
    hgapA (fun _ hp ↦ transportAveragedGradient_symbolInverse T Q hηb hr hInv htrans hp)
    ((symbolJacobian_eq_actual T Q hηb hr hf).mono (hWBi.trans hBiDom))
    (fun p hp ↦ hreg.jacobian_ne_zero p (hBiDom (hWBi hp)))
    (fun p hp ↦ hJacLow p (hWBi (hKiW hp))) le_rfl (by simpa only [mul_one, PrimitiveNormChart.carrier] using hYhigh)
    hreg (symbolInverse_maps T Q hηb hr hInv htrans)
    (fun p hp hx hy ha ↦ primitive_masks_mem_conicMaskSupport hηb hr' ha' hp.2.2.1 hx hy ha)
    hR (fun p hp ↦ norm_ne_zero_iff.mp (by rw [hp]; norm_num))
    (fun p hp ↦ hpunctured ⟨hp.1, hp.2.1⟩)
    (fun x hx v _ hv ↦ hshell x hx v hv) hcoeff
    (fun _ ht p ↦ symbolDomain_smul_iff T Q ht p)
    (fun _ ht _ hp ↦ symbolInverse_smul T Q hηb hr hInv htrans hp ht)
    (fun _ ht _ hp ↦ symbolJacobian_scale_inverse T Q hηb hr hf hInv htrans hp ht)
    hupper hpunctured (scaleFrequency_mem_fixed_sphere (by norm_num : (0 : ℝ) < 1 / 4))
  have hd : {d with high := FixedCutoffs.highFrequency} = d := by
    dsimp only [d, e]
    rw [coefficientsOfCarrier_data]
  rw [hd] at hb hAb
  exact ⟨hb, by simpa only [mul_one] using hAb⟩

end JanetCartan.ContinuumCommutator.RetainedLowBudget
