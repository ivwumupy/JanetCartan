module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.LeadingPrimitive.Controls
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.RetainedFrozen.Geometry
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.CarrierNormalRealization.SupportedShell.PrimitiveBudget
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.SupportedInputs

/-!
# All-order amplitudes on the initialized density geometry

Apply the retained full-normal and primitive estimates to the supplied incidence
masks and inverse charts. This is the high-order companion to the sharp baseline;
it retains the original reserve fourteen and the same reflected amplitude.
The concrete consumer is the admitted-history application of
`exists_retained_history_elliptic_estimates_with_exterior`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumInverse
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open NullTransport ActualFlow FlowAmplitude LeadingWave.FullModulation ProjectedStressFrame
open ContinuumRow LeadingPrimitive CanonicalCarrier CanonicalConic TransportKernel CarrierNormalRealization
open ContinuumNormalReduction.TransportSymbol ContinuumNormal.RetainedFrozen
open Pseudodifferential AmplitudeBound

/-- The supplied retained density geometry and the original full-leading estimate
produce every high reflected-amplitude bound. No carrier, cutoff, inverse chart
or normal operator is selected here. The frame tolerance precedes all geometric
budgets, and each amplitude constant precedes the map and scalar. The high norm
appears once at order `s + 14`, as required by the admitted-history elliptic
bootstrap (`app:ch_background:eq:bg-full-complex-amplitude`,
`app:ch_background:eq:bg-commutator`, `app:ch_waves:eq:joint-tame`). -/
theorem exists_reflected_profiles_on_initialized_density_geometry {n N : ℕ} {P : Patch n}
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {c C : ℝ} (hP : P.IsValid c C)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (D : CoefficientNormCharts n)
    (Kinitial : Set (Euclidean (n - 1) × Euclidean 3))
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
    (hsupport : tsupport (FixedCutoffs.physical (n := n) ha' 1) ×ˢ
      carrierSupport z₀ (r := a') ⊆ D.field.carrier)
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
    ∃ δ > (0 : ℝ),
    ∀ (Bfull : ℕ → ℝ), (∀ j, 0 < Bfull j) →
    ∀ {MF Minitial κmet κ : ℝ},
      0 ≤ MF → 0 ≤ Minitial → 0 < κmet → 0 < κ →
    ∀ s : ℕ, 2 ≤ s → ∃ Cprofile > (0 : ℝ),
    ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
      (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
      cNorm K 15 F ≤ MF →
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
      cNorm Kinitial 15 initial ≤ Minitial →
      (∀ j, cNorm Jfull j (fullNormal T Q F row col Φ Y initial) ≤
        Bfull j * (1 + cNorm K (j + 14) F + cNorm Kinitial (j + 14) initial)) →
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
        s (Cprofile * (1 + cNorm K (s + 14) F + cNorm Kinitial (s + 14) initial)) := by
  let angular := angularMask z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1
  obtain ⟨δbase, hδbase, hcontrols⟩ := exists_primitive_controls_of_jointLeading T (N := N)
    hP hK hKU hball Kinitial D hJfull hgraph (hDE.trans hfield) (hDE.trans hphase)
    adet hρdet hxdet hdet hmaps ha' hcell angular (angularMask_smooth ..)
    (carrierSupport_compact z₀)
    (fun _ hz η ↦ angularMask_zero_outside z₀ (NormedSpace.normalize ηb) ha'
      (angularWidth_spec hηb hr').1 hz η) hsupport
  refine ⟨min δbase δgeometry, lt_min hδbase hδgeometry, ?_⟩
  intro Bfull hBfull MF Minitial κmet κ hMF hMinitial hκmet hκ s hs
  obtain ⟨M, hM, _Cmask, _hCmask, B, hB, hcontrols⟩ :=
    hcontrols Bfull hBfull MF Minitial κmet κ hMF hMinitial hκmet hκ
  obtain ⟨Cprofile, hCprofile, hbudget⟩ :=
    exists_fullReflectedMatrixAmplitude_supported_bounds_of_primitiveNorms (N := N)
      (adaptedSliceCoordinates T) p₀ q₀ hρ hτ hW hKiW hBi hWBi
      (O := ball q₀ (2 * τ)) isOpen_ball (closedBall_subset_ball (by linarith))
      D.field.isOpen_region (isCompact_closedBall _ _) D.field.ball_subset
      hIt hIIt hsegT hseg A hM.le hM.le (hB s) hgap hε (zero_le_one.trans (hB s))
      (fun p hp ↦ hfreq p (hWBi (hKiW hp))) D hfoot
      (Cupper := 2) (ℓ := 1 / 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (S := closedBall (spectatorCenter z₀) (a' / 2)) (isCompact_closedBall _ _)
      s hs FixedCutoffs.highFrequency_smooth
      (fun _ ht ↦ FixedCutoffs.highFrequency_zero ht)
      (fun _ ht ↦ FixedCutoffs.highFrequency_one ht)
  refine ⟨Cprofile, hCprofile, ?_⟩
  intro F hF hi hrank hFM hmet hnormal hlow hclose
  let Q := (⟨projectedStress F, contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩ :
    {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
  dsimp only
  intro row col Φ Y φ y initial O Vcomp hO hOU hOdom hJO hgraphO hcompE hnull hcomp hinitial hfull
  obtain ⟨_hkernel, _hsize, hY, hYlow, hprofiles⟩ := hcontrols Q F rfl hF hi hrank hFM hmet hnormal
    (hclose.trans_le (min_le_left _ _)) row col Φ Y φ y initial O Vcomp
    hO hOU hOdom hJO (fun _ hp ↦ hgraphO (hDE hp))
    (fun _ hp ↦ hcompE (hDE hp)) hnull hcomp hinitial hfull
  obtain ⟨hcoeff, hYhigh⟩ := hprofiles s
  let Hhigh := 1 + cNorm K (s + 14) F + cNorm Kinitial (s + 14) initial
  have hHhigh : 1 ≤ Hhigh := by
    dsimp only [Hhigh]
    linarith [cNorm_nonneg K (s + 14) F, cNorm_nonneg Kinitial (s + 14) initial]
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
    (conicMaskSupport z₀ ηb r' a') {p | ‖p.2.2‖ = 1 / 4} {p | p.2.2 ≠ 0} Hhigh
    hY hYlow hΩ (ball_subset_closedBall.trans houtput)
    (symbolInverse_smooth T Q hηb hr hInv htrans hLV)
    (hrange.mono (closedBall_subset_closedBall (by linarith)) Subset.rfl)
    hgapA (fun _ hp ↦ transportAveragedGradient_symbolInverse T Q hηb hr hInv htrans hp)
    ((symbolJacobian_eq_actual T Q hηb hr hf).mono (hWBi.trans hBiDom))
    (fun p hp ↦ hreg.jacobian_ne_zero p (hBiDom (hWBi hp)))
    (fun p hp ↦ hJacLow p (hWBi (hKiW hp))) hHhigh hYhigh
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
  exact ⟨hb, hAb⟩

end JanetCartan.ContinuumInverse
