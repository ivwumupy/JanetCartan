module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.CurrentFullPhase.LocalFrameAgreement.ProjectedStress
public import JanetCartan.Geometry.IsometricEmbedding.Response.PrimarySources.Envelopes.Extension
public import JanetCartan.Geometry.IsometricEmbedding.Response.PrimarySources.Admission.Linearity.Calculus
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.BackgroundModulation.CanonicalEndpoint

/-!
# Local formula identities for the original primary source

These deductions consume the proved chart agreement from `LocalFrameAgreement`.
They keep the original independent covector, row, column, transport, scalar and
cutoff. The final application supplies chart agreement from actual coefficient
agreement (`app:lem:common-hamilton-phase`, `app:ch_waves:thm:leading`,
`app:ch_response:eq:response-graded-source`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.RawPrimary.LocalFrameAgreement
open ActualCarriers FrozenMenu CurrentFullPhase LeadingWave.FullModulation
open NullTransport ResponsePrimarySources ResponseTransfer

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)
  (Q Q' : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress n) < T.family.threshold})

private theorem slice_eventuallyEq {A B : Type*} [TopologicalSpace A]
    {f g : Euclidean n × A → B} {Ω : Set (Euclidean n × A)} (hΩ : IsOpen Ω)
    (he : EqOn f g Ω) {w : Euclidean n × A} (hw : w ∈ Ω) :
    (fun x ↦ f (x, w.2)) =ᶠ[𝓝 w.1] (fun x ↦ g (x, w.2)) :=
  eventuallyEq_of_mem ((hΩ.preimage (continuous_id.prodMk continuous_const)).mem_nhds hw)
    (fun _ hx ↦ he hx)

/-- The proved full chart equality restricts to the entire original
zero-energy phase domain, with its covector still independent
(`app:lem:common-hamilton-phase`, `app:ch_waves:thm:leading`). -/
theorem phase_eqOn_of_coordinates_eqOn
    (hc : EqOn (T.currentChart Q).coordinates (T.currentChart Q').coordinates T.target) :
    EqOn (fun w : Euclidean n × Euclidean (n - 1) ↦ phase T Q w.1 w.2)
      (fun w ↦ phase T Q' w.1 w.2) (phaseDomain T) := by
  intro w hw
  have hh := hc ((inclusion_mem_ball T).mpr hw)
  change (T.currentChart Q).coordinates (w.1, (0, w.2)) =
    (T.currentChart Q').coordinates (w.1, (0, w.2)) at hh
  change HamiltonPhase.phase (T.currentChart Q).coordinates (w.1, (0, w.2)) =
    HamiltonPhase.phase (T.currentChart Q').coordinates (w.1, (0, w.2))
  simp only [HamiltonPhase.phase, hh]

/-- Physical gradients agree on the same open full-covector domain; equality
at a carrier center alone would not suffice (`app:ch_waves:thm:leading`). -/
theorem phaseGradient_eqOn_of_coordinates_eqOn
    (hc : EqOn (T.currentChart Q).coordinates (T.currentChart Q').coordinates T.target) :
    EqOn (fun w : Euclidean n × Euclidean (n - 1) ↦ phaseGradient T Q w.1 w.2)
      (fun w ↦ phaseGradient T Q' w.1 w.2) (phaseDomain T) := by
  intro w hw
  exact (slice_eventuallyEq isOpen_ball (phase_eqOn_of_coordinates_eqOn T Q Q' hc) hw).gradient_eq

private theorem reducedOperator_eq_of_germ
    (F : Euclidean n → Euclidean N)
    {Q Q' : Euclidean n → Fin n → MetricTensor n}
    {u v : Euclidean n → Euclidean n} {x : Euclidean n}
    (hQ : Q x = Q' x) (he : u =ᶠ[𝓝 x] v) :
    reducedOperator F Q u x = reducedOperator F Q' v x := by
  have hd (i j : Fin n) : partialDeriv (fun y ↦ u y j) x i =
      partialDeriv (fun y ↦ v y j) x i := by
    have hj : (fun y ↦ u y j) =ᶠ[𝓝 x] (fun y ↦ v y j) :=
      he.mono (fun _ h ↦ congrArg (fun b ↦ b j) h)
    exact congrArg (fun L : Euclidean n →L[ℝ] ℝ ↦ L (EuclideanSpace.single i 1)) hj.fderiv_eq
  have hs : symmCovariantDeriv F u x = symmCovariantDeriv F v x := by
    ext i j
    simp only [symmCovariantDeriv, hd, he.eq_of_nhds]
  change (fun i ↦ tensorPairing (Q x i) (symmCovariantDeriv F u x)) = _
  rw [hQ, hs]
  rfl

variable (F : Euclidean n → Euclidean N) (row col : Fin n)
  {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
  (hΩ : IsOpen Ω)
  (hc : EqOn (T.currentChart Q).coordinates (T.currentChart Q').coordinates T.target)
  (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)
  (hframe : ∀ w ∈ Ω, Q.1 w.1 = Q'.1 w.1)

include hc hphase hframe

/-- The literal fixed null column, conull row and adapted denominator agree
on the original open coefficient domain (`app:ch_waves:thm:leading`). -/
theorem null_coefficients_eqOn_of_coordinates_eqOn :
    EqOn (nullvector T Q col) (nullvector T Q' col) Ω ∧
    EqOn (conullvector T Q row) (conullvector T Q' row) Ω ∧
    EqOn (adaptedDenominator T Q row col) (adaptedDenominator T Q' row col) Ω := by
  have hg := phaseGradient_eqOn_of_coordinates_eqOn T Q Q' hc
  exact ⟨fun w hw ↦ by simp only [nullvector, hframe w hw, hg (hphase w hw)],
    fun w hw ↦ by simp only [conullvector, hframe w hw, hg (hphase w hw)],
    fun w hw ↦ by simp only [adaptedDenominator, hframe w hw, hg (hphase w hw)]⟩

include hΩ

/-- Both actual transport coefficients agree, including physical derivatives
of the null column and the original Christoffel terms. This lets the parent
reuse its retained transport (`app:ch_waves:thm:leading`). -/
theorem transport_coefficients_eqOn_of_coordinates_eqOn :
    EqOn (transportDirection T Q row col) (transportDirection T Q' row col) Ω ∧
    EqOn (transportPotential T Q F row col) (transportPotential T Q' F row col) Ω := by
  obtain ⟨hk, hl, hd⟩ := null_coefficients_eqOn_of_coordinates_eqOn T Q Q' row col hc hphase hframe
  constructor
  · intro w hw
    simp only [transportDirection, hframe w hw, hk hw, hl hw, hd hw]
  · intro w hw
    have hop := reducedOperator_eq_of_germ F (hframe w hw) (slice_eventuallyEq hΩ hk hw)
    simp only [transportPotential, hl hw, hd hw, hop]

open FlowAmplitude ActualFlow

variable
  (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
    Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
  {D : Set (ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))))}
  {L : Set (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))}
  {timeRadius : ℝ} (htime : 0 < timeRadius)

variable
  (hDΩ : (coordinates (Z := Euclidean 3 × Euclidean (n - 1)) (adaptedCoordinates T.data.adapted)) ⁻¹' D ⊆ Ω)
  (hforward : MapsTo (fun q ↦ (q.1, Φ q)) (Ioo (-timeRadius) timeRadius ×ˢ L) D)
  (hbackward : MapsTo (fun q ↦ (q.1, Y q)) D (Ioo (-timeRadius) timeRadius ×ˢ L))

include htime hDΩ hforward hbackward

/-- The SAME retained flow and footpoint give the same scalar on their entire
original physical domain. The forward/backward maps place every integration
point in the open coefficient domain; no scalar equality or new transport is
assumed (`app:ch_waves:thm:leading`). -/
theorem scalarAmplitude_eqOn_of_retained_transport
    (r : Euclidean (n - 1) × Euclidean 3 → ℝ) :
    EqOn (scalarAmplitude T Q F row col Φ Y r)
      (scalarAmplitude T Q' F row col Φ Y r) ((coordinates (Z := Euclidean 3 × Euclidean (n - 1)) (adaptedCoordinates T.data.adapted)) ⁻¹' D) := by
  have hp := (transport_coefficients_eqOn_of_coordinates_eqOn T Q Q' F row col
    hΩ hc hphase hframe).2
  intro w hw
  have hb := hbackward hw
  have hzero : (0 : ℝ) ∈ Ioo (-timeRadius) timeRadius := ⟨by linarith, htime⟩
  have hpath (s : ℝ) (hs : s ∈ uIcc (0 : ℝ) ((coordinates (Z := Euclidean 3 × Euclidean (n - 1)) (adaptedCoordinates T.data.adapted)) w).1) :
      (coordinates (Z := Euclidean 3 × Euclidean (n - 1)) (adaptedCoordinates T.data.adapted)).symm (s, Φ (s, Y ((coordinates (Z := Euclidean 3 × Euclidean (n - 1)) (adaptedCoordinates T.data.adapted)) w))) ∈ Ω := by
    apply hDΩ
    change (coordinates (Z := Euclidean 3 × Euclidean (n - 1)) (adaptedCoordinates T.data.adapted)) ((coordinates (Z := Euclidean 3 × Euclidean (n - 1)) (adaptedCoordinates T.data.adapted)).symm (s, Φ (s, Y ((coordinates (Z := Euclidean 3 × Euclidean (n - 1)) (adaptedCoordinates T.data.adapted)) w)))) ∈ D
    rw [(coordinates (Z := Euclidean 3 × Euclidean (n - 1)) (adaptedCoordinates T.data.adapted)).apply_symm_apply]
    exact hforward (x := (s, Y (coordinates (adaptedCoordinates T.data.adapted) w)))
      ⟨ordConnected_Ioo.uIcc_subset hzero hb.1 hs, hb.2⟩
  have hi : (∫ s in (0 : ℝ)..((coordinates (Z := Euclidean 3 × Euclidean (n - 1)) (adaptedCoordinates T.data.adapted)) w).1,
      transportPotential T Q F row col ((coordinates (Z := Euclidean 3 × Euclidean (n - 1)) (adaptedCoordinates T.data.adapted)).symm (s, Φ (s, Y ((coordinates (Z := Euclidean 3 × Euclidean (n - 1)) (adaptedCoordinates T.data.adapted)) w))))) =
      ∫ s in (0 : ℝ)..((coordinates (Z := Euclidean 3 × Euclidean (n - 1)) (adaptedCoordinates T.data.adapted)) w).1,
        transportPotential T Q' F row col ((coordinates (Z := Euclidean 3 × Euclidean (n - 1)) (adaptedCoordinates T.data.adapted)).symm (s, Φ (s, Y ((coordinates (Z := Euclidean 3 × Euclidean (n - 1)) (adaptedCoordinates T.data.adapted)) w)))) :=
    intervalIntegral.integral_congr (fun s hs ↦ hp (hpath s hs))
  simp only [scalarAmplitude, transportFromFootpoint, characteristicTransport,
    scalarTransport, transportFactor, flowTransportCoefficient, hi]

omit htime hbackward in
/-- Transfer the retained derivative equation itself to the locally equal
frame, preserving the same solution and every label. All inverse and range
identities remain literal identities of these same maps
(`app:ch_waves:thm:leading`). -/
theorem retained_transport_derivative_for_local_frame
    (hderiv : ∀ p ∈ L, ∀ t ∈ Ioo (-timeRadius) timeRadius,
      HasDerivAt (fun s ↦ Φ (s, p))
        ((adaptedCoordinates T.data.adapted
          (transportDirection T Q row col ((coordinates (Z := Euclidean 3 × Euclidean (n - 1)) (adaptedCoordinates T.data.adapted)).symm (t, Φ (t, p))))).2, 0) t) :
    ∀ p ∈ L, ∀ t ∈ Ioo (-timeRadius) timeRadius,
      HasDerivAt (fun s ↦ Φ (s, p))
        ((adaptedCoordinates T.data.adapted
          (transportDirection T Q' row col ((coordinates (Z := Euclidean 3 × Euclidean (n - 1)) (adaptedCoordinates T.data.adapted)).symm (t, Φ (t, p))))).2, 0) t := by
  have hd := (transport_coefficients_eqOn_of_coordinates_eqOn T Q Q' (fun _ ↦ (0 : Euclidean 0)) row col
    hΩ hc hphase hframe).1
  intro p hp t ht
  have hm : (coordinates (Z := Euclidean 3 × Euclidean (n - 1)) (adaptedCoordinates T.data.adapted)).symm (t, Φ (t, p)) ∈ Ω :=
    hDΩ (by simpa only [mem_preimage, (coordinates (Z := Euclidean 3 × Euclidean (n - 1)) (adaptedCoordinates T.data.adapted)).apply_symm_apply] using hforward (x := (t, p)) ⟨ht, hp⟩)
  rw [← hd hm]
  exact hderiv p hp t ht

variable (hD : IsOpen D)
include hD

/-- The entire leading/correction/primary/strain formulas agree on the
original transport domain. The proof retains all physical derivatives and
every inverse-frequency power, including the cubic residual
(`app:ch_waves:eq:primary-algebraic-correction`, `app:ch_waves:eq:WKB-strain`). -/
theorem primary_formulas_eqOn_of_retained_transport
    (r : Euclidean (n - 1) × Euclidean 3 → ℝ) (τ : ℝ) :
    EqOn (fullLeadingCovector T Q F row col Φ Y r)
      (fullLeadingCovector T Q' F row col Φ Y r) ((coordinates (Z := Euclidean 3 × Euclidean (n - 1)) (adaptedCoordinates T.data.adapted)) ⁻¹' D) ∧
    EqOn (fullCorrectionCovector T Q F row col Φ Y r)
      (fullCorrectionCovector T Q' F row col Φ Y r) ((coordinates (Z := Euclidean 3 × Euclidean (n - 1)) (adaptedCoordinates T.data.adapted)) ⁻¹' D) ∧
    EqOn (fun w ↦ fullPrimaryAtom T Q F row col Φ Y τ r w.2.1 (w.1, w.2.2))
      (fun w ↦ fullPrimaryAtom T Q' F row col Φ Y τ r w.2.1 (w.1, w.2.2)) ((coordinates (Z := Euclidean 3 × Euclidean (n - 1)) (adaptedCoordinates T.data.adapted)) ⁻¹' D) ∧
    EqOn (fullPrimaryStrainAmplitude T Q F row col Φ Y r τ)
      (fullPrimaryStrainAmplitude T Q' F row col Φ Y r τ) ((coordinates (Z := Euclidean 3 × Euclidean (n - 1)) (adaptedCoordinates T.data.adapted)) ⁻¹' D) := by
  have hO : IsOpen ((coordinates (Z := Euclidean 3 × Euclidean (n - 1)) (adaptedCoordinates T.data.adapted)) ⁻¹' D) := hD.preimage (coordinates (Z := Euclidean 3 × Euclidean (n - 1)) (adaptedCoordinates T.data.adapted)).continuous
  have hs := phase_eqOn_of_coordinates_eqOn T Q Q' hc
  have hS : EqOn (fun w ↦ phase T Q w.1 w.2.2)
      (fun w ↦ phase T Q' w.1 w.2.2) ((coordinates (Z := Euclidean 3 × Euclidean (n - 1)) (adaptedCoordinates T.data.adapted)) ⁻¹' D) :=
    fun w hw ↦ hs (hphase w (hDΩ hw))
  have hg := phaseGradient_eqOn_of_coordinates_eqOn T Q Q' hc
  have hk := (null_coefficients_eqOn_of_coordinates_eqOn T Q Q' row col hc hphase hframe).1
  have ha := scalarAmplitude_eqOn_of_retained_transport T Q Q' F row col hΩ hc hphase hframe
    Φ Y htime hDΩ hforward hbackward r
  have hlead : EqOn (fullLeadingCovector T Q F row col Φ Y r)
      (fullLeadingCovector T Q' F row col Φ Y r) ((coordinates (Z := Euclidean 3 × Euclidean (n - 1)) (adaptedCoordinates T.data.adapted)) ⁻¹' D) := by
    intro w hw
    simp only [fullLeadingCovector, ha hw, hk (hDΩ hw)]
  have hcorr : EqOn (fullCorrectionCovector T Q F row col Φ Y r)
      (fullCorrectionCovector T Q' F row col Φ Y r) ((coordinates (Z := Euclidean 3 × Euclidean (n - 1)) (adaptedCoordinates T.data.adapted)) ⁻¹' D) := by
    intro w hw
    have hop := reducedOperator_eq_of_germ F (hframe w (hDΩ hw))
      (slice_eventuallyEq hO hlead hw)
    simp only [fullCorrectionCovector, hframe w (hDΩ hw), hg (hphase w (hDΩ hw)), hop]
  have hatom : EqOn
      (fun w ↦ fullPrimaryAtom T Q F row col Φ Y τ r w.2.1 (w.1, w.2.2))
      (fun w ↦ fullPrimaryAtom T Q' F row col Φ Y τ r w.2.1 (w.1, w.2.2)) ((coordinates (Z := Euclidean 3 × Euclidean (n - 1)) (adaptedCoordinates T.data.adapted)) ⁻¹' D) := by
    intro w hw
    apply PrimarySourceAdmission.InitialScalarCalculus.completedVariationComplex_zero_congr
    filter_upwards [slice_eventuallyEq hO hS hw, slice_eventuallyEq hO hlead hw,
      slice_eventuallyEq hO hcorr hw] with x hx h₀ h₁
    simp only [twoTermWave, modulatedWave, waveCarrier, hx, h₀, h₁]
  refine ⟨hlead, hcorr, hatom, ?_⟩
  intro w hw
  have he := slice_eventuallyEq hO hatom hw
  have hd := he.fderiv_eq (𝕜 := ℝ)
  have hm : WKB.complexLinearizedMetric F
      (fun x ↦ fullPrimaryAtom T Q F row col Φ Y τ r w.2.1 (x, w.2.2)) w.1 =
      WKB.complexLinearizedMetric F
        (fun x ↦ fullPrimaryAtom T Q' F row col Φ Y τ r w.2.1 (x, w.2.2)) w.1 := by
    ext i j
    simp only [WKB.complexLinearizedMetric, partialDeriv, hd]
  simp only [fullPrimaryStrainAmplitude, hS hw, hm]

/-- Transfer the original scalar smoothness and null transport, and preserve
every correction seminorm exactly on its original compact. These are the
literal analytic inputs of
`exists_localized_extended_reducedSource_physical_fourier_profiles`, with
unchanged order fourteen in the correction and reserve sixteen in the source
(`app:ch_waves:thm:leading`, `app:ch_response:eq:response-graded-source`). -/
theorem source_inputs_of_retained_transport
    (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (hscalar : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r)
      ((coordinates (Z := Euclidean 3 × Euclidean (n - 1))
        (adaptedCoordinates T.data.adapted)) ⁻¹' D))
    (hnull : ∀ w ∈ (coordinates (Z := Euclidean 3 × Euclidean (n - 1))
        (adaptedCoordinates T.data.adapted)) ⁻¹' D,
      conullvector T Q row w ⬝ᵥ reducedOperator F Q.1
        (fun x ↦ fullLeadingCovector T Q F row col Φ Y r (x, w.2)) w.1 = 0) :
    ContDiffOn ℝ ∞ (scalarAmplitude T Q' F row col Φ Y r)
      ((coordinates (Z := Euclidean 3 × Euclidean (n - 1))
        (adaptedCoordinates T.data.adapted)) ⁻¹' D) ∧
    (∀ w ∈ (coordinates (Z := Euclidean 3 × Euclidean (n - 1))
        (adaptedCoordinates T.data.adapted)) ⁻¹' D,
      conullvector T Q' row w ⬝ᵥ reducedOperator F Q'.1
        (fun x ↦ fullLeadingCovector T Q' F row col Φ Y r (x, w.2)) w.1 = 0) ∧
    ∀ (Ksrc : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))),
      Ksrc ⊆ (coordinates (Z := Euclidean 3 × Euclidean (n - 1))
        (adaptedCoordinates T.data.adapted)) ⁻¹' D → ∀ m : ℕ,
        cNorm Ksrc m (fullCorrectionCovector T Q' F row col Φ Y r) =
          cNorm Ksrc m (fullCorrectionCovector T Q F row col Φ Y r) := by
  have hO := hD.preimage
    (coordinates (Z := Euclidean 3 × Euclidean (n - 1)) (adaptedCoordinates T.data.adapted)).continuous
  have hscalarEq := scalarAmplitude_eqOn_of_retained_transport T Q Q' F row col
    hΩ hc hphase hframe Φ Y htime hDΩ hforward hbackward r
  obtain ⟨hlead, hcorr, _hatom, _hstrain⟩ := primary_formulas_eqOn_of_retained_transport T Q Q' F row col
    hΩ hc hphase hframe Φ Y htime hDΩ hforward hbackward hD r 1
  have hl := (null_coefficients_eqOn_of_coordinates_eqOn T Q Q' row col hc hphase hframe).2.1
  refine ⟨hscalar.congr hscalarEq.symm, ?_, ?_⟩
  · intro w hw
    have hop := reducedOperator_eq_of_germ F (hframe w (hDΩ hw))
      (slice_eventuallyEq hO hlead hw)
    rw [← hl (hDΩ hw), ← hop]
    exact hnull w hw
  · intro Ksrc hKsrc m
    apply Finset.sum_congr rfl
    intro k _
    congr 1
    apply Set.image_congr
    intro w hw
    exact congrArg norm
      ((eventuallyEq_of_mem (hO.mem_nhds (hKsrc hw))
        (fun _ hz ↦ (hcorr hz).symm)).iteratedFDeriv ℝ k).eq_of_nhds

open ResponseSourceExtension Sampling.BackgroundModulation

/-- The complete localized reduced source is identical on the original open
parameter neighborhood and all physical space. Both physical masks, the output
cutoff and the factor one half are literal. All joint jets consequently agree,
so the cubic Fourier profiles transfer with the same reserve sixteen and
constants (`app:ch_response:eq:response-graded-source`). -/
theorem localized_reducedSource_eqOn_of_retained_transport
    (r : Euclidean (n - 1) × Euclidean 3 → ℝ) (τ : ℝ)
    {core chart : Set (Euclidean n)} (χ : OutputCutoff core chart)
    (χsrc η : Euclidean n → ℝ)
    {Vsrc : Set (Euclidean 3 × Euclidean (n - 1))} (hVsrc : IsOpen Vsrc)
    (hproduct : chart ×ˢ Vsrc ⊆
      (coordinates (Z := Euclidean 3 × Euclidean (n - 1))
        (adaptedCoordinates T.data.adapted)) ⁻¹' D) :
    (∀ c ∈ Vsrc, fullStrainEnvelope T Q F row col Φ Y r χ τ c =
      fullStrainEnvelope T Q' F row col Φ Y r χ τ c) ∧
    let b := fun w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦
      χsrc w.1 • (η w.1 • ((1 / 2 : ℝ) • complexStressContraction (Q.1 w.1)
        (fullStrainEnvelope T Q F row col Φ Y r χ τ w.2 w.1)))
    let b' := fun w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦
      χsrc w.1 • (η w.1 • ((1 / 2 : ℝ) • complexStressContraction (Q'.1 w.1)
        (fullStrainEnvelope T Q' F row col Φ Y r χ τ w.2 w.1)))
    EqOn b b' (univ ×ˢ Vsrc) ∧
      ∀ m : ℕ, EqOn (iteratedFDeriv ℝ m b) (iteratedFDeriv ℝ m b') (univ ×ˢ Vsrc) := by
  have hamp := (primary_formulas_eqOn_of_retained_transport T Q Q' F row col
    hΩ hc hphase hframe Φ Y htime hDΩ hforward hbackward hD r τ).2.2.2
  have henv (c) (hcV : c ∈ Vsrc) : fullStrainEnvelope T Q F row col Φ Y r χ τ c =
      fullStrainEnvelope T Q' F row col Φ Y r χ τ c := by
    rw [fullStrainEnvelope_eq, fullStrainEnvelope_eq]
    funext x
    by_cases hx : χ.toFun x = 0
    · simp only [hx, zero_smul]
    · rw [hamp (hproduct (a := (x, c)) ⟨χ.support_chart (subset_tsupport _ hx), hcV⟩)]
  refine ⟨henv, ?_⟩
  dsimp only
  have he : EqOn
      (fun w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦
        χsrc w.1 • (η w.1 • ((1 / 2 : ℝ) • complexStressContraction (Q.1 w.1)
          (fullStrainEnvelope T Q F row col Φ Y r χ τ w.2 w.1))))
      (fun w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦
        χsrc w.1 • (η w.1 • ((1 / 2 : ℝ) • complexStressContraction (Q'.1 w.1)
          (fullStrainEnvelope T Q' F row col Φ Y r χ τ w.2 w.1)))) (univ ×ˢ Vsrc) := by
    intro w hw
    by_cases hx : χ.toFun w.1 = 0
    · simp only [fullStrainEnvelope_eq, hx, zero_smul, map_zero, smul_zero]
    · simp only [henv w.2 hw.2, hframe w
        (hDΩ (hproduct (a := w) ⟨χ.support_chart (subset_tsupport _ hx), hw.2⟩))]
  refine ⟨he, fun m w hw ↦ ?_⟩
  exact ((eventuallyEq_of_mem ((isOpen_univ.prod hVsrc).mem_nhds hw)
    (fun _ hz ↦ he hz)).iteratedFDeriv ℝ m).eq_of_nhds

end JanetCartan.RawPrimary.LocalFrameAgreement
