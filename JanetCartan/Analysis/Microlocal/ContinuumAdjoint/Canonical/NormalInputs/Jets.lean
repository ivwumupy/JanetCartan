module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.NormalInputs.Jets.Arguments
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.NormalInputs.Jets.BallBounds
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.NormalInputs.Jets.Homogeneity
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.NormalInputs.Jets.Inverse
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.NormalInputs.Jets.Jacobian
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.NormalInputs.Determinant

/-!
# Canonical finite normalized-jet geometry

The actual `normalJetRescaling`, its degree-minus-one column determinant,
normalized Jacobian identity, common-ball jet estimates, and explicit finite
immersion reserve for `app:ch_background:prop:bg-adjoint`.

The normalized inverse and ORIGINAL Jacobian estimates are assembled on the
same supported conic image, with threshold one and the original spectator
support. The geometric hypotheses are the retained outputs of
`exists_actual_refined_supported_geometry` and
`exists_canonical_coefficient_buffers`; the support inclusion is supplied by
the supported-image construction. No inverse or Jacobian jet is assumed.

The final projected-stress endpoint chooses its budget before the immersion
from its fixed bound at order `2 * (n + 1) + 6`. The finite-family selection
and instantiation of the geometric hypotheses belong to the parent canonical
normal-input construction.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint.Canonical.NormalInputs
open ContinuumRow DerivativeKernels ModifiedNormalSymbol
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open CanonicalConic ContinuumNormalReduction.TransportSymbol

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- The finite normalized geometry consumed by
`graphNormalAmplitudeBounds_of_densityJets`, for the SAME `normalChart` and
`normalJetRescaling`. The fixed primitive position bound supplies every
analytic jet field through `2 * (n + 1)`. Original Jacobian jets require one
more forward derivative, hence position order `2 * (n + 1) + 2`.

The common balls, augmented half-gap, buffered inverse and supported output
shell are produced by `exists_actual_refined_supported_geometry`; coefficient
and segment buffers, including the positive input-frequency bound, are
produced by `exists_canonical_coefficient_buffers`. The only support inclusion
is the exact obligation of `normalSupport_subset_inputDomain`.
Sources: `app:ch_background:prop:bg-adjoint`, `bg-Psi`, `bg-jacobian`,
`bg-mixed-input`, and `bg-full-complex-amplitude`. -/
theorem exists_normalChart_primitiveJetGeometry
    {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)}
    {r aOuter aPhase rMask aMask ρ : ℝ}
    (hηb : ηb ≠ 0) (hr : 0 < r) (hρ : 0 < ρ)
    (hrMask : 0 < rMask) (haMask : 0 < aMask)
    (hphysical : 4 * aMask < ρ) (hradial : rMask ≤ ρ)
    {W K : Set (InputVariables n)} (hW : IsOpen W)
    (hball : closedBall (((0, 0), (z₀ 0, spectatorCenter z₀), ηb) : InputVariables n) ρ ⊆ W)
    (hK : IsCompact K) (hWK : W ⊆ K)
    {Vphase Lphase : Set (Euclidean n × CarrierParameter)}
    (hVphase : IsOpen Vphase) (hLphase : IsCompact Lphase) (hLVphase : Lphase ⊆ Vphase)
    {I : Set ℝ} (hI : IsOpen I) (hIT : Icc (0 : ℝ) 1 ⊆ I)
    (hsegI : ∀ t ∈ I, MapsTo (transportSegmentInput n t) W Vphase)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, MapsTo (transportSegmentInput n t) W Lphase)
    (A : InputVariables n ≃L[ℝ] ContinuumNormalReduction.TransportSymbol.Variables n × Euclidean 2)
    (q₀ : JointVariables n) {τ ℓ ε : ℝ} (hτ : 0 < τ) (hℓ : 0 < ℓ) (hε : 0 < ε)
    (hlower : ∀ q ∈ closedBall
      (((0, 0), (z₀ 0, spectatorCenter z₀), ηb) : InputVariables n) ρ, ε ≤ ‖q.2.2‖)
    {M : ℝ} (hM : 0 ≤ M) :
    ∃ B > (0 : ℝ), ∀
      (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold}),
      ContDiffOn ℝ ∞ (CanonicalCarrier.transportPosition T Q) Vphase →
      cNorm Lphase (2 * (n + 1) + 2) (CanonicalCarrier.transportPosition T Q) ≤ M →
      ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
        (physicalParameterSet z₀ aOuter ×ˢ dataSet z₀ ηb (3 * r)) →
      ∀ {b cJ : ℝ} {V L : Set (ℝ × Euclidean (n - 1))}
        {G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1))},
      0 < cJ →
      BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ aOuter)
        (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r)) V L b cJ G →
      IsOpen V → L ⊆ V →
      (∀ p ∈ physicalParameterSet z₀ aOuter,
        ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r),
          ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖) →
      closedBall q₀ (2 * τ) ⊆ symbolDomain T Q z₀ ηb r aOuter →
      MapsTo (inverseCoordinates (symbolInverse T Q z₀ ηb r aOuter))
        (closedBall q₀ (2 * τ))
        (closedBall (((0, 0), (z₀ 0, spectatorCenter z₀), ηb) : InputVariables n) ρ) →
      (∀ q ∈ closedBall (((0, 0), (z₀ 0, spectatorCenter z₀), ηb) : InputVariables n) ρ,
        ‖A.symm.toContinuousLinearMap.comp
          (fderiv ℝ (augmentedTransportGradient (CanonicalCarrier.transportPosition T Q)) q) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) →
      (∀ x : ContinuumNormalReduction.TransportSymbol.Variables n, ‖x.2.2‖ = ℓ → ∀ v : Euclidean 2,
        (x, v) ∈ closure (augmentedTransportGradient (CanonicalCarrier.transportPosition T Q) ''
          conicMaskSupport z₀ ηb rMask aMask) → (x, v) ∈ closedBall q₀ τ) →
      normalSupport T z₀ ηb rMask aMask ⊆
        (normalChart T Q z₀ ηb r aOuter aPhase).inputDomain →
      PrimitiveJetGeometry (normalChart T Q z₀ ηb r aOuter aPhase)
        (normalJetRescaling T Q z₀ ηb r aOuter aPhase) (2 * (n + 1)) 1 B (cJ / ‖ηb‖)
        (normalSupport T z₀ ηb rMask aMask)
        (Prod.snd '' (carrierSupport z₀ (r := aMask))) := by
  obtain ⟨Bi, hBi, hi⟩ := exists_normalJetRescaling_normalizedPull_bound T hηb hr
    ((0, 0), (z₀ 0, spectatorCenter z₀), ηb) hρ hW hball hK hWK
    hVphase hLphase hLVphase hI hIT hsegI hseg A q₀ hτ hℓ hε hlower (2 * (n + 1)) hM
  obtain ⟨Bj, hBj, hj⟩ := exists_normalJetRescaling_normalizedJacobian_jet_bound T hηb hr
    hrMask haMask hphysical hradial hW hball hK hWK
    hVphase hLphase hLVphase hI hIT hsegI hseg (2 * (n + 1)) hM
  obtain ⟨Ba, hBa, ha⟩ := exists_normalChart_argument_jet_bound T
  refine ⟨Bi + Bj + Ba, by linarith, ?_⟩
  intro Q hY hYM hf b cJ V L G hcJ hInv hV hLV htrans houtput hrange hgap hshell hsupport
  have hi' := hi Q hY hYM hInv hV hLV htrans houtput hrange hgap hshell hsupport
  have hj' := hj Q hY hYM hf hInv htrans hsupport
  have hBiB : Bi ≤ Bi + Bj + Ba := by linarith
  have hBjB : Bj ≤ Bi + Bj + Ba := by linarith
  have hBaB : Ba ≤ Bi + Bj + Ba := by linarith
  refine {
    threshold_pos := zero_lt_one
    budget_nonneg := by linarith
    gap_pos := div_pos hcJ (norm_pos_iff.mpr hηb)
    input_open := normalChart_inputDomain_open T Q z₀ ηb r aOuter aPhase
    jacobian_is_fderiv := fun _ hp ↦ normalChart_jacobian_is_fderiv T Q hηb hr hf hp
    determinant_gap := fun _ hp ↦ normalChart_determinant_gap T Q hηb hr hf hInv htrans hp
    high_frequency := fun _ hp _ ↦ normalSupport_image_high_frequency T Q hηb hr hInv htrans hsupport hp
    inverse_jets := fun p hp _ j hj hjN ↦ (hi' p hp j hj hjN).trans hBiB
    jacobian_jets := fun p hp _ j hjN ↦ (hj' p hp j hjN).trans hBjB
    carrier_jets := ?_
    left_jets := ?_
    right_jets := ?_ }
  · intro p _ _
    dsimp only
    intro j hj _
    exact (ha Q z₀ ηb r aOuter aPhase _ j hj).1.trans hBaB
  · intro p _ _
    dsimp only
    intro j hj _
    exact (ha Q z₀ ηb r aOuter aPhase _ j hj).2.1.trans hBaB
  · intro p _ _
    dsimp only
    intro j hj _
    exact (ha Q z₀ ηb r aOuter aPhase _ j hj).2.2.trans hBaB

/-- The normalized finite geometry budget is fixed BEFORE the immersion varies.
The only analytic norm input is the primitive immersion bound at the explicit
order `2 * (n + 1) + 6`, together with the original metric and normal gaps.
`exists_projected_normalPosition_finite_bound` supplies the position reserve;
the extra forward derivative needed for the original Jacobian is included.

Choose `E = PhaseExtension.extensionDomain T` in
`exists_canonical_coefficient_buffers` to obtain `hphaseDomain`. All remaining
varying hypotheses are precisely retained geometric outputs of
`exists_actual_refined_supported_geometry`, apart from the explicit support
inclusion produced by `normalSupport_subset_inputDomain`. The parent canonical
normal-input construction must instantiate these geometric hypotheses for its
finite family; no operator estimate or desired normalized jet is an input.
Sources: `app:ch_background:prop:bg-adjoint`, `bg-Psi`, `bg-jacobian`,
`bg-mixed-input`, and `bg-full-complex-amplitude`. -/
theorem exists_projected_normalChart_primitiveJetGeometry {d : ℕ}
    {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)}
    {r aOuter aPhase rMask aMask ρ : ℝ}
    (hηb : ηb ≠ 0) (hr : 0 < r) (hρ : 0 < ρ)
    (hrMask : 0 < rMask) (haMask : 0 < aMask)
    (hphysical : 4 * aMask < ρ) (hradial : rMask ≤ ρ)
    {W K : Set (InputVariables n)} (hW : IsOpen W)
    (hball : closedBall (((0, 0), (z₀ 0, spectatorCenter z₀), ηb) : InputVariables n) ρ ⊆ W)
    (hK : IsCompact K) (hWK : W ⊆ K)
    {Vphase Lphase : Set (Euclidean n × CarrierParameter)}
    (hVphase : IsOpen Vphase) (hLphase : IsCompact Lphase) (hLVphase : Lphase ⊆ Vphase)
    (hphaseDomain : Vphase ⊆ PhaseExtension.extensionDomain T)
    {I : Set ℝ} (hI : IsOpen I) (hIT : Icc (0 : ℝ) 1 ⊆ I)
    (hsegI : ∀ t ∈ I, MapsTo (transportSegmentInput n t) W Vphase)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, MapsTo (transportSegmentInput n t) W Lphase)
    (A : InputVariables n ≃L[ℝ] ContinuumNormalReduction.TransportSymbol.Variables n × Euclidean 2)
    (q₀ : JointVariables n) {τ ℓ ε : ℝ} (hτ : 0 < τ) (hℓ : 0 < ℓ) (hε : 0 < ε)
    (hlower : ∀ q ∈ closedBall
      (((0, 0), (z₀ 0, spectatorCenter z₀), ηb) : InputVariables n) ρ, ε ≤ ‖q.2.2‖)
    {KF : Set (Euclidean n)} (hKF : IsCompact KF) (hKU : KF ⊆ U)
    (hFball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ KF)
    {M κmet κ : ℝ} (hM : 0 ≤ M) (hκmet : 0 < κmet) (hκ : 0 < κ) :
    ∃ B > (0 : ℝ), ∀ (F : Euclidean n → Euclidean d)
      (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
      (hrank : HasFullNormalRankOn F U),
      cNorm KF (2 * (n + 1) + 6) F ≤ M →
      (∀ x ∈ KF, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ KF, ∀ w ∈ normalSpace F x,
        κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      ∀ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (ProjectedStressFrame.projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
      let Q := ⟨ProjectedStressFrame.projectedStress F,
        contDiffOn_pi.mpr (ProjectedStressFrame.contDiffOn_projectedStress hU hF hi hrank), hlow⟩
      ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
        (physicalParameterSet z₀ aOuter ×ˢ dataSet z₀ ηb (3 * r)) →
      ∀ {b cJ : ℝ} {V L : Set (ℝ × Euclidean (n - 1))}
        {G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1))},
      0 < cJ →
      BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ aOuter)
        (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r)) V L b cJ G →
      IsOpen V → L ⊆ V →
      (∀ p ∈ physicalParameterSet z₀ aOuter,
        ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r),
          ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖) →
      closedBall q₀ (2 * τ) ⊆ symbolDomain T Q z₀ ηb r aOuter →
      MapsTo (inverseCoordinates (symbolInverse T Q z₀ ηb r aOuter))
        (closedBall q₀ (2 * τ))
        (closedBall (((0, 0), (z₀ 0, spectatorCenter z₀), ηb) : InputVariables n) ρ) →
      (∀ q ∈ closedBall (((0, 0), (z₀ 0, spectatorCenter z₀), ηb) : InputVariables n) ρ,
        ‖A.symm.toContinuousLinearMap.comp
          (fderiv ℝ (augmentedTransportGradient (CanonicalCarrier.transportPosition T Q)) q) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) →
      (∀ x : ContinuumNormalReduction.TransportSymbol.Variables n, ‖x.2.2‖ = ℓ → ∀ v : Euclidean 2,
        (x, v) ∈ closure (augmentedTransportGradient (CanonicalCarrier.transportPosition T Q) ''
          conicMaskSupport z₀ ηb rMask aMask) → (x, v) ∈ closedBall q₀ τ) →
      normalSupport T z₀ ηb rMask aMask ⊆
        (normalChart T Q z₀ ηb r aOuter aPhase).inputDomain →
      PrimitiveJetGeometry (normalChart T Q z₀ ηb r aOuter aPhase)
        (normalJetRescaling T Q z₀ ηb r aOuter aPhase) (2 * (n + 1)) 1 B (cJ / ‖ηb‖)
        (normalSupport T z₀ ηb rMask aMask)
        (Prod.snd '' (carrierSupport z₀ (r := aMask))) := by
  have hLO : Lphase ⊆ ball (0 : Euclidean n) T.physicalRadius ×ˢ
      (CanonicalCarrier.parameter ⁻¹' parameterInterior (2 * P.radius)) := by
    intro p hp
    have h := hphaseDomain (hLVphase hp)
    refine ⟨h.1, fun i ↦ ?_⟩
    exact (h.2 i).trans (by linarith [hP.1])
  obtain ⟨Mphase, hMphase, hposition⟩ := exists_projected_normalPosition_finite_bound T
    (d := d) hP hLphase hLO hKF hKU hFball hM hκmet hκ
  obtain ⟨B, hB, hgeometry⟩ := exists_normalChart_primitiveJetGeometry T hηb hr hρ
    hrMask haMask hphysical hradial hW hball hK hWK hVphase hLphase hLVphase
    hI hIT hsegI hseg A q₀ hτ hℓ hε hlower hMphase.le
  refine ⟨B, hB, ?_⟩
  intro F hF hi hrank hFM hmet hnormal hlow
  dsimp only
  apply hgeometry _
    ((PhaseExtension.transportPosition_contDiffOn_extensionDomain T hP _).mono hphaseDomain)
    (hposition F hF hi hrank hFM hmet hnormal hlow)

end JanetCartan.ContinuumAdjoint.Canonical.NormalInputs
