module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.NormalInputs.Jets
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.NormalInputs.Support
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.NormalInputs.Phase
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.PrimitiveNorms

/-!
# Raw normal geometry on the original supplied masks

Apply the projected-frame normal-jet producer to the original coefficient
chart and its retained buffered inverse. The phase agreement radius is supplied
independently of the mask selection. Every geometric field of the raw-adjoint
endpoint is proved for the same `normalChart`; no further chart or mask is chosen.

The concrete consumer is `ContinuumInverse.exists_generic_current_rawAdjoint_cap`
in `InitializedCorrectedRegularity/SuppliedRaw`. Its parent applies this result
to the local geometry returned by `RawCappedInitialization`, after the actual
history has been admitted. Sources: `app:ch_background:prop:bg-adjoint`,
`app:ch_background:eq:bg-Psi`, `app:ch_background:eq:bg-jacobian`, and
`app:ch_background:eq:bg-full-complex-amplitude`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumInverse
open ContinuumRow CanonicalConic
open ContinuumAdjoint ContinuumAdjoint.Canonical ContinuumAdjoint.Canonical.NormalInputs
open ContinuumAdjoint.DerivativeKernels ContinuumAdjoint.DerivativeKernels.ModifiedNormalSymbol
open PhaseExtension
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison CanonicalCarrier
open ContinuumNormalReduction TransportSymbol TransportKernel

/-- The supplied coefficient chart and retained conic inverse give the entire
normal-geometry input of the generic current raw-adjoint estimate. The finite
jet bound precedes the varying immersion. The parameter `aPhase` is the
original phase producer's radius; only the original masks must fit inside it.
The local transport hypotheses are precisely the varying fields of
`RetainedJointGeometry.exists_retained_joint_comparison_geometry`, retained by
the capped selector (`bg-adjoint`, `bg-Psi`, `bg-jacobian`). -/
theorem exists_supplied_retained_normal_geometry
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)}
    {r a rMask aMask aPhase ρ τ ε : ℝ}
    (hηb : ηb ≠ 0) (hr : 0 < r) (ha : 0 < a)
    (hrMask : 0 < rMask) (haMask : 0 < aMask)
    (har : 6 * a ≤ r) (haR : 6 * a < T.family.radius)
    (hrr : rMask ≤ r) (haa : aMask ≤ a) (haPhase : aMask < aPhase)
    (hρ : 0 < ρ) (hτ : 0 < τ) (hε : 0 < ε)
    (hphysical : 4 * aMask < ρ) (hradial : rMask ≤ ρ)
    (hcarrier : closedBall (spectatorCenter z₀) (3 * r) ×ˢ closedBall (z₀ 0) (3 * r) ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2))
    (D : CoefficientNormCharts n)
    (p₀ : InputVariables n)
    (hp₀ : p₀ = (((0, 0), (z₀ 0, spectatorCenter z₀), ηb) : InputVariables n))
    (q₀ : JointVariables n)
    (A : InputVariables n ≃L[ℝ] ContinuumNormalReduction.TransportSymbol.Variables n × Euclidean 2)
    {W Bi : Set (InputVariables n)} (hW : IsOpen W)
    (hball : closedBall p₀ ρ ⊆ W) (hBi : IsCompact Bi) (hWBi : W ⊆ Bi)
    (hphaseDomain : D.field.region ⊆ PhaseExtension.extensionDomain T)
    {It : Set ℝ} (hIt : IsOpen It) (hIT : Icc (0 : ℝ) 1 ⊆ It)
    (hsegI : ∀ t ∈ It, MapsTo (transportSegmentInput n t) W D.field.region)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1,
      MapsTo (transportSegmentInput n t) W D.field.carrier)
    (hfrequency : ∀ p ∈ Bi, ε ≤ ‖p.2.2‖)
    {β cJ : ℝ} (hcJ : 0 < cJ)
    {Vinv Linv : Set (ℝ × Euclidean (n - 1))}
    (hVinv : IsOpen Vinv) (hLVinv : Linv ⊆ Vinv)
    (G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1)))
    {KF : Set (Euclidean n)} (hKF : IsCompact KF) (hKU : KF ⊆ U)
    (hFball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ KF)
    {MF κmet κ : ℝ} (hMF : 0 ≤ MF) (hκmet : 0 < κmet) (hκ : 0 < κ) :
    ∃ B > (0 : ℝ),
      ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        cNorm KF (2 * (n + 1) + 6) F ≤ MF →
        (∀ x ∈ KF, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ KF, ∀ w ∈ normalSpace F x,
          κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        ∀ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (ProjectedStressFrame.projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
        let Q := ⟨ProjectedStressFrame.projectedStress F,
          contDiffOn_pi.mpr (ProjectedStressFrame.contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
          (physicalParameterSet z₀ (6 * a) ×ˢ dataSet z₀ ηb (3 * r)) →
        BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ (6 * a))
          (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r))
          Vinv Linv β cJ G →
        (∀ p ∈ physicalParameterSet z₀ (6 * a),
          ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r),
            ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖) →
        closedBall q₀ (2 * τ) ⊆ symbolDomain T Q z₀ ηb r (6 * a) →
        MapsTo (inverseCoordinates (symbolInverse T Q z₀ ηb r (6 * a)))
          (closedBall q₀ (2 * τ)) (closedBall p₀ ρ) →
        (∀ p ∈ closedBall p₀ ρ,
          ‖A.symm.toContinuousLinearMap.comp
            (fderiv ℝ (augmentedTransportGradient (transportPosition T Q)) p) -
              ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) →
        (∀ x : ContinuumNormalReduction.TransportSymbol.Variables n,
          ‖x.2.2‖ = (1 / 4 : ℝ) → ∀ v : Euclidean 2,
          (x, v) ∈ closure (augmentedTransportGradient (transportPosition T Q) ''
            conicMaskSupport z₀ ηb rMask aMask) → (x, v) ∈ closedBall q₀ τ) →
        let g := normalChart T Q z₀ ηb r (6 * a) aPhase
        let J := normalSupport T z₀ ηb rMask aMask
        let X := closedBall (0 : Euclidean n) (4 * aMask)
        let Z := carrierSupport z₀ (r := aMask)
        let Ω := closedDirections ηb rMask
        0 < n ∧ PrimitiveJetGeometry g (normalJetRescaling T Q z₀ ηb r (6 * a) aPhase)
            (2 * (n + 1)) 1 B (cJ / ‖ηb‖) J (Prod.snd '' Z) ∧
        IsCompact X ∧ IsCompact Z ∧ IsCompact Ω ∧ Ω ⊆ {η | ‖η‖ = 1} ∧
        (∀ amplitude : AdjointAmplitude n,
          ContDiff ℝ ∞ (fun p : AmplitudeVariables n ↦ amplitude p.1 p.2.1 p.2.2) →
          PrimitiveRegularity g amplitude (fun _ ↦ 1)) ∧
        MeasurePreserving g.coordinates volume (volume.prod volume) ∧
        Continuous g.coordinates.symm ∧
        (∀ x y v w,
          ((chartCarrierVariable g.coordinates v w).1, x,
            (chartCarrierVariable g.coordinates v w).2) ∈ adjointConicBuffer X Z Ω 1 →
          ((chartCarrierVariable g.coordinates v w).1, y,
            (chartCarrierVariable g.coordinates v w).2) ∈ adjointConicBuffer X Z Ω 1 →
          w ∈ g.domain x y v) ∧
        ContinuousOn g.push g.inputDomain ∧
        (∀ x y v, MeasurableSet (g.domain x y v)) ∧
        (∀ x y v w, w ∈ g.domain x y v →
          HasFDerivWithinAt (g.forward x y v) (g.jacobian x y v w) (g.domain x y v) w) ∧
        (∀ x y v, InjOn (g.forward x y v) (g.domain x y v)) ∧
        (∀ x y v w, w ∈ g.domain x y v → g.inverse x y v (g.forward x y v w) = w) ∧
        (∀ Yext : Euclidean n × CarrierParameter → Euclidean (n - 1),
          EqOn Yext (transportPosition T Q) (supportedChart z₀ aPhase) →
          ∀ x y v w, w ∈ g.domain x y v →
            phase Yext (chartCarrierVariable g.coordinates v w).1 x
                (chartCarrierVariable g.coordinates v w).2 -
              phase Yext (chartCarrierVariable g.coordinates v w).1 y
                (chartCarrierVariable g.coordinates v w).2 =
              inner ℝ (x - y) (g.forward x y v w)) ∧
        (∀ p ∈ g.inputDomain,
          ((g.carrier p).1, p.1.1, (g.carrier p).2) ∈ adjointConicBuffer X Z Ω 1 →
          ((g.carrier p).1, p.1.2.1, (g.carrier p).2) ∈ adjointConicBuffer X Z Ω 1 → p ∈ J) ∧
        J ⊆ g.inputDomain ∧ IsClosed (g.push '' J) ∧ g.push '' J ⊆ g.outputDomain := by
  subst p₀
  have hn : 0 < n := by
    by_contra hn
    apply hηb
    ext i
    have hn0 : n - 1 = 0 := by omega
    exact Fin.elim0 (hn0 ▸ i)
  have hDcompact : IsCompact D.field.carrier := isCompact_closedBall _ _
  have hDsubset : D.field.carrier ⊆ D.field.region := D.field.ball_subset
  obtain ⟨B, hB, hjets⟩ := exists_projected_normalChart_primitiveJetGeometry T (d := N) hP
    (aPhase := aPhase) hηb hr hρ hrMask haMask hphysical hradial hW hball hBi hWBi
    D.field.isOpen_region hDcompact hDsubset hphaseDomain hIt hIT hsegI hseg A q₀
    hτ (by norm_num : (0 : ℝ) < 1 / 4) hε
    (fun p hp ↦ hfrequency p (hWBi (hball hp))) hKF hKU hFball hMF hκmet hκ
  refine ⟨B, hB, ?_⟩
  intro F hF hi hrank hFM hmet hnormal hlow
  dsimp only
  intro hf hInv htrans houtput hrange hhalf hshell
  let Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold} :=
    ⟨ProjectedStressFrame.projectedStress F,
      contDiffOn_pi.mpr (ProjectedStressFrame.contDiffOn_projectedStress hU hF hi hrank), hlow⟩
  have har₀ : a ≤ r := by linarith
  have hJ := normalSupport_subset_inputDomain T Q (z₀ := z₀)
    hηb hr ha har₀ hrr haa haPhase
  have hg := hjets F hF hi hrank hFM hmet hnormal hlow hf hcJ hInv hVinv hLVinv
    htrans houtput hrange hhalf hshell hJ
  obtain ⟨hX, hZ, hΩ⟩ := normalSupport_compact_parameters (n := n) z₀ ηb rMask aMask
  exact ⟨hn, hg, hX, hZ, hΩ, normalSupport_directions_unit ηb rMask,
    normalChart_primitiveRegularity T Q hηb hr hf hInv htrans hVinv hLVinv hcJ,
    normalChart_measurePreserving T Q z₀ ηb r (6 * a) aPhase,
    normalChart_coordinates_symm_continuous T Q z₀ ηb r (6 * a) aPhase,
    normalChart_domain_of_conicBuffers T Q hηb hr ha har₀ hrr haa haPhase,
    (normalChart_push_contDiffOn T Q hηb hr hf).continuousOn,
    fun x y v ↦ (normalChart_domain_open T Q z₀ ηb r (6 * a) aPhase x y v).measurableSet,
    fun x y v w hw ↦ (normalChart_hasFDerivAt T Q hηb hr hf x y v hw).hasFDerivWithinAt,
    normalChart_forward_injective T Q hηb hr hInv htrans,
    fun x y v w hw ↦ normalChart_inverse_forward T Q hηb hr hInv htrans x y v hw,
    fun Yext hYext ↦ normalChart_phase_identity T Q hP hr haR (by linarith) hcarrier Yext hYext,
    fun p _ hx hy ↦ normalSupport_of_conicBuffers T Q p hx hy, hJ,
    normalSupport_image_isClosed T Q hηb hr ha har₀ hrr haa haPhase hInv htrans hf hVinv hLVinv,
    normalSupport_image_subset_outputDomain T Q hηb hr ha har₀ hrr haa haPhase⟩

end JanetCartan.ContinuumInverse
