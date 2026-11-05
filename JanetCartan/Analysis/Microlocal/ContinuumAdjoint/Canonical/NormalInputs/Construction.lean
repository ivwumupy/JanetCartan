module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.NormalInputs.Jets
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.NormalInputs.Support
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.NormalInputs.Phase
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.CoefficientBuffers

/-!
# Actual canonical normal inputs for the raw adjoint

The construction instantiates the retained geometric producers, including their
common balls, augmented half-gap and supported shell, then discharges the support
premise of the normalized-jet deduction. Every radius, threshold and budget
precedes the immersion. The original amplitude and extended phase are supplied
independently by the canonical amplitude and phase constructions.

Consumer: `DerivativeKernels.exists_scalarTransportCarrierAdjoint_periodic_raw_bound`.
Sources: `app:ch_background:prop:bg-adjoint`, `app:ch_background:eq:bg-Psi`,
`app:ch_background:eq:bg-jacobian`, and `app:ch_background:eq:bg-full-complex-amplitude`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint.Canonical.NormalInputs
open ContinuumRow DerivativeKernels ModifiedNormalSymbol PhaseExtension TransportKernel
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open CanonicalConic ContinuumNormalReduction.TransportSymbol

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- Actual geometric inputs of the scalar-transport raw adjoint endpoint, with
threshold one, the SAME canonical coordinates and inverse, and constants fixed
by the primitive immersion bound at order `2 * (n + 1) + 6`.

`exists_actual_refined_supported_geometry` supplies outer smoothness, the buffered
inverse, transverse comparison, common balls, augmented half-gap and supported
shell. `exists_canonical_coefficient_buffers`, with `E = extensionDomain T`,
supplies the finite primitive coefficient domains. Neither normalized jets nor
an operator bound is assumed. Halving the smaller masks puts their closed support
strictly inside the phase-agreement chart while retaining shell containment.

The parent chooses the finite incidence family and supplies the actual original
amplitude and `PhaseExtension` agreement. Phase matching holds on the ENTIRE
working domain, independently of amplitude nonvanishing.
Sources: `app:ch_background:prop:bg-adjoint`, `bg-Psi`, `bg-jacobian`,
`bg-mixed-input`, and `bg-full-complex-amplitude`. -/
theorem exists_projected_normalInputs {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    {k : Euclidean n} (hk : k ≠ 0) (hinc : incidence k (P.toFun z₀) = 0)
    (hd : fderiv ℝ (fun z ↦ incidence k (P.toFun z)) z₀
      (EuclideanSpace.single 0 1) ≠ 0)
    {N : ℕ} {KF : Set (Euclidean n)} (hKF : IsCompact KF) (hKU : KF ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ KF)
    {M κmet κ cap : ℝ} (hM : 0 ≤ M) (hκmet : 0 < κmet) (hκ : 0 < κ)
    (hcap : 0 < cap) :
    let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
    ∃ r > (0 : ℝ), ∃ a > (0 : ℝ),
      6 * a < cap ∧ 6 * a ≤ r ∧ 6 * a < T.family.radius ∧
      4 * a < T.physicalRadius ∧ 4 * a < 1 / 2 ∧
      (closedBall (spectatorCenter z₀) (3 * r) ×ˢ closedBall (z₀ 0) (3 * r) ⊆
        carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2)) ∧
    ∃ rMask > (0 : ℝ), rMask < r ∧
    ∃ aMask > (0 : ℝ), aMask < a ∧ aMask ≤ rMask ∧
    ∃ δ > (0 : ℝ), ∃ B > (0 : ℝ), ∃ cJ > (0 : ℝ),
      ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        cNorm KF (2 * (n + 1) + 6) F ≤ M →
        (∀ x ∈ KF, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ KF, ∀ w ∈ normalSpace F x,
          κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        ∀ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (ProjectedStressFrame.projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (ProjectedStressFrame.projectedStress F - fun _ ↦ cubeStress n) < δ →
        let Q := ⟨ProjectedStressFrame.projectedStress F,
          contDiffOn_pi.mpr (ProjectedStressFrame.contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        let g := normalChart T Q z₀ ηb r (6 * a) a
        let J := normalSupport T z₀ ηb rMask aMask
        let X := closedBall (0 : Euclidean n) (4 * aMask)
        let Z := carrierSupport z₀ (r := aMask)
        let Ω := closedDirections ηb rMask
        0 < n ∧ PrimitiveJetGeometry g (normalJetRescaling T Q z₀ ηb r (6 * a) a)
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
        (∀ Y : Euclidean n × CarrierParameter → Euclidean (n - 1),
          EqOn Y (CanonicalCarrier.transportPosition T Q) (supportedChart z₀ a) →
          ∀ x y v w, w ∈ g.domain x y v →
            phase Y (chartCarrierVariable g.coordinates v w).1 x
                (chartCarrierVariable g.coordinates v w).2 -
              phase Y (chartCarrierVariable g.coordinates v w).1 y
                (chartCarrierVariable g.coordinates v w).2 =
              inner ℝ (x - y) (g.forward x y v w)) ∧
        (∀ p ∈ g.inputDomain,
          ((g.carrier p).1, p.1.1, (g.carrier p).2) ∈ adjointConicBuffer X Z Ω 1 →
          ((g.carrier p).1, p.1.2.1, (g.carrier p).2) ∈ adjointConicBuffer X Z Ω 1 → p ∈ J) ∧
        J ⊆ g.inputDomain ∧ IsClosed (g.push '' J) ∧ g.push '' J ⊆ g.outputDomain ∧
        IsOpen g.inputDomain ∧ IsOpen g.outputDomain ∧
        MapsTo g.pull g.outputDomain g.inputDomain ∧
        (∀ p ∈ g.outputDomain, g.push (g.pull p) = p) ∧
        (∀ p ∈ g.push '' J, 1 ≤ ‖(g.carrier (g.pull p)).2‖) ∧
        (∀ p ∈ g.inputDomain, ∀ t : ℝ, 0 < t →
          let q := scaleJointInput T t p
          |(g.jacobian q.1.1 q.1.2.1 q.2 q.1.2.2).det| =
            t * |(g.jacobian p.1.1 p.1.2.1 p.2 p.1.2.2).det|) := by
  dsimp only
  let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
  have hηb : ηb ≠ 0 := FrozenIncidence.tangential_direction_ne_zero T hP hz₀ hk hinc
  have hn : 0 < n := by
    by_contra hn
    have hn₀ : n = 0 := by omega
    subst n
    exact hk (Subsingleton.elim _ _)
  have hcenter : ((0 : Euclidean n), (z₀ 0, spectatorCenter z₀)) ∈ extensionDomain T := by
    refine ⟨mem_ball_self T.physicalRadius_pos, ?_⟩
    change carrierParameters (spectatorCenter z₀, z₀ 0) ∈ parameterInterior (3 * P.radius / 2)
    rw [carrierParameters_spectatorCenter]
    exact fun i ↦ (hz₀ i).trans (by linarith [hP.1])
  obtain ⟨cap₀, hcap₀, hbuffers⟩ := exists_canonical_coefficient_buffers T hP hz₀ hk hinc
    (extensionDomain T) (extensionDomain_open T) hcenter
  obtain ⟨r, hr, a, ha, hacap, har, haR, hcell, hcarrier,
    ρ, hρ, hρcap, hinput, τ, hτ, r', hr', hrr, hrρ, a', ha', haa, har', haρ,
    δ, hδ, cJ, hcJ, b, hb, V, L, hV, hVc, hLc, hLV, hactual⟩ :=
    exists_actual_refined_supported_geometry T (N := N) hP hz₀ hk hinc hd
      hKF hKU hball M hκmet hκ
      (lt_min hcap₀ (lt_min hcap T.physicalRadius_pos))
  obtain ⟨W, K, Vphase, Lphase, I, D, ε, hW, hK, hballW, hWK, hKdom,
    hVp, hLp, hLVp, hI, hinterval, hIT, hsegI, hseg, hDcar, hDreg, hDom,
    hfoot, hsupport, hε, hη, hJac⟩ :=
    hbuffers hr hρ (hρcap.trans_le (min_le_left _ _)) hinput
  have hrMask : 0 < r' / 2 := half_pos hr'
  have haMask : 0 < a' / 2 := half_pos ha'
  have hrrMask : r' / 2 < r := (half_lt_self hr').trans_le hrr
  have haaMask : a' / 2 < a := (half_lt_self ha').trans_le haa
  have hphysical : 4 * (a' / 2) < ρ := by linarith
  obtain ⟨B, hB, hjets⟩ := exists_projected_normalChart_primitiveJetGeometry T (d := N) hP
    (aPhase := a) hηb hr hρ hrMask haMask hphysical
    ((half_le_self hr'.le).trans hrρ) hW hballW hK hWK hVp hLp hLVp
    (fun _ hp ↦ (hDom hp).1) hI hIT hsegI hseg
    (augmentedReferenceEquiv T hP hz₀ hinc hd)
    (frozenAugmentedChart T (augmentedInputCenter T (z₀ := z₀) (k := k)))
    hτ (norm_pos_iff.mpr hk) hε hη hKF hKU hball hM hκmet hκ
  refine ⟨r, hr, a, ha,
    hacap.trans_le ((min_le_right _ _).trans (min_le_left _ _)), har, haR,
    by linarith [hacap.trans_le ((min_le_right _ _).trans (min_le_right _ _))],
    hcell, hcarrier, r' / 2, hrMask, hrrMask, a' / 2, haMask, haaMask,
    by linarith, δ, hδ, B, hB, cJ, hcJ, ?_⟩
  intro F hF hi hrank hFM hmet hnormal hlow hclose
  let Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold} :=
    ⟨ProjectedStressFrame.projectedStress F,
    contDiffOn_pi.mpr (ProjectedStressFrame.contDiffOn_projectedStress hU hF hi hrank), hlow⟩
  have hfour : cNorm KF 4 F ≤ M :=
    (cNorm_mono_order (by omega : 4 ≤ 2 * (n + 1) + 6)).trans hFM
  obtain ⟨hf, hslice, hInv, htrans, houtput, hrange, hgap, hbuffer, hshell, hupper⟩ :=
    hactual F hF hi hrank hfour hmet hnormal hlow hclose
  have har₀ : a ≤ r := by linarith
  have hJ := normalSupport_subset_inputDomain T Q (z₀ := z₀)
    hηb hr ha har₀ hrrMask.le haaMask.le haaMask
  have hshell' : ∀ x : ContinuumNormalReduction.TransportSymbol.Variables n,
      ‖x.2.2‖ = ‖k‖ → ∀ v : Euclidean 2,
      (x, v) ∈ closure (augmentedTransportGradient (CanonicalCarrier.transportPosition T Q) ''
        conicMaskSupport z₀ ηb (r' / 2) (a' / 2)) → (x, v) ∈ closedBall
          (frozenAugmentedChart T (augmentedInputCenter T (z₀ := z₀) (k := k))) τ := by
    intro x hx v hv
    exact hshell x hx v (closure_mono (image_mono (conicMaskSupport_mono z₀ ηb
      (half_le_self hr'.le) (half_le_self ha'.le))) hv)
  have hg := hjets F hF hi hrank hFM hmet hnormal hlow hf hcJ hInv hV hLV
    htrans houtput hrange hgap hshell' hJ
  obtain ⟨hX, hZ, hΩ⟩ := normalSupport_compact_parameters (n := n) z₀ ηb (r' / 2) (a' / 2)
  refine ⟨hn, hg, hX, hZ, hΩ, normalSupport_directions_unit ηb (r' / 2),
    normalChart_primitiveRegularity T Q hηb hr hf hInv htrans hV hLV hcJ,
    normalChart_measurePreserving T Q z₀ ηb r (6 * a) a,
    normalChart_coordinates_symm_continuous T Q z₀ ηb r (6 * a) a,
    normalChart_domain_of_conicBuffers T Q hηb hr ha har₀ hrrMask.le haaMask.le haaMask,
    (normalChart_push_contDiffOn T Q hηb hr hf).continuousOn,
    fun x y v ↦ (normalChart_domain_open T Q z₀ ηb r (6 * a) a x y v).measurableSet,
    fun x y v w hw ↦ (normalChart_hasFDerivAt T Q hηb hr hf x y v hw).hasFDerivWithinAt,
    normalChart_forward_injective T Q hηb hr hInv htrans,
    fun x y v w hw ↦ normalChart_inverse_forward T Q hηb hr hInv htrans x y v hw,
    fun Y hY ↦ normalChart_phase_identity T Q hP hr haR (by linarith) hcarrier Y hY,
    fun p _ hx hy ↦ normalSupport_of_conicBuffers T Q p hx hy, hJ,
    normalSupport_image_isClosed T Q hηb hr ha har₀ hrrMask.le haaMask.le haaMask
      hInv htrans hf hV hLV,
    normalSupport_image_subset_outputDomain T Q hηb hr ha har₀ hrrMask.le haaMask.le haaMask,
    normalChart_inputDomain_open T Q z₀ ηb r (6 * a) a,
    normalChart_outputDomain_open T Q hηb hr hInv htrans hV hLV,
    normalChart_inverse_mem T Q hηb hr hInv htrans,
    fun p hp ↦ normalChart_push_pull T Q hηb hr hInv htrans hp,
    fun p hp ↦ normalSupport_inverse_high_frequency T Q hηb hr ha har₀
      hrrMask.le haaMask.le haaMask hInv htrans hp,
    fun p hp t ht ↦ normalChart_determinant_scaling T Q hηb hr hf hInv htrans hp ht⟩

end JanetCartan.ContinuumAdjoint.Canonical.NormalInputs
