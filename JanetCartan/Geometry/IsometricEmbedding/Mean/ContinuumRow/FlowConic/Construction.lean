module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.FlowConic.Geometry
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.SupportedInputs
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalBudgets.Kernel
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.CarrierNormalRealization.SupportedShell

/-!
# Construct the supported canonical carrier inside the transport-flow domain

All charts, masks, finite domains and frame thresholds are constructed before
`F`. The entire coefficient evaluation domain is contained in the prescribed
open flow neighborhood `E`. Normal and detector smoothness are required only
on `E`, exactly as produced by `CanonicalCarrier.exists_actual_canonical_primitive_controls`
in `ActualPrimitive`. That producer also supplies the primitive finite norms
on the returned `CoefficientNormCharts`. No inverse, support, substitution, symbol estimate,
operator bound or normal identity is assumed.

The conclusion retains the uncut operator, literal adjoint, regularization
limits and global reflected matrix normal, including both quadratures and the
original product measure. The row parent must instantiate the primitive inputs
on its common flow and finite family; this is not the unconditional row theorem.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.FlowConic
open CanonicalConic
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ActualComparison CanonicalCarrier ContinuumNormalReduction TransportSymbol TransportKernel
open CarrierNormalRealization Pseudodifferential AmplitudeBound PeriodicLocalL2

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- Construct the supported geometry and apply the global carrier producer to
its SAME canonical kernel. The norm inputs are exactly the primitive outputs
of `CanonicalCarrier.exists_actual_canonical_primitive_controls`, including
normal and detector smoothness on `E`. Both incidence and physical radii
are chosen so that the entire coefficient domain lies in `E`; no regularity
beyond the actual flow neighborhood is required.
All geometric premises are discharged here, and all fixed choices precede
`F`. A positive rescaling of the incidence covector selects the sphere of
radius `1/4` while preserving both selected directions.
Sources: `app:ch_background:eq:bg-Psi`, `bg-jacobian`, `bg-mixed-input`, `bg-T`,
`bg-full-complex-amplitude`, `bg-real-symbol`, and `app:ch_background:defn:bg-row`. -/
theorem exists_actual_supported_carrier_in_open_of_primitive_controls
    {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    {k : Euclidean n} (hk : k ≠ 0) (hinc : incidence k (P.toFun z₀) = 0)
    (hd : fderiv ℝ (fun z ↦ incidence k (P.toFun z)) z₀
      (EuclideanSpace.single 0 1) ≠ 0)
    {KF : Set (Euclidean n)} (hKF : IsCompact KF) (hKU : KF ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ KF)
    (C₀ : ℝ) {κmet κ : ℝ} (hκmet : 0 < κmet) (hκ : 0 < κ)
    {cap : ℝ} (hcap : 0 < cap)
    (E : Set (Euclidean n × CarrierParameter)) (hE : IsOpen E)
    (hcenter : ((0 : Euclidean n), (z₀ 0, spectatorCenter z₀)) ∈ E) :
    ∃ hn : 0 < n, ∃ t > (0 : ℝ), ‖t • k‖ = 1 / 4 ∧
      NormedSpace.normalize (t • k) = NormedSpace.normalize k ∧
      NormedSpace.normalize (T.data.adapted.embedding.toContinuousLinearMap.adjoint (t • k)) =
        NormedSpace.normalize (T.data.adapted.embedding.toContinuousLinearMap.adjoint k) ∧
    let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint (t • k)
    ∃ (r a r' a' : ℝ) (hr : 0 < r) (ha : 0 < a) (hr' : 0 < r') (ha' : 0 < a')
      (hcell' : 4 * a' < 1 / 2) (hηb : ηb ≠ 0),
      6 * a < cap ∧ coefficientDomain z₀ r (6 * a) ⊆ E ∧
      r' ≤ r ∧ a' ≤ a ∧ a' ≤ r' ∧
    ∃ D : CoefficientNormCharts n, D.field.region ⊆ E ∧
      D.field.region ⊆ coefficientDomain z₀ r (6 * a) ∧
      tsupport (FixedCutoffs.physical (n := n) ha' 1) ×ˢ
        carrierSupport z₀ (r := a') ⊆ D.field.carrier ∧
    ∃ δ > (0 : ℝ), ∀ (M M₀ B₀ B : ℝ), 0 ≤ M → 0 ≤ M₀ → 1 ≤ B₀ → 0 ≤ B →
      ∀ (s : ℕ) (hreserve : 2 * (n + 1) ≤ s),
    ∃ C > (0 : ℝ), ∃ Cpdo > (0 : ℝ), ∃ Cmask ≥ (0 : ℝ),
      ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        cNorm KF 4 F ≤ C₀ →
        (∀ x ∈ KF, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ KF, ∀ w ∈ normalSpace F x,
          κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        ∀ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (ProjectedStressFrame.projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (ProjectedStressFrame.projectedStress F - fun _ ↦ cubeStress n) < δ →
        ∀ (row col : Fin n)
          (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
          (initial : Euclidean (n - 1) × Euclidean 3 → ℝ),
        let Q := ⟨ProjectedStressFrame.projectedStress F,
          contDiffOn_pi.mpr (ProjectedStressFrame.contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        let e := data T Q F row col Φ Y initial ha' hcell'
          (angularMask z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1)
          FixedCutoffs.highFrequency
        let d := coefficientsOfCarrier e (FixedCutoffs.physical ha' 1)
        let J := symbolJacobian T Q
        let u := symbolInverse T Q z₀ ηb r (6 * a)
        let Ω := symbolDomain T Q z₀ ηb r (6 * a)
        let S := closedBall (spectatorCenter z₀) (a' / 2)
        ContDiffOn ℝ ∞ (Function.uncurry (normalField T Q F row col Φ Y initial))
          E →
        (∀ i : Fin n, ContDiffOn ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦
          quadratic (Q.1 p.1) (T.carrierGradient Q p.1 (parameter p.2)) i)
          E) →
        ∀ H : ℝ, 1 ≤ H →
        cNorm D.field.carrier 3 (transportPosition T Q) ≤ M →
        1 + cNorm D.field.carrier (s + 2) (transportPosition T Q) ≤ B * H →
        D.Controls s M₀ B₀ H d →
      ∃ hsupport : ∀ x, d.measurement x ≠ 0 → ∀ j, |x j| ≤ 4 * a',
      ∃ Lmask > 0, ∃ Mmask ≥ 0,
      ∃ hmask : ∀ (Q : ℝ), 1 ≤ Q → CarrierRegularization.MaskHypotheses e
        (parameterTruncatedMask (carrierSupport z₀ (r := a')) (radialCarrierMask FixedCutoffs.radialRegularization Q)) (carrierSupport z₀ (r := a')) (Lmask * Q) Mmask Cmask,
      (∀ (Q : ℝ) (hQ : 1 ≤ Q),
        ‖(hmask Q hQ).operator.comp (hmask Q hQ).operator.adjoint‖ ≤
            (n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n (4 * a') * (C * H)) ∧
          ‖(realQuadratureChannel (hmask Q hQ).operator).comp
            (realQuadratureChannel (hmask Q hQ).operator).adjoint‖ ≤
            (n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n (4 * a') * (C * H))) ∧
      (∀ v : carrierInitialTestSpace n,
        MemLp (carrierTestIntegral e v.val) 2 volume ∧
        (eLpNorm (carrierTestIntegral e v.val) 2 volume).toReal ≤
          Real.sqrt ((n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n (4 * a') * (C * H))) *
            ‖carrierInitialTestToLp v‖) ∧
      ∃ (hb : ContDiff ℝ ∞ (Function.uncurry
        (fullReflectedMatrixAmplitude d J u Ω S)))
        (hA : ∀ i j, HasAmplitudeDerivativeBound
          (fun ξ z ↦ fullReflectedMatrixAmplitude d J u Ω S ξ z i j)
          s (Cpdo * H)),
      ∃ U : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
        ‖U‖ ≤ Real.sqrt ((n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n (4 * a') * (C * H))) ∧
        ‖U.adjoint‖ ≤ Real.sqrt ((n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n (4 * a') * (C * H))) ∧
        (∀ v : carrierInitialTestSpace n,
          U (carrierInitialTestToLp v) =ᵐ[volume] carrierTestIntegral e v.val) ∧
        (∀ f : CarrierL2 n, ∀ᵐ x ∂volume, x ∉ e.outputChart → U f x = 0) ∧
        (∀ W : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
          (∀ v : carrierInitialTestSpace n,
            W (carrierInitialTestToLp v) =ᵐ[volume] carrierTestIntegral e v.val) → W = U) ∧
        (∀ w : ComplexOutputL2 n,
          MemLp (carrierAdjointIntegral e w) 2 (carrierMeasure n) ∧
          U.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral e w) ∧
        (∀ w : ComplexOutputL2 n,
          Filter.Tendsto (fun k : ℕ ↦
            (hmask ((k : ℝ) + 1) (by exact le_add_of_nonneg_left (Nat.cast_nonneg k))).operator.adjoint w)
            Filter.atTop (nhds (U.adjoint w))) ∧
        (realQuadratureChannel U).comp (realQuadratureChannel U).adjoint =
          realOutputCompression (transferOperator
            (vectorTwoPositionL2Operator hn (4 * a')
              (fullReflectedMatrixAmplitude d J u Ω S) hb
              (fullReflectedMatrixAmplitude_supportedInCenteredBox
                d J u Ω S (4 * a') hsupport)
              (Cpdo * H) (fun i j ξ is his ↦ hA i j ξ is (his.trans hreserve)))) := by
  classical
  have hn : 0 < n := by
    by_contra h
    have hn0 : n = 0 := by omega
    apply hk
    ext i
    exact Fin.elim0 (hn0 ▸ i)
  refine ⟨hn, ?_⟩
  obtain ⟨t, ht, hknorm, hk', hinc', hd', hdir, hηdir⟩ :=
    exists_small_incidence_representative T hk hinc hd
  let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint (t • k)
  have hηb : ηb ≠ 0 := FrozenIncidence.tangential_direction_ne_zero T hP hz₀ hk' hinc'
  obtain ⟨cap₀, hcap₀, hbuffers⟩ :=
    exists_canonical_coefficient_buffers T hP hz₀ hk' hinc' E hE hcenter
  obtain ⟨r, hr, a, ha, hacap, houterE, har, haR, hcell, hcarrier,
    ρ, hρ, hρcap, hinput, τ, hτ, r', hr', hrr, hrρ, a', ha', haa, har', haρ,
    δ, hδ, cJ, hcJ, b, hb, V, L, hV, hVc, hLc, hLV, hgeometry⟩ :=
    exists_actual_refined_supported_geometry_in_open T hP hz₀ hk' hinc' hd'
      hKF hKU hball C₀ hκmet hκ (lt_min hcap hcap₀) E hE hcenter
  obtain ⟨W, K, Vphase, Lphase, I, D, ε, hW, hK, hinputW, hWK, hKdom,
    hVphase, hLphase, hLphaseV, hI, _, hIT, hsegT, hseg, hDcar, hDreg, hDom,
    hfoot, hsupportD, hε, hη, hjac⟩ :=
    hbuffers hr hρ (hρcap.trans_le (min_le_right _ _)) hinput
  obtain ⟨δJ, hδJ, hjac⟩ := hjac hcJ
  let p₀ := augmentedInputCenter T (z₀ := z₀) (k := t • k)
  let q₀ := frozenAugmentedChart T p₀
  let G := FrozenIncidence.referenceEquiv T hP hz₀ hinc' hd'
  obtain ⟨Cfreq₀, hCfreq₀, hdiffbound⟩ := exists_reference_differential_upper G
  have hcell' : 4 * a' < 1 / 2 := by linarith
  have hDouter : D.field.region ⊆ coefficientDomain z₀ r (6 * a) := by
    rw [hDreg]
    exact fun _ hp ↦ (hDom hp).2
  have hDsupp := hsupportD ha' haρ
  refine ⟨t, ht, hknorm, hdir, hηdir, r, a, r', a', hr, ha, hr', ha', hcell', hηb,
    hacap.trans_le (min_le_left _ _), houterE, hrr, haa, har', D,
    ?_, hDouter, hDsupp, δ, hδ, ?_⟩
  · rw [hDreg]
    exact fun _ hp ↦ (hDom hp).1
  intro M M₀ B₀ B hM hM₀ hB₀ hB s hreserve
  let angular := angularMask z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1
  let Lq := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ ℝ)).symm.toContinuousLinearMap
  let Cmask := cNorm (carrierSupport z₀ (r := a') ×ˢ closedBall (0 : Euclidean (n - 1)) 1)
    0 (Function.uncurry angular) * M₀ ^ 2 * (‖Lq‖ * M₀)
  have hCmask : 0 ≤ Cmask := mul_nonneg (mul_nonneg (cNorm_nonneg ..) (sq_nonneg _))
    (mul_nonneg (norm_nonneg _) hM₀)
  obtain ⟨Cnorm, hCnorm, Cpdo, hCpdo, hconstruct⟩ :=
    exists_carrierL2Extension_supported_globalNormal_of_primitiveNorms (N := N)
      (adaptedSliceCoordinates T) p₀ q₀ hρ hτ hW hinputW hK hWK
      (O := ball q₀ (2 * τ)) isOpen_ball (closedBall_subset_ball (by linarith))
      hVphase hLphase hLphaseV hI hIT hsegT hseg
      (augmentedReferenceEquiv T hP hz₀ hinc' hd')
      hM hM₀ hB₀ hδJ hε hB hη D hfoot
      (Cupper := 2) (ℓ := ‖t • k‖) (by norm_num)
      (norm_pos_iff.mpr hk') (by rw [hknorm]; norm_num) (by rw [hknorm]; norm_num)
      (S := closedBall (spectatorCenter z₀) (a' / 2)) (isCompact_closedBall _ _)
      s (by omega) FixedCutoffs.highFrequency_smooth
      (fun _ ht ↦ FixedCutoffs.highFrequency_zero ht)
      (fun _ ht ↦ FixedCutoffs.highFrequency_one ht)
      FixedCutoffs.radialRegularization_smooth FixedCutoffs.radialRegularization_compact
      (fun _ ht ↦ FixedCutoffs.radialRegularization_one ht)
  refine ⟨Cnorm, hCnorm, Cpdo, hCpdo, Cmask, hCmask, ?_⟩
  intro F hF hi hrank hFM hmet hnormal hlow hclose row col Φ Y initial
  dsimp only
  let Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold} :=
    ⟨ProjectedStressFrame.projectedStress F,
      contDiffOn_pi.mpr (ProjectedStressFrame.contDiffOn_projectedStress hU hF hi hrank), hlow⟩
  let e := data T Q F row col Φ Y initial ha' hcell' angular FixedCutoffs.highFrequency
  let d := coefficientsOfCarrier e (FixedCutoffs.physical ha' 1)
  intro hνE hdetE H hH hlowY hhighY hcoeff
  have hν := hνE.mono houterE
  have hdet := fun i ↦ (hdetE i).mono houterE
  obtain ⟨hf, hsliceGap, hInv, htrans, houtput, hrange, hgap, hpunctured, hshell, hupper⟩ :=
    hgeometry F hF hi hrank hFM hmet hnormal hlow hclose
  obtain ⟨hJeq, hJne, hJlow⟩ := hjac Q hf hInv htrans
  have houter : 6 * a ≤ 3 * r := by linarith
  have hphase := transportPosition_smooth_coefficientDomain T Q hP hr haR houter hcarrier
  have hphaseV : ContDiffOn ℝ ∞ (transportPosition T Q) Vphase :=
    hphase.mono (fun _ hp ↦ (hDom hp).2)
  have hνD := hν.mono hDouter
  have hq : ContDiffOn ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦
      quadratic (Q.1 p.1) (T.carrierGradient Q p.1 (parameter p.2)))
      (coefficientDomain z₀ r (6 * a)) :=
    (contDiffOn_piLp 2).mpr hdet
  have hqD := hq.mono hDouter
  have hang : ContDiff ℝ ∞ (Function.uncurry angular) := angularMask_smooth ..
  have hangular : ∀ z ∉ carrierSupport z₀ (r := a'), ∀ η, angular z η = 0 :=
    fun _ hz η ↦ angularMask_zero_outside z₀ (NormedSpace.normalize ηb) ha'
      (angularWidth_spec hηb hr').1 hz η
  have hcoeff' := hcoeff
  change D.Controls s M₀ B₀ H (coefficientsOfCarrier
    (data T Q F row col Φ Y initial ha' hcell' angular FixedCutoffs.highFrequency)
    (FixedCutoffs.physical ha' 1)) at hcoeff'
  rw [coefficientsOfCarrier_data] at hcoeff'
  have hqM : cNorm D.field.carrier 1 (fun p : Euclidean n × CarrierParameter ↦
      quadratic (Q.1 p.1) (T.carrierGradient Q p.1 (parameter p.2))) ≤ ‖Lq‖ * M₀ := by
    have hbound := InverseEstimates.cNorm_postLinear_le_on
      (isCompact_closedBall D.field.center D.field.radius) 1 Lq
      (fun x hx ↦ (hcoeff'.reduced.smooth.contDiffAt
        (D.field.isOpen_region.mem_nhds (D.field.ball_subset hx))).of_le (by simp))
    exact hbound.trans (mul_le_mul_of_nonneg_left hcoeff'.reduced.low (norm_nonneg _))
  have hkernel := stronglyMeasurable_carrierKernel_of_local_primitives T Q F row col Φ Y initial
    ha' hcell' angular D.field.isOpen_region (hphase.mono hDouter).continuousOn
    hνD.continuousOn hqD.continuousOn hang.continuous hangular
    (hDsupp.trans D.field.ball_subset)
  have hamp := norm_carrierAmplitude_le_of_primitive_norms T Q F row col Φ Y initial
    ha' hcell' angular D.field (carrierSupport_compact z₀) hangular hang hDsupp hνD hqD
    hM₀ (mul_nonneg (norm_nonneg _) hM₀) hcoeff'.normal.low hqM
  have hsupport : ∀ x, d.measurement x ≠ 0 → ∀ j, |x j| ≤ 4 * a' := by
    intro x hx j
    have hx' := FixedCutoffs.physical_tsupport_four ha' 1 (subset_tsupport _ hx)
    exact (PiLp.norm_apply_le x j).trans (mem_closedBall_zero_iff.mp hx')
  obtain ⟨charts, symbols, hsymbols⟩ := exists_refined_kernel_inputs T Q F row col Φ Y initial
    hηb hr hr' ha' hrr haa har' hcell' hP haR houter hcarrier hf hInv htrans hV hLV hcJ hν hdet
  have hreg := refined_coefficients_regularity T Q F row col Φ Y initial
    hηb hr' ha' hcell' hν hdet hr hf hInv htrans hcJ
  have hΩ := symbolDomain_open T Q hηb hr hInv htrans hV hLV
  have hR : IsOpen {p : Variables n | p.2.2 ≠ 0} :=
    isOpen_compl_singleton.preimage (continuous_snd.snd)
  refine ⟨hsupport, ?_⟩
  exact hconstruct d (transportPosition T Q) (symbolInverse T Q z₀ ηb r (6 * a))
    (symbolJacobian T Q) (symbolDomain T Q z₀ ηb r (6 * a))
    (symbolInputDomain z₀ ηb r (6 * a)) (conicMaskSupport z₀ ηb r' a')
    {p | ‖p.2.2‖ = ‖t • k‖} {p | p.2.2 ≠ 0} H
    hphaseV (by rwa [← hDcar]) hΩ (ball_subset_closedBall.trans houtput)
    (symbolInverse_smooth T Q hηb hr hInv htrans hLV)
    (hrange.mono (closedBall_subset_closedBall (by linarith)) Subset.rfl)
    hgap (fun _ hp ↦ transportAveragedGradient_symbolInverse T Q hηb hr hInv htrans hp)
    hJeq hJne hJlow hH (by rwa [← hDcar]) hreg
    (symbolInverse_maps T Q hηb hr hInv htrans)
    (fun p hp hx hy ha ↦ primitive_masks_mem_conicMaskSupport hηb hr' ha' hp.2.2.1 hx hy ha)
    hR (fun p hp ↦ norm_ne_zero_iff.mp (by rw [hp]; exact norm_ne_zero_iff.mpr hk'))
    (fun p hp ↦ hpunctured ⟨hp.1, hp.2.1⟩)
    (fun x hx v _ hv ↦ hshell x hx v hv) hcoeff
    (fun _ ht p ↦ symbolDomain_smul_iff T Q ht p)
    (fun _ ht _ hp ↦ symbolInverse_smul T Q hηb hr hInv htrans hp ht)
    (fun _ ht _ hp ↦ symbolJacobian_scale_inverse T Q hηb hr hf hInv htrans hp ht)
    hupper hpunctured (scaleFrequency_mem_fixed_sphere (norm_pos_iff.mpr hk'))
    hn (4 * a') hsupport hreserve e (carrierSupport z₀ (r := a'))
    (carrierSupport_compact z₀) hangular Cmask hCmask hkernel hamp
    (closedBall 0 (4 * a')) (FixedCutoffs.closedBall_four_subset_cell hcell') rfl
    (fun _ _ ↦ rfl) (FixedCutoffs.physical ha' 2)
    (fun _ hx ↦ FixedCutoffs.physical_eq_zero_outside_four ha' 2 hx)
    (FixedCutoffs.physical ha' 2).contDiff (FixedCutoffs.physical ha' 2).hasCompactSupport
    (fun _ hx ↦ FixedCutoffs.source_one_on_measurement ha' hx)
    charts symbols (fun R hR x hx y hy ↦ (hsymbols R hR x hx y hy).1)
    (fun R hR x hx y hy ↦ (hsymbols R hR x hx y hy).2.1)
    (fun R hR x hx y hy ↦ (hsymbols R hR x hx y hy).2.2.1)
    (fun R hR x hx y hy ↦ (hsymbols R hR x hx y hy).2.2.2.1)
    (fun R hR x hx y hy ↦ (hsymbols R hR x hx y hy).2.2.2.2.1)
    (‖(adaptedSliceCoordinates T).equiv.symm.toContinuousLinearMap‖ * Cfreq₀)
    (mul_nonneg (norm_nonneg _) hCfreq₀.le)
    (fun _ hp ↦ symbolInverse_frequency_comparison T Q hηb hr hf hInv htrans hsliceGap
      (fun D hD ↦ (hdiffbound D hD).1) hp)

end JanetCartan.ContinuumRow.FlowConic
