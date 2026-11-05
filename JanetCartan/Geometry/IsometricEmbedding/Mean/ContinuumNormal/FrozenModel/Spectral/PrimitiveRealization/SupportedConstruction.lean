module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.PrimitiveRealization.Geometry
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.PrimitiveRealization.Kernel
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.CarrierNormalRealization.SupportedShell

/-!
# The literal frozen carrier from supported primitive inputs

The geometric refinement and all coefficient and kernel estimates are instantiated
for the actual normalized carrier at zero scale. Only the outer local conic inputs
produced by `exists_frozen_conic_inputs` remain explicit. The additional frame
threshold is constructed before the frame, and the finite analytic budgets are
proved for each fixed seed. No operator or normal identity is assumed.

Consumer: `canonicalFrozenCarrierExtension_adjoint_norm_sq_eq_energy_unit`.
Sources: `new:lem:scaling`, `app:ch_background:prop:bg-frame`, and
`app:ch_background:eq:bg-full-complex-amplitude`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.FrozenModel
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic CarrierNormalRealization
open ContinuumNormalReduction TransportSymbol TransportKernel
open Pseudodifferential AmplitudeBound PeriodicLocalL2

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- Construct the smaller original masks, their canonical inverse, and the
uncut frozen carrier with its literal test action, adjoint and global reflected
normal. All finite coefficient and kernel budgets are discharged for the seed.
The outer inverse is retained in the displayed normal; `InverseEnlargement`
identifies it with the smaller canonical amplitude. The small incidence
representative required here is supplied by `exists_small_incidence_representative`.
The only analytic premises are the exact outer conic outputs of
`exists_frozen_conic_inputs` and the explicitly produced frame threshold
(`new:lem:scaling`, `app:ch_background:prop:bg-frame`). -/
theorem exists_frozen_supported_carrier_unit
    {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    {k : Euclidean n} (hk : k ≠ 0) (hksmall : ‖k‖ ≤ 1 / 2)
    (hinc : incidence k (P.toFun z₀) = 0)
    (hd : fderiv ℝ (fun z ↦ incidence k (P.toFun z)) z₀
      (EuclideanSpace.single 0 1) ≠ 0)
    {r a : ℝ} (hr : 0 < r) (ha : 0 < a) (har : 6 * a ≤ 3 * r)
    (hcarrier : closedBall (spectatorCenter z₀) (3 * r) ×ˢ closedBall (z₀ 0) (3 * r) ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2)) :
    let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
    let hηb := FrozenIncidence.tangential_direction_ne_zero T hP hz₀ hk hinc
    let G' := FrozenIncidence.referenceEquiv T hP hz₀ hinc hd
    ∃ (r' a' : ℝ) (hr' : 0 < r') (ha' : 0 < a') (hcell : 4 * a' < 1 / 2),
      r' ≤ r ∧ a' ≤ a ∧ 6 * a' ≤ r' ∧
    ∃ cJ' > (0 : ℝ), ∃ b' > (0 : ℝ), ∃ V' L' : Set (ℝ × Euclidean (n - 1)),
      IsOpen V' ∧ IsCompact (closure V') ∧ IsCompact L' ∧ L' ⊆ V' ∧
    ∃ δ > (0 : ℝ), ∀ Q,
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress n) < δ →
      ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
        (physicalParameterSet z₀ (6 * a) ×ˢ dataSet z₀ ηb (3 * r)) →
      ∀ {b cJ : ℝ} {V L : Set (ℝ × Euclidean (n - 1))}
        {G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1))},
      BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ (6 * a))
        (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r)) V L b cJ G →
      (∀ p ∈ physicalParameterSet z₀ (6 * a),
        ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r),
          ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖) →
      (∀ p ∈ physicalParameterSet z₀ (6 * a), ∀ u ∈ dataBox z₀ ηb (2 * r),
        ‖G.symm.toContinuousLinearMap.comp (fderiv ℝ (adaptedTransportChart T Q p) u) -
          ContinuousLinearMap.id ℝ (ℝ × Euclidean (n - 1))‖ ≤ 1 / 2) →
      IsOpen V → L ⊆ V → 0 < cJ →
      ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
        (physicalParameterSet z₀ (6 * a') ×ˢ dataSet z₀ ηb (3 * r')) ∧
      (∀ p ∈ physicalParameterSet z₀ (6 * a'), ∀ u ∈ dataBox z₀ ηb (2 * r'),
        ‖G'.symm.toContinuousLinearMap.comp (fderiv ℝ (adaptedTransportChart T Q p) u) -
          ContinuousLinearMap.id ℝ (ℝ × Euclidean (n - 1))‖ ≤ 1 / 2) ∧
      BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ (6 * a'))
        (dataBox z₀ ηb r') (dataSet z₀ ηb (2 * r')) (dataBox z₀ ηb (2 * r')) V' L' b' cJ' G' ∧
      (∀ p ∈ physicalParameterSet z₀ (6 * a'),
        ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r' (angularWidth ηb r'),
          ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r' / 4) * ‖u.2‖) ∧
      ∀ (F : Euclidean n → Euclidean N) (row col : Fin n)
        (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
        (s : ℕ) (hs : 2 * (n + 1) ≤ s),
      let e := normalizedCarrierData T Q F row col Φ Y (fun _ ↦ 1) ha' hcell
        (angularMask z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1)
        FixedCutoffs.highFrequency 0
      let d := coefficientsOfCarrier e (FixedCutoffs.physical ha' 1)
      let J := transportAbsoluteJacobian (adaptedSliceCoordinates T) (normalizedTransportPosition T Q 0)
      let u := frozenSymbolInverse T Q z₀ ηb r (6 * a)
      let Ω := frozenSymbolDomain T Q z₀ ηb r (6 * a)
      let S := closedBall (spectatorCenter z₀) (a' / 2)
      ∃ hn : 0 < n,
      ∃ hsupport : ∀ x, d.measurement x ≠ 0 → ∀ j, |x j| ≤ 4 * a',
      ∃ B > (0 : ℝ),
      ∃ (hb : ContDiff ℝ ∞ (Function.uncurry (fullReflectedMatrixAmplitude d J u Ω S)))
        (hA : ∀ i j, HasAmplitudeDerivativeBound
          (fun ξ z ↦ fullReflectedMatrixAmplitude d J u Ω S ξ z i j) s B),
      ∃ Vcarrier : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
        (∀ v : carrierInitialTestSpace n,
          Vcarrier (carrierInitialTestToLp v) =ᵐ[volume] carrierTestIntegral e v.val) ∧
        (∀ f : CarrierL2 n, ∀ᵐ x ∂volume, x ∉ e.outputChart → Vcarrier f x = 0) ∧
        (∀ W : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
          (∀ v : carrierInitialTestSpace n,
            W (carrierInitialTestToLp v) =ᵐ[volume] carrierTestIntegral e v.val) → W = Vcarrier) ∧
        (∀ w : ComplexOutputL2 n,
          MemLp (carrierAdjointIntegral e w) 2 (carrierMeasure n) ∧
          Vcarrier.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral e w) ∧
        (realQuadratureChannel Vcarrier).comp (realQuadratureChannel Vcarrier).adjoint =
          realOutputCompression (transferOperator
            (vectorTwoPositionL2Operator hn (4 * a') (fullReflectedMatrixAmplitude d J u Ω S) hb
              (fullReflectedMatrixAmplitude_supportedInCenteredBox d J u Ω S (4 * a') hsupport)
              B (fun i j ξ is his ↦ hA i j ξ is (his.trans hs)))) := by
  classical
  let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
  have hηb : ηb ≠ 0 := FrozenIncidence.tangential_direction_ne_zero T hP hz₀ hk hinc
  obtain ⟨ρ, hρ, _, τ, hτ, _, hballout, W, K, Vphase, Lphase, I, D, ε,
    hW, hK, hball, hWK, hKdom, hVphase, hLphase, hLVphase, hI, _, hIT, hsegT, hseg,
    _, _, hDom, _, hfoot, _, hε, hη, hcontrols, r', hr', hrr, _, a', ha', haa,
    har', _, _, hcell, _, cJ', hcJ', b', hb', V', L', hV', hVc', hLc', hLV',
    δ, hδ, hgeometry⟩ := exists_frozen_primitive_buffers T hP hz₀ hk hinc hd hr ha har hcarrier
  refine ⟨r', a', hr', ha', hcell, hrr, haa, har', cJ', hcJ', b', hb',
    V', L', hV', hVc', hLc', hLV', δ, hδ, ?_⟩
  intro Q hQ hf b cJ V L G hInv htrans hslice hV hLV hcJ
  obtain ⟨houtput, hrange, hgap, _, hf', hgap', hInv', htrans', hshell, hpunctured⟩ :=
    hgeometry Q hQ hf hInv htrans
  refine ⟨hf', hgap', hInv', htrans', ?_⟩
  intro F row col Φ Y s hs
  let e := normalizedCarrierData T Q F row col Φ Y (fun _ ↦ 1) ha' hcell
    (angularMask z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1)
    FixedCutoffs.highFrequency 0
  let d := coefficientsOfCarrier e (FixedCutoffs.physical ha' 1)
  let p₀ := augmentedInputCenter T (z₀ := z₀) (k := k)
  let q₀ := frozenAugmentedChart T p₀
  obtain ⟨M₀, hM₀, B₀, hB₀, hcoeff⟩ := hcontrols Q F row col Φ Y hr' ha' hcell
  obtain ⟨M, hM, B, hB, hphase, hlow, hhigh⟩ :=
    exists_frozen_geometry_norms T Q hP hr har hcarrier hDom
  obtain ⟨δJ, hδJ, hjac⟩ := exists_frozen_primitive_jacobian_lower_bound T hP
    hηb hr (by positivity : 0 < 6 * a) har hcarrier hcJ hε hball (hWK.trans hKdom) hη
  obtain ⟨hJne, hJlow⟩ := hjac Q hf hInv htrans
  obtain ⟨Cnorm, _, Cpdo, hCpdo, hconstruct⟩ :=
    exists_carrierL2Extension_supported_globalNormal_of_primitiveNorms (N := N)
      (adaptedSliceCoordinates T) p₀ q₀ hρ hτ hW hball hK hWK
      (O := ball q₀ (2 * τ)) isOpen_ball hballout
      hVphase hLphase hLVphase hI hIT hsegT hseg
      (augmentedReferenceEquiv T hP hz₀ hinc hd)
      hM hM₀ (hB₀ s) hδJ hε (zero_le_one.trans (hB s)) hη D hfoot
      (Cupper := 2) (ℓ := ‖k‖) (by norm_num) (norm_pos_iff.mpr hk)
      (by linarith) (by linarith)
      (S := closedBall (spectatorCenter z₀) (a' / 2)) (isCompact_closedBall _ _)
      s (by omega) FixedCutoffs.highFrequency_smooth
      (fun _ ht ↦ FixedCutoffs.highFrequency_zero ht)
      (fun _ ht ↦ FixedCutoffs.highFrequency_one ht)
      FixedCutoffs.radialRegularization_smooth FixedCutoffs.radialRegularization_compact
      (fun _ ht ↦ FixedCutoffs.radialRegularization_one ht)
  have hn : 0 < n := by
    by_contra h
    have hn0 : n = 0 := by omega
    apply hk
    ext i
    exact Fin.elim0 (hn0 ▸ i)
  have hsupport : ∀ x, d.measurement x ≠ 0 → ∀ j, |x j| ≤ 4 * a' := by
    intro x hx j
    have hx' := FixedCutoffs.physical_tsupport_four ha' 1 (subset_tsupport _ hx)
    exact (PiLp.norm_apply_le x j).trans (mem_closedBall_zero_iff.mp hx')
  have har'' : a' ≤ r' := by linarith
  obtain ⟨hkernel, Cmask, hCmask, hamp⟩ := frozenRefinedCarrier_finite_kernel_inputs
    T Q F row col Φ Y hP z₀ hηb hr hr' ha' haa hcell har hcarrier
  obtain ⟨charts, symbols, hsymbols⟩ := exists_frozen_refined_kernel_inputs
    T Q F row col Φ Y hηb hr hr' ha' hrr haa har'' hcell
      hP har hcarrier hf hInv htrans hV hLV hcJ
  have hreg := frozenMeasured_refined_primitiveRegularity T Q hP hηb hr ha har
    hcarrier hf hInv htrans hcJ hr' ha' hcell F row col Φ Y
  have hΩ := frozenSymbolDomain_open T Q hηb hr hInv htrans hV hLV
  have hR : IsOpen {p : Variables n | p.2.2 ≠ 0} :=
    isOpen_compl_singleton.preimage continuous_snd.snd
  have hupdate : { d with high := FixedCutoffs.highFrequency } = d := rfl
  have hreal := hconstruct d (normalizedTransportPosition T Q 0)
    (frozenSymbolInverse T Q z₀ ηb r (6 * a))
    (transportAbsoluteJacobian (adaptedSliceCoordinates T) (normalizedTransportPosition T Q 0))
    (frozenSymbolDomain T Q z₀ ηb r (6 * a))
    (frozenInputDomain z₀ ηb r (6 * a)) (conicMaskSupport z₀ ηb r' a')
    {p | ‖p.2.2‖ = ‖k‖} {p | p.2.2 ≠ 0} 1
    hphase hlow hΩ houtput (frozenSymbolInverse_smooth T Q hηb hr hInv htrans hLV)
    hrange hgap (fun _ hp ↦ frozenTransportGradient_inverse T Q hP hηb hr har hcarrier hInv htrans hp)
    (fun _ _ ↦ rfl) hJne hJlow le_rfl (hhigh s 1 le_rfl) hreg
    (frozenSymbolInverse_maps T Q hηb hr hInv htrans)
    (fun p hp hx hy hang ↦ primitive_masks_mem_conicMaskSupport hηb hr' ha' hp.2.2.1 hx hy hang)
    hR (fun p hp ↦ norm_ne_zero_iff.mp (by rw [hp]; exact norm_ne_zero_iff.mpr hk))
    (fun p hp ↦ hpunctured ⟨hp.1, hp.2.1⟩)
    (fun x hx v _ hv ↦ hshell x hx v hv) (hcoeff s 1 le_rfl)
    (fun _ ht p ↦ frozenSymbolDomain_smul_iff T Q z₀ ηb r (6 * a) ht p)
    (fun _ ht _ hp ↦ frozenSymbolInverse_smul T Q hηb hr hInv htrans hp ht)
    (fun _ ht _ hp ↦ frozenJacobian_scaling T Q hP hηb hr har hcarrier hf hInv htrans
      (frozenSymbolInverse_maps T Q hηb hr hInv htrans hp) ht)
    (fun _ hp ↦ frozenSymbolInverse_norm_le_two T Q hηb hr hInv htrans hp)
    hpunctured (scaleFrequency_mem_fixed_sphere (norm_pos_iff.mpr hk))
    hn (4 * a') hsupport hs e (carrierSupport z₀ (r := a'))
    (carrierSupport_compact z₀)
    (fun z hz η ↦ angularMask_zero_outside z₀ (NormedSpace.normalize ηb) ha'
      (angularWidth_spec hηb hr').1 hz η)
    Cmask hCmask hkernel hamp
    (closedBall 0 (4 * a')) (FixedCutoffs.closedBall_four_subset_cell hcell) rfl
    (fun _ _ ↦ rfl) (FixedCutoffs.physical ha' 2)
    (fun _ hx ↦ FixedCutoffs.physical_eq_zero_outside_four ha' 2 hx)
    (FixedCutoffs.physical ha' 2).contDiff (FixedCutoffs.physical ha' 2).hasCompactSupport
    (fun _ hx ↦ FixedCutoffs.source_one_on_measurement ha' hx)
    charts symbols (fun R hR x hx y hy ↦ by rw [hupdate]; exact (hsymbols R hR x hx y hy).1)
    (fun R hR x hx y hy ↦ (hsymbols R hR x hx y hy).2.1)
    (fun R hR x hx y hy ↦ (hsymbols R hR x hx y hy).2.2.1)
    (fun R hR x hx y hy ↦ (hsymbols R hR x hx y hy).2.2.2.1)
    (fun R hR x hx y hy ↦ (hsymbols R hR x hx y hy).2.2.2.2.1)
    (frozenFrequencyBound T G) (frozenFrequencyBound_pos T G).le
    (fun _ hp ↦ frozenInverse_frequency_comparison T G Q hηb hr hf hInv htrans hslice hp)
  simp only [hupdate, mul_one] at hreal
  obtain ⟨_, _, _, _, _, _, _, hb, hA, Vcarrier, _, _, htest, hsupp, hunique,
    hadjoint, _, hnormal⟩ := hreal
  exact ⟨hn, hsupport, Cpdo, hCpdo, hb, hA, Vcarrier, htest, hsupp, hunique, hadjoint, hnormal⟩

end JanetCartan.ContinuumNormal.FrozenModel
