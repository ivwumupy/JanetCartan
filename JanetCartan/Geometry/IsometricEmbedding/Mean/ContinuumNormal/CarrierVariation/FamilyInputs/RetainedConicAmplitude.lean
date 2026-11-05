module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.ComplexAmplitude
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.SupportedInputs

/-!
# The literal outer amplitude on the common comparison cone

The punctured image of the complete original masks lies in the common
conic target. Hence zero extension there equals zero extension on the
original outer symbol domain. The actual slice Jacobian equals the kernel
Jacobian at each inverse point. These exact identities keep the original
operators, measures, spectator integral, physical frequency and reflection.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic ContinuumNormalReduction TransportSymbol
open CarrierNormalRealization

/-- A buffered conic image changes neither the supported zero extension nor
its original Jacobian. This is a set-theoretic consequence of the primitive
mask support and right inverse, used below for the actual carrier amplitude
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
private theorem extendedDensity_eq_of_punctured_image_buffer {n N : ℕ}
    (d : Coefficients n N) (J Jouter : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
    (F : InputVariables n → Variables n × Euclidean 2)
    {Ω Ωouter : Set (Variables n × Euclidean 2)} {W Z : Set (InputVariables n)}
    (hΩ : Ω ⊆ Ωouter) (hmap : MapsTo (inverseCoordinates u) Ωouter W)
    (hright : ∀ p ∈ Ωouter, F (inverseCoordinates u p) = p)
    (hsupport : ∀ p ∈ W, d.measurement p.1.1 ≠ 0 → d.measurement p.1.2 ≠ 0 →
      d.angular (p.2.1, ‖p.2.2‖⁻¹ • p.2.2) ≠ 0 → p ∈ Z)
    (hbuffer : closure (F '' Z) ∩ {p | p.1.2.2 ≠ 0} ⊆ Ω)
    (hne : ∀ p ∈ Z, (F p).1.2.2 ≠ 0) (hJ : EqOn Jouter J W) :
    extendedDensity d J u Ω = extendedDensity d Jouter u Ωouter := by
  have hs := support_extendedDensity_subset d Jouter u F hmap hright
    (fun p hp hl hr ha _ ↦ hsupport p hp hl hr ha)
  funext q
  by_cases hq : q ∈ Ω
  · simp only [extendedDensity, indicator_of_mem hq, indicator_of_mem (hΩ hq)]
    simp only [inputDensity, inputWeight, hJ (hmap (hΩ hq))]
  · have hz : extendedDensity d Jouter u Ωouter q = 0 := by
      by_contra hnonzero
      obtain ⟨p, hp, rfl⟩ := hs hnonzero
      exact hq (hbuffer ⟨subset_closure ⟨p, hp, rfl⟩, hne p hp⟩)
    simp only [extendedDensity, indicator_of_notMem hq]
    exact hz.symm

/-- The actual canonical complex and reflected amplitudes on the common
comparison cone are EXACTLY their original outer-domain amplitudes. The
original unbounded conic masks are kept: their punctured image buffer and
the actual inverse equations prove the identity. The scalar and its initial
data are arbitrary and unchanged. All Lebesgue/Haar conventions, `2π`
normalization and the reflected factor four remain literal.

Producer of the geometric inputs:
`RetainedRowGeometry.exists_joint_carrier_normal_geometry_with_comparison`.
Consumers: the SAME-row operator realization and the full-amplitude
comparison for `app:ch_osc:prop:osc-normal`, Step 4'; source formulas:
`app:ch_background:eq:bg-full-complex-amplitude`, `bg-Psi`, `bg-jacobian`,
`bg-real-symbol`. -/
theorem retained_amplitudes_eq_on_common_conic_target
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {zRoot : Euclidean 3} {ηb : Euclidean (n - 1)} {r a r' a' : ℝ}
    (hηb : ηb ≠ 0) (hr : 0 < r) (hr' : 0 < r') (ha' : 0 < a')
    (hrr : r' ≤ r) (haa : a' ≤ a) (har' : a' ≤ r') (hcell' : 4 * a' < 1 / 2)
    {b cJ : ℝ} {V L : Set (ℝ × Euclidean (n - 1))}
    {G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1))}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
      (physicalParameterSet zRoot (6 * a) ×ˢ dataSet zRoot ηb (3 * r)))
    (hInv : BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet zRoot (6 * a))
      (dataBox zRoot ηb r) (dataSet zRoot ηb (2 * r)) (dataBox zRoot ηb (2 * r)) V L b cJ G)
    (htrans : ∀ p ∈ physicalParameterSet zRoot (6 * a),
      ∀ u ∈ supportedCone zRoot (NormedSpace.normalize ηb) r (angularWidth ηb r),
        ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖)
    {Ω : Set (Variables n × Euclidean 2)}
    (hΩ : Ω ⊆ symbolDomain T Q zRoot ηb r (6 * a))
    (hbuffer : closure (augmentedTransportGradient (transportPosition T Q) ''
      conicMaskSupport zRoot ηb r' a') ∩ {q | q.1.2.2 ≠ 0} ⊆ Ω)
    (S : Set (Euclidean 2)) :
    let d := TransportKernel.coefficientsOfCarrier
      (data T Q F row col Φ Y initial ha' hcell'
        (angularMask zRoot (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1)
        FixedCutoffs.highFrequency) (FixedCutoffs.physical ha' 1)
    let u := symbolInverse T Q zRoot ηb r (6 * a)
    let J := transportAbsoluteJacobian (adaptedSliceCoordinates T) (transportPosition T Q)
    extendedDensity d J u Ω =
      extendedDensity d (symbolJacobian T Q) u (symbolDomain T Q zRoot ηb r (6 * a)) ∧
    fullComplexMatrixAmplitude d J u Ω S =
      fullComplexMatrixAmplitude d (symbolJacobian T Q) u (symbolDomain T Q zRoot ηb r (6 * a)) S ∧
    fullReflectedMatrixAmplitude d J u Ω S =
      fullReflectedMatrixAmplitude d (symbolJacobian T Q) u (symbolDomain T Q zRoot ηb r (6 * a)) S := by
  dsimp only
  let d := TransportKernel.coefficientsOfCarrier
    (data T Q F row col Φ Y initial ha' hcell'
      (angularMask zRoot (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1)
      FixedCutoffs.highFrequency) (FixedCutoffs.physical ha' 1)
  let u := symbolInverse T Q zRoot ηb r (6 * a)
  let J := transportAbsoluteJacobian (adaptedSliceCoordinates T) (transportPosition T Q)
  have hmask : conicMaskSupport zRoot ηb r' a' ⊆ symbolInputDomain zRoot ηb r (6 * a) :=
    (conicMaskSupport_subset hηb hr' ha' har').trans
      (symbolInputDomain_mono zRoot ηb hrr (mul_le_mul_of_nonneg_left haa (by norm_num)))
  have he := extendedDensity_eq_of_punctured_image_buffer d J (symbolJacobian T Q) u
    (augmentedTransportGradient (transportPosition T Q)) hΩ
    (symbolInverse_maps T Q hηb hr hInv htrans)
    (fun p hp ↦ augmentedTransportGradient_symbolInverse T Q hηb hr hInv htrans hp)
    (fun p hp hx hy hang ↦ primitive_masks_mem_conicMaskSupport hηb hr' ha' hp.2.2.1 hx hy hang)
    hbuffer (fun p hp ↦ transportGradient_ne_zero T Q hηb hr htrans (hmask hp))
    (symbolJacobian_eq_actual T Q hηb hr hf)
  have hamp : amplitude d J u Ω S =
      amplitude d (symbolJacobian T Q) u (symbolDomain T Q zRoot ηb r (6 * a)) S := by
    funext p
    simp only [amplitude, he]
  have hc : fullComplexMatrixAmplitude d J u Ω S =
      fullComplexMatrixAmplitude d (symbolJacobian T Q) u (symbolDomain T Q zRoot ηb r (6 * a)) S := by
    funext ξ z i j
    simp only [fullComplexMatrixAmplitude, hamp]
  refine ⟨he, hc, ?_⟩
  funext ξ z
  rw [fullReflectedMatrixAmplitude_eq_complex_add_reflection,
    fullReflectedMatrixAmplitude_eq_complex_add_reflection, hc]

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
