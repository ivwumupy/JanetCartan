module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.NormalInputs.Basic

/-!
# Qualitative geometry of the restricted canonical adjoint chart

Every hypothesis below is a retained output of
`CanonicalConic.exists_actual_refined_supported_geometry`. In particular the
inverse is the published outer inverse restricted to the actual smaller image.
No normal estimate, inverse derivative estimate, or amplitude is assumed.

Consumer: the geometric fields of `PrimitiveRegularity` and the change of
variables in `exists_scalarTransportCarrierAdjoint_periodic_raw_bound`
(`app:ch_background:eq:bg-Psi`, `bg-jacobian`, `bg-full-complex-amplitude`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint.Canonical.NormalInputs
open ContinuumRow DerivativeKernels ModifiedNormalSymbol PhaseExtension
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open CanonicalConic ContinuumNormalReduction.TransportSymbol

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)} {r aOuter aPhase : ℝ}
    (hηb : ηb ≠ 0) (hr : 0 < r)

local notation "g" => normalChart T Q z₀ ηb r aOuter aPhase

variable
    (hf : ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
      (physicalParameterSet z₀ aOuter ×ˢ dataSet z₀ ηb (3 * r)))

include hηb hr hf in
/-- The actual restricted forward map is smooth jointly in all variables
(`app:ch_background:eq:bg-Psi`). -/
theorem normalChart_push_contDiffOn : ContDiffOn ℝ ∞ (g).push (g).inputDomain := by
  have hh : ContDiffOn ℝ ∞ (fun p : JointVariables n ↦
      transportAveragedGradient (CanonicalCarrier.transportPosition T Q)
        (jointInputCoordinates T p)) (g).inputDomain :=
    (transportAveragedGradient_smooth_on_symbolInputDomain T Q hηb hr hf).comp
    (jointInputCoordinates T).contDiff.contDiffOn (fun _ hp ↦ hp.1)
  exact (contDiffOn_fst.fst.prodMk (contDiffOn_fst.snd.fst.prodMk hh)).prodMk contDiffOn_snd

include hηb hr hf in
/-- The derivative used for substitution is the literal derivative of the
retained forward map, throughout the restricted domain (`bg-jacobian`). -/
theorem normalChart_hasFDerivAt (x y : Euclidean n) (v : Euclidean 2)
    {w : Euclidean n} (hw : w ∈ (g).domain x y v) :
    HasFDerivAt ((g).forward x y v) ((g).jacobian x y v w) w :=
  kernelForward_hasFDerivAt T Q hηb hr hf x y v hw.1

include hηb hr hf in
/-- Exact derivative equality for `PrimitiveJetGeometry` (`bg-jacobian`). -/
theorem normalChart_jacobian_is_fderiv {p : JointVariables n} (hp : p ∈ (g).inputDomain) :
    (g).jacobian p.1.1 p.1.2.1 p.2 p.1.2.2 =
      fderiv ℝ ((g).forward p.1.1 p.1.2.1 p.2) p.1.2.2 :=
  (normalChart_hasFDerivAt T Q hηb hr hf _ _ _ hp).fderiv.symm

include hηb hr hf in
/-- The full Jacobian field is smooth; this follows by restricting the
joint forward differential, rather than assuming Jacobian regularity
(`app:ch_background:eq:bg-jacobian`). -/
theorem normalChart_jacobian_contDiffOn :
    ContDiffOn ℝ ∞ (fun p : JointVariables n ↦
      (g).jacobian p.1.1 p.1.2.1 p.2 p.1.2.2) (g).inputDomain := by
  have hs := transportAveragedGradient_smooth_on_symbolInputDomain T Q hηb hr hf
  have hj : ContDiffOn ℝ ∞ (symbolDifferential T Q) (symbolInputDomain z₀ ηb r aOuter) := by
    intro p hp
    exact ((transportDifferentialRestriction (adaptedSliceCoordinates T)).contDiff.contDiffAt.comp p
      ((hs.contDiffAt ((symbolInputDomain_open z₀ ηb r aOuter).mem_nhds hp)).fderiv_right
        (m := ∞) (by simp))).contDiffWithinAt
  exact hj.comp (jointInputCoordinates T).contDiff.contDiffOn (fun _ hp ↦ hp.1)

variable {b cJ : ℝ} {V L : Set (ℝ × Euclidean (n - 1))}
    {G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1))}
    (hInv : BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ aOuter)
      (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r)) V L b cJ G)
    (htrans : ∀ p ∈ physicalParameterSet z₀ aOuter,
      ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r),
        ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖)

include hηb hr hInv htrans in
/-- The restricted map keeps the original inverse (`app:ch_background:eq:bg-Psi`). -/
theorem normalChart_inverse_forward (x y : Euclidean n) (v : Euclidean 2)
    {w : Euclidean n} (hw : w ∈ (g).domain x y v) :
    (g).inverse x y v ((g).forward x y v w) = w :=
  kernelInverse_forward T Q hηb hr hInv htrans x y v hw.1

include hηb hr hInv htrans in
/-- Injectivity survives restriction to the phase-agreement domain (`bg-Psi`). -/
theorem normalChart_forward_injective (x y : Euclidean n) (v : Euclidean 2) :
    InjOn ((g).forward x y v) ((g).domain x y v) :=
  (kernelForward_injective T Q hηb hr hInv htrans x y v).mono (fun _ hp ↦ hp.1)

include hηb hr hInv htrans in
/-- The unchanged inverse maps the ACTUAL restricted image back into the
restricted domain, including its phase buffer (`bg-full-complex-amplitude`). -/
theorem normalChart_inverse_mem : MapsTo (g).pull (g).outputDomain (g).inputDomain := by
  rintro ⟨⟨x, y, k⟩, v⟩ hp
  change k ∈ (g).forward x y v '' (g).domain x y v at hp
  rcases hp with ⟨w, hw, rfl⟩
  change (g).inverse x y v ((g).forward x y v w) ∈ (g).domain x y v
  rw [normalChart_inverse_forward T Q hηb hr hInv htrans x y v hw]
  exact hw

include hηb hr hInv htrans in
/-- Exact right inversion on the actual smaller image (`bg-Psi`). -/
theorem normalChart_push_pull {p : JointVariables n} (hp : p ∈ (g).outputDomain) :
    (g).push ((g).pull p) = p := by
  rcases p with ⟨⟨x, y, k⟩, v⟩
  change k ∈ (g).forward x y v '' (g).domain x y v at hp
  rcases hp with ⟨w, hw, rfl⟩
  change ((x, y, (g).forward x y v ((g).inverse x y v ((g).forward x y v w))), v) = _
  rw [normalChart_inverse_forward T Q hηb hr hInv htrans x y v hw]

include hηb hr hInv htrans in
/-- The smaller output is precisely the outer output intersected with the
inverse image of the fixed open phase buffer (`bg-full-complex-amplitude`). -/
theorem normalChart_outputDomain_eq :
    (g).outputDomain = symbolDomain T Q z₀ ηb r aOuter ∩
      inverseCoordinates (symbolInverse T Q z₀ ηb r aOuter) ⁻¹'
        phaseAgreementDomain z₀ aPhase := by
  ext ⟨⟨x, y, k⟩, v⟩
  change k ∈ (g).forward x y v '' (g).domain x y v ↔ _
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨(kernel_image_iff T Q x y v _).mp ⟨w, hw.1, rfl⟩, ?_⟩
    change inverseCoordinates (symbolInverse T Q z₀ ηb r aOuter)
      (augmentedTransportGradient (CanonicalCarrier.transportPosition T Q)
        (kernelInput T x y v w)) ∈ phaseAgreementDomain z₀ aPhase
    rw [symbolInverse_augmentedTransportGradient T Q hηb hr hInv htrans hw.1]
    exact hw.2
  · rintro ⟨hk, hphase⟩
    obtain ⟨w, hw, rfl⟩ := (kernel_image_iff T Q x y v k).mpr hk
    refine ⟨w, ⟨hw, ?_⟩, rfl⟩
    change inverseCoordinates (symbolInverse T Q z₀ ηb r aOuter)
      (augmentedTransportGradient (CanonicalCarrier.transportPosition T Q)
        (kernelInput T x y v w)) ∈ phaseAgreementDomain z₀ aPhase at hphase
    rwa [symbolInverse_augmentedTransportGradient T Q hηb hr hInv htrans hw] at hphase

include hηb hr hInv htrans in
/-- The restricted image remains inside the original open conic image
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem normalChart_outputDomain_subset :
    (g).outputDomain ⊆ symbolDomain T Q z₀ ηb r aOuter := by
  rw [normalChart_outputDomain_eq T Q hηb hr hInv htrans]
  exact inter_subset_left

include hηb hr hInv htrans in
/-- Smoothness of the SAME inverse on the actual smaller image
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem normalChart_inverse_contDiffOn (hLV : L ⊆ V) :
    ContDiffOn ℝ ∞ (fun p : JointVariables n ↦
      (g).inverse p.1.1 p.1.2.1 p.2 p.1.2.2) (g).outputDomain :=
  ((adaptedSliceCoordinates T).equiv.symm.contDiff.comp_contDiffOn
    (symbolInverse_smooth T Q hηb hr hInv htrans hLV)).mono
      (normalChart_outputDomain_subset T Q hηb hr hInv htrans)

include hηb hr hInv htrans in
/-- Openness is proved for the actual restricted output, not just the outer
output chart (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem normalChart_outputDomain_open (hV : IsOpen V) (hLV : L ⊆ V) :
    IsOpen (g).outputDomain := by
  have hO := symbolDomain_open T Q hηb hr hInv htrans hV hLV
  have hu := (symbolInverse_smooth T Q hηb hr hInv htrans hLV).continuousOn
  have hi : ContinuousOn (inverseCoordinates (symbolInverse T Q z₀ ηb r aOuter))
      (symbolDomain T Q z₀ ηb r aOuter) :=
    (continuousOn_fst.fst.prodMk continuousOn_fst.snd.fst).prodMk
      ((hu.fst.prodMk continuousOn_snd).prodMk hu.snd)
  rw [normalChart_outputDomain_eq T Q hηb hr hInv htrans]
  exact hi.isOpen_inter_preimage hO (phaseAgreementDomain_open z₀ aPhase)

include hηb hr hf hInv htrans in
/-- Nonvanishing of the actual determinant on the whole restricted domain
comes from the published annular gap and homogeneity (`bg-jacobian`). -/
theorem normalChart_determinant_ne_zero (hcJ : 0 < cJ)
    {p : JointVariables n} (hp : p ∈ (g).inputDomain) :
    ((g).jacobian p.1.1 p.1.2.1 p.2 p.1.2.2).det ≠ 0 := by
  have he := symbolJacobian_eq_actual T Q hηb hr hf hp.1
  have hpos := transportAbsoluteJacobian_pos T Q hηb hr hf hInv htrans hcJ hp.1
  rw [← he] at hpos
  exact abs_pos.mp hpos

include hηb hr hf hInv htrans in
/-- All geometric fields of the endpoint's `PrimitiveRegularity` are proved.
Only global smoothness of the ORIGINAL amplitude remains an input, produced
by the canonical amplitude-profile construction (`bg-full-complex-amplitude`). -/
theorem normalChart_primitiveRegularity (hV : IsOpen V) (hLV : L ⊆ V) (hcJ : 0 < cJ)
    (amplitude : AdjointAmplitude n)
    (ha : ContDiff ℝ ∞ (fun p : AmplitudeVariables n ↦ amplitude p.1 p.2.1 p.2.2)) :
    ModifiedNormalSymbol.PrimitiveRegularity g amplitude (fun _ ↦ 1) where
  coordinates := (adaptedSliceCoordinates T).equiv.contDiff
  amplitude := ha
  regularizer := contDiff_const
  jacobian := normalChart_jacobian_contDiffOn T Q hηb hr hf
  determinant_ne_zero := fun _ hp ↦ normalChart_determinant_ne_zero T Q hηb hr hf hInv htrans hcJ hp
  output_open := normalChart_outputDomain_open T Q hηb hr hInv htrans hV hLV
  inverse := normalChart_inverse_contDiffOn T Q hηb hr hInv htrans hLV
  inverse_mem := normalChart_inverse_mem T Q hηb hr hInv htrans
  right_inverse := fun _ hp ↦ normalChart_push_pull T Q hηb hr hInv htrans hp

end JanetCartan.ContinuumAdjoint.Canonical.NormalInputs
