module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.NormalInputs.Jets.Rescaling

/-!
# Exact normalization identities for the canonical jets

The matrix normalization follows by differentiating the actual homogeneous
forward map. The inverse normalization follows from the genuine conic inverse.
These are identities on the working domains, so they can be differentiated
locally without any assumption about an unrestricted output shell.

Consumer: the inverse and Jacobian jet bounds in `PrimitiveJetGeometry`
(`app:ch_background:eq:bg-Psi`, `bg-jacobian`, `bg-full-complex-amplitude`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint.Canonical.NormalInputs
open ContinuumRow DerivativeKernels ModifiedNormalSymbol
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open CanonicalConic ContinuumNormalReduction.TransportSymbol

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)} {r aOuter aPhase : ℝ}

/-- The incidence-column normalization is the covector dilation divided by
its scale, on the original integration slice (`bg-jacobian`). -/
theorem normalColumnDilation_insertion {t : ℝ} (ht : t ≠ 0) (w : Euclidean n) :
    transportSliceInsertion (adaptedSliceCoordinates T) (normalColumnDilation T t w) =
      t⁻¹ • inputCovectorDilation t ht
        (transportSliceInsertion (adaptedSliceCoordinates T) w) := by
  ext <;> simp [transportSliceInsertion, normalColumnDilation, inputCovectorDilation,
    scaleInput, smul_smul, ht]

variable (hηb : ηb ≠ 0) (hr : 0 < r)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
      (physicalParameterSet z₀ aOuter ×ˢ dataSet z₀ ηb (3 * r)))

include hηb hr hf in
/-- Exact matrix normalization of the ORIGINAL Jacobian. This is stronger
than its determinant law and is proved from the forward homogeneity, not
assumed as a Jacobian-jet premise (`app:ch_background:eq:bg-jacobian`). -/
theorem symbolDifferential_comp_normalColumnDilation
    {p : InputVariables n} (hp : p ∈ symbolInputDomain z₀ ηb r aOuter)
    {t : ℝ} (ht : 0 < t) :
    (symbolDifferential T Q (scaleInput t p)).comp (normalColumnDilation T t) =
      symbolDifferential T Q p := by
  let f := transportAveragedGradient (CanonicalCarrier.transportPosition T Q)
  let D := inputCovectorDilation (n := n) t ht.ne'
  have htp : scaleInput t p ∈ symbolInputDomain z₀ ηb r aOuter :=
    ⟨hp.1, radialScale_mem_supportedCone hp.2 ht⟩
  have hs := transportAveragedGradient_smooth_on_symbolInputDomain T Q hηb hr hf
  have hd : DifferentiableAt ℝ f p :=
    (hs.contDiffAt ((symbolInputDomain_open z₀ ηb r aOuter).mem_nhds hp)).differentiableAt
      (by simp)
  have hdt : DifferentiableAt ℝ f (D p) :=
    (hs.contDiffAt ((symbolInputDomain_open z₀ ηb r aOuter).mem_nhds htp)).differentiableAt
      (by simp)
  have he : (fderiv ℝ f (D p)).comp D.toContinuousLinearMap = t • fderiv ℝ f p := by
    apply (hdt.hasFDerivAt.comp p D.hasFDerivAt).unique
    exact (hd.hasFDerivAt.const_smul t).congr_of_eventuallyEq
      (Eventually.of_forall (fun q ↦ transportAveragedGradient_smul _ t q))
  ext1 w
  change fderiv ℝ f (D p)
      (transportSliceInsertion (adaptedSliceCoordinates T) (normalColumnDilation T t w)) =
    fderiv ℝ f p (transportSliceInsertion (adaptedSliceCoordinates T) w)
  rw [normalColumnDilation_insertion T ht.ne', map_smul]
  have hw := congrArg (fun A : InputVariables n →L[ℝ] Euclidean n ↦
    A (transportSliceInsertion (adaptedSliceCoordinates T) w)) he
  change fderiv ℝ f (D p)
    (D (transportSliceInsertion (adaptedSliceCoordinates T) w)) =
      t • fderiv ℝ f p (transportSliceInsertion (adaptedSliceCoordinates T) w) at hw
  rw [hw, inv_smul_smul₀ ht.ne']

include hηb hr hf in
/-- After normalizing the incidence column, the original-Jacobian field
is independent of the frozen frequency scale on the whole restricted domain
(`app:ch_background:eq:bg-jacobian`). -/
theorem normalJetRescaling_normalizedJacobian_eq
    {p : JointVariables n} (hp : p ∈ (normalChart T Q z₀ ηb r aOuter aPhase).inputDomain)
    {t : ℝ} (ht : 0 < t) :
    (normalJetRescaling T Q z₀ ηb r aOuter aPhase).normalizedJacobian t p =
      symbolDifferential T Q (jointInputCoordinates T p) := by
  change (symbolDifferential T Q
    (jointInputCoordinates T (normalInputDilation T t p))).comp (normalColumnDilation T t) = _
  rw [normalInputDilation_apply T ht.ne']
  simp only [scaleJointInput, ContinuousLinearEquiv.apply_symm_apply]
  exact symbolDifferential_comp_normalColumnDilation T Q hηb hr hf hp.1 ht

include hηb hr hf in
/-- Local equality of normalized ORIGINAL Jacobian jets; the scale is held
fixed while differentiating (`app:ch_background:eq:bg-jacobian`). -/
theorem normalJetRescaling_iteratedFDeriv_normalizedJacobian
    {p : JointVariables n} (hp : p ∈ (normalChart T Q z₀ ηb r aOuter aPhase).inputDomain)
    {t : ℝ} (ht : 0 < t) (j : ℕ) :
    iteratedFDeriv ℝ j
        ((normalJetRescaling T Q z₀ ηb r aOuter aPhase).normalizedJacobian t) p =
      iteratedFDeriv ℝ j (symbolDifferential T Q ∘ jointInputCoordinates T) p := by
  have he : (normalJetRescaling T Q z₀ ηb r aOuter aPhase).normalizedJacobian t =ᶠ[𝓝 p]
      symbolDifferential T Q ∘ jointInputCoordinates T :=
    ((normalChart_inputDomain_open T Q z₀ ηb r aOuter aPhase).eventually_mem hp).mono
      (fun _ hq ↦ normalJetRescaling_normalizedJacobian_eq T Q hηb hr hf hq ht)
  exact (he.iteratedFDeriv ℝ j).eq_of_nhds

variable {b cJ : ℝ} {V L : Set (ℝ × Euclidean (n - 1))}
    {G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1))}
    (hInv : BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ aOuter)
      (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r)) V L b cJ G)
    (htrans : ∀ p ∈ physicalParameterSet z₀ aOuter,
      ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r),
        ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖)

include hηb hr hInv htrans in
/-- Joint left inversion on the restricted input domain, including its
phase-agreement buffer (`app:ch_background:eq:bg-Psi`). -/
theorem normalChart_pull_push {p : JointVariables n}
    (hp : p ∈ (normalChart T Q z₀ ηb r aOuter aPhase).inputDomain) :
    (normalChart T Q z₀ ηb r aOuter aPhase).pull
      ((normalChart T Q z₀ ηb r aOuter aPhase).push p) = p := by
  rw [normalChart_pull_eq, normalChart_push_eq]
  simp only [Function.comp_apply]
  rw [symbolInverse_augmentedTransportGradient T Q hηb hr hInv htrans
      (p := jointInputCoordinates T p) hp.1,
    ContinuousLinearEquiv.symm_apply_apply]

include hηb hr hInv htrans in
/-- Threshold one follows from the ORIGINAL support and inverse identity.
The only extra support premise is the exact containment assigned to the
supported-image producer (`app:ch_background:prop:bg-adjoint`). -/
theorem normalSupport_image_high_frequency {rMask aMask : ℝ}
    (hsupport : normalSupport T z₀ ηb rMask aMask ⊆
      (normalChart T Q z₀ ηb r aOuter aPhase).inputDomain)
    {p : JointVariables n}
    (hp : p ∈ (normalChart T Q z₀ ηb r aOuter aPhase).push ''
      normalSupport T z₀ ηb rMask aMask) :
    1 ≤ ‖((normalChart T Q z₀ ηb r aOuter aPhase).carrier
      ((normalChart T Q z₀ ηb r aOuter aPhase).pull p)).2‖ := by
  obtain ⟨q, hq, rfl⟩ := hp
  rw [normalChart_pull_push T Q hηb hr hInv htrans (hsupport hq), normalChart_carrier_eq]
  exact hq.2

end JanetCartan.ContinuumAdjoint.Canonical.NormalInputs
