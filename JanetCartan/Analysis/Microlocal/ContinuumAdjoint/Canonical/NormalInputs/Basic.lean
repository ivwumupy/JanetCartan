module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.SupportedData
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.LowBounds.SymbolJets.PrimitiveBounds
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.RefinedGeometry
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.RefinedKernel

/-!
# The retained canonical chart on the phase-agreement domain

The raw adjoint endpoint requires phase agreement everywhere on its domain.
We intersect the published conic input domain with the interior of the fixed
closed chart on which the affine extension agrees with the Hamilton position.
The coordinate map, forward map, inverse and Jacobian are unchanged.

Consumer: `exists_scalarTransportCarrierAdjoint_periodic_raw_bound`, geometric
inputs for `app:ch_background:prop:bg-adjoint` and `app:ch_background:eq:bg-Psi`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint.Canonical.NormalInputs
open ContinuumRow DerivativeKernels ModifiedNormalSymbol PhaseExtension
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open CanonicalConic ContinuumNormalReduction.TransportSymbol

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- Reorder the joint adjoint input into the SAME canonical symbol input,
using the published physical slice coordinates (`bg-full-complex-amplitude`). -/
def jointInputCoordinates : JointVariables n ≃L[ℝ] InputVariables n where
  toFun p := kernelInput T p.1.1 p.1.2.1 p.2 p.1.2.2
  invFun p := ((p.1.1, p.1.2, (adaptedSliceCoordinates T).equiv.symm
    (p.2.1.1, p.2.2)), p.2.1.2)
  left_inv p := by simp only [kernelInput, Prod.mk.eta, ContinuousLinearEquiv.symm_apply_apply]
  right_inv p := by simp only [kernelInput, ContinuousLinearEquiv.apply_symm_apply]
  map_add' p q := by simp [kernelInput, map_add]
  map_smul' t p := by simp [kernelInput, map_smul]
  continuous_toFun := by
    exact (continuous_fst.fst.prodMk continuous_fst.snd.fst).prodMk
      ((((adaptedSliceCoordinates T).equiv.continuous.comp continuous_fst.snd.snd).fst.prodMk
        continuous_snd).prodMk
          ((adaptedSliceCoordinates T).equiv.continuous.comp continuous_fst.snd.snd).snd)
  continuous_invFun := by
    exact (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk
      ((adaptedSliceCoordinates T).equiv.symm.continuous.comp
        (continuous_snd.fst.fst.prodMk continuous_snd.snd)))).prodMk continuous_snd.fst.snd

/-- The restriction is independent of the immersion. Both positions must
belong to the phase-agreement chart with the original carrier (`bg-Psi`). -/
def phaseAgreementDomain (z₀ : Euclidean 3) (aPhase : ℝ) : Set (InputVariables n) :=
  {p | (p.1.1, p.2.1) ∈ interior (supportedChart z₀ aPhase) ∧
    (p.1.2, p.2.1) ∈ interior (supportedChart z₀ aPhase)}

/-- The fixed phase restriction is open (`app:ch_background:eq:bg-Psi`). -/
theorem phaseAgreementDomain_open (z₀ : Euclidean 3) (aPhase : ℝ) :
    IsOpen (phaseAgreementDomain (n := n) z₀ aPhase) :=
  (isOpen_interior.preimage (continuous_fst.fst.prodMk continuous_snd.fst)).inter
    (isOpen_interior.preimage (continuous_fst.snd.prodMk continuous_snd.fst))

/-- Dilate only the original covector in the retained physical input
coordinates, fixing the incidence label and spectator (`bg-Psi`). -/
def scaleJointInput (t : ℝ) (p : JointVariables n) : JointVariables n :=
  (jointInputCoordinates T).symm (scaleInput t (jointInputCoordinates T p))

/-- The fixed high-frequency input buffer, with the original physical,
carrier and angular masks and threshold one. No image support is assumed
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
def normalSupport (z₀ : Euclidean 3) (ηb : Euclidean (n - 1)) (rMask aMask : ℝ) :
    Set (JointVariables n) :=
  jointInputCoordinates T ⁻¹'
    {p | p ∈ conicMaskSupport z₀ ηb rMask aMask ∧ 1 ≤ ‖p.2.2‖}

variable (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress n) < T.family.threshold})

/-- The actual adjoint chart. Only its domain is restricted; all functions
are precisely those of `CanonicalConic.refinedKernelChartInputs` (`bg-Psi`). -/
def normalChart (z₀ : Euclidean 3) (ηb : Euclidean (n - 1))
    (r aOuter aPhase : ℝ) : Chart n where
  coordinates := kernelSliceCoordinates T
  domain x y v := kernelInput T x y v ⁻¹'
    (symbolInputDomain z₀ ηb r aOuter ∩ phaseAgreementDomain z₀ aPhase)
  forward := kernelForward T Q
  inverse := kernelInverse T Q z₀ ηb r aOuter
  jacobian x y v w := symbolDifferential T Q (kernelInput T x y v w)

variable (z₀ : Euclidean 3) (ηb : Euclidean (n - 1)) (r aOuter aPhase : ℝ)

/-- The original integration coordinates and measure are retained exactly
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem normalChart_measurePreserving :
    MeasurePreserving (normalChart T Q z₀ ηb r aOuter aPhase).coordinates
      volume (volume.prod volume) := kernelSliceCoordinates_measurePreserving T

/-- The inverse coordinates are continuous, as required for literal kernel
substitution (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem normalChart_coordinates_symm_continuous :
    Continuous (normalChart T Q z₀ ηb r aOuter aPhase).coordinates.symm :=
  (adaptedSliceCoordinates T).equiv.symm.continuous

/-- Joint input membership includes the phase buffer at BOTH positions
(`app:ch_background:eq:bg-Psi`). -/
theorem normalChart_inputDomain_eq :
    (normalChart T Q z₀ ηb r aOuter aPhase).inputDomain =
      jointInputCoordinates T ⁻¹'
        (symbolInputDomain z₀ ηb r aOuter ∩ phaseAgreementDomain z₀ aPhase) := rfl

/-- Openness of the entire restricted joint input domain (`bg-Psi`). -/
theorem normalChart_inputDomain_open :
    IsOpen (normalChart T Q z₀ ηb r aOuter aPhase).inputDomain :=
  ((symbolInputDomain_open z₀ ηb r aOuter).inter
    (phaseAgreementDomain_open z₀ aPhase)).preimage (jointInputCoordinates T).continuous

/-- Every restricted slice domain is open (`bg-Psi`). -/
theorem normalChart_domain_open (x y : Euclidean n) (v : Euclidean 2) :
    IsOpen ((normalChart T Q z₀ ηb r aOuter aPhase).domain x y v) :=
  ((symbolInputDomain_open z₀ ηb r aOuter).inter
    (phaseAgreementDomain_open z₀ aPhase)).preimage
      ((kernelInput_smooth T x y).continuous.comp (continuous_const.prodMk continuous_id))

/-- The push is the published augmented gradient after the fixed reordering;
there is no new phase or Fourier normalization (`bg-full-complex-amplitude`). -/
theorem normalChart_push_eq :
    (normalChart T Q z₀ ηb r aOuter aPhase).push =
      augmentedTransportGradient (CanonicalCarrier.transportPosition T Q) ∘
        jointInputCoordinates T := rfl

/-- The pull is the published inverse in the SAME input coordinates
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem normalChart_pull_eq :
    (normalChart T Q z₀ ηb r aOuter aPhase).pull =
      (jointInputCoordinates T).symm ∘
        inverseCoordinates (symbolInverse T Q z₀ ηb r aOuter) := rfl

/-- The original carrier is exactly the second canonical input component
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem normalChart_carrier_eq (p : JointVariables n) :
    (normalChart T Q z₀ ηb r aOuter aPhase).carrier p =
      (jointInputCoordinates T p).2 := rfl

/-- The phase restriction is invariant under positive covector dilation.
Thus the working domain remains conic, not merely a supported subset
(`app:ch_background:eq:bg-Psi`). -/
theorem normalChart_scaleJointInput_mem {p : JointVariables n}
    (hp : p ∈ (normalChart T Q z₀ ηb r aOuter aPhase).inputDomain)
    {t : ℝ} (ht : 0 < t) :
    scaleJointInput T t p ∈ (normalChart T Q z₀ ηb r aOuter aPhase).inputDomain := by
  rw [normalChart_inputDomain_eq]
  change jointInputCoordinates T ((jointInputCoordinates T).symm
    (scaleInput t (jointInputCoordinates T p))) ∈
      symbolInputDomain z₀ ηb r aOuter ∩ phaseAgreementDomain z₀ aPhase
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact ⟨⟨hp.1.1, radialScale_mem_supportedCone hp.1.2 ht⟩, hp.2⟩

end JanetCartan.ContinuumAdjoint.Canonical.NormalInputs
