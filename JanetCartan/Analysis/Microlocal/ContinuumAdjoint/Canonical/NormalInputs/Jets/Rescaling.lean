module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.NormalInputs.Determinant

/-!
# Linear normalization in the retained canonical coordinates

The input dilation scales only the original covector. The column normalization
scales the incidence column by the reciprocal frequency, so its determinant is
exactly `r⁻¹`. Both use the published physical slice coordinates.

Consumer: the normalized inverse and original-Jacobian fields of
`ModifiedNormalSymbol.PrimitiveJetGeometry` for
`app:ch_background:prop:bg-adjoint`, `bg-Psi`, and `bg-jacobian`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint.Canonical.NormalInputs
open ContinuumRow DerivativeKernels ModifiedNormalSymbol
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open CanonicalConic ContinuumNormalReduction.TransportSymbol

variable {n : ℕ}

/-- Invertible covector dilation in the canonical input coordinates
(`app:ch_background:eq:bg-Psi`). -/
def inputCovectorDilation (t : ℝ) (ht : t ≠ 0) : InputVariables n ≃L[ℝ] InputVariables n where
  toFun := scaleInput t
  invFun := scaleInput t⁻¹
  left_inv p := by simp [scaleInput, smul_smul, ht]
  right_inv p := by simp [scaleInput, smul_smul, ht]
  map_add' p q := by simp [scaleInput, smul_add]
  map_smul' r p := by simp [scaleInput, smul_smul, mul_comm]
  continuous_toFun := continuous_fst.prodMk
    (continuous_snd.fst.prodMk (continuous_snd.snd.const_smul t))
  continuous_invFun := continuous_fst.prodMk
    (continuous_snd.fst.prodMk (continuous_snd.snd.const_smul t⁻¹))

variable {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- The fixed input equivalence used in the normalized jets. At zero we use
the identity to give the total family required by `JetRescaling`; every
analytic use has strictly positive scale (`bg-Psi`). -/
def normalInputDilation (t : ℝ) : JointVariables n ≃L[ℝ] JointVariables n :=
  if ht : t = 0 then ContinuousLinearEquiv.refl ℝ _ else
    (jointInputCoordinates T).trans
      ((inputCovectorDilation t ht).trans (jointInputCoordinates T).symm)

/-- The retained physical input dilation is the canonical covector dilation
after the fixed coordinate reordering (`app:ch_background:eq:bg-Psi`). -/
theorem normalInputDilation_apply {t : ℝ} (ht : t ≠ 0) (p : JointVariables n) :
    normalInputDilation T t p = scaleJointInput T t p := by
  simp [normalInputDilation, ht, scaleJointInput, inputCovectorDilation]

/-- The inverse of the fixed input dilation divides the original covector
by the scale (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem normalInputDilation_symm_apply {t : ℝ} (ht : t ≠ 0) (p : JointVariables n) :
    (normalInputDilation T t).symm p = scaleJointInput T t⁻¹ p := by
  rw [normalInputDilation, dite_eq_right ht]
  rfl

/-- Scale the incidence column, keeping all covector columns unchanged in
the SAME volume-preserving slice coordinates (`bg-jacobian`). -/
def normalColumnDilation (t : ℝ) : Euclidean n →L[ℝ] Euclidean n :=
  (adaptedSliceCoordinates T).equiv.symm.toContinuousLinearMap.comp
    (((t⁻¹ • ContinuousLinearMap.id ℝ ℝ).prodMap
      (ContinuousLinearMap.id ℝ (Euclidean (n - 1)))).comp
        (adaptedSliceCoordinates T).equiv.toContinuousLinearMap)

/-- The column normalization has degree minus one, independently of the
dimension of the transverse covector (`app:ch_background:eq:bg-jacobian`). -/
theorem normalColumnDilation_det (t : ℝ) :
    (normalColumnDilation T t).det = t⁻¹ := by
  have h := LinearMap.det_conj
    (((t⁻¹ • ContinuousLinearMap.id ℝ ℝ).prodMap
      (ContinuousLinearMap.id ℝ (Euclidean (n - 1)))).toLinearMap)
    (adaptedSliceCoordinates T).equiv.symm.toLinearEquiv
  change (normalColumnDilation T t).det =
    LinearMap.det ((t⁻¹ • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)).prodMap
      (LinearMap.id : Euclidean (n - 1) →ₗ[ℝ] Euclidean (n - 1))) at h
  rw [h, LinearMap.det_prodMap, LinearMap.det_smul]
  simp

variable (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (z₀ : Euclidean 3) (ηb : Euclidean (n - 1)) (r aOuter aPhase : ℝ)

/-- The actual rescaling for `normalChart`, retaining its original coordinates
and its degree-one Jacobian (`app:ch_background:eq:bg-Psi`, `bg-jacobian`). -/
def normalJetRescaling : JetRescaling (normalChart T Q z₀ ηb r aOuter aPhase) where
  input := normalInputDilation T
  columns := normalColumnDilation T
  columns_det t _ := normalColumnDilation_det T t
  carrier t ht p := by
    rw [normalInputDilation_apply T ht.ne', normalChart_carrier_eq,
      normalChart_carrier_eq]
    simp only [scaleJointInput, ContinuousLinearEquiv.apply_symm_apply, scaleInput]
  left_position t ht p := by
    rw [normalInputDilation_apply T ht.ne']
    rfl
  right_position t ht p := by
    rw [normalInputDilation_apply T ht.ne']
    rfl

/-- The concrete normalized pull is exactly the retained inverse followed
by covector division, with positions and spectator untouched
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem normalJetRescaling_normalizedPull {t : ℝ} (ht : 0 < t) (p : JointVariables n) :
    (normalJetRescaling T Q z₀ ηb r aOuter aPhase).normalizedPull t p =
      (jointInputCoordinates T).symm
        (scaleInput t⁻¹ (inverseCoordinates (symbolInverse T Q z₀ ηb r aOuter) p)) := by
  change (normalInputDilation T t).symm
    ((normalChart T Q z₀ ηb r aOuter aPhase).pull p) = _
  rw [normalInputDilation_symm_apply T ht.ne', normalChart_pull_eq]
  simp only [scaleJointInput, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]

end JanetCartan.ContinuumAdjoint.Canonical.NormalInputs
