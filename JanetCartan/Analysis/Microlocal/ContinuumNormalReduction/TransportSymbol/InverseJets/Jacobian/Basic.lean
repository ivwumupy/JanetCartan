module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.InverseJets.Forward
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportKernel.Spectator
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ConicChart.Jacobian

/-!
# The literal transport slice Jacobian

Fixed Euclidean coordinates for `(s,η)` in `app:ch_background:eq:bg-Psi`.
Measure preservation is part of the coordinate interface: an arbitrary linear
identification would introduce an unwanted constant in `bg-jacobian`.
Both physical positions and the spectator remain arguments of the Jacobian.
-/

@[expose] public noncomputable section
open Set MeasureTheory
namespace JanetCartan.ContinuumNormalReduction.TransportSymbol

/-- Fixed, volume-preserving coordinates for the slice transformed in
`app:ch_background:eq:bg-Psi`. The canonical measurable coordinates are
`ContinuumRow.TransportKernel.sliceCoordinates`. -/
structure TransportSliceCoordinates (n : ℕ) where
  equiv : Euclidean n ≃L[ℝ] ℝ × Euclidean (n - 1)
  measurePreserving : MeasurePreserving equiv volume (volume.prod volume)

/-- Canonical fixed coordinates: the first Euclidean coordinate is `s` and
all remaining coordinates form `η`. Measure preservation is the checked
spectator-coordinate theorem, so the determinant is literal (`bg-jacobian`). -/
def canonicalTransportSliceCoordinates (m : ℕ) : TransportSliceCoordinates (m + 1) where
  equiv := ({
    toEquiv := (ContinuumRow.TransportKernel.sliceCoordinates m).toEquiv
    map_add' := by
      intro x y
      change (x 0 + y 0, _) = _
      rfl
    map_smul' := by
      intro t x
      rfl
    } : Euclidean (m + 1) ≃ₗ[ℝ] ℝ × Euclidean m).toContinuousLinearEquiv
  measurePreserving := ContinuumRow.TransportKernel.sliceCoordinates_measurePreserving m

/-- The continuous linear coordinates are exactly the canonical measurable
coordinates used by the literal kernel (`app:ch_background:eq:bg-Psi`). -/
theorem canonicalTransportSliceCoordinates_eq (m : ℕ) :
    ((canonicalTransportSliceCoordinates m).equiv : Euclidean (m + 1) → ℝ × Euclidean m) =
      (ContinuumRow.TransportKernel.sliceCoordinates m : Euclidean (m + 1) → _) := rfl

variable {n : ℕ}

/-- The actual forward map in fixed Euclidean slice coordinates, retaining
both positions and the spectator (`app:ch_background:eq:bg-Psi`). -/
def transportSliceForward (c : TransportSliceCoordinates n)
    (Y : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1))
    (p : InputVariables n) (z : Euclidean n) : Euclidean n :=
  transportAveragedGradient Y (p.1, ((c.equiv z).1, p.2.1.2), (c.equiv z).2)

/-- The derivative in `(s,η)`, in fixed volume-preserving Euclidean
coordinates (`app:ch_background:eq:bg-jacobian`). -/
def transportSliceDifferential (c : TransportSliceCoordinates n)
    (Y : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1))
    (p : InputVariables n) : Euclidean n →L[ℝ] Euclidean n :=
  fderiv ℝ (transportSliceForward c Y p) (c.equiv.symm (p.2.1.1, p.2.2))

/-- Genuine absolute input Jacobian in `app:ch_background:eq:bg-jacobian`.
No Jacobian or amplitude estimate is included in this definition. -/
def transportAbsoluteJacobian (c : TransportSliceCoordinates n)
    (Y : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1))
    (p : InputVariables n) : ℝ := |(transportSliceDifferential c Y p).det|

/-- The literal Euclidean Jacobian formula, with the coordinate measure
identity needed for the change of variables in `bg-full-complex-amplitude`. -/
theorem transportAbsoluteJacobian_eq_abs_det (c : TransportSliceCoordinates n)
    (Y : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1))
    (p : InputVariables n) :
    transportAbsoluteJacobian c Y p =
      |(fderiv ℝ (transportSliceForward c Y p)
        (c.equiv.symm (p.2.1.1, p.2.2))).det| ∧
      MeasurePreserving c.equiv volume (volume.prod volume) :=
  ⟨rfl, c.measurePreserving⟩

private def sliceDilation (c : TransportSliceCoordinates n) (t : ℝ) :
    Euclidean n →L[ℝ] Euclidean n :=
  c.equiv.symm.toContinuousLinearMap.comp
    ((ConicChart.radialLinearMap (E := Euclidean (n - 1)) t).comp
      c.equiv.toContinuousLinearMap)

private theorem det_sliceDilation (c : TransportSliceCoordinates n) (t : ℝ) :
    (sliceDilation c t).det = t ^ (n - 1) := by
  have h := LinearMap.det_conj (ConicChart.radialLinearMap
    (E := Euclidean (n - 1)) t).toLinearMap c.equiv.symm.toLinearEquiv
  change (sliceDilation c t).det = (ConicChart.radialLinearMap
    (E := Euclidean (n - 1)) t).det at h
  rw [h, ConicChart.det_radialLinearMap]
  simp

set_option maxHeartbeats 800000 in
/-- Degree one follows by differentiating the actual forward scaling law.
Only differentiability at the two slice points is required; no Jacobian
scaling premise occurs (`app:ch_background:eq:bg-jacobian`). -/
theorem transportAbsoluteJacobian_pos_smul (c : TransportSliceCoordinates n)
    (hn : 0 < n)
    (Y : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1))
    (p : InputVariables n) {t : ℝ} (ht : 0 < t)
    (hp : DifferentiableAt ℝ (transportSliceForward c Y p)
      (c.equiv.symm (p.2.1.1, p.2.2)))
    (htp : DifferentiableAt ℝ (transportSliceForward c Y p)
      (c.equiv.symm (p.2.1.1, t • p.2.2))) :
    transportAbsoluteJacobian c Y (scaleInput t p) =
      t * transportAbsoluteJacobian c Y p := by
  let z := c.equiv.symm (p.2.1.1, p.2.2)
  have hscale (w : Euclidean n) :
      transportSliceForward c Y p (sliceDilation c t w) =
        t • transportSliceForward c Y p w := by
    simp only [transportSliceForward, sliceDilation, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, ConicChart.radialLinearMap_apply,
      ContinuousLinearEquiv.apply_symm_apply, ConicChart.radialScale]
    exact transportAveragedGradient_smul Y t
      (p.1, ((c.equiv w).1, p.2.1.2), (c.equiv w).2)
  have hz : sliceDilation c t z = c.equiv.symm (p.2.1.1, t • p.2.2) := by
    simp [sliceDilation, z, ConicChart.radialScale]
  rw [← hz] at htp
  have hd' := (htp.hasFDerivAt.comp z ((sliceDilation c t).hasFDerivAt))
  have he : (fderiv ℝ (transportSliceForward c Y p) (sliceDilation c t z)).comp
      (sliceDilation c t) = t • fderiv ℝ (transportSliceForward c Y p) z := by
    apply hd'.unique
    exact (hp.hasFDerivAt.const_smul t).congr_of_eventuallyEq
      (Filter.Eventually.of_forall hscale)
  have hdet := congrArg ContinuousLinearMap.det he
  change LinearMap.det ((fderiv ℝ (transportSliceForward c Y p)
      (sliceDilation c t z)).toLinearMap.comp (sliceDilation c t).toLinearMap) =
    LinearMap.det (t • (fderiv ℝ (transportSliceForward c Y p) z).toLinearMap) at hdet
  rw [LinearMap.det_comp, LinearMap.det_smul] at hdet
  change (fderiv ℝ (transportSliceForward c Y p) (sliceDilation c t z)).det *
      (sliceDilation c t).det = _ at hdet
  rw [det_sliceDilation] at hdet
  simp only [finrank_euclideanSpace_fin] at hdet
  have hedet : (transportSliceDifferential c Y (scaleInput t p)).det =
      t * (transportSliceDifferential c Y p).det := by
    apply mul_right_cancel₀ (pow_ne_zero (n - 1) ht.ne')
    change (fderiv ℝ (transportSliceForward c Y p)
      (c.equiv.symm (p.2.1.1, t • p.2.2))).det * t ^ (n - 1) = _
    have htPow : t ^ n = t * t ^ (n - 1) := by
      conv_lhs => rw [show n = 1 + (n - 1) from by omega]
      rw [pow_add, pow_one]
    rw [← hz, hdet, htPow]
    change t * t ^ (n - 1) * (transportSliceDifferential c Y p).det = _
    ring
  simp only [transportAbsoluteJacobian, hedet, abs_mul, abs_of_pos ht]

end JanetCartan.ContinuumNormalReduction.TransportSymbol
