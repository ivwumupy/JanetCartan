module

public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.CompleteResidual.TransportColumns

/-!
# The selected physical coordinates in the complete residual

The residual uses time coordinate zero. The physical construction selects a
coordinate `i`. The permutation below changes the independent variables only;
the column and row indices of the pencil retain their original meaning.
It preserves the physical Fourier pairing and Lebesgue measure.
Consumer: `CompleteResidual.completeResidual_operators_of_graph_regularizations`.
Source: `app:ch_regular_base:eq:two-term-null-identity` and
`app:ch_regular_base:eq:energy-complete-residual` in `paper-v2.tex`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Matrix
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.RegularSector.Characteristic.ResidualCoordinates
open EvolutionIntegral EvolutionIntegral.KernelIdentification ActualCarriers
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Mat" => MetricTensor (d + 1)

/-- From the residual's time-zero coordinates to the selected physical chart.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
def physicalCoordinates (i : Fin (d + 1)) : E ≃L[ℝ] E :=
  (coordinateSplit 0).trans (coordinateSplit i).symm

/-- The canonical split agrees with the existing retarded integral's split.
Source: `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem coordinateSplit_zero (x : E) : coordinateSplit 0 x = (x 0, spatialPart x) := rfl

/-- The physical point corresponding to the residual's independent variable.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem physicalCoordinates_apply (i : Fin (d + 1)) (x : E) :
    physicalCoordinates i x = (coordinateSplit i).symm (x 0, spatialPart x) := rfl

/-- Rejoining time and space recovers the selected physical point.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
@[simp] theorem physicalCoordinates_timeSpacePoint (i : Fin (d + 1))
    (t : ℝ) (y : Euclidean d) :
    physicalCoordinates i (timeSpacePoint t y) = (coordinateSplit i).symm (t, y) := by
  simp [physicalCoordinates_apply]

/-- The time direction is precisely the selected physical direction.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
@[simp] theorem physicalCoordinates_single_zero (i : Fin (d + 1)) :
    physicalCoordinates i (EuclideanSpace.single 0 1) = EuclideanSpace.single i 1 := by
  simp [physicalCoordinates]

/-- Spatial directions keep the original order after removing the time coordinate.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
@[simp] theorem physicalCoordinates_single_succ (i : Fin (d + 1)) (j : Fin d) :
    physicalCoordinates i (EuclideanSpace.single j.succ 1) =
      EuclideanSpace.single (i.succAbove j) 1 := by
  have h := coordinateSplit_single_space (0 : Fin (d + 1)) j
  simpa [physicalCoordinates] using congrArg (coordinateSplit i).symm h

/-- The same coordinate change acts on frequencies and preserves the physical
Fourier pairing, without changing the Fourier normalization.
Source: `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem physicalCoordinates_inner (i : Fin (d + 1)) (x ξ : E) :
    ⟪physicalCoordinates i x, physicalCoordinates i ξ⟫_ℝ = ⟪x, ξ⟫_ℝ := by
  rw [physicalCoordinates_apply, coordinateSplit_covector_pairing]
  rw [show coordinateSplit i (physicalCoordinates i ξ) = coordinateSplit 0 ξ from
    (coordinateSplit i).apply_symm_apply _]
  exact (inner_eq_time_add_spatial x ξ).symm

/-- The selected split preserves the same Lebesgue measures as the canonical
split. Consumer: physical kernel changes of variables in the complete residual.
Source: `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem measurePreserving_coordinateSplit (i : Fin (d + 1)) :
    MeasurePreserving (coordinateSplit i) volume (volume.prod volume) := by
  exact ((MeasurePreserving.id volume).prod (PiLp.volume_preserving_toLp (Fin d))).comp
    ((volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) ↦ ℝ) i).comp
      (PiLp.volume_preserving_ofLp (Fin (d + 1))))

/-- The coordinate permutation has unit volume Jacobian.
Source: `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem measurePreserving_physicalCoordinates (i : Fin (d + 1)) :
    MeasurePreserving (physicalCoordinates i) volume volume := by
  exact ((measurePreserving_coordinateSplit i).symm
    (coordinateSplit i).toHomeomorph.toMeasurableEquiv).comp
      (measurePreserving_coordinateSplit 0)

/-- All first-order coefficients pulled to canonical coordinates. Matrix indices
are unchanged; the independent-variable direction is permuted.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
def coefficient (i : Fin (d + 1)) (Q : E → Fin (d + 1) → Mat)
    (x : E) (a : Fin (d + 1)) : Mat :=
  pencil (Q (physicalCoordinates i x)) (physicalCoordinates i (EuclideanSpace.single a 1))

/-- The entire zeroth-order coefficient in the same physical chart.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
def zeroth (i : Fin (d + 1)) (B : E → Mat) (x : E) : Mat :=
  B (physicalCoordinates i x)

/-- Exact differential conjugacy, including `B`. This does not differentiate
any matrix coefficient: the operator is in the paper's nondivergence form.
Source: `app:ch_regular_base:eq:two-term-null-identity`. -/
theorem firstOrderApply_physicalCoordinates
    (i : Fin (d + 1)) (Q : E → Fin (d + 1) → Mat) (B : E → Mat)
    {u : E → Fin (d + 1) → ℂ} {x : E}
    (hu : DifferentiableAt ℝ u (physicalCoordinates i x)) :
    WKB.firstOrderApply (fun y a ↦ ((coefficient i Q y a).map Complex.ofReal).mulVecLin)
      (fun y ↦ ((zeroth i B y).map Complex.ofReal).mulVecLin)
      (u ∘ physicalCoordinates i) x =
      WKB.firstOrderApply (complexPencilCoefficient Q) (complexPencilZeroth B)
        u (physicalCoordinates i x) := by
  have hd (a : Fin (d + 1)) : partialDeriv (u ∘ physicalCoordinates i) x a =
      fderiv ℝ u (physicalCoordinates i x)
        (physicalCoordinates i (EuclideanSpace.single a 1)) := by
    rw [partialDeriv, (hu.hasFDerivAt.comp x (physicalCoordinates i).hasFDerivAt).fderiv]
    rfl
  simp only [WKB.firstOrderApply, coefficient, zeroth, hd,
    complexPencilCoefficient, complexPencilZeroth, Function.comp_apply]
  congr 1
  rw [Fin.sum_univ_succ, ← Fin.add_sum_removeNth i]
  simp only [physicalCoordinates_single_zero, physicalCoordinates_single_succ,
    Fin.removeNth, partialDeriv]

end JanetCartan.RegularSector.Characteristic.ResidualCoordinates
