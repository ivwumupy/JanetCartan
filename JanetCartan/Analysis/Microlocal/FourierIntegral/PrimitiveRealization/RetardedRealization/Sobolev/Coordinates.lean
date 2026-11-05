module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.PrimitiveRealization.RetardedRealization.Operators
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.FourierAssembly.Extension
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionLocalization.SobolevRealization.Fourier
public import JanetCartan.Analysis.Operator.RetardedSobolev.PositiveExtension

/-!
# Classical coordinates for the Fourier retarded bound

The selected time coordinate and scalar fiber projections connect the existing
classical jets to the SAME graph tests. Consumer: the natural-order bounds of
`app:ch_osc:prop:osc-retarded-tube`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped ContDiff

namespace JanetCartan.FourierIntegral.RetardedRealization
open RegularSector.Characteristic RetardedSobolev RetardedSobolev.Spaces
open ArbitraryAccuracy.EvolutionLocalization.SobolevRealization
open FiniteChain.Graph.KernelLimits Pseudodifferential

variable {d r : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "P" => ℝ × (Fin d → ℝ)
local notation "V" => EuclideanSpace ℂ (Fin r)

/-- The actual selected time split with Cartesian transverse coordinates.
Consumer: `retardedScalarTest`; source: `app:ch_osc:prop:osc-retarded-tube`. -/
def retardedCartesianCoordinates (t : Fin (d + 1)) : P ≃L[ℝ] E :=
  ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d ↦ ℝ)).symm).trans
      (coordinateSplit t).symm

/-- The Cartesian coordinates preserve the specified Lebesgue measure.
Source: `app:ch_osc:prop:osc-retarded-tube`. -/
theorem measurePreserving_retardedCartesianCoordinates (t : Fin (d + 1)) :
    MeasurePreserving (graphInputCoordinates (retardedCartesianCoordinates t))
      volume volume := by
  exact ((ResidualCoordinates.measurePreserving_coordinateSplit t).symm
    (coordinateSplit t).toHomeomorph.toMeasurableEquiv).comp
      (((MeasurePreserving.id volume).prod (PiLp.volume_preserving_toLp (Fin d))).comp
        Measure.measurePreserving_swap)

/-- A scalar coordinate of a graph test in the classical retarded coordinates.
Consumer: the input jet comparison; source: `app:ch_osc:prop:osc-retarded-tube`. -/
def retardedScalarTest (t : Fin (d + 1)) (u : graphTestSpace (d + 1) r)
    (a : Fin r) : Test d :=
  ⟨fun p ↦ u.val (retardedCartesianCoordinates t p) a,
    ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin r ↦ ℂ) a).restrictScalars ℝ).contDiff.comp
      (u.property.1.comp (retardedCartesianCoordinates t).contDiff),
    (u.property.2.comp_homeomorph (retardedCartesianCoordinates t).toHomeomorph).comp_left
      (map_zero (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin r ↦ ℂ) a))⟩

/-- The existing Fourier realization of these jets is exactly the scalar
coordinate of the original Euclidean graph test, at every budget.
Source: `app:ch_osc:prop:osc-retarded-tube`. -/
theorem physicalZeroJet_retardedScalarTest (t : Fin (d + 1)) (s : ℕ)
    (u : graphTestSpace (d + 1) r) (a : Fin r) :
    physicalZeroJet (retardedCartesianCoordinates t)
      (measurePreserving_retardedCartesianCoordinates t) s
      (ofTest s volume (retardedScalarTest t u a)) =
        finiteL2CoordinateIsometry volume (graphTestToLp u) a := by
  apply Lp.ext
  filter_upwards [physicalZeroJet_ofTest_ae (retardedCartesianCoordinates t)
    (measurePreserving_retardedCartesianCoordinates t) s (retardedScalarTest t u a),
    finiteL2Coordinates_apply_ae volume (graphTestToLp u) a,
    (graphTest_memLp u).coeFn_toLp] with x hx hy hz
  simp only [retardedScalarTest, ContinuousLinearEquiv.apply_symm_apply] at hx
  exact hx.trans ((congrArg (fun v : V ↦ v a) hz).symm.trans hy.symm)

/-- Chain rule for scalar graph tests in the Cartesian coordinates. It retains
the selected physical direction. Consumer: the mixed-word input estimate;
source: `app:ch_osc:prop:osc-retarded-tube`. -/
theorem directionalTest_retardedScalarTest (t : Fin (d + 1))
    (v : P) (i : Fin (d + 1))
    (hv : retardedCartesianCoordinates t v = EuclideanSpace.single i 1)
    (u : graphTestSpace (d + 1) r) (a : Fin r) :
    directionalTest v (retardedScalarTest t u a) =
      retardedScalarTest t (graphTestPartialDeriv i u) a := by
  apply Subtype.ext
  funext p
  let J := retardedCartesianCoordinates t
  let L := (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin r ↦ ℂ) a).restrictScalars ℝ
  have h := L.hasFDerivAt.comp p
    (((u.property.1.differentiable (by simp) (J p)).hasFDerivAt).comp p J.hasFDerivAt)
  exact (congrArg (fun D : P →L[ℝ] ℂ ↦ D v) h.fderiv).trans (by
    change L (fderiv ℝ u.val (J p) (J v)) = _
    rw [hv]
    rfl)

/-- The Cartesian time direction is the selected Euclidean coordinate.
Source: `app:ch_osc:prop:osc-retarded-tube`. -/
@[simp] theorem retardedCartesianCoordinates_time (t : Fin (d + 1)) :
    retardedCartesianCoordinates t (1, 0) = EuclideanSpace.single t 1 := by
  exact coordinateSplit_symm_time t

/-- Cartesian transverse directions are the remaining Euclidean coordinates.
Source: `app:ch_osc:prop:osc-retarded-tube`. -/
@[simp] theorem retardedCartesianCoordinates_space (t : Fin (d + 1)) (i : Fin d) :
    retardedCartesianCoordinates t (0, Pi.single i 1) =
      EuclideanSpace.single (t.succAbove i) 1 := by
  exact coordinateSplit_symm_space t i

end JanetCartan.FourierIntegral.RetardedRealization
