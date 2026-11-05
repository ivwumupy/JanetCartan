module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.Threshold
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.ActualTerminal

/-!
# The actual finite source symbol at the final threshold

The canonical PDO of the finite source symbol, expressed in original physical
coordinates, is exactly the terminal angular PDO of the same family with its
enlarged threshold. Both original physical masks are retained. This identifies
the source operator and its full identity defect at the symbol-realization
level; equality with the sum of chart operator realizations is a separate
finite-calculus obligation (`energy-complete-residual`, `resolved-angular-tail`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FiniteAssembly
open Characteristic Characteristic.ResidualCoordinates Characteristic.EvolutionIntegral
open FiniteMasks FiniteMasks.ActualFamily FinitePdo
open JanetCartan.CharacteristicTransport.CompleteResidual
open ArbitraryAccuracy.ResidualLocalization.IdentityDefect
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "H" => SpacetimeL2 d (d+1)

/-- The finite source symbol in ORIGINAL coordinates, with the actual
enlarged threshold. Its literal canonical realization retains both original
physical masks (`energy-complete-residual`, index one). -/
def selectedFiniteSourcePDO (f : ActualMaskFamily Ω x RQ A₀ K M) (L : ℝ) : H →L[ℂ] H :=
  maskedPhysicalPDO (fun y ↦ (f.outputMask y : ℂ)) (fun y ↦ (f.inputMask y : ℂ))
    (fun y ζ ↦ ∑ p, selectedSourceSymbol f p (2*L)
      ((physicalCoordinates (f.chart p).index).symm y)
      ((physicalCoordinates (f.chart p).index).symm ζ))

/-- The actual finite source PDO uses exactly the terminal angular
operator's stored threshold. No equality of different cutoff functions or
commutation with the source mask is used (`prop:complete-residual`). -/
theorem selectedFiniteSourcePDO_eq_actualAngularPDO
    (f : ActualMaskFamily Ω x RQ A₀ K M) (L : ℝ) (hL : f.radialThreshold ≤ L) :
    selectedFiniteSourcePDO f L = actualAngularPDO (r := d+1) (withEnlargedThreshold f L hL) := by
  classical
  unfold selectedFiniteSourcePDO actualAngularPDO maskedPhysicalPDO
  congr 1
  funext y z ζ
  change ((f.outputMask y : ℂ) * (f.inputMask z : ℂ)) •
    (∑ p, selectedSourceSymbol f p (2*L)
      ((physicalCoordinates (f.chart p).index).symm y)
      ((physicalCoordinates (f.chart p).index).symm ζ)) =
    ((f.outputMask y : ℂ) * (f.inputMask z : ℂ)) •
      ((∑ p, dilatedConicMask (f.angularMask p) (2*L) ζ : ℝ) : ℂ) •
        (1 : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
  by_cases hy : f.outputMask y = 0
  · simp only [hy, Complex.ofReal_zero, zero_mul, zero_smul]
  · have hyball : y ∈ closedBall x (4*f.physicalRadius) :=
      ball_subset_closedBall ((ball_subset_ball (by
        linarith [f.physicalRadius_pos] : 2*f.physicalRadius ≤ 4*f.physicalRadius))
          (f.outputMask_support (subset_tsupport _ hy)))
    simp_rw [selectedSourceSymbol_on_common_ball_enlarged f _ hL hyball]
    rw [← Finset.sum_smul, ← Complex.ofReal_sum]

/-- The literal adjoints agree as well, with the two original physical
masks reversed by the terminal realization (`measured-adjoint`). -/
theorem selectedFiniteSourcePDO_adjoint_eq
    (f : ActualMaskFamily Ω x RQ A₀ K M) (L : ℝ) (hL : f.radialThreshold ≤ L) :
    (selectedFiniteSourcePDO f L).adjoint =
      (actualAngularPDO (r := d+1) (withEnlargedThreshold f L hL)).adjoint := by
  rw [selectedFiniteSourcePDO_eq_actualAngularPDO f L hL]

/-- Retain the COMPLETE `Op(α)-I` term at the identical final threshold.
These are its actual L² bounds, not an asserted smoothing estimate
(`prop:complete-residual`, `resolved-angular-tail`). -/
theorem selectedFiniteSourcePDO_identity_defect_bounds
    (f : ActualMaskFamily Ω x RQ A₀ K M) (L : ℝ) (hL : f.radialThreshold ≤ L) :
    ‖selectedFiniteSourcePDO f L‖ ≤ 1 ∧
      ‖(selectedFiniteSourcePDO f L).adjoint‖ ≤ 1 ∧
      ‖selectedFiniteSourcePDO f L - 1‖ ≤ 2 ∧
      ‖(selectedFiniteSourcePDO f L).adjoint - 1‖ ≤ 2 := by
  rw [selectedFiniteSourcePDO_eq_actualAngularPDO f L hL]
  exact actualAngularPDO_low_bounds (r := d+1) (withEnlargedThreshold f L hL)

end JanetCartan.RegularSector.FiniteAssembly
