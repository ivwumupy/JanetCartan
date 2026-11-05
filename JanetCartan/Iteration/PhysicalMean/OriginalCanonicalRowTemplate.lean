module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalRowComparison.PeriodicComparison
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalRowComparison.BandIdentification
public import JanetCartan.Iteration.PhysicalSamplingShells.Native
public import JanetCartan.Iteration.PhysicalSamplingShells.Realification
public import JanetCartan.Iteration.PhysicalMean.MomentRows
public import JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEvent
import all JanetCartan.Iteration.PhysicalSampling.OriginalJointEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSmoothEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalBareEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonStageApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonThresholdApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredFamilyApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredCurrentApplication
import all JanetCartan.Iteration.PhysicalPrimary.OriginalJointResponseRegularityTemplate
import all JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWaveGeometryTemplate
import all JanetCartan.Iteration.PhysicalNormalInverse.OriginalComparisonCurrentApplication
public meta import Lean

/-!
# The exact sampled raw row on its unchanged native input

The bounded raw component is the existing `rawIntegralSampledComponent`, with
its fixed inverse Fourier scalar. Identify its entire weighted row with the
existing `sampledRefinedRow`, before taking any normal or inverse. Transport
through the original sampled-shell isometry changes no measure and divides
by no weight. These deductions are for the precise original `BandKernelData`
interface; the actual original-data specialization and the physical G action
belong to `OriginalCanonicalRow`, not to an assumed G/A equality.

Consumers: `app:ch_mean_pairs:defn:mean-canonical`, the literal input of
`weightedAnnularInput_eq_nativeAdjoint`, and `canonicalSourceIterate_toL2`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

open MeasureTheory
namespace JanetCartan.PhysicalMean.OriginalCanonicalRow
open RawInputPartition Sampling SamplingKernelBounds SeparatedSampling
open CanonicalRowComparison PhysicalSamplingShells PeriodicLocalL2

variable {ι : Type*} [Fintype ι] {n J p : ℕ}
local notation "CP" => (Fin 3 → Fin (p + 1)) × Point

/-- The real version of the SAME unweighted sampled-shell isometry. Both
complex quadratures remain; square-root sample weights stay in the row, not
in this measure (`app:ch_waves:eq:sampling-prefix-normal`). -/
def nativeInputEquiv (B : ℝ) (ψ : ι → Point → ℝ) (w : ℝ → ℝ) (h : ℝ)
    (U : ι → Lattice → Point) :
    Lp ℂ 2 (sampledShellMeasure (ι := SampleIndex p B ψ w h U) n J) ≃ₗᵢ[ℝ]
      PiLp 2 (fun _ : SampleIndex p B ψ w h U ↦ RefinedInput n J) :=
  { toLinearEquiv := (sampledShellEquiv (V := ℂ) (ι := SampleIndex p B ψ w h U)
      n J).toLinearEquiv.restrictScalars ℝ
    norm_map' := (sampledShellEquiv (V := ℂ) (ι := SampleIndex p B ψ w h U) n J).norm_map }

/-- The bounded real input map is literally the one used by the native
adjoint-input identity; there is no new realization. -/
theorem nativeInputEquiv_map (B : ℝ) (ψ : ι → Point → ℝ) (w : ℝ → ℝ) (h : ℝ)
    (U : ι → Lattice → Point) :
    (nativeInputEquiv (n := n) (J := J) (p := p) B ψ w h U).toContinuousLinearEquiv.toContinuousLinearMap =
      (sampledShellEquiv (V := ℂ) (ι := SampleIndex p B ψ w h U)
        n J).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ := rfl

/-- The full raw weighted row is the literal original complex sampled row,
realified by `2 Re` and transferred only on its output. The fixed Fourier
scalar is explicit; no sign or nonzero-weight assumption is required. -/
theorem sampled_raw_row_eq (B : ℝ) (ψ : ι → Point → ℝ) (w : ℝ → ℝ) (h : ℝ)
    (U : ι → Lattice → Point) (D : ι → BandKernelData (Fin J × CP) n) (L : ℕ) :
    CanonicalRow.weightedRow (sampleWeight B ψ w h U)
      (rawIntegralSampledComponent B ψ w h U
        (fun i c z ↦ refinedKernelPrefix (D i) L (c,z))) =
      ((2 * Real.pi) ^ (-(n : ℝ) / 2))⁻¹ •
        transferOutputOperator (realQuadratureChannel (sampledRefinedRow B ψ w h U D L)) := by
  rw [weightedRow_rawIntegralSampledComponent, weightedRow_periodicSampledComponent,
    ← sampledRefinedRow_realQuadrature_eq]

/-- The exact physical raw row on native sampled-shell L². This is an equality
of the whole operators, not merely of their normal operators. All original
sample labels and shell copies survive even when their weights vanish. -/
theorem sampled_raw_row_native_input (B : ℝ) (ψ : ι → Point → ℝ)
    (w : ℝ → ℝ) (h : ℝ) (U : ι → Lattice → Point)
    (D : ι → BandKernelData (Fin J × CP) n) (L : ℕ) :
    (CanonicalRow.weightedRow (sampleWeight B ψ w h U)
      (rawIntegralSampledComponent B ψ w h U
        (fun i c z ↦ refinedKernelPrefix (D i) L (c,z)))).comp
      ((sampledShellEquiv (V := ℂ) (ι := SampleIndex p B ψ w h U)
        n J).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ) =
      ((2 * Real.pi) ^ (-(n : ℝ) / 2))⁻¹ • transferOutputOperator
        (realQuadratureChannel ((sampledRefinedRow B ψ w h U D L).comp
          (sampledShellEquiv (V := ℂ) (ι := SampleIndex p B ψ w h U)
            n J).toContinuousLinearEquiv.toContinuousLinearMap)) := by
  rw [sampled_raw_row_eq]
  ext f
  rfl

/-- Coordinatewise identification with the SAME native adjoint-amplitude
convention. The measured coefficient is the conjugate of the forward
coefficient, including the fixed inverse Fourier scalar. This is used by the
actual `hAn`/`hrow` join of `fixedSourceQuadratic_low_bound`; it neither changes
G nor absorbs any sample weight into the native input measure. -/
theorem raw_band_coordinate_eq_moment_kernel
    (phase : Euclidean (n-1) → Euclidean n → ℝ)
    (mask : Euclidean (n-1) → ℝ)
    (amplitude : Euclidean (n-1) → Euclidean n → EuclideanSpace ℂ (Fin n))
    (η : Euclidean (n-1)) (x : Euclidean n) (i : Fin n) :
    ((((2 * Real.pi) ^ (-(n : ℝ) / 2))⁻¹ : ℝ) : ℂ) *
      (bandKernel phase (fun η ↦ (mask η : ℂ)) amplitude η x) i =
      sampledMomentKernel phase (fun η ↦ mask η * Real.sqrt ‖η‖)
        (fun η x ↦ star (((((2 * Real.pi) ^ (-(n : ℝ) / 2))⁻¹ : ℝ) : ℂ) * amplitude η x i)) x η := by
  simp only [bandKernel, PiLp.smul_apply, smul_eq_mul, sampledMomentKernel,
    NormalComparison.oscillatoryFactor, one_mul, Complex.ofReal_mul, star_star]
  rw [mul_comm (phase η x : ℂ) Complex.I]
  ring

end JanetCartan.PhysicalMean.OriginalCanonicalRow
end

public meta section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
namespace JanetCartan.PhysicalMean.OriginalCanonicalRow
open Lean Meta Elab Command

private def nativeEvent := `JanetCartan.PhysicalSampling.OriginalNativeGradedEvent.exists_on_original_history
private def measuredFamily := `JanetCartan.PhysicalSampling.OriginalJointEvent.measured_kernel
private def actualFamily := `JanetCartan.PhysicalMean.OriginalCanonicalRow.D

private def storeActual (name : Name) (xs : Array Expr) (term : Expr)
    (target : Expr) (data : Bool) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars xs target)
  let value ← instantiateMVars (← mkLambdaFVars xs term)
  if type.hasFVar || type.hasMVar || type.hasLevelMVar || type.hasLooseBVars || type.hasSorry ||
      value.hasFVar || value.hasMVar || value.hasLevelMVar || value.hasLooseBVars || value.hasSorry then
    throwError "actual canonical row: open or analytic-success input in {name}"
  if data then
    addDecl (.defnDecl {name, levelParams := [], type, value, hints := .abbrev, safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name, levelParams := [], type, value}) (forceExpose := true)

/-- Read the existing saved50 type; never rerun its selector or stage producer.
The measured family is independent of its already-issued existential sample. -/
elab "retain_original_canonical_measured_family " which:num : command => liftTermElabM do
  if which.getNat == 0 then
    forallBoundedTelescope (← getConstInfo nativeEvent).type (some 50) fun xs result => do
      unless xs.size == 50 do throwError "actual canonical row: native50 changed"
      let some D := result.find? (·.isAppOfArity measuredFamily 60)
        | throwError "actual canonical row: original measured60 missing from saved50"
      storeActual actualFamily xs D (← inferType D) true
      logInfo "actual canonical D50: SAME native measured60, no response-budget/profile/jets/sample-choice input"
  else if which.getNat == 1 then
    forallBoundedTelescope (← getConstInfo actualFamily).type (some 50) fun xs remaining => do
      let some value := (← getConstInfo actualFamily).value? (allowOpaque := true)
        | throwError "actual canonical row: D50 has no checked body"
      let D := (value.beta xs).headBeta
      unless D.isAppOfArity measuredFamily 60 do throwError "actual canonical row: changed saved measured60"
      let some familyBody := (← getConstInfo measuredFamily).value? (allowOpaque := true)
        | throwError "actual canonical row: measured60 has no saved body"
      forallBoundedTelescope remaining (some 1) fun i _ => do
        unless i.size == 1 do throwError "actual canonical row: original row index missing"
        let nativeRow := mkAppN ((familyBody.beta D.getAppArgs).headBeta) i |>.headBeta
        unless nativeRow.isAppOfArity `JanetCartan.PhysicalSampling.OriginalMeasuredFamily.Row.kernel 64 do
          throwError "actual canonical row: original measured kernel64 changed"
        let row := mkAppN (mkConst actualFamily) (xs ++ i)
        storeActual `JanetCartan.PhysicalMean.OriginalCanonicalRow.D_row (xs ++ i)
          (← mkEqRefl nativeRow) (← mkEq row nativeRow) false
        logInfo "actual canonical D_row51: literal SAME Row.kernel64, original native scalar/uncut response/rate retained"
  else throwError "actual canonical row: unknown retained family field"

end JanetCartan.PhysicalMean.OriginalCanonicalRow
end

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 32000
set_option backward.isDefEq.respectTransparency false

retain_original_canonical_measured_family 0
retain_original_canonical_measured_family 1

