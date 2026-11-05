module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification.TimeSpace
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets.Coordinates

/-!
# Fixed-frequency diagonal primitives for the complete elliptic term

The source integrations in `app:ch_response:eq:direct-envelope-profile` hold
the entire physical covector fixed.  A two-time auxiliary expression can
therefore encode an arbitrary full-covector elliptic symbol at that frequency.
The statements below retain its temporal component.  Their consumer is the
outside-annulus source-kernel estimate for the same elliptic PDO.
-/

@[expose] public noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.FullEllipticResidualEnvelopes
open JanetCartan.RegularSector.Characteristic.EvolutionIntegral
open JanetCartan.RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets
open JanetCartan.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification

variable {d r : ℕ}
local notation "E" => Euclidean (d+1)
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ

/-- Reconstruct the physical position from the joint two-time variables.
The source time and the auxiliary spatial covector do not enter this map.
Consumer: the fixed-frequency elliptic source kernel in
`app:ch_response:eq:direct-envelope-profile`. -/
def frozenFrequencyPosition : TwoTimePoint d →L[ℝ] E :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p ↦ timeSpacePoint p.1.1 p.1.2.2
      map_add' := by
        intro p q
        ext i
        refine Fin.cases ?_ (fun j ↦ ?_) i <;> rfl
      map_smul' := by
        intro t p
        ext i
        refine Fin.cases ?_ (fun j ↦ ?_) i <;> rfl }

/-- The reconstruction uses the original physical position, including its
time coordinate (`app:ch_response:eq:direct-envelope-profile`). -/
@[simp] theorem frozenFrequencyPosition_elapsed (t : ℝ) (y ξ : E) :
    frozenFrequencyPosition (elapsedPoint t ((y, 0), ξ)) = y := by
  change timeSpacePoint (elapsedPoint t ((y, 0), ξ)).1.1
    (elapsedPoint t ((y, 0), ξ)).1.2.2 = y
  simp only [elapsedPoint_eq]
  exact timeSpaceMeasurableEquiv.symm_apply_apply y

/-- Auxiliary diagonal phase at one fixed full physical frequency.  This
definition is used only under that fixed-frequency source integral; it is not
a replacement phase for the elliptic operator
(`app:ch_response:eq:direct-envelope-profile`). -/
def frozenFrequencyDiagonalPhase (ξ : E) : TwoTimePhase d :=
  fun _ _ y _ ↦ inner ℝ y (spatialPart ξ)

/-- An arbitrary full physical symbol at one fixed frequency, before the
two physical masks (`app:ch_response:eq:direct-envelope-profile`). -/
def frozenFrequencyDiagonalAmplitude (a : E → E → Mat) (ξ : E) :
    TwoTimeAmplitude d r := fun t _ y _ ↦ a (timeSpacePoint t y) ξ

/-- Exact diagonal phase at the same fixed frequency.  In particular the
temporal covector has not been suppressed
(`app:ch_response:eq:direct-envelope-profile`). -/
@[simp] theorem elapsedPhase_frozenFrequencyDiagonalPhase (ξ y : E) :
    elapsedPhase (frozenFrequencyDiagonalPhase ξ) 0 y ξ = inner ℝ y ξ := by
  simp only [elapsedPhase, frozenFrequencyDiagonalPhase, sub_zero,
    inner_eq_time_add_spatial]

/-- Exact complete physical amplitude at the same fixed frequency.  No
annular selector or frequency truncation occurs in this identity
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem elapsedAmplitude_frozenFrequencyDiagonalAmplitude
    (a : E → E → Mat) (χout χsource : E → ℂ) (ξ y z : E) :
    elapsedAmplitude (frozenFrequencyDiagonalAmplitude a ξ)
      χout χsource (fun _ ↦ 1) 0 y z ξ = (χout y * χsource z) • a y ξ := by
  simp only [elapsedAmplitude, frozenFrequencyDiagonalAmplitude, mul_one]
  rw [show timeSpacePoint (y 0) (spatialPart y) = y from
    timeSpaceMeasurableEquiv.symm_apply_apply y]

private def frozenFrequencySpatialProjection : TwoTimePoint d →L[ℝ] Euclidean d :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p ↦ p.1.2.2
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }

private theorem norm_frozenFrequencySpatialProjection_le :
    ‖frozenFrequencySpatialProjection (d := d)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro p
  change ‖p.1.2.2‖ ≤ 1 * ‖p‖
  rw [one_mul]
  exact (norm_snd_le p.1.2).trans ((norm_snd_le p.1).trans (norm_fst_le p))

private def frozenFrequencyPhaseLinear (ξ : E) : TwoTimePoint d →L[ℝ] ℝ :=
  (InnerProductSpace.toDual ℝ (Euclidean d) (spatialPart ξ)).comp
    frozenFrequencySpatialProjection

private theorem jointPhase_frozen_eq (ξ : E) :
    jointPhase (frozenFrequencyDiagonalPhase ξ) = frozenFrequencyPhaseLinear ξ := by
  funext p
  exact real_inner_comm _ _

private theorem norm_frozenFrequencyPhaseLinear_le (ξ : E) :
    ‖frozenFrequencyPhaseLinear ξ‖ ≤ ‖ξ‖ := by
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  calc
    _ ≤ ‖spatialPart ξ‖ * 1 := by
      rw [LinearIsometryEquiv.norm_map]
      exact mul_le_mul_of_nonneg_left norm_frozenFrequencySpatialProjection_le (norm_nonneg _)
    _ ≤ ‖ξ‖ := by simpa using norm_spatialPart_le ξ

/-- The fixed diagonal auxiliary phase is globally smooth
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem contDiff_jointPhase_frozenFrequencyDiagonalPhase (ξ : E) :
    ContDiff ℝ ∞ (jointPhase (frozenFrequencyDiagonalPhase ξ)) := by
  rw [jointPhase_frozen_eq]
  exact (frozenFrequencyPhaseLinear ξ).contDiff

/-- All original phase jets are bounded without a frequency restriction.
The profile is linear in the complete covector, including its time component
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem norm_jet_jointPhase_frozenFrequencyDiagonalPhase
    {R : ℝ} (hR : 0 ≤ R) (ξ y : E) (hy : ‖y‖ ≤ R) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (jointPhase (frozenFrequencyDiagonalPhase ξ))
      (elapsedPoint 0 ((y, 0), ξ))‖ ≤ (R+1) * (1+‖ξ‖) := by
  rw [jointPhase_frozen_eq]
  let l := frozenFrequencyPhaseLinear ξ
  have hd : fderiv ℝ (frozenFrequencyPhaseLinear ξ) =
      fun _ ↦ frozenFrequencyPhaseLinear ξ := by
    funext z
    exact (frozenFrequencyPhaseLinear ξ).hasFDerivAt.fderiv
  have hv : ‖l (elapsedPoint 0 ((y, 0), ξ))‖ ≤ R * ‖ξ‖ := by
    change ‖inner ℝ (spatialPart ξ) (elapsedPoint 0 ((y, 0), ξ)).1.2.2‖ ≤ _
    simp only [elapsedPoint_eq]
    exact (norm_inner_le_norm _ _).trans
      ((mul_le_mul (norm_spatialPart_le ξ) ((norm_spatialPart_le y).trans hy)
        (norm_nonneg _) (norm_nonneg _)).trans_eq (mul_comm _ _))
  have hl : ‖l‖ ≤ ‖ξ‖ := norm_frozenFrequencyPhaseLinear_le ξ
  cases k with
  | zero =>
      rw [norm_iteratedFDeriv_zero]
      exact hv.trans (by nlinarith [norm_nonneg ξ])
  | succ k =>
      rw [← norm_iteratedFDeriv_fderiv, hd]
      cases k with
      | zero =>
          rw [norm_iteratedFDeriv_zero]
          exact hl.trans (by nlinarith [norm_nonneg ξ])
      | succ k =>
          rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero k), Pi.zero_apply, norm_zero]
          positivity

/-- The higher source-phase derivatives of the frozen diagonal primitive
vanish exactly.  The annular source integral thus incurs no additional
phase reserve (`app:ch_response:eq:direct-envelope-profile`). -/
theorem norm_higher_jet_jointPhase_frozenFrequencyDiagonalPhase
    (ξ : E) (p : TwoTimePoint d) {k : ℕ} (hk : 1 ≤ k) :
    ‖iteratedFDeriv ℝ (k+1) (jointPhase (frozenFrequencyDiagonalPhase ξ)) p‖ = 0 := by
  have hd : fderiv ℝ (frozenFrequencyPhaseLinear ξ) =
      fun _ ↦ frozenFrequencyPhaseLinear ξ := by
    funext z
    exact (frozenFrequencyPhaseLinear ξ).hasFDerivAt.fderiv
  rw [jointPhase_frozen_eq, ← norm_iteratedFDeriv_fderiv, hd]
  rw [iteratedFDeriv_const_of_ne (by omega : k ≠ 0), Pi.zero_apply, norm_zero]

/-- Joint smoothness of the auxiliary amplitude follows from the original
full symbol.  Only a fixed frequency is substituted
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem contDiff_jointAmplitude_frozenFrequencyDiagonalAmplitude
    (a : E → E → Mat) (ha : ContDiff ℝ ∞ (Function.uncurry a)) (ξ : E) :
    ContDiff ℝ ∞ (jointAmplitude (frozenFrequencyDiagonalAmplitude a ξ)) := by
  exact ha.comp (frozenFrequencyPosition.contDiff.prodMk contDiff_const)

/-- The fixed-frequency joint amplitude jets use only the physical symbol
jets, with a fixed linear-coordinate cost independent of frequency.  This
allows the complete temporal covector to remain in the elliptic symbol
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem norm_jet_jointAmplitude_frozenFrequencyDiagonalAmplitude
    (a : E → E → Mat) (ha : ContDiff ℝ ∞ (Function.uncurry a))
    (ξ : E) (p : TwoTimePoint d) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (jointAmplitude (frozenFrequencyDiagonalAmplitude a ξ)) p‖ ≤
      ‖iteratedFDeriv ℝ k (fun y ↦ a y ξ) (frozenFrequencyPosition p)‖ *
        ‖frozenFrequencyPosition (d := d)‖ ^ k := by
  let aξ := fun y ↦ a y ξ
  have hs : ContDiff ℝ ∞ aξ := ha.comp (contDiff_id.prodMk contDiff_const)
  change ‖iteratedFDeriv ℝ k (aξ ∘ frozenFrequencyPosition) p‖ ≤ _
  rw [frozenFrequencyPosition.iteratedFDeriv_comp_right hs p (by simp)]
  simpa using (iteratedFDeriv ℝ k aξ (frozenFrequencyPosition p)).norm_compContinuousLinearMap_le
    (fun _ : Fin k ↦ frozenFrequencyPosition (d := d))

end JanetCartan.ResponseTransfer.FullEllipticResidualEnvelopes
