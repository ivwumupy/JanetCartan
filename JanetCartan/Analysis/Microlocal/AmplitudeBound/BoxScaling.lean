module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.CompactAmplitude
/-!
# Scaling arbitrary physical boxes to the auxiliary torus

For `app:ch_osc:lem:osc-amplitude`, enlarge any fixed bounded physical box,
rescale its amplitude, and periodize. The derivative loss depends only on the
fixed scale. The outer cutoffs remove every periodic copy exactly.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff
namespace JanetCartan.AmplitudeBound
variable {n : ℕ}
/-- Ordered physical derivatives obey the exact dilation rule in
`app:ch_osc:lem:osc-amplitude`. -/
theorem euclideanCoordinateDerivList_comp_smul {f : EuclideanSpace ℝ (Fin n) → ℂ} (hf : ContDiff ℝ ∞ f)
    (ℓ : ℝ) (is : List (Fin n)) :
    euclideanCoordinateDerivList is (fun z ↦ f (ℓ • z)) =
      fun z ↦ ℓ ^ is.length • euclideanCoordinateDerivList is f (ℓ • z) := by
  induction is with
  | nil => simp [euclideanCoordinateDerivList]
  | cons i is ih =>
    funext z
    simp only [euclideanCoordinateDerivList, ih]
    have hd := (contDiff_euclideanCoordinateDerivList hf is).differentiable (by simp)
    have hc := (hd (ℓ • z)).hasFDerivAt.comp z
      ((hasFDerivAt_id z).const_smul ℓ)
    have hcc : HasFDerivAt
        (fun w ↦ ℓ ^ is.length • euclideanCoordinateDerivList is f (ℓ • w))
        ((ℓ ^ is.length) • (fderiv ℝ (euclideanCoordinateDerivList is f) (ℓ • z)).comp
          (ℓ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))) z := by
      convert hc.const_smul (ℓ ^ is.length) using 1
      funext w
      simp
    rw [hcc.fderiv]
    simp [pow_succ, mul_smul]

/-- Physical dilation puts a fixed support strictly inside the unit cell in
`app:ch_osc:lem:osc-amplitude`. -/
theorem supportedInCenteredBox_comp_smul {f : EuclideanSpace ℝ (Fin n) → ℂ}
    {R ℓ : ℝ} (hℓ : 0 < ℓ) (hs : SupportedInCenteredBox R f) :
    SupportedInCenteredBox (R / ℓ) (fun z ↦ f (ℓ • z)) := by
  intro z hz i
  apply (le_div_iff₀ hℓ).mpr
  have h := hs (ℓ • z) hz i
  simpa only [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hℓ, mul_comm] using h

/-- Periodization on a physical box of side length `ℓ` for
`app:ch_osc:lem:osc-amplitude`. -/
def boxAmplitudePeriodization (ℓ : ℝ) (f : EuclideanSpace ℝ (Fin n) → ℂ) :
    Torus n → ℂ := amplitudePeriodization (fun z ↦ f (ℓ • z))

/-- Enlarging the box gives a smooth periodic amplitude
(`app:ch_osc:lem:osc-amplitude`). -/
theorem isSmoothPeriodic_boxAmplitudePeriodization {f : EuclideanSpace ℝ (Fin n) → ℂ}
    {R ℓ : ℝ} (hℓ : 0 < ℓ) (hR : R / ℓ < 1 / 2)
    (hs : SupportedInCenteredBox R f) (hf : ContDiff ℝ ∞ f) :
    IsSmoothPeriodic (boxAmplitudePeriodization ℓ f) :=
  isSmoothPeriodic_amplitudePeriodization hR (supportedInCenteredBox_comp_smul hℓ hs)
    (hf.comp (contDiff_const_smul ℓ))

/-- Physical dilation and periodization preserve parameter measurability
(`app:ch_osc:lem:osc-amplitude`). -/
theorem stronglyMeasurable_boxAmplitudePeriodization {X : Type*} [MeasurableSpace X]
    {b : X → EuclideanSpace ℝ (Fin n) → ℂ}
    (hb : StronglyMeasurable (Function.uncurry b)) (ℓ : ℝ) :
    StronglyMeasurable (Function.uncurry (fun ξ ↦ boxAmplitudePeriodization ℓ (b ξ))) :=
  stronglyMeasurable_amplitudePeriodization (by
    have hm : Measurable (fun p : X × EuclideanSpace ℝ (Fin n) ↦ (p.1, ℓ • p.2)) := by
      fun_prop
    exact hb.comp_measurable hm)

/-- Zeroth order bounds are unchanged by dilation and periodization
(`app:ch_osc:lem:osc-amplitude`). -/
theorem norm_boxAmplitudePeriodization_le {f : EuclideanSpace ℝ (Fin n) → ℂ}
    {A : ℝ} (hA : ∀ z, ‖f z‖ ≤ A) (ℓ : ℝ) (z : Torus n) :
    ‖boxAmplitudePeriodization ℓ f z‖ ≤ A := norm_amplitudePeriodization_le (fun _ ↦ hA _) z

/-- Each ordered derivative gains precisely the fixed scale to its order in
`app:ch_osc:lem:osc-amplitude`. -/
theorem norm_coordinateDerivList_boxAmplitudePeriodization_le
    {f : EuclideanSpace ℝ (Fin n) → ℂ} {R ℓ : ℝ}
    (hℓ : 0 < ℓ) (hR : R / ℓ < 1 / 2)
    (hs : SupportedInCenteredBox R f) (hf : ContDiff ℝ ∞ f)
    (is : List (Fin n)) {A : ℝ} (hA : ∀ z, ‖euclideanCoordinateDerivList is f z‖ ≤ A)
    (z : Torus n) :
    ‖periodicCoordinateDerivList is (boxAmplitudePeriodization ℓ f) z‖ ≤ |ℓ| ^ is.length * A := by
  apply norm_coordinateDerivList_amplitudePeriodization_le hR
    (supportedInCenteredBox_comp_smul hℓ hs) (hf.comp (contDiff_const_smul ℓ))
  intro x
  rw [euclideanCoordinateDerivList_comp_smul hf, norm_smul, Real.norm_eq_abs, abs_pow]
  exact mul_le_mul_of_nonneg_left (hA _) (by positivity)

variable {d : ℕ}

/-- The fixed physical-box cutoff used in `app:ch_osc:lem:osc-amplitude`. -/
def boxCellCutoff (ℓ : ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℂ :=
  physicalCellCutoff (ℓ⁻¹ • x)

/-- Measurability of the physical-box cutoff (`app:ch_osc:lem:osc-amplitude`). -/
theorem aestronglyMeasurable_boxCellCutoff (ℓ : ℝ) :
    AEStronglyMeasurable (boxCellCutoff (d := d) ℓ) :=
  by
    have hm : Measurable (fun x : EuclideanSpace ℝ (Fin d) ↦ ℓ⁻¹ • x) := by fun_prop
    exact (((stronglyMeasurable_const (b := (1 : ℂ))).indicator
      (isCompact_fundamentalCell d).measurableSet).comp_measurable hm).aestronglyMeasurable

/-- The physical-box cutoff is contractive (`app:ch_osc:lem:osc-amplitude`). -/
theorem norm_boxCellCutoff_le (ℓ : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    ‖boxCellCutoff ℓ x‖ ≤ 1 := norm_physicalCellCutoff_le _

/-- The enlarged physical-box cutoff is compactly supported
(`app:ch_osc:lem:osc-amplitude`). -/
theorem hasCompactSupport_boxCellCutoff {ℓ : ℝ} (hℓ : ℓ ≠ 0) :
    HasCompactSupport (boxCellCutoff (d := d) ℓ) :=
  hasCompactSupport_physicalCellCutoff.comp_smul (inv_ne_zero hℓ)

/-- Pairing physical positions commutes with dilation
(`app:ch_osc:lem:osc-amplitude`). -/
theorem pairedPosition_smul (ℓ : ℝ) (x y : EuclideanSpace ℝ (Fin d)) :
    pairedPosition (ℓ • x) (ℓ • y) = ℓ • pairedPosition x y := by
  ext i
  by_cases hi : i.val < d <;> simp [pairedPosition, hi]

/-- The two charts on a general physical box equal the unit charts after
rescaling (`app:ch_osc:lem:osc-amplitude`). -/
theorem positionCharts_comp_smul (ℓ : ℝ) (x y : EuclideanSpace ℝ (Fin d)) :
    leftPositionChart 1 (ℓ⁻¹ • x) + rightPositionChart 1 (ℓ⁻¹ • y) =
      leftPositionChart ℓ x + rightPositionChart ℓ y := by
  funext i
  by_cases hi : i.val < d <;>
    simp [leftPositionChart, rightPositionChart, scaledTorusChart, hi]

/-- Outer cutoffs recover the original amplitude globally on arbitrary fixed
physical boxes (`app:ch_osc:lem:osc-amplitude`). -/
theorem boxCellCutoff_boxAmplitudePeriodization_eq
    {f : EuclideanSpace ℝ (Fin (2 * d)) → ℂ} {R ℓ : ℝ}
    (hℓ : 0 < ℓ) (hR : R / ℓ < 1 / 2) (hs : SupportedInCenteredBox R f)
    (x y : EuclideanSpace ℝ (Fin d)) :
    boxCellCutoff ℓ x * boxAmplitudePeriodization ℓ f
      (leftPositionChart ℓ x + rightPositionChart ℓ y) * boxCellCutoff ℓ y =
        f (pairedPosition x y) := by
  have h := physicalCellCutoff_amplitudePeriodization_eq hR
    (supportedInCenteredBox_comp_smul hℓ hs) (ℓ⁻¹ • x) (ℓ⁻¹ • y)
  simpa only [boxCellCutoff, boxAmplitudePeriodization, positionCharts_comp_smul, pairedPosition_smul, smul_smul,
    mul_inv_cancel₀ hℓ.ne', one_smul] using h

/-- A fixed-box derivative loss, independent of frequency support, in
`app:ch_osc:lem:osc-amplitude`. -/
def boxDerivativeFactor (d : ℕ) (ℓ : ℝ) : ℝ := 1 + |ℓ| ^ (2 * (d + 1))

/-- The box derivative loss is at least one (`app:ch_osc:lem:osc-amplitude`). -/
theorem one_le_boxDerivativeFactor (d : ℕ) (ℓ : ℝ) : 1 ≤ boxDerivativeFactor d ℓ := by
  exact le_add_of_nonneg_right (by positivity)

/-- The common zeroth order bound after periodization on any fixed box
(`app:ch_osc:lem:osc-amplitude`). -/
theorem norm_boxAmplitudePeriodization_le_factor
    {f : EuclideanSpace ℝ (Fin (2 * d)) → ℂ} {A : ℝ}
    (hA : ∀ z, ‖f z‖ ≤ A) (ℓ : ℝ) (z : Torus (2 * d)) :
    ‖boxAmplitudePeriodization ℓ f z‖ ≤ boxDerivativeFactor d ℓ * A :=
  (norm_boxAmplitudePeriodization_le hA ℓ z).trans
    (le_mul_of_one_le_left ((norm_nonneg (f 0)).trans (hA 0)) (one_le_boxDerivativeFactor d ℓ))

/-- The pure derivatives needed for the summable coefficient estimate have a
common bound depending only on the physical box (`app:ch_osc:lem:osc-amplitude`). -/
theorem norm_pureDeriv_boxAmplitudePeriodization_le_factor
    {f : EuclideanSpace ℝ (Fin (2 * d)) → ℂ} {R ℓ : ℝ}
    (hℓ : 0 < ℓ) (hR : R / ℓ < 1 / 2)
    (hs : SupportedInCenteredBox R f) (hf : ContDiff ℝ ∞ f) {A : ℝ}
    (hA : 0 ≤ A)
    (hderiv : ∀ i z,
      ‖euclideanCoordinateDerivList (List.replicate (2 * (d + 1)) i) f z‖ ≤ A)
    (i : Fin (2 * d)) (z : Torus (2 * d)) :
    ‖periodicCoordinateDerivList (List.replicate (2 * (d + 1)) i)
      (boxAmplitudePeriodization ℓ f) z‖ ≤ boxDerivativeFactor d ℓ * A := by
  apply (norm_coordinateDerivList_boxAmplitudePeriodization_le hℓ hR hs hf
    _ (hderiv i) z).trans
  apply mul_le_mul_of_nonneg_right _ hA
  simp only [List.length_replicate, boxDerivativeFactor]
  linarith

/-- Any fixed bounded centered box admits the strict enlargement used above
(`app:ch_osc:lem:osc-amplitude`). -/
theorem exists_boxPeriodization_scale (R : ℝ) : ∃ ℓ : ℝ, 0 < ℓ ∧ R / ℓ < 1 / 2 := by
  refine ⟨2 * |R| + 1, by positivity, ?_⟩
  apply (div_lt_iff₀ (by positivity : 0 < 2 * |R| + 1)).mpr
  linarith [le_abs_self R]

/-- Uniform support in any fixed bounded set gives a common centered-box
radius for `app:ch_osc:lem:osc-amplitude`; no centering assumption is needed. -/
theorem exists_supportedInCenteredBox_of_isBounded {X : Type*}
    {b : X → EuclideanSpace ℝ (Fin n) → ℂ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : Bornology.IsBounded K) (hs : ∀ ξ, Function.support (b ξ) ⊆ K) :
    ∃ R : ℝ, ∀ ξ, SupportedInCenteredBox R (b ξ) := by
  obtain ⟨R, hR⟩ := hK.exists_norm_le
  refine ⟨R, fun ξ z hz i ↦ ?_⟩
  exact (show |z i| ≤ ‖z‖ from (Real.norm_eq_abs _).symm ▸ PiLp.norm_apply_le z i).trans
    (hR z (hs ξ hz))

end JanetCartan.AmplitudeBound
