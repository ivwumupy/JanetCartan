module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.PhysicalKernel
public import JanetCartan.Analysis.Microlocal.AmplitudeBound.Periodization

/-!
# Compact Euclidean amplitudes on a normalized physical box

Connect the quantitative periodization and the operator estimates for
`app:ch_osc:lem:osc-amplitude`. All analytic assumptions below concern the
original Euclidean amplitude. The box is normalized to lie strictly inside the
unit cell; rescaling arbitrary fixed boxes is a separate step.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal ContDiff

namespace JanetCartan.AmplitudeBound

variable {d : ℕ} {X : Type*} [MeasurableSpace X]

/-- The two physical positions concatenated in the auxiliary Euclidean space
of `app:ch_osc:lem:osc-amplitude`. -/
def pairedPosition (x y : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin (2 * d)) :=
  WithLp.toLp 2 (fun i ↦ if hi : i.val < d then x ⟨i.val, hi⟩
    else y ⟨i.val - d, by omega⟩)

/-- The product cell is the physical cell used to periodize two-position
amplitudes (`app:ch_osc:lem:osc-amplitude`). -/
theorem pairedPosition_mem_fundamentalCell
    {x y : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ fundamentalCell d) (hy : y ∈ fundamentalCell d) :
    pairedPosition x y ∈ fundamentalCell (2 * d) := by
  intro i
  by_cases hi : i.val < d
  · simpa only [pairedPosition, PiLp.toLp_apply, dite_eq_left hi] using hx ⟨i.val, hi⟩
  · simpa only [pairedPosition, PiLp.toLp_apply, dite_eq_right hi] using
      hy ⟨i.val - d, by omega⟩

/-- Each position of a pair in the centered cell belongs to its own cell
(`app:ch_osc:lem:osc-amplitude`). -/
theorem pairedPosition_mem_fundamentalCell_iff
    (x y : EuclideanSpace ℝ (Fin d)) :
    pairedPosition x y ∈ fundamentalCell (2 * d) ↔
      x ∈ fundamentalCell d ∧ y ∈ fundamentalCell d := by
  constructor
  · intro h
    constructor
    · intro i
      have hi : i.val < d := i.isLt
      simpa only [pairedPosition, PiLp.toLp_apply, dite_eq_left hi] using
        h ⟨i.val, by omega⟩
    · intro i
      have hi : ¬d + i.val < d := by omega
      simpa only [pairedPosition, PiLp.toLp_apply, dite_eq_right hi, Nat.add_sub_cancel_left]
        using h ⟨d + i.val, by omega⟩
  · rintro ⟨hx, hy⟩
    exact pairedPosition_mem_fundamentalCell hx hy

/-- The outer cutoff removing periodic copies in the normalized-box case of
`app:ch_osc:lem:osc-amplitude`. No smoothness of this multiplication cutoff is needed. -/
def physicalCellCutoff (x : EuclideanSpace ℝ (Fin d)) : ℂ :=
  (fundamentalCell d).indicator (fun _ ↦ 1) x

/-- Measurability of the fixed outer cutoff (`app:ch_osc:lem:osc-amplitude`). -/
theorem aestronglyMeasurable_physicalCellCutoff :
    AEStronglyMeasurable (physicalCellCutoff (d := d)) :=
  aestronglyMeasurable_const.indicator (isCompact_fundamentalCell d).measurableSet

/-- The outer cutoff is contractive (`app:ch_osc:lem:osc-amplitude`). -/
theorem norm_physicalCellCutoff_le (x : EuclideanSpace ℝ (Fin d)) :
    ‖physicalCellCutoff x‖ ≤ 1 := by
  exact (norm_indicator_le_norm_self _ x).trans_eq (norm_one (α := ℂ))

/-- The outer cutoff has compact support (`app:ch_osc:lem:osc-amplitude`). -/
theorem hasCompactSupport_physicalCellCutoff :
    HasCompactSupport (physicalCellCutoff (d := d)) :=
  HasCompactSupport.intro (isCompact_fundamentalCell d) fun _ hx ↦
    Set.indicator_of_notMem hx _

/-- Compatibility of the physical pair and the two modulation charts in
`app:ch_osc:lem:osc-amplitude`. -/
theorem torusQuotient_pairedPosition (x y : EuclideanSpace ℝ (Fin d)) :
    torusQuotient (pairedPosition x y) = leftPositionChart 1 x + rightPositionChart 1 y := by
  funext i
  by_cases hi : i.val < d <;>
    simp [torusQuotient, pairedPosition, leftPositionChart, rightPositionChart,
      scaledTorusChart, hi]

/-- The physical derivative assumptions give the summable coefficient decay
for the original compact Euclidean amplitude (`app:ch_osc:lem:osc-amplitude`). -/
theorem norm_mFourierCoeff_amplitudePeriodization_le_twoPositionWeight
    (hd : 0 < d) {r : ℝ} (hr : r < 1 / 2)
    {b : EuclideanSpace ℝ (Fin (2 * d)) → ℂ}
    (hs : SupportedInCenteredBox r b) (hf : ContDiff ℝ ∞ b) {A : ℝ}
    (hzero : ∀ x, ‖b x‖ ≤ A)
    (hderiv : ∀ i x,
      ‖euclideanCoordinateDerivList (List.replicate (2 * (d + 1)) i) b x‖ ≤ A)
    (k : Fin (2 * d) → ℤ) :
    ‖UnitAddTorus.mFourierCoeff (amplitudePeriodization b) k‖ ≤
      (smoothCoefficientConstant d * A) * twoPositionWeight d k :=
  norm_mFourierCoeff_le_twoPositionWeight hd
    (isSmoothPeriodic_amplitudePeriodization hr hs hf)
    (norm_amplitudePeriodization_le hzero)
    (fun i ↦ norm_coordinateDerivList_amplitudePeriodization_le hr hs hf _ (hderiv i)) k

/-- Fourier reconstruction agrees with the original Euclidean two-position
amplitude throughout the physical cell (`app:ch_osc:lem:osc-amplitude`). -/
theorem hasSum_compactAmplitude_expansion
    (hd : 0 < d) {r : ℝ} (hr : r < 1 / 2)
    {b : EuclideanSpace ℝ (Fin (2 * d)) → ℂ}
    (hs : SupportedInCenteredBox r b) (hf : ContDiff ℝ ∞ b) {A : ℝ}
    (hzero : ∀ x, ‖b x‖ ≤ A)
    (hderiv : ∀ i x,
      ‖euclideanCoordinateDerivList (List.replicate (2 * (d + 1)) i) b x‖ ≤ A)
    (χ ψ : EuclideanSpace ℝ (Fin d) → ℂ)
    {x y : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ fundamentalCell d) (hy : y ∈ fundamentalCell d) :
    HasSum (fun k ↦ (χ x * UnitAddTorus.mFourier k (leftPositionChart 1 x)) *
      UnitAddTorus.mFourierCoeff (amplitudePeriodization b) k *
      (ψ y * UnitAddTorus.mFourier k (rightPositionChart 1 y)))
      (χ x * b (pairedPosition x y) * ψ y) := by
  have he : amplitudePeriodization b (leftPositionChart 1 x + rightPositionChart 1 y) =
      b (pairedPosition x y) := by
    rw [← torusQuotient_pairedPosition]
    exact periodicLift_amplitudePeriodization_eq hr hs (pairedPosition_mem_fundamentalCell hx hy)
  simpa only [he] using hasSum_cutoff_twoPosition_expansion hd
    (isSmoothPeriodic_amplitudePeriodization hr hs hf)
    (norm_amplitudePeriodization_le hzero)
    (fun i ↦ norm_coordinateDerivList_amplitudePeriodization_le hr hs hf _ (hderiv i))
    1 χ ψ x y

/-- The fixed outer cutoffs remove every periodic copy and preserve the original
compact amplitude at every pair of physical positions (`app:ch_osc:lem:osc-amplitude`). -/
theorem physicalCellCutoff_amplitudePeriodization_eq
    {r : ℝ} (hr : r < 1 / 2)
    {b : EuclideanSpace ℝ (Fin (2 * d)) → ℂ} (hs : SupportedInCenteredBox r b)
    (x y : EuclideanSpace ℝ (Fin d)) :
    physicalCellCutoff x *
      amplitudePeriodization b (leftPositionChart 1 x + rightPositionChart 1 y) *
      physicalCellCutoff y = b (pairedPosition x y) := by
  have hcell (h : b (pairedPosition x y) ≠ 0) :
      x ∈ fundamentalCell d ∧ y ∈ fundamentalCell d := by
    apply (pairedPosition_mem_fundamentalCell_iff x y).mp
    intro i
    exact abs_le.mp ((hs _ h i).trans hr.le)
  by_cases hx : x ∈ fundamentalCell d
  · by_cases hy : y ∈ fundamentalCell d
    · simp only [physicalCellCutoff, Set.indicator_of_mem hx, Set.indicator_of_mem hy,
        one_mul, mul_one, ← torusQuotient_pairedPosition]
      exact periodicLift_amplitudePeriodization_eq hr hs
        (pairedPosition_mem_fundamentalCell hx hy)
    · have hb : b (pairedPosition x y) = 0 := by
        by_contra hb
        exact hy (hcell hb).2
      simp [physicalCellCutoff, hy, hb]
  · have hb : b (pairedPosition x y) = 0 := by
      by_contra hb
      exact hx (hcell hb).1
    simp [physicalCellCutoff, hx, hb]

/-- Global exact Fourier expansion of the original compact Euclidean amplitude
with the fixed outer cutoffs (`app:ch_osc:lem:osc-amplitude`). -/
theorem hasSum_compactAmplitude_cellCutoff_expansion
    (hd : 0 < d) {r : ℝ} (hr : r < 1 / 2)
    {b : EuclideanSpace ℝ (Fin (2 * d)) → ℂ}
    (hs : SupportedInCenteredBox r b) (hf : ContDiff ℝ ∞ b) {A : ℝ}
    (hzero : ∀ x, ‖b x‖ ≤ A)
    (hderiv : ∀ i x,
      ‖euclideanCoordinateDerivList (List.replicate (2 * (d + 1)) i) b x‖ ≤ A)
    (x y : EuclideanSpace ℝ (Fin d)) :
    HasSum (fun k ↦
      (physicalCellCutoff x * UnitAddTorus.mFourier k (leftPositionChart 1 x)) *
      UnitAddTorus.mFourierCoeff (amplitudePeriodization b) k *
      (physicalCellCutoff y * UnitAddTorus.mFourier k (rightPositionChart 1 y)))
      (b (pairedPosition x y)) := by
  simpa only [physicalCellCutoff_amplitudePeriodization_eq hr hs] using
    hasSum_cutoff_twoPosition_expansion hd
      (isSmoothPeriodic_amplitudePeriodization hr hs hf)
      (norm_amplitudePeriodization_le hzero)
      (fun i ↦ norm_coordinateDerivList_amplitudePeriodization_le hr hs hf _ (hderiv i))
      1 physicalCellCutoff physicalCellCutoff x y

section Operator

variable (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
  (hb : StronglyMeasurable (Function.uncurry b)) (hd : 0 < d)
  {r : ℝ} (hr : r < 1 / 2) (hs : ∀ ξ, SupportedInCenteredBox r (b ξ))
  (hf : ∀ ξ, ContDiff ℝ ∞ (b ξ)) (A : ℝ)
  (hzero : ∀ ξ x, ‖b ξ x‖ ≤ A)
  (hderiv : ∀ ξ i x,
    ‖euclideanCoordinateDerivList (List.replicate (2 * (d + 1)) i) (b ξ) x‖ ≤ A)
  (χ ψ : EuclideanSpace ℝ (Fin d) → ℂ)
  (hχ : AEStronglyMeasurable χ) (hψ : AEStronglyMeasurable ψ)
  (hχbound : ∀ᵐ x, ‖χ x‖ ≤ 1) (hψbound : ∀ᵐ y, ‖ψ y‖ ≤ 1)

/-- The bounded operator series constructed from a compact Euclidean amplitude
in a normalized box (`app:ch_osc:lem:osc-amplitude`). Its finite kernel
regularizations are the ones in `regularizedPhysicalAmplitudeKernel`. -/
def compactPhysicalAmplitudeOperator :
    Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2 →L[ℂ] Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2 :=
  physicalAmplitudeOperator (fun ξ ↦ amplitudePeriodization (b ξ))
    (stronglyMeasurable_amplitudePeriodization hb) hd
    (fun ξ ↦ isSmoothPeriodic_amplitudePeriodization hr (hs ξ) (hf ξ)) A
    (fun ξ ↦ norm_amplitudePeriodization_le (hzero ξ))
    (fun ξ i ↦ norm_coordinateDerivList_amplitudePeriodization_le hr (hs ξ) (hf ξ)
      _ (hderiv ξ i)) 1 χ ψ hχ hψ hχbound hψbound

/-- The scalar series bound for compact Euclidean amplitudes in a normalized
physical box (`app:ch_osc:lem:osc-amplitude`). The hypotheses are support,
measurability, smoothness, and physical derivative bounds of the original
amplitude, with no assumed coefficient estimates. -/
theorem norm_compactPhysicalAmplitudeOperator_le :
    ‖compactPhysicalAmplitudeOperator b hb hd hr hs hf A hzero hderiv χ ψ
      hχ hψ hχbound hψbound‖ ≤
      (coefficientSumConstant d * smoothCoefficientConstant d) * A :=
  norm_physicalAmplitudeOperator_le ..

/-- The literal finite integrals for a compact Euclidean amplitude converge to
the constructed operator as tempered distributions (`app:ch_osc:lem:osc-amplitude`).
The only additional physical condition is compact support of the input cutoff. -/
theorem tendsto_compactPhysicalAmplitudeKernel_temperedDistribution
    (hψcompact : HasCompactSupport ψ)
    {β : Type*} {m : Filter β} (s : β → Finset (Fin (2 * d) → ℤ)) (ρ : β → ℝ)
    (hsexhaust : ∀ k, ∀ᶠ j in m, k ∈ s j) (hρ : Filter.Tendsto ρ m Filter.atTop)
    (f : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2) :
    Filter.Tendsto (fun j ↦ Lp.toTemperedDistribution
      (regularizedPhysicalAmplitudeKernelLp (fun ξ ↦ amplitudePeriodization (b ξ))
        (stronglyMeasurable_amplitudePeriodization hb) hd
        (fun ξ ↦ isSmoothPeriodic_amplitudePeriodization hr (hs ξ) (hf ξ)) A
        (fun ξ ↦ norm_amplitudePeriodization_le (hzero ξ))
        (fun ξ i ↦ norm_coordinateDerivList_amplitudePeriodization_le hr (hs ξ) (hf ξ)
          _ (hderiv ξ i))
        1 χ ψ hχ hψ hχbound hψbound hψcompact (s j) (ρ j) f)) m
      (nhds (Lp.toTemperedDistribution (compactPhysicalAmplitudeOperator b hb hd hr hs hf A
        hzero hderiv χ ψ hχ hψ hχbound hψbound f))) :=
  tendsto_regularizedPhysicalAmplitudeKernel_temperedDistribution
    (fun ξ ↦ amplitudePeriodization (b ξ))
    (stronglyMeasurable_amplitudePeriodization hb) hd
    (fun ξ ↦ isSmoothPeriodic_amplitudePeriodization hr (hs ξ) (hf ξ)) A
    (fun ξ ↦ norm_amplitudePeriodization_le (hzero ξ))
    (fun ξ i ↦ norm_coordinateDerivList_amplitudePeriodization_le hr (hs ξ) (hf ξ)
      _ (hderiv ξ i)) 1 χ ψ hχ hψ hχbound hψbound hψcompact s ρ hsexhaust hρ f

end Operator

end JanetCartan.AmplitudeBound
