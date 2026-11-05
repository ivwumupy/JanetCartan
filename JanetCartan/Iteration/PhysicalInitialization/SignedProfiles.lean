module

public import JanetCartan.Iteration.PhysicalGeometry
public import JanetCartan.Geometry.IsometricEmbedding.Reference.Initialization.ScaledReference

/-!
# Original signed-source coefficients on the initialized physical history

The consumers are `original_signed_residual_decay_on_supplied_core` and the
same-source normalized inverse in paper-v2 `app:ch_regular:eq:initial-coefficient-profile`.
The actual fields are the prescribed affine extension of the current projected
frame and the FULL extended reduced zeroth coefficient. A common budget and
threshold precede every physical history, source slow scale and compact set.

The final initialized reference can have a smaller chart than the fixed source
coefficient ball. Its original wide chart is recovered by the deterministic
`sourceDilationReference` with the SAME map, not by another existential choice.
This closes the coefficient inputs, not the source inverse or mixed-word decay.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalInitialization

open GeometricProfile ProtectedFlow ProjectedStressFrame
open CurrentCoefficientProfiles ResponseTransfer.RetainedFactors

variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Coeff" => Fin (d + 1) → MetricTensor (d + 1)

/-- `main:prop:current-scale` and
`app:ch_regular:eq:initial-coefficient-profile`: actual physical admissibility
produces the original signed source's common Q/full-B coefficient budget.
The arbitrary supplied raw frame is retained only via its literal identity with
the projected frame of the SAME current map. No coefficient estimate is a premise. -/
theorem exists_signed_history_coefficient_inputs
    (Gref : FlatReference (d + 1)) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hR : R < Gref.domain.chartRadius)
    (ext : BallExtension.Parameters E) (hext : ext.center = 0) (hextRadius : ext.radius = r)
    {Cband : ℝ} (hband : 1 ≤ Cband) {rStar reserve kMin : ℕ}
    (hStar : 8 ≤ rStar) (hreserve : 2 + reserve ≤ rStar)
    (horder : RevisedScales.displacementLoss (d + 1) +
      bandExponent * ((rStar : ℝ) + ((d + 1 : ℕ) : ℝ) / 2) + 2 < (kMin : ℝ)) :
    ∃ threshold : ℝ, 2 ≤ threshold ∧ ∃ Aprofile : ℕ → ℝ,
      (∀ k, 0 ≤ Aprofile k) ∧
    ∀ (I : Type*) (R₀ L : I → ℝ), (∀ v, threshold ≤ R₀ v) →
    ∀ (j : I → ℕ)
      (history : ∀ v, Fin (j v) → SchwartzMap E (Euclidean (embeddingDimension (d + 1))))
      (ell : ∀ v, Fin (j v) → ℕ),
      (∀ v, RevisedGlobal.IsAdmissibleHistory Cband (R₀ v) kMin (history v) (ell v)) →
      (∀ v, currentCoefficientScale (R₀ v) (j v) ≤ L v) →
    ∀ Qraw : I → E → Coeff,
      (∀ v, Qraw v = projectedStress (RevisedGlobal.finiteMap Gref.map (history v))) →
    let F := fun v ↦ RevisedGlobal.finiteMap Gref.map (history v)
    let Q := fun v ↦ affineFrameExtension ext (Qraw v)
    let B := fun v ↦ reducedZerothProjection (d + 1) ∘
      extendedReducedCoefficients ext (fun _ _ ↦ 0) (F v)
    (∀ v, Q v = extendedProjectedStress ext (F v)) ∧
    (∀ v, ContDiff ℝ ∞ (Q v) ∧ ContDiff ℝ ∞ (B v)) ∧
    ∀ K : Set E, IsCompact K → ∀ v,
      HasDerivativeProfile K (Q v) reserve (L v) Aprofile ∧
      HasDerivativeProfile K (B v) reserve (L v) Aprofile := by
  obtain ⟨threshold, hthreshold, AQ, AB, hAQ, _hAB, hprofiles⟩ :=
    PhysicalGeometry.exists_retained_coefficient_profiles Gref hr hrR hR
      ext hext hextRadius hband hStar hreserve horder
  let Aprofile := fun k ↦ max (AQ k) (AB k)
  have hAprofile k : 0 ≤ Aprofile k := (hAQ k).trans (le_max_left _ _)
  refine ⟨threshold, hthreshold, Aprofile, hAprofile, ?_⟩
  intro I R₀ L hR₀ j history ell hhistory hslow Qraw hraw F Q B
  have hcoeff v := hprofiles (R₀ v) (hR₀ v) (j v) (history v) (ell v) (hhistory v)
  have hQeq v : Q v = extendedProjectedStress ext (F v) := by
    change affineFrameExtension ext (Qraw v) = _
    rw [hraw v]
    rfl
  refine ⟨hQeq, fun v ↦ ⟨(hQeq v).symm ▸ (hcoeff v).1, (hcoeff v).2.1⟩, ?_⟩
  intro K hK v
  have hcurrent : 1 ≤ currentCoefficientScale (R₀ v) (j v) :=
    one_le_currentCoefficientScale ((by norm_num : (1 : ℝ) ≤ 2).trans
      (hthreshold.trans (hR₀ v))) (j v)
  constructor <;> intro k
  · rw [hQeq v]
    exact (((hcoeff v).2.2 K hK).1 k).trans
      (mul_le_mul (le_max_left _ _)
        (pow_le_pow_left₀ (zero_le_one.trans hcurrent) (hslow v) _)
        (pow_nonneg (zero_le_one.trans hcurrent) _) (hAprofile k))
  · exact (((hcoeff v).2.2 K hK).2 k).trans
      (mul_le_mul (le_max_right _ _)
        (pow_le_pow_left₀ (zero_le_one.trans hcurrent) (hslow v) _)
        (pow_nonneg (zero_le_one.trans hcurrent) _) (hAprofile k))

/-- `main:eq:normalized` and the original signed-source coefficient input on
one prescribed final initializer. The source coefficient ball belongs to the
original wide chart. The final shrunken chart is NOT assumed to contain it;
the deterministic wide reference has literally the same `Gref.map`.
All estimates concern the original real physical increments and revised loss. -/
theorem exists_initialized_signed_history_coefficient_inputs
    (G₀ Gref : FlatReference (d + 1)) {σ : ℝ} (hσ : 0 < σ) (hσone : σ ≤ 1)
    (hmap : Gref.map = sourceDilation G₀.map σ)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) (hR : R < G₀.domain.chartRadius)
    (ext : BallExtension.Parameters E) (hext : ext.center = 0) (hextRadius : ext.radius = r)
    {Cband : ℝ} (hband : 1 ≤ Cband) {rStar reserve kMin : ℕ}
    (hStar : 8 ≤ rStar) (hreserve : 2 + reserve ≤ rStar)
    (horder : RevisedScales.displacementLoss (d + 1) +
      bandExponent * ((rStar : ℝ) + ((d + 1 : ℕ) : ℝ) / 2) + 2 < (kMin : ℝ)) :
    ∃ threshold : ℝ, 2 ≤ threshold ∧ ∃ Aprofile : ℕ → ℝ,
      (∀ k, 0 ≤ Aprofile k) ∧
    ∀ (I : Type*) (R₀ L : I → ℝ), (∀ v, threshold ≤ R₀ v) →
    ∀ (j : I → ℕ)
      (history : ∀ v, Fin (j v) → SchwartzMap E (Euclidean (embeddingDimension (d + 1))))
      (ell : ∀ v, Fin (j v) → ℕ),
      (∀ v, RevisedGlobal.IsAdmissibleHistory Cband (R₀ v) kMin (history v) (ell v)) →
      (∀ v, currentCoefficientScale (R₀ v) (j v) ≤ L v) →
    ∀ Qraw : I → E → Coeff,
      (∀ v, Qraw v = projectedStress (RevisedGlobal.finiteMap Gref.map (history v))) →
    let F := fun v ↦ RevisedGlobal.finiteMap Gref.map (history v)
    let Q := fun v ↦ affineFrameExtension ext (Qraw v)
    let B := fun v ↦ reducedZerothProjection (d + 1) ∘
      extendedReducedCoefficients ext (fun _ _ ↦ 0) (F v)
    (∀ v, Q v = extendedProjectedStress ext (F v)) ∧
    (∀ v, ContDiff ℝ ∞ (Q v) ∧ ContDiff ℝ ∞ (B v)) ∧
    ∀ K : Set E, IsCompact K → ∀ v,
      HasDerivativeProfile K (Q v) reserve (L v) Aprofile ∧
      HasDerivativeProfile K (B v) reserve (L v) Aprofile := by
  let Gwide := sourceDilationReference G₀ hσ hσone
  have hsame : Gwide.map = Gref.map := hmap.symm
  simpa only [hsame] using
    exists_signed_history_coefficient_inputs Gwide hr hrR hR
      ext hext hextRadius hband hStar hreserve horder

end JanetCartan.PhysicalInitialization
