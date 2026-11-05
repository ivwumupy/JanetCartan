module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.NormalizedSymbol.Transversality
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.ZeroEnergy
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.SymbolRegularity

/-!
# The actual degree-one determinant Hamilton symbol

The symbol in Step 1 of `app:ch_seed:prop:seed-actual-menu` is constructed
literally from the current stress frame. Its smoothness, homogeneity, Euler
identity and characteristic Hamilton-field identity are proved, not inputs.

The projected-frame producer must supply the smooth frame on an open physical
patch; the characteristic-root and pencil-continuity producers must supply the
determinant transverse gap on the chosen annulus. This module constructs no
Hamilton flow. The consumers `ActualCarriers` and compatible phase geometry must
instantiate these inputs and construct their charts separately.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ActualCarriers

open NormalizedSymbol HamiltonPhase

/-- The actual normalized determinant, bundled in the published Hamilton-phase
interface (`app:ch_seed:prop:seed-actual-menu`, Step 1). All differential fields
are computed from the scalar formula; frame smoothness is the sole analytic input. -/
def normalizedHomogeneousSymbol {n : ℕ} {Ω : Set (Euclidean n)} (hΩ : IsOpen Ω)
    (Q : Euclidean n → Fin n → MetricTensor n) (hQ : ContDiffOn ℝ ∞ Q Ω) :
    HomogeneousSymbol (Euclidean n) where
  domain := normalizedSymbolDomain Ω
  isOpen_domain := isOpen_normalizedSymbolDomain hΩ
  h := normalizedSymbol Q
  hx := physicalGradient (normalizedSymbol Q)
  hp := covectorGradient (normalizedSymbol Q)
  hpDerivative := fderiv ℝ (covectorGradient (normalizedSymbol Q))
  hasFDerivAt_h := by
    intro z hz
    rw [hamiltonDifferential_eq_fderiv]
    exact ((contDiffAt_normalizedSymbol (hQ.contDiffAt (hΩ.mem_nhds hz.1)) hz.2).differentiableAt
      (by simp)).hasFDerivAt
  hasFDerivAt_hp := by
    intro z hz
    exact ((contDiffAt_covectorGradient
      (contDiffAt_normalizedSymbol (hQ.contDiffAt (hΩ.mem_nhds hz.1)) hz.2)).differentiableAt
        (by simp)).hasFDerivAt
  homogeneous := by
    intro z _
    filter_upwards [eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)] with r hr
    exact normalizedSymbol_pos_homogeneous Q z hr

/-- The literal formula in the order expected by `carrierPhase_determinant_eq_zero`
(`app:ch_seed:prop:seed-actual-menu`, Step 1). -/
theorem normalizedHomogeneousSymbol_h {n : ℕ} {Ω : Set (Euclidean n)} (hΩ : IsOpen Ω)
    (Q : Euclidean n → Fin n → MetricTensor n) (hQ : ContDiffOn ℝ ∞ Q Ω)
    (z : Euclidean n × Euclidean n) :
    (normalizedHomogeneousSymbol hΩ Q hQ).h z =
      ‖z.2‖ ^ (1 - (n : ℤ)) * determinant (Q z.1) z.2 := by
  exact mul_comm _ _

/-- Euler's identity for the actual normalized determinant
(`app:lem:common-hamilton-phase` and `app:ch_seed:prop:seed-actual-menu`, Step 1). -/
theorem normalizedSymbol_euler {n : ℕ} {Ω : Set (Euclidean n)} (hΩ : IsOpen Ω)
    (Q : Euclidean n → Fin n → MetricTensor n) (hQ : ContDiffOn ℝ ∞ Q Ω)
    {z : Euclidean n × Euclidean n} (hz : z ∈ normalizedSymbolDomain Ω) :
    ⟪z.2, covectorGradient (normalizedSymbol Q) z⟫_ℝ = normalizedSymbol Q z :=
  (normalizedHomogeneousSymbol hΩ Q hQ).euler hz

/-- The Hamilton field is smooth on the punctured phase-space domain
(`app:lem:common-hamilton-phase`), as required by the separate local-flow producer. -/
theorem contDiffOn_normalizedHomogeneousSymbol_vectorField {n : ℕ}
    {Ω : Set (Euclidean n)} (hΩ : IsOpen Ω)
    (Q : Euclidean n → Fin n → MetricTensor n) (hQ : ContDiffOn ℝ ∞ Q Ω) :
    ContDiffOn ℝ ∞ (normalizedHomogeneousSymbol hΩ Q hQ).vectorField
      (normalizedSymbolDomain Ω) := by
  apply HomogeneousSymbol.contDiffOn_vectorField
  simpa [normalizedHomogeneousSymbol] using contDiffOn_normalizedSymbol hΩ hQ

/-- The exact characteristic Hamilton-field identity, including its physical
and covector components (`app:ch_seed:prop:seed-actual-menu`, Step 1). -/
theorem normalizedHomogeneousSymbol_vectorField_of_determinant_eq_zero {n : ℕ}
    {Ω : Set (Euclidean n)} (hΩ : IsOpen Ω)
    (Q : Euclidean n → Fin n → MetricTensor n) (hQ : ContDiffOn ℝ ∞ Q Ω)
    {z : Euclidean n × Euclidean n} (hz : z ∈ normalizedSymbolDomain Ω)
    (hp : determinant (Q z.1) z.2 = 0) :
    (normalizedHomogeneousSymbol hΩ Q hQ).vectorField z =
      determinantNormalization z.2 •
        (covectorGradient (fun w ↦ determinant (Q w.1) w.2) z,
          -physicalGradient (fun w ↦ determinant (Q w.1) w.2) z) := by
  have hQa := hQ.contDiffAt (hΩ.mem_nhds hz.1)
  simp only [HomogeneousSymbol.vectorField, normalizedHomogeneousSymbol,
    covectorGradient_normalizedSymbol_of_determinant_eq_zero hQa hz.2 hp,
    physicalGradient_normalizedSymbol_of_determinant_eq_zero hQa hz.2 hp,
    Prod.smul_mk, smul_neg]

/-- The existing zero-energy carrier theorem now applies to the constructed
literal symbol, with no symbol-identification premise
(`app:ch_seed:prop:seed-actual-menu`, Steps 1–2). A Hamilton chart is still an input. -/
theorem carrierPhase_normalizedSymbol_determinant_eq_zero {n : ℕ} {U Z : Type*}
    [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    {Ω : Set (Euclidean n)} (hΩ : IsOpen Ω)
    (Q : Euclidean n → Fin n → MetricTensor n) (hQ : ContDiffOn ℝ ∞ Q Ω)
    {Φ : HamiltonFlow (normalizedHomogeneousSymbol hΩ Q hQ) U}
    (C : ProjectionChart Φ) (ζ : Z → U)
    {x : Euclidean n} {z : Z} (hz : (x, (0, ζ z)) ∈ C.target) :
    determinant (Q x) (gradient (fun y ↦ carrierPhase C ζ y z) x) = 0 :=
  carrierPhase_determinant_eq_zero C ζ Q
    (fun w _ ↦ normalizedHomogeneousSymbol_h hΩ Q hQ w) (fun _ hw ↦ hw.2) hz

/-- The quantitative adapted gap expressed directly using the constructed
Hamilton velocity, as required by `app:lem:common-hamilton-phase`. The determinant
gap and bounded annulus are the explicit inputs of Step 1 of
`app:ch_seed:prop:seed-actual-menu`. -/
theorem normalizedHomogeneousSymbol_transverse_gap {n : ℕ}
    {Ω : Set (Euclidean n)} (hΩ : IsOpen Ω)
    (Q : Euclidean n → Fin n → MetricTensor n) (hQ : ContDiffOn ℝ ∞ Q Ω)
    {z : Euclidean n × Euclidean n} (hz : z ∈ normalizedSymbolDomain Ω)
    (v : Euclidean n) {r R c : ℝ} (hr : 0 < r) (hc : 0 < c)
    (hlower : r ≤ ‖z.2‖) (hupper : ‖z.2‖ ≤ R)
    (hp : determinant (Q z.1) z.2 = 0)
    (hgap : c ≤ fderiv ℝ (determinant (Q z.1)) z.2 v) :
    (r / R ^ n) * c ≤ ⟪(normalizedHomogeneousSymbol hΩ Q hQ).hp z, v⟫_ℝ := by
  change _ ≤ ⟪covectorGradient (normalizedSymbol Q) z, v⟫_ℝ
  rw [covectorGradient_eq_gradient
    ((contDiffAt_normalizedSymbol (hQ.contDiffAt (hΩ.mem_nhds hz.1)) hz.2).differentiableAt
      (by simp)), inner_gradient_left]
  exact normalizedSymbol_transverse_gap Q z.1 z.2 v hr hc hlower hupper hp hgap

end JanetCartan.ActualCarriers
