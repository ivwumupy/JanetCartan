module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.BackgroundQuadrature
public import JanetCartan.Analysis.Fourier.SeparatedSampling

/-! # Geometry and background estimates for the selected shifts

These are deterministic consequences for `app:ch_waves:thm:sampling` and
`app:ch_waves:eq:background-quadrature`, used by `SamplingRealization` on its
single selected realization. Chart identity is part of the color: separation
is asserted within each chart, in its own Euclidean carrier coordinates.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff

namespace JanetCartan.Sampling.Realization
open SeparatedSampling LatticeQuadrature BackgroundQuadrature

/-- The deterministic conclusions of `app:ch_waves:thm:sampling` for one chart.
This predicate is an output of the realization theorem, never an input. -/
structure SampleGeometry (p : ℕ) (B P W : ℝ) (ψ : Point → ℝ) (w : ℝ → ℝ)
    (h : ℝ) (U : Lattice → Point) : Prop where
  enumeration : ∀ a, a ∈ samples p B ψ w h U ↔ weight ψ w h U a ≠ 0
  count : ((samples p B ψ w h U).card : ℝ) ≤ countConstant p B / h ^ 3
  weights : ∀ a, 0 ≤ weight ψ w h U a ∧ weight ψ w h U a ≤ h ^ 3 * (P * W ^ 3)
  mass : 0 ≤ totalMass p B ψ w h U ∧
    totalMass p B ψ w h U ≤ countConstant p B * (P * W ^ 3)
  separation : ∀ a ∈ samples p B ψ w h U, ∀ b ∈ samples p B ψ w h U,
    a ≠ b → color p a.1 = color p b.1 → h / 2 ≤ ‖node h U a - node h U b‖

/-- Counts, weights, mass and same-color separation hold on every admissible
shift (`app:ch_waves:thm:sampling`). -/
theorem sampleGeometry_of_admissible {p : ℕ} {B P W h : ℝ}
    {ψ : Point → ℝ} {w : ℝ → ℝ}
    (hw : WindowBounds p w W) (hψ : PatchBounds ψ B P) (hh : 0 < h) (hh₁ : h ≤ 1)
    (U : Lattice → Point) (hU : ∀ q i, 0 ≤ U q i ∧ U q i < h) :
    SampleGeometry p B P W ψ w h U where
  enumeration _ := mem_samples_iff hw hψ hh hh₁ hU
  count := card_samples_le hψ.radius_nonneg hh hh₁
  weights a := ⟨weight_nonneg hw hψ hh.le a, weight_le hw hψ hh.le a⟩
  mass := ⟨totalMass_nonneg hw hψ hh.le, totalMass_le hw hψ hh hh₁⟩
  separation _a ha _b hb hab hc := nonzero_samples_separated hw hh
    ((mem_samples_iff hw hψ hh hh₁ hU).mp ha)
    ((mem_samples_iff hw hψ hh hh₁ hU).mp hb) hab hc

variable {J V : Type*} [Fintype J] [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The actual sampled-minus-colored-integral background over the fixed chart
family, in `app:ch_waves:eq:background-quadrature`. -/
def familyBackgroundError (p : ℕ) (B : ℝ) (ψ : J → Point → ℝ) (w : ℝ → ℝ)
    (h : ℝ) (U : J → Lattice → Point)
    (H : J → (Fin 3 → Fin (p + 1)) → Point → V) : V :=
  ∑ j, ((∑ a ∈ samples p B (ψ j) w h (U j),
    weight (ψ j) w h (U j) a • H j (color p a.1) (node h (U j) a)) -
    ∑ c, ∫ z : Point, coloredBlockMask p (integerCube (blockCutoff p B h)) w h c z •
      (ψ j z • H j c z))

/-- Deterministic quadrature for a fixed finite chart family, on the same shifts
as all normal prefixes. It holds for every carrier family satisfying actual
regularity and derivative bounds, including later accuracy choices
(`app:ch_waves:eq:background-quadrature`). -/
theorem norm_familyBackgroundError_le [CompleteSpace V] {κ : ℝ → ℝ}
    (hc : HasCompactSupport κ) (hs : ContDiff ℝ ∞ κ)
    (hm : ∫ t, κ t = 1) (hn : ∀ t, 0 ≤ κ t)
    (hk : Function.support κ ⊆ Set.Icc (-(1 / 4)) (1 / 4))
    {p : ℕ} (hp : 0 < p) {ψ : J → Point → ℝ} {B : ℝ} {P : J → ℝ}
    (hψ : ∀ j, PatchBounds (ψ j) B (P j))
    (H : J → (Fin 3 → Fin (p + 1)) → Point → V)
    (hH : ∀ j c, ContDiff ℝ p (fun z ↦ ψ j z • H j c z))
    (D : J → ℝ) (hD : ∀ j, 0 ≤ D j)
    (hderiv : ∀ j c z, ‖iteratedFDeriv ℝ p (fun z ↦ ψ j z • H j c z) z‖ ≤ D j)
    {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1)
    (U : J → Lattice → Point) (hU : ∀ j q i, 0 ≤ U j q i ∧ U j q i < h) :
    ‖familyBackgroundError p B ψ (convolvedBoxWindow κ p) h U H‖ ≤
      backgroundQuadratureConstant p B * (∑ j, D j) * h ^ p := by
  unfold familyBackgroundError
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ j, backgroundQuadratureConstant p B * D j * h ^ p :=
      Finset.sum_le_sum fun j _ ↦ norm_background_quadrature_colored_le hc hs hm hn hk hp
        (hψ j) (H j) (hH j) (hD j) (hderiv j) hh hh₁ (U j) (hU j)
    _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum]

end JanetCartan.Sampling.Realization
