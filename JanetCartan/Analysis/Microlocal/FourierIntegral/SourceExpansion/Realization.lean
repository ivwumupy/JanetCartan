module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SourceExpansion.OperatorSeries
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SourceExpansion.LiteralKernel
public import JanetCartan.Analysis.Microlocal.FourierIntegral.L2Realization
public import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

/-!
# Identification with the same literal full graph regularizations

Source: `app:ch_regular_base:thm:actual-calculus`, Step 1. Source-independent
compact-frequency realizations and their low graph bounds are analytic inputs.
The full-amplitude operator is obtained by the source series; its literal test
identity is a conclusion, not an interface field. Euclidean Lebesgue measures,
physical covectors, and the original full amplitude are unchanged.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory Filter
open scoped ContDiff ENNReal Topology Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.SourceExpansion
open AmplitudeBound
variable {n r : ℕ} {R ℓ : ℝ}
local notation "E" => Euclidean n
local notation "V" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp V 2 (volume : Measure E)

section Regularized
variable (hn : 0 < n) (hℓ : 0 < ℓ) (hR : R / ℓ < 1 / 2)
  (A : FullAmplitude n r)
  (hs : ∀ x η i j, SupportedInCenteredBox R (fun y ↦ A x y η i j))
  (hA : ContDiff ℝ ∞ (fun p : (Euclidean n) × (Euclidean n) × (Euclidean n) ↦ A p.1 p.2.1 p.2.2))
  (μ : ℕ) {B : ℝ} (hb : HasFullSourceSymbolBound A (μ + lowReserve n) B)
  (β : SourceCutoff n R ℓ)
  (C : (Fin n → ℤ) →
    Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure (Euclidean n)) →L[ℂ]
    Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure (Euclidean n))) (G : ℝ)
  (hgraph : ∀ k b, HasCoefficientSymbolBound (matrixCoefficient ℓ A k) μ b →
    ‖C k‖ ≤ G * b)
  (S : (Euclidean n) → (Euclidean n) → ℝ) (hS : ContDiff ℝ ∞ (Function.uncurry S))
  (θ : (Euclidean n) → ℂ) (hθ : ContDiff ℝ ∞ θ) (hθc : HasCompactSupport θ)
  (hreal : ∀ k (u : graphTestSpace n r), C k (graphTestToLp u) =ᵐ[volume]
    graphTestOutput S (fun x _ η ↦ θ η • matrixCoefficient ℓ A k x η) u)
include hn hℓ hR hs hA hb hgraph hS hθ hθc hreal

/-- The bounded sum realizes the SAME literal full-amplitude compact-frequency
integral, not a new full PDO construction. All source derivatives used below are
extracted from the primitive total budget
(`app:ch_regular_base:thm:actual-calculus`, Step 1). -/
theorem sourceOperatorSeries_regularized_coeFn (u : graphTestSpace n r) :
    sourceOperatorSeries β C (graphTestToLp u) =ᵐ[volume]
      graphTestOutput S (fun x y η ↦ θ η • A x y η) u := by
  let F : (Fin n → ℤ) → H := fun k ↦ (C k).comp (sourceModulation β k) (graphTestToLp u)
  have hsn : Summable (fun k ↦ ‖F k‖) :=
    ((summable_norm_sourceOperatorTerm hn hℓ hR A hs hA μ hb β C G hgraph).mul_right
      ‖graphTestToLp u‖).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
        (fun k ↦ ((C k).comp (sourceModulation β k)).le_opNorm _)
  have hsL : HasSum F (sourceOperatorSeries β C (graphTestToLp u)) :=
    hasSum_apply (hasSum_sourceOperatorTerm hn hℓ hR A hs hA μ hb β C G hgraph)
      (graphTestToLp u)
  have hae := Lp.hasSum_coeFn_tsum (tsum_enorm_ne_top_iff_summable_norm.mpr hsn)
  rw [hsL.tsum_eq] at hae
  have hterms : ∀ k, F k =ᵐ[volume]
      graphTestOutput S (fun x _ η ↦ θ η • matrixCoefficient ℓ A k x η)
        (sourceModulatedTest β k u) := by
    intro k
    dsimp only [F, ContinuousLinearMap.comp_apply]
    rw [sourceModulation_graphTestToLp]
    exact hreal k _
  have hz (x η y) : ‖A x y η‖ ≤ B := by
    have h := hb [] [] (by simp) x y η
    change 1 * ‖A x y η‖ ≤ B at h
    simpa only [one_mul] using h
  have hd (x η i y) :
      ‖matrixAmplitudeCoordinateDerivList (List.replicate (lowReserve n) i)
        (fun y ↦ A x y η) y‖ ≤ B := by
    have h := hb [] (List.replicate (lowReserve n) i) (by simp) x y η
    change 1 * ‖matrixAmplitudeCoordinateDerivList (List.replicate (lowReserve n) i)
      (fun y ↦ A x y η) y‖ ≤ B at h
    simpa only [one_mul] using h
  have hv : ContDiff ℝ ∞ (fun y ↦ (u.val y).ofLp) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin r ↦ ℂ)).contDiff.comp u.property.1
  have hvc : HasCompactSupport (fun y ↦ (u.val y).ofLp) :=
    u.property.2.comp_left (g := WithLp.ofLp) rfl
  filter_upwards [hae, ae_all_iff.mpr hterms] with x hx htx
  have hpoint := (Pi.hasSum.mp (hasSum_graphOperator_regularizedSourceExpansion hn hℓ hR
    A hA hs hz hd β.toFun β.smooth β.compact β.cell (β.one_on_amplitude A hs)
    S hS θ hθ hθc (fun y ↦ (u.val y).ofLp) hv hvc)) x
  simp only [matrixCoefficient_external_smul] at hpoint
  have hpointV := (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin r ↦ ℂ)).symm.toContinuousLinearMap.hasSum hpoint
  apply HasSum.unique hx
  convert hpointV using 1
  · funext k
    exact htx k
  · rfl

/-- The actual Hilbert adjoint represents the literal full-amplitude adjoint
test pairing. Its source-series summands therefore estimate the original
adjoint, with no replacement of the full kernel
(`app:ch_regular_base:thm:actual-calculus`, Step 1). -/
theorem sourceOperatorSeries_regularized_adjoint_pairing
    (u : graphTestSpace n r) (w : H) :
    inner ℂ (graphTestToLp u) ((sourceOperatorSeries β C).adjoint w) =
      ∫ x, inner ℂ (graphTestOutput S (fun x y η ↦ θ η • A x y η) u x) (w x) := by
  rw [ContinuousLinearMap.adjoint_inner_right, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [sourceOperatorSeries_regularized_coeFn hn hℓ hR A hs hA μ hb β C G
    hgraph S hS θ hθ hθc hreal u] with x hx
  rw [hx]

/-- Uniqueness of the bounded realization on the compact smooth Euclidean tests.
Thus changing the source-series representation cannot change the full operator
(`app:ch_regular_base:thm:actual-calculus`, Step 1). -/
theorem sourceOperatorSeries_regularized_unique (W : H →L[ℂ] H)
    (hW : ∀ u : graphTestSpace n r, W (graphTestToLp u) =ᵐ[volume]
      graphTestOutput S (fun x y η ↦ θ η • A x y η) u) :
    W = sourceOperatorSeries β C := by
  apply DFunLike.coe_injective
  apply denseRange_graphTestToLp.equalizer W.continuous (sourceOperatorSeries β C).continuous
  funext u
  apply Lp.ext
  exact (hW u).trans (sourceOperatorSeries_regularized_coeFn hn hℓ hR A hs hA μ hb β C G
    hgraph S hS θ hθ hθc hreal u).symm

end Regularized
end JanetCartan.FourierIntegral.SourceExpansion
