module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.PhaseTrade.PrimitiveJets

/-!
# Primitive one-high bounds for the rectangular phase coefficients

The final quantitative assembly of `app:ch_background:eq:bg-derivative-trade`.
Order zero of the primitive input estimate fixes the matrix range from primitive
C³ bounds. The rational inverse estimates then give joint physical/carrier Cᵏ
bounds for both `L` and `V`, with a single additive primitive Cᵏ⁺³ budget.

The consumer `jc-continuum-initial-adjoint` must supply the smooth Hamilton phase
and carrier extensions, the buffered chart containment, their primitive C³
budgets, and the positive transverse gap. No differentiated-input bounds are
assumed here.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumAdjoint

/-- The literal `L = (Aᵀ A)⁻¹ Aᵀ` and `V = (D_z Y)L` have uniform one-high
joint physical/carrier jet bounds, including order zero. The constant is chosen
before the phase and carrier. Only their primitive C³ bounds, chart containment,
and the transverse gap are required; the fixed derivative reserve is three.
The joint Cᵏ norms control all mixed derivatives of total order at most `k`.
This closes the coefficient estimate in `app:ch_background:eq:bg-derivative-trade`
for the continuum initial-adjoint consumer. -/
theorem exists_cNorm_transversePhaseCoefficients_le_primitives
    {n p : ℕ} (q₀ : Euclidean n × Euclidean p) {ρ R : ℝ}
    (hρ : 0 < ρ) (a : Euclidean n × Euclidean (n - 1)) (hR : 0 < R)
    {M δ : ℝ} (hM : 0 ≤ M) (hδ : 0 < δ) (k : ℕ) :
    ∃ C > 0, ∀ (S : Euclidean n → Euclidean (n - 1) → ℝ)
      (ζ : Euclidean p → Euclidean (n - 1)),
      ContDiff ℝ ∞ (Function.uncurry S) → ContDiff ℝ ∞ ζ →
      Set.MapsTo (fun q ↦ (q.1, ζ q.2)) (Metric.closedBall q₀ ρ)
        (Metric.closedBall a R) →
      cNorm (Metric.closedBall a R) 3 (Function.uncurry S) ≤ M →
      cNorm (Metric.closedBall q₀.2 ρ) 3 ζ ≤ M →
      (∀ q ∈ Metric.closedBall q₀ ρ,
        TransverseGap δ (transversePhaseMatrix S q.1 (ζ q.2))) →
      cNorm (Metric.closedBall q₀ ρ) k
          (fun q ↦ transverseLeftInverse (transversePhaseMatrix S q.1 (ζ q.2))) +
        cNorm (Metric.closedBall q₀ ρ) k
          (fun q ↦ transversePhaseCarrierCoefficient S ζ q.1 q.2) ≤
        C * (1 + cNorm (Metric.closedBall a R) (k + 3) (Function.uncurry S) +
          cNorm (Metric.closedBall q₀.2 ρ) (k + 3) ζ) := by
  obtain ⟨C₀, hC₀, hlow⟩ :=
    exists_cNorm_transversePhaseInputs_le_primitives q₀ hρ a hR hM 0
  let B := C₀ * (1 + M + M)
  obtain ⟨CL, hCL, hleft⟩ :=
    exists_cNorm_transversePhaseLeftInverse_le_inputs q₀ hρ B hδ (le_refl k)
  obtain ⟨CV, hCV, hcarrier⟩ :=
    exists_cNorm_transversePhaseCarrierCoefficient_le_inputs q₀ hρ B B hδ (le_refl k)
  obtain ⟨CH, hCH, hhigh⟩ :=
    exists_cNorm_transversePhaseInputs_le_primitives q₀ hρ a hR hM k
  refine ⟨(CL + CV) * (1 + CH), mul_pos (add_pos hCL hCV) (by positivity), ?_⟩
  intro S ζ hS hζ hmap hSlow hζlow hgap
  let K := Metric.closedBall q₀ ρ
  let A := fun q : Euclidean n × Euclidean p ↦ transversePhaseMatrix S q.1 (ζ q.2)
  let U := transversePhaseInputs S ζ
  let H := 1 + cNorm (Metric.closedBall a R) (k + 3) (Function.uncurry S) +
    cNorm (Metric.closedBall q₀.2 ρ) (k + 3) ζ
  have hH : 1 ≤ H := by
    dsimp [H]
    linarith [cNorm_nonneg (Metric.closedBall a R) (k + 3) (Function.uncurry S),
      cNorm_nonneg (Metric.closedBall q₀.2 ρ) (k + 3) ζ]
  have hlow' : cNorm K 0 A + cNorm K 0 U ≤ B := by
    have hb := hlow S ζ hS hζ hmap hSlow hζlow
    change cNorm K 0 A + cNorm K 0 U ≤
      C₀ * (1 + cNorm (Metric.closedBall a R) 3 (Function.uncurry S) +
        cNorm (Metric.closedBall q₀.2 ρ) 3 ζ) at hb
    exact hb.trans (mul_le_mul_of_nonneg_left (by linarith) hC₀.le)
  have hArange (q) (hq : q ∈ K) : ‖A q‖ ≤ B := by
    have hn := norm_le_cNorm (isCompact_closedBall q₀ ρ)
      (contDiff_infty.mp (contDiff_transversePhaseMatrix hS hζ) 0) hq
    have hU0 := cNorm_nonneg K 0 U
    change ‖A q‖ ≤ cNorm K 0 A at hn
    linarith
  have hBrange (q) (hq : q ∈ K) :
      ‖transverseFootpointCarrierMatrix S ζ q.1 q.2‖ ≤ B := by
    have hn := norm_le_cNorm (isCompact_closedBall q₀ ρ)
      (contDiff_infty.mp (contDiff_transversePhaseInputs hS hζ) 0) hq
    have hsnd := norm_snd_le (U q)
    have hA0 := cNorm_nonneg K 0 A
    change ‖U q‖ ≤ cNorm K 0 U at hn
    change ‖transverseFootpointCarrierMatrix S ζ q.1 q.2‖ ≤ ‖U q‖ at hsnd
    linarith
  have hL := hleft S ζ hS hζ (fun q hq ↦ ⟨hArange q hq, hgap q hq⟩)
  have hV := hcarrier S ζ hS hζ
    (fun q hq ↦ ⟨⟨hArange q hq, hgap q hq⟩, hBrange q hq⟩)
  have hhigh' : cNorm K k A + cNorm K k U ≤ CH * H :=
    hhigh S ζ hS hζ hmap hSlow hζlow
  have hAhigh : cNorm K k A ≤ CH * H := by
    linarith [cNorm_nonneg K k U]
  have hUhigh : cNorm K k U ≤ CH * H := by
    linarith [cNorm_nonneg K k A]
  calc
    _ ≤ CL * (1 + cNorm K k A) + CV * (1 + cNorm K k U) := add_le_add hL hV
    _ ≤ CL * (1 + CH * H) + CV * (1 + CH * H) :=
      add_le_add (mul_le_mul_of_nonneg_left (by linarith) hCL.le)
        (mul_le_mul_of_nonneg_left (by linarith) hCV.le)
    _ = (CL + CV) * (1 + CH * H) := by ring
    _ ≤ (CL + CV) * (1 + CH) * H := by
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (add_pos hCL hCV).le
      nlinarith

end JanetCartan.ContinuumAdjoint
