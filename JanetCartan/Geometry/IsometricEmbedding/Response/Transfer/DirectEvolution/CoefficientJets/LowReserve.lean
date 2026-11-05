module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.CoefficientJets.Bounds

/-!
# Fixed low-calculus reserve and the original coefficient scale

Convert `new:eq:carrier-coefficient` to the precise coefficient budget
consumed by `paper.tex`, `app:ch_response:eq:direct-envelope-profile`.
At order `k`, all coefficient jets through the fixed low-calculus reserve
`c + k` cost `C k * L^k`. The phase costs two additional orders, independent
of `k`. Neither the input scale `K` nor the frequency enters this argument;
the parent retains the original window `1 ≤ L ≤ K ≤ λ^(1-ν)`.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace JanetCartan.ResponseTransfer.DirectEvolution

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Low coefficient jets through `c + k` cost `C k * L^k` with a fixed
two-derivative loss on the primitive phase. The coefficient reserve `c`
is independent of any input reserve. Constants precede the scale and
varying phase, as required by `app:ch_response:eq:direct-envelope-profile`.
The estimate holds throughout the box, hence on every buffered compact
support contained in that same box. -/
theorem exists_transferCoefficient_lowJet_profile
    (c : ℕ) (hc : 1 ≤ c) (A : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j)
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ C : ℕ → ℝ, (∀ k, 0 ≤ C k) ∧ ∀ (L : ℝ), 1 ≤ L → ∀ (k : ℕ),
      ∀ (f : E → CarrierVariables n → ℝ) (w₀ : E → CarrierVariables n)
        (U : Set E) (D : Set (CarrierVariables n)),
      IsOpen U → IsOpen D → Convex ℝ D →
      ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ D) →
      ContDiffOn ℝ ∞ w₀ U → MapsTo w₀ U D →
      (∀ q ∈ U, gradient (f q) (w₀ q) = 0) →
      (∀ q ∈ U, ∀ w ∈ D, IsUnit (averagedPhaseHessian f w₀ q w)) →
      (∀ q ∈ U, ∀ w ∈ D, ‖Ring.inverse (averagedPhaseHessian f w₀ q w)‖ ≤ B) →
      (∀ j ≤ c + k + 2, ∀ z ∈ U ×ˢ D,
        ‖iteratedFDeriv ℝ j (Function.uncurry f) z‖ ≤ A j * L ^ (j - (c + 2))) →
      ∀ e : E, ‖e‖ ≤ 1 → ∀ j ≤ c + k, ∀ z ∈ U ×ˢ D,
        ‖iteratedFDeriv ℝ j (Function.uncurry (transferCoefficient f w₀ e)) z‖ ≤
          C k * L ^ k := by
  obtain ⟨D, hD, hb⟩ := exists_transferCoefficient_jet_profile (n := n) (E := E) A hA hB
  let C := fun k ↦ ∑ j ∈ Finset.range (c + k + 1), D j
  refine ⟨C, fun k ↦ Finset.sum_nonneg (fun j _ ↦ hD j), ?_⟩
  intro L hL k f w₀ U V hU hV hcV hf hw₀ h₀ hcrit hu hi hp e he j hj z hz
  apply (hb c hc L hL (c + k) f w₀ U V hU hV hcV hf hw₀ h₀ hcrit hu hi hp
    e he j hj z hz).trans
  exact mul_le_mul (Finset.single_le_sum (fun i _ ↦ hD i)
      (Finset.mem_range.mpr (by omega)))
    (pow_le_pow_right₀ hL (by omega)) (pow_nonneg (zero_le_one.trans hL) _)
    (Finset.sum_nonneg (fun i _ ↦ hD i))

end JanetCartan.ResponseTransfer.DirectEvolution
