module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.CompactTransfer.Expressions
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.GradedPrimitives.Extension
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.DerivativeBounds.LowOperator

/-!
# Local jets of the actual carrier amplitude expressions

The primitive geometry for `new:eq:carrier-ibp` is local to one open box.
The global expression estimates are used by extending the primitive fields
near the point of evaluation, with the existing fixed-cutoff construction.
Locality proves exact agreement of the differentiated expressions. No global
inverse-Hessian hypothesis is introduced. The consumer is the source-symbol
budget for each actual branch of `app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace JanetCartan.ResponseTransfer.DirectEvolution.BranchAmplitudes
open IsometricEmbedding.Response.NearCarrier

variable {X M J : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup M] [NormedSpace ℝ M]

/-- Primitive neighborhood agreement implies agreement of every actual
differential expression, including its derivative nodes (`new:eq:carrier-ibp`). -/
theorem amplitudeExpression_eventuallyEq (e : AmplitudeExpression X M J)
    {a b : J → X → M} {x : X} (h : ∀ i, a i =ᶠ[𝓝 x] b i) :
    e.evaluate a =ᶠ[𝓝 x] e.evaluate b := by
  induction e with
  | primitive i => exact h i
  | add e f he hf => exact he.add hf
  | bilinear B e f he hf =>
    filter_upwards [he, hf] with y hy hz
    simp only [AmplitudeExpression.evaluate, hy, hz]
  | deriv v e he =>
    filter_upwards [he.fderiv (𝕜 := ℝ)] with y hy
    exact congrArg (fun T : X →L[ℝ] M => T v) hy

variable [FiniteDimensional ℝ X]

/-- The existing expression jet estimate holds from local primitive jets
on the same open box. The numerical constant and derivative cost are exactly
those of the shared expression API; the cutoff is used only to prove locality.
Source: `new:eq:carrier-coefficient`, consumed by the original direct envelope. -/
theorem norm_iteratedFDeriv_evaluate_on_open_le
    {U : Set X} (hU : IsOpen U)
    (a : J → X → M) (ha : ∀ i, ContDiffOn ℝ ∞ (a i) U)
    (Pj : J → ℕ → ℝ) (hPj : ∀ i j, 0 ≤ Pj i j)
    {L : ℝ} (hL : 1 ≤ L) (R N : ℕ) {x : X} (hx : x ∈ U)
    (hj : ∀ i j, j ≤ N →
      ‖iteratedFDeriv ℝ j (a i) x‖ ≤ Pj i j * L ^ (j - R))
    (e : AmplitudeExpression X M J) (j : ℕ) (hcost : j + e.derivativeCost ≤ N) :
    ‖iteratedFDeriv ℝ j (e.evaluate a) x‖ ≤
      e.jetConstant Pj j * L ^ (j + e.derivativeCost - R) := by
  obtain ⟨χ, V, H, hχ, _, _, hs, hV, hKV, _, hp, _, _⟩ :=
    GradedPrimitives.exists_fixed_cutoff_jet_profile isCompact_singleton hU
      (singleton_subset_iff.mpr hx)
  let b := fun i => GradedPrimitives.cutoffExtension χ (a i)
  have hb : ∀ i, ContDiff ℝ ∞ (b i) := fun i =>
    GradedPrimitives.contDiff_cutoffExtension hU hχ hs (ha i)
  have heq : ∀ i, b i =ᶠ[𝓝 x] a i := fun i =>
    GradedPrimitives.cutoffExtension_eventuallyEq (a i) hV hp (hKV (mem_singleton x))
  rw [← ((amplitudeExpression_eventuallyEq e heq).iteratedFDeriv ℝ j).eq_of_nhds]
  apply e.norm_iteratedFDeriv_evaluate_le b hb Pj hPj L hL R N x _ j hcost
  intro i k hk
  rw [((heq i).iteratedFDeriv ℝ k).eq_of_nhds]
  exact hj i k hk

/-- Local primitive jets through the fixed low reserve plus the derivative
cost give the original `L^k` budget. This does not assume any bound for the
modified amplitude (`app:ch_response:eq:direct-envelope-profile`). -/
theorem norm_lowJet_evaluate_on_open_le
    {U : Set X} (hU : IsOpen U)
    (a : J → X → M) (ha : ∀ i, ContDiffOn ℝ ∞ (a i) U)
    (Pj : J → ℕ → ℝ) (hPj : ∀ i j, 0 ≤ Pj i j)
    (e : AmplitudeExpression X M J) (c R k : ℕ) (hR : c + 2 < R)
    (hcost : e.derivativeCost ≤ k) {L : ℝ} (hL : 1 ≤ L)
    {x : X} (hx : x ∈ U)
    (hjet : ∀ i j, j ≤ c + k →
      ‖iteratedFDeriv ℝ j (a i) x‖ ≤ Pj i j * L ^ (j + 2 - R))
    {j : ℕ} (hj : j ≤ c) :
    ‖iteratedFDeriv ℝ j (e.evaluate a) x‖ ≤ e.lowJetConstant Pj c * L ^ k := by
  have hb := norm_iteratedFDeriv_evaluate_on_open_le hU a ha Pj hPj hL
    (R - 2) (c + k) hx (fun i l hl => by
      simpa only [show l - (R - 2) = l + 2 - R by omega] using hjet i l hl)
    e j (by omega)
  exact hb.trans (mul_le_mul
    (Finset.single_le_sum (fun l _ => e.jetConstant_nonneg Pj hPj l)
      (Finset.mem_range.mpr (by omega)))
    (pow_le_pow_right₀ hL (by omega)) (pow_nonneg (zero_le_one.trans hL) _)
    (e.lowJetConstant_nonneg Pj hPj c))

end JanetCartan.ResponseTransfer.DirectEvolution.BranchAmplitudes
