module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DiagonalPdo.HistoryPhaseProfiles

/-!
# Original source boxes for the diagonal response

The actual spatial gradient is bounded by the original joint C² cap. A fixed
physical/frequency product box then contains the stationary point and all
spatial segments required by the averaged Hessian estimate. No characteristic
chart, new phase cap or altered source parameters enter this construction
(`app:ch_response:eq:direct-envelope-profile`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace
namespace JanetCartan.ResponseTransfer.DiagonalPdo
open DirectEvolution FullSourceStationary
variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "Par" => Euclidean 3 × Euclidean d
local notation "W" => CarrierVariables (d+1)

/-- The original joint C² cap bounds the actual spatial source gradient
with constant one (`app:ch_response:eq:direct-envelope-profile`). -/
theorem norm_diagonal_source_gradient_le_cNorm
    {φ : E → Par → ℝ} (hφ : ContDiff ℝ ∞ (Function.uncurry φ))
    {KP : Set (E × Par)} (hKP : IsCompact KP) {q : E × Par} (hq : q ∈ KP) :
    ‖gradient (fun y ↦ φ y q.2) q.1‖ ≤ cNorm KP 2 (Function.uncurry φ) := by
  have hs := ResponsePrimarySources.norm_iteratedFDeriv_primary_spatialSlice_le
    isOpen_univ isOpen_univ (a := Function.uncurry φ) hφ.contDiffOn
    (mem_univ q.1) (mem_univ q.2) 1
  calc
    _ = ‖iteratedFDeriv ℝ 1 (fun y ↦ φ y q.2) q.1‖ := by
      simp only [gradient,LinearIsometryEquiv.norm_map,norm_iteratedFDeriv_one]
    _ ≤ ‖iteratedFDeriv ℝ 1 (Function.uncurry φ) q‖ := hs
    _ ≤ _ := norm_iteratedFDeriv_le_cNorm hKP (hφ.of_le (by simp)) hq (by norm_num)

/-- The actual diagonal critical point lies in one explicit convex integration
box. All physical segments remain in the SAME source compact. The frequency
buffer depends only on the original low cap and selector radius, before the
source or history is varied (`app:ch_response:eq:direct-envelope-profile`). -/
theorem diagonal_source_box_geometry
    (x₀ : E) (r B radius : ℝ)
    {Cpar Kpar : Set Par} (hKpar : IsCompact Kpar) (hCK : Cpar ⊆ Kpar) :
    let e := WithLp.prodContinuousLinearEquiv 2 ℝ E E
    let U := ball x₀ r ×ˢ Cpar
    let KP := closedBall x₀ r ×ˢ Kpar
    let D := e ⁻¹' (ball x₀ r ×ˢ ball (0 : E) (1 + max B radius))
    IsOpen D ∧ Convex ℝ D ∧
      ∀ (φ : E → Par → ℝ), ContDiff ℝ ∞ (Function.uncurry φ) →
        cNorm KP 2 (Function.uncurry φ) ≤ B →
      let κ : E × Par → W := fun q ↦ WithLp.toLp 2 (q.1,gradient (fun y ↦ φ y q.2) q.1)
      MapsTo κ U D ∧
        ∀ q ∈ U, ∀ w ∈ D, ∀ t ∈ Icc (0 : ℝ) 1,
          ((κ q + t • (w-κ q)).fst,q.2) ∈ KP := by
  intro e U KP D
  have hD : IsOpen D := (isOpen_ball.prod isOpen_ball).preimage e.continuous
  have hDc : Convex ℝ D := ((convex_ball x₀ r).prod (convex_ball (0 : E) _)).linear_preimage e.toLinearMap
  refine ⟨hD,hDc,?_⟩
  intro φ hφ hcap κ
  have hmap : MapsTo κ U D := by
    intro q hq
    change q.1 ∈ ball x₀ r ∧ gradient (fun y ↦ φ y q.2) q.1 ∈ ball (0 : E) (1 + max B radius)
    refine ⟨hq.1,?_⟩
    rw [mem_ball_zero_iff]
    have hb := (norm_diagonal_source_gradient_le_cNorm hφ
      ((isCompact_closedBall x₀ r).prod hKpar) ⟨ball_subset_closedBall hq.1,hCK hq.2⟩).trans hcap
    linarith [le_max_left B radius]
  refine ⟨hmap,?_⟩
  intro q hq w hw t ht
  have hseg : κ q + t • (w-κ q) ∈ D := by
    convert hDc (hmap hq) hw (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel 1 t) using 1; module
  exact ⟨ball_subset_closedBall hseg.1,hCK hq.2⟩

end JanetCartan.ResponseTransfer.DiagonalPdo
