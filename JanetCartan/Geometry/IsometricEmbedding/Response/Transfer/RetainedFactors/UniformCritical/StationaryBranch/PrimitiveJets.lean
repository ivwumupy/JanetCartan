module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.JointPhaseJets
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.CoefficientJets.Primitive
public import JanetCartan.Analysis.Calculus.BufferedInverse

/-!
# Low joint jets for the uniform stationary construction

The second and third original phase jets control the joint stationary system
and its integration-variable derivative. These estimates are used to choose
the contraction radius before the varying primary phase and retained charts.
The actual budgets come from `HistoryJointPhaseJets`, with the original
`phaseCost`. Source: `app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped ContDiff Topology

namespace JanetCartan.ResponseTransfer.RetainedFactors
open DirectEvolution

variable {d : ℕ}
local notation "W" => CarrierVariables (d + 1)
local notation "P" => ℝ × (Euclidean (d + 1) × Euclidean 3)

/-- The full stationary system is smooth, and its first joint derivative
costs only the original second phase jet. This local form accepts the
actual open retained carrier, without requiring a product domain
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem retained_stationarySystem_local_jet
    {f : RetainedCarrierPoint d → ℝ} {V : Set (RetainedCarrierPoint d)}
    (hV : IsOpen V) (hf : ContDiffOn ℝ ∞ f V)
    {v : RetainedCarrierPoint d} (hv : v ∈ V) :
    ContDiffAt ℝ ∞ (fun p : RetainedCarrierPoint d ↦ gradient (fun w ↦ f (p.1, w)) p.2) v ∧
      ‖fderiv ℝ (fun p : RetainedCarrierPoint d ↦ gradient (fun w ↦ f (p.1, w)) p.2) v‖ ≤
        ‖iteratedFDeriv ℝ 2 f v‖ := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hv)
  have hsub : ball v.1 ε ×ˢ ball v.2 ε ⊆ V := by
    simpa only [ball_prod_same] using hball
  have hm : v ∈ ball v.1 ε ×ˢ ball v.2 ε :=
    ⟨mem_ball_self hε, mem_ball_self hε⟩
  refine ⟨(contDiffOn_jointPhaseGradient (n := d + 1) (f := fun p : P ↦ fun w : W ↦ f (p, w))
    isOpen_ball isOpen_ball (hf.mono hsub)).contDiffAt
      ((isOpen_ball.prod isOpen_ball).mem_nhds hm), ?_⟩
  have hb := norm_jet_jointPhaseGradient_le_phase (n := d + 1)
    (f := fun p : P ↦ fun w : W ↦ f (p, w))
    isOpen_ball isOpen_ball (hf.mono hsub) 1 hm
  have he : Function.uncurry (fun p : P ↦ fun w : W ↦ f (p, w)) = f := rfl
  rw [he] at hb
  simpa only [norm_iteratedFDeriv_one] using hb

/-- The stationary Hessian is jointly smooth, with first derivative bounded
by the original third phase jet. This supplies the spatial as well as elapsed
variation needed for the uniform contraction
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem retained_stationaryHessian_local_jet
    {f : RetainedCarrierPoint d → ℝ} {V : Set (RetainedCarrierPoint d)}
    (hV : IsOpen V) (hf : ContDiffOn ℝ ∞ f V)
    {v : RetainedCarrierPoint d} (hv : v ∈ V) :
    ContDiffAt ℝ ∞ (fun p : RetainedCarrierPoint d ↦
      fderiv ℝ (gradient (fun w ↦ f (p.1, w))) p.2) v ∧
      ‖fderiv ℝ (fun p : RetainedCarrierPoint d ↦
        fderiv ℝ (gradient (fun w ↦ f (p.1, w))) p.2) v‖ ≤
          ‖iteratedFDeriv ℝ 3 f v‖ := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hv)
  have hsub : ball v.1 ε ×ˢ ball v.2 ε ⊆ V := by
    simpa only [ball_prod_same] using hball
  have hm : v ∈ ball v.1 ε ×ˢ ball v.2 ε :=
    ⟨mem_ball_self hε, mem_ball_self hε⟩
  refine ⟨(contDiffOn_jointPhaseHessian (n := d + 1) (f := fun p : P ↦ fun w : W ↦ f (p, w))
    isOpen_ball isOpen_ball (hf.mono hsub)).contDiffAt
      ((isOpen_ball.prod isOpen_ball).mem_nhds hm), ?_⟩
  have hb := norm_jet_jointPhaseHessian_le_phase (n := d + 1)
    (f := fun p : P ↦ fun w : W ↦ f (p, w))
    isOpen_ball isOpen_ball (hf.mono hsub) 1 hm
  have he : Function.uncurry (fun p : P ↦ fun w : W ↦ f (p, w)) = f := rfl
  rw [he] at hb
  simpa only [norm_iteratedFDeriv_one] using hb

/-- The primitive second jet controls stationary-system differences on any
supplied convex part of the retained joint carrier. The fixed budget is
produced by `HistoryJointPhaseJets`, not by a stationary-branch hypothesis
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem norm_retained_stationarySystem_sub_le
    {f : RetainedCarrierPoint d → ℝ} {V S : Set (RetainedCarrierPoint d)}
    (hV : IsOpen V) (hf : ContDiffOn ℝ ∞ f V) (hS : Convex ℝ S) (hSV : S ⊆ V)
    {B : ℝ} (hB : ∀ p ∈ S, ‖iteratedFDeriv ℝ 2 f p‖ ≤ B)
    {u v : RetainedCarrierPoint d} (hu : u ∈ S) (hv : v ∈ S) :
    ‖gradient (fun w ↦ f (v.1, w)) v.2 - gradient (fun w ↦ f (u.1, w)) u.2‖ ≤
      B * ‖v - u‖ :=
  hS.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
    (f := fun p : RetainedCarrierPoint d ↦ gradient (fun w ↦ f (p.1, w)) p.2)
    (fun p hp ↦ ((retained_stationarySystem_local_jet (f := f) hV hf (hSV hp)).1).differentiableAt
      (by simp))
    (fun p hp ↦ (retained_stationarySystem_local_jet (f := f) hV hf (hSV hp)).2.trans (hB p hp)) hu hv

/-- The primitive third jet controls stationary-Hessian differences on any
supplied convex part of the retained carrier. In particular this estimates
the positive-time Hessian against the explicit zero-time diagonal block
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem norm_retained_stationaryHessian_sub_le
    {f : RetainedCarrierPoint d → ℝ} {V S : Set (RetainedCarrierPoint d)}
    (hV : IsOpen V) (hf : ContDiffOn ℝ ∞ f V) (hS : Convex ℝ S) (hSV : S ⊆ V)
    {B : ℝ} (hB : ∀ p ∈ S, ‖iteratedFDeriv ℝ 3 f p‖ ≤ B)
    {u v : RetainedCarrierPoint d} (hu : u ∈ S) (hv : v ∈ S) :
    ‖fderiv ℝ (gradient (fun w ↦ f (v.1, w))) v.2 -
      fderiv ℝ (gradient (fun w ↦ f (u.1, w))) u.2‖ ≤ B * ‖v - u‖ :=
  hS.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
    (f := fun p : RetainedCarrierPoint d ↦ fderiv ℝ (gradient (fun w ↦ f (p.1, w))) p.2)
    (fun p hp ↦ ((retained_stationaryHessian_local_jet (f := f) hV hf (hSV hp)).1).differentiableAt
      (by simp))
    (fun p hp ↦ (retained_stationaryHessian_local_jet (f := f) hV hf (hSV hp)).2.trans (hB p hp)) hu hv

end JanetCartan.ResponseTransfer.RetainedFactors
