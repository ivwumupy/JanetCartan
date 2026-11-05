module

public import JanetCartan.Analysis.Microlocal.FullSourceStationary.Geometry
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.CoefficientJets.Primitive

/-!
# Full-parameter stationary-system derivatives

The generic partial-derivative API supplies the first stationary-system and
Hessian jets on the actual non-product full-source carrier. The independent
full covector is included in every joint derivative. Consumer: the quantitative
full-source stationary constructor for `app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Topology

namespace JanetCartan.FullSourceStationary
open ResponseTransfer.DirectEvolution
variable {d : ℕ}
local notation "W" => CarrierVariables (d + 1)
local notation "P" => ℝ × (Euclidean (d + 1) × (Euclidean 3 × Euclidean d))

/-- The full stationary system is smooth, and its first joint derivative
costs only the original second phase jet. This local form accepts the
actual open retained carrier, without requiring a product domain
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem full_source_stationarySystem_local_jet
    {f : FullSourcePoint d → ℝ} {V : Set (FullSourcePoint d)}
    (hV : IsOpen V) (hf : ContDiffOn ℝ ∞ f V)
    {v : FullSourcePoint d} (hv : v ∈ V) :
    ContDiffAt ℝ ∞ (fun p : FullSourcePoint d ↦ gradient (fun w ↦ f (p.1, w)) p.2) v ∧
      ‖fderiv ℝ (fun p : FullSourcePoint d ↦ gradient (fun w ↦ f (p.1, w)) p.2) v‖ ≤
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
theorem full_source_stationaryHessian_local_jet
    {f : FullSourcePoint d → ℝ} {V : Set (FullSourcePoint d)}
    (hV : IsOpen V) (hf : ContDiffOn ℝ ∞ f V)
    {v : FullSourcePoint d} (hv : v ∈ V) :
    ContDiffAt ℝ ∞ (fun p : FullSourcePoint d ↦
      fderiv ℝ (gradient (fun w ↦ f (p.1, w))) p.2) v ∧
      ‖fderiv ℝ (fun p : FullSourcePoint d ↦
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
produced by `exists_admissible_history_full_source_joint_phase_profiles`, not by a stationary-branch hypothesis
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem norm_full_source_stationarySystem_sub_le
    {f : FullSourcePoint d → ℝ} {V S : Set (FullSourcePoint d)}
    (hV : IsOpen V) (hf : ContDiffOn ℝ ∞ f V) (hS : Convex ℝ S) (hSV : S ⊆ V)
    {B : ℝ} (hB : ∀ p ∈ S, ‖iteratedFDeriv ℝ 2 f p‖ ≤ B)
    {u v : FullSourcePoint d} (hu : u ∈ S) (hv : v ∈ S) :
    ‖gradient (fun w ↦ f (v.1, w)) v.2 - gradient (fun w ↦ f (u.1, w)) u.2‖ ≤
      B * ‖v - u‖ :=
  hS.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
    (f := fun p : FullSourcePoint d ↦ gradient (fun w ↦ f (p.1, w)) p.2)
    (fun p hp ↦ ((full_source_stationarySystem_local_jet (f := f) hV hf (hSV hp)).1).differentiableAt
      (by simp))
    (fun p hp ↦ (full_source_stationarySystem_local_jet (f := f) hV hf (hSV hp)).2.trans (hB p hp)) hu hv

/-- The primitive third jet controls stationary-Hessian differences on any
supplied convex part of the retained carrier. In particular this estimates
the positive-time Hessian against the explicit zero-time diagonal block
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem norm_full_source_stationaryHessian_sub_le
    {f : FullSourcePoint d → ℝ} {V S : Set (FullSourcePoint d)}
    (hV : IsOpen V) (hf : ContDiffOn ℝ ∞ f V) (hS : Convex ℝ S) (hSV : S ⊆ V)
    {B : ℝ} (hB : ∀ p ∈ S, ‖iteratedFDeriv ℝ 3 f p‖ ≤ B)
    {u v : FullSourcePoint d} (hu : u ∈ S) (hv : v ∈ S) :
    ‖fderiv ℝ (gradient (fun w ↦ f (v.1, w))) v.2 -
      fderiv ℝ (gradient (fun w ↦ f (u.1, w))) u.2‖ ≤ B * ‖v - u‖ :=
  hS.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
    (f := fun p : FullSourcePoint d ↦ fderiv ℝ (gradient (fun w ↦ f (p.1, w))) p.2)
    (fun p hp ↦ ((full_source_stationaryHessian_local_jet (f := f) hV hf (hSV hp)).1).differentiableAt
      (by simp))
    (fun p hp ↦ (full_source_stationaryHessian_local_jet (f := f) hV hf (hSV hp)).2.trans (hB p hp)) hu hv

end JanetCartan.FullSourceStationary
