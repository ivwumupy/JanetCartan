module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.ReducedSource.MixedL2
public import JanetCartan.Analysis.Microlocal.NormalComparison.LocalOperators.Localization

/-!
# Parameter localization of the original reduced source

The full-source envelope calculus uses globally smooth joint data. A fixed
parameter cutoff provides that representative on an open neighborhood of
the original retained compact set, preserving every mixed derivative and
its L² bound exactly. The physical support and all coefficient/source
choices remain unchanged (`app:ch_response:eq:response-graded-reduced`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace JanetCartan.ResponseTransfer.ReducedSource
variable {n d r : ℕ}
local notation "E" => Euclidean n
local notation "Par" => Euclidean 3 × Euclidean d
local notation "Vf" => EuclideanSpace ℂ (Fin r)

/-- A fixed parameter cutoff makes the original source globally smooth
without changing its physical support (`app:ch_response:eq:direct-envelope-profile`). -/
theorem contDiff_parameterLocalizedSource
    {V : Set Par} (hV : IsOpen V) {θ : Par → ℝ} (hθ : ContDiff ℝ ∞ θ)
    (hsθ : tsupport θ ⊆ V) {b : E × Par → Vf}
    (hb : ContDiffOn ℝ ∞ b (univ ×ˢ V)) :
    ContDiff ℝ ∞ (fun w : E × Par ↦ θ w.2 • b w) := by
  apply contDiff_iff_contDiffAt.mpr
  intro w
  by_cases hw : w.2 ∈ tsupport θ
  · exact (hθ.contDiffAt.comp w contDiffAt_snd).smul
      (hb.contDiffAt ((isOpen_univ.prod hV).mem_nhds ⟨mem_univ _, hsθ hw⟩))
  · apply (contDiffAt_const (c := (0 : Vf))).congr_of_eventuallyEq
    have he := (notMem_tsupport_iff_eventuallyEq.mp hw).comp_tendsto (continuous_snd.tendsto w)
    filter_upwards [he] with z hz
    change θ z.2 = 0 at hz
    simp only [hz, zero_smul]

/-- The original physical support remains fixed after parameter localization
(`app:ch_response:eq:response-graded-source`). -/
theorem parameterLocalizedSource_zero_off_spatial_support
    {V : Set Par} {θ : Par → ℝ} (hsθ : tsupport θ ⊆ V)
    (b : E × Par → Vf) {S : Set E}
    (hb : ∀ c ∈ V, ∀ x, x ∉ S → b (x,c) = 0) :
    ∀ w : E × Par, w.1 ∉ S → θ w.2 • b w = 0 := by
  intro w hw
  by_cases hc : θ w.2 = 0
  · rw [hc, zero_smul]
  · rw [show b w = 0 from hb w.2 (hsθ (subset_tsupport _ hc)) w.1 hw, smul_zero]

/-- A parameter plateau preserves the entire physical source family on one
parameter neighborhood, hence the same fixed response may be used there
(`app:ch_response:eq:response-actual-solver-formula`). -/
theorem parameterLocalizedSource_slice_eventuallyEq
    (b : E × Par → Vf) {θ : Par → ℝ} {c : Par}
    (hθ : θ =ᶠ[𝓝 c] (fun _ ↦ 1)) :
    (fun q : Par ↦ fun x : E ↦ θ q • b (x,q)) =ᶠ[𝓝 c]
      (fun q : Par ↦ fun x : E ↦ b (x,q)) := by
  filter_upwards [hθ] with q hq
  funext x
  rw [hq, one_smul]

/-- Every mixed tensor is exactly the original source tensor on the parameter
plateau. No profile constant or derivative reserve is changed
(`app:ch_response:eq:response-graded-reduced`). -/
theorem parameterLocalizedSource_joint_jet_eq
    (b : E × Par → Vf) {θ : Par → ℝ} {c : Par}
    (hθ : θ =ᶠ[𝓝 c] (fun _ ↦ 1)) (j : ℕ) (x : E) :
    iteratedFDeriv ℝ j (fun w : E × Par ↦ θ w.2 • b w) (x,c) =
      iteratedFDeriv ℝ j b (x,c) := by
  have he := hθ.comp_tendsto (continuous_snd.tendsto (x,c))
  have hb : (fun w : E × Par ↦ θ w.2 • b w) =ᶠ[𝓝 (x,c)] b := by
    filter_upwards [he] with z hz
    change θ z.2 = 1 at hz
    rw [hz, one_smul]
  exact (hb.iteratedFDeriv ℝ j).self_of_nhds

/-- Choose one cutoff and one open parameter plateau before the varying
source family. The original compact set is covered without changing its
parameters (`app:ch_response:eq:response-graded-source`). -/
theorem exists_full_source_parameter_cutoff
    {V K : Set Par} (hV : IsOpen V) (hK : IsCompact K) (hKV : K ⊆ V) :
    ∃ θ : Par → ℝ, ContDiff ℝ ∞ θ ∧ HasCompactSupport θ ∧ tsupport θ ⊆ V ∧
      ∃ W : Set Par, IsOpen W ∧ K ⊆ W ∧ W ⊆ V ∧
        ∀ c ∈ W, θ =ᶠ[𝓝 c] (fun _ ↦ 1) := by
  obtain ⟨θ,hθ,hcθ,hsθ,_,heθ⟩ := NormalComparison.exists_contDiff_localization
    hV hK hKV (contDiff_const (c := (1 : ℝ))).contDiffOn
  refine ⟨θ,hθ,hcθ,hsθ,V ∩ interior {c | θ c = 1},hV.inter isOpen_interior,?_,inter_subset_left,?_⟩
  · intro c hc
    exact ⟨hKV hc,mem_interior_iff_mem_nhds.mpr (heθ c hc)⟩
  · intro c hc
    filter_upwards [isOpen_interior.mem_nhds hc.2] with q hq
    have hq' : q ∈ {q : Par | θ q = 1} := interior_subset hq
    exact hq'


/-- Exact plateau equality transfers the mixed L² bound with the SAME constant
and derivative order (`app:ch_response:eq:response-graded-reduced`). -/
theorem parameterLocalizedSource_mixedL2_bound
    (b : E × Par → Vf) {θ : Par → ℝ} {c : Par}
    (hθ : θ =ᶠ[𝓝 c] (fun _ ↦ 1)) (j : ℕ) (B : ℝ)
    (hb : ∃ hm : MemLp (fun x : E ↦ iteratedFDeriv ℝ j b (x,c)) 2 volume,
      ‖hm.toLp (fun x : E ↦ iteratedFDeriv ℝ j b (x,c))‖ ≤ B) :
    ∃ hm : MemLp (fun x : E ↦ iteratedFDeriv ℝ j
        (fun w : E × Par ↦ θ w.2 • b w) (x,c)) 2 volume,
      ‖hm.toLp (fun x : E ↦ iteratedFDeriv ℝ j
        (fun w : E × Par ↦ θ w.2 • b w) (x,c))‖ ≤ B := by
  have he : (fun x : E ↦ iteratedFDeriv ℝ j
      (fun w : E × Par ↦ θ w.2 • b w) (x,c)) =
      fun x : E ↦ iteratedFDeriv ℝ j b (x,c) :=
    funext (parameterLocalizedSource_joint_jet_eq b hθ j)
  simpa only [he] using hb

end JanetCartan.ResponseTransfer.ReducedSource
