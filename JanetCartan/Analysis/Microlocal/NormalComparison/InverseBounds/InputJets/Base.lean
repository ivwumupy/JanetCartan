module

public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.PhaseTransport
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Original input jets on the open boxes

Extract the four separate estimates of `app:ch_osc:setup:osc-normal` from the
stored sum, and retain the extension smoothness needed for mixed derivatives.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace JanetCartan.NormalComparison

variable {n r : ℕ} {G : UniformNormalGeometry n r} {C : ℕ → ℝ}

/-- Joint amplitude smoothness at the original input points, including the
parameter endpoints (`app:ch_osc:setup:osc-normal`). -/
theorem UniformNormalData.amplitude_contDiffAt (F : UniformNormalData G C)
    {ε : ℝ} (hε : ε ∈ F.parameterDomain) {x u : Euclidean n}
    (hx : x ∈ G.X) (hu : u ∈ G.D) :
    ContDiffAt ℝ ∞ (fun q : ℝ × (Euclidean n × Euclidean n) ↦
      F.amplitude q.1 q.2.1 q.2.2) (ε, (x, u)) :=
  F.amplitude_smooth.contDiffAt ((F.isOpen_parameterDomain.prod F.isOpen_extensionDomain).mem_nhds
    ⟨hε, F.spatial_subset ⟨subset_closure hx, subset_closure hu⟩⟩)

/-- Smooth spatial phase slices on the original open boxes
(`app:ch_osc:setup:osc-normal`). -/
theorem UniformNormalData.phase_contDiffOn_spatial (F : UniformNormalData G C)
    {ε : ℝ} (hε : ε ∈ F.parameterDomain) :
    ContDiffOn ℝ ∞ (Function.uncurry (F.phase ε)) (G.X ×ˢ G.D) := by
  intro z hz
  exact ((F.phase_contDiffAt hε hz.1 hz.2).comp z
    (contDiffAt_const.prodMk contDiffAt_id)).contDiffWithinAt

/-- Smooth spatial amplitude slices on the original open boxes
(`app:ch_osc:setup:osc-normal`). -/
theorem UniformNormalData.amplitude_contDiffOn_spatial (F : UniformNormalData G C)
    {ε : ℝ} (hε : ε ∈ F.parameterDomain) :
    ContDiffOn ℝ ∞ (Function.uncurry (F.amplitude ε)) (G.X ×ˢ G.D) := by
  intro z hz
  exact ((F.amplitude_contDiffAt hε hz.1 hz.2).comp z
    (contDiffAt_const.prodMk contDiffAt_id)).contDiffWithinAt

/-- Each of the four original jets is bounded by the same input constant;
no spatial/parameter interchange is assumed (`app:ch_osc:setup:osc-normal`). -/
theorem UniformNormalData.input_jet_bounds (F : UniformNormalData G C)
    {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀) {z : Euclidean n × Euclidean n}
    (hz : z ∈ G.X ×ˢ G.D) {k : ℕ} (hk : k ≤ 20 * (n + 1)) :
    ‖iteratedFDeriv ℝ k (Function.uncurry (F.phase ε)) z‖ ≤ C k ∧
    ‖iteratedFDeriv ℝ k (Function.uncurry (F.amplitude ε)) z‖ ≤ C k ∧
    ‖deriv (fun t ↦ iteratedFDeriv ℝ k (Function.uncurry (F.phase t)) z) ε‖ ≤ C k ∧
    ‖deriv (fun t ↦ iteratedFDeriv ℝ k (Function.uncurry (F.amplitude t)) z) ε‖ ≤ C k := by
  have h := F.input_jets ε hε z hz k hk
  have h₁ := norm_nonneg (iteratedFDeriv ℝ k (Function.uncurry (F.phase ε)) z)
  have h₂ := norm_nonneg (iteratedFDeriv ℝ k (Function.uncurry (F.amplitude ε)) z)
  have h₃ := norm_nonneg (deriv
    (fun t ↦ iteratedFDeriv ℝ k (Function.uncurry (F.phase t)) z) ε)
  have h₄ := norm_nonneg (deriv
    (fun t ↦ iteratedFDeriv ℝ k (Function.uncurry (F.amplitude t)) z) ε)
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Restricting a spatial jet along a fixed linear map incurs precisely its
operator norm to the jet order. This local form is used for the two physical
positions and for the convex segment in `app:ch_osc:prop:osc-normal`. -/
theorem norm_iteratedFDeriv_comp_linear_on_open_le
    {E H V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : H →L[ℝ] E) {f : E → V} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) {x : H} (hx : L x ∈ U) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (f ∘ L) x‖ ≤ ‖iteratedFDeriv ℝ k f (L x)‖ * ‖L‖ ^ k := by
  have hpre : IsOpen (L ⁻¹' U) := hU.preimage L.continuous
  have h := L.iteratedFDerivWithin_comp_right hf hU.uniqueDiffOn hpre.uniqueDiffOn hx
    (i := k) (by simp)
  rw [iteratedFDerivWithin_of_isOpen _ hpre hx,
    iteratedFDerivWithin_of_isOpen _ hU hx] at h
  rw [h]
  simpa using (iteratedFDeriv ℝ k f (L x)).norm_compContinuousLinearMap_le (fun _ ↦ L)

end JanetCartan.NormalComparison
