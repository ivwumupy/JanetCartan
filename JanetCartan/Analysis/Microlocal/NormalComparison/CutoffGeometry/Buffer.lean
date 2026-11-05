module

public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.InputJets.AveragedGradient
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# A uniform enlargement of the input support

For the scalar channel in Step 2 of `app:ch_osc:prop:osc-normal`, the first
forward jet controls how far the image moves when the input support is enlarged.
The radius is chosen from the original geometry and input budget alone.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff

namespace JanetCartan.NormalComparison

variable {n r : ℕ} {G : UniformNormalGeometry n r} {C : ℕ → ℝ}

/-- Uniform input Lipschitz estimate used to choose the fixed scalar cutoff
in `app:ch_osc:prop:osc-normal`, Step 2. -/
theorem UniformNormalData.averagedGradient_dist_le (F : UniformNormalData G C)
    {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀) {x y u v : Euclidean n}
    (hx : x ∈ G.X) (hy : y ∈ G.X) (hu : u ∈ G.D) (hv : v ∈ G.D) :
    dist (averagedGradient (F.phase ε) x y u) (averagedGradient (F.phase ε) x y v) ≤
      averagedGradientJetBound C 1 * dist u v := by
  let f := fun q : Euclidean n × (Euclidean n × Euclidean n) ↦
    averagedGradient (F.phase ε) q.1 q.2.1 q.2.2
  have hs : ContDiffOn ℝ ∞ f (G.X ×ˢ (G.X ×ˢ G.D)) :=
    F.averagedGradient_contDiffOn.comp (contDiffOn_const.prodMk contDiffOn_id)
      (fun _ hz ↦ ⟨F.parameter_subset hε, hz⟩)
  have hd (q) (hq : q ∈ G.X ×ˢ (G.X ×ˢ G.D)) : DifferentiableAt ℝ f q :=
    (hs.contDiffAt ((G.isOpen_X.prod (G.isOpen_X.prod G.isOpen_D)).mem_nhds hq)).differentiableAt
      (by simp)
  have hb (q) (hq : q ∈ G.X ×ˢ (G.X ×ˢ G.D)) :
      ‖fderiv ℝ f q‖ ≤ averagedGradientJetBound C 1 := by
    simpa only [norm_iteratedFDeriv_one] using
      F.averagedGradient_spatial_jet_bound hε (k := 1) (by omega) hq
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le hd hb
    (G.convex_X.prod (G.convex_X.prod G.convex_D))
    (x := (x, (y, v))) (y := (x, (y, u))) ⟨hx, hy, hv⟩ ⟨hx, hy, hu⟩
  simpa [f, dist_eq_norm] using h

/-- The input enlargement for the scalar cutoff channel of
`app:ch_osc:prop:osc-normal`. The added `1` handles a zero forward bound. -/
def UniformNormalGeometry.cutoffInputRadius (G : UniformNormalGeometry n r) (C : ℕ → ℝ) : ℝ :=
  min (G.inputBuffer / 2) (G.inverseBuffer / (2 * (averagedGradientJetBound C 1 + 1)))

/-- Positivity of the fixed enlargement (`app:ch_osc:prop:osc-normal`). -/
theorem UniformNormalGeometry.cutoffInputRadius_pos (G : UniformNormalGeometry n r)
    (C : ℕ → ℝ) : 0 < G.cutoffInputRadius C := by
  have h := averagedGradientJetBound_nonneg C 1
  exact lt_min (half_pos G.inputBuffer_pos) (div_pos G.inverseBuffer_pos (by positivity))

/-- The enlarged support still has half the original input buffer
(`app:ch_osc:prop:osc-normal`, Step 2). -/
theorem UniformNormalGeometry.cutoff_input_buffer (G : UniformNormalGeometry n r)
    (C : ℕ → ℝ) :
    cthickening (G.inputBuffer / 2) (cthickening (G.cutoffInputRadius C) G.D₀) ⊆ G.D := by
  apply (cthickening_cthickening_subset (half_pos G.inputBuffer_pos).le (G.cutoffInputRadius_pos C).le _).trans
  apply (cthickening_mono ?_ _).trans G.input_buffer
  have h := min_le_left (G.inputBuffer / 2)
    (G.inverseBuffer / (2 * (averagedGradientJetBound C 1 + 1)))
  change G.cutoffInputRadius C ≤ G.inputBuffer / 2 at h
  linarith

/-- The common inverse image buffer for the enlarged scalar input support,
proved from the original forward jets (`app:ch_osc:prop:osc-normal`, Step 2). -/
theorem UniformNormalData.cutoff_image_buffer (F : UniformNormalData G C)
    {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀) {x y : Euclidean n}
    (hx : x ∈ G.X) (hy : y ∈ G.X) :
    cthickening (G.inverseBuffer / 2)
      (averagedGradient (F.phase ε) x y '' cthickening (G.cutoffInputRadius C) G.D₀) ⊆ G.V := by
  let δ := G.cutoffInputRadius C
  let L := averagedGradientJetBound C 1
  have hδ : 0 < δ := G.cutoffInputRadius_pos C
  have hL : 0 ≤ L := averagedGradientJetBound_nonneg C 1
  have hδD : cthickening δ G.D₀ ⊆ G.D :=
    (self_subset_cthickening _).trans (G.cutoff_input_buffer C)
  have hsize : L * δ ≤ G.inverseBuffer / 2 := by
    have h := min_le_right (G.inputBuffer / 2) (G.inverseBuffer / (2 * (L + 1)))
    change δ ≤ G.inverseBuffer / (2 * (L + 1)) at h
    have hm := (le_div_iff₀ (by positivity : 0 < 2 * (L + 1))).mp h
    nlinarith
  have himage : averagedGradient (F.phase ε) x y '' cthickening δ G.D₀ ⊆
      cthickening (G.inverseBuffer / 2) (averagedGradient (F.phase ε) x y '' G.D₀) := by
    rintro _ ⟨u, hu, rfl⟩
    have huD := hδD hu
    rw [G.compact_D₀.cthickening_eq_biUnion_closedBall hδ.le] at hu
    obtain ⟨v, hv, huv⟩ := mem_iUnion₂.mp hu
    apply closedBall_subset_cthickening (mem_image_of_mem _ hv) _
    exact (F.averagedGradient_dist_le hε hx hy huD (G.D₀_subset hv)).trans
      ((mul_le_mul_of_nonneg_left huv hL).trans hsize)
  apply (cthickening_subset_of_subset _ himage).trans
  apply (cthickening_cthickening_subset (half_pos G.inverseBuffer_pos).le
    (half_pos G.inverseBuffer_pos).le _).trans
  simpa only [add_halves] using F.image_buffer ε hε x hx y hy

end JanetCartan.NormalComparison
