module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenImageComparison.SourceTail.Identity.TestSpace
public import JanetCartan.Analysis.Extension.Mollification

/-!
# Supported L² density inside the auxiliary plateau

For `paper-v2.tex`, `app:ch_background:prop:bg-frame`, every L² input
supported almost everywhere in the input ball is a global L² limit of compact
smooth tests inside the auxiliary plateau. Replacing its representative by
the closed-ball indicator gives compact support before mollification.
Consumer: `fixedEuclideanChannel_energy_defect_eq_kernel`, extending the
compact-test identity by continuity of the bounded-operator quadratic forms.
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric
open scoped ContDiff
open JanetCartan.PeriodicLocalL2

namespace JanetCartan.ContinuumNormal.FrozenImageComparison

variable {n : ℕ} {R : ℝ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "R²" => EuclideanL2 n E

/-- Compact smooth tests inside the auxiliary plateau are dense at every L²
input supported almost everywhere in the input ball
(`paper-v2.tex`, `app:ch_background:prop:bg-frame`). The approximation is in
global L², so it applies to both bounded-operator quadratic forms in
`fixedEuclideanChannel_energy_defect_eq_kernel`. -/
theorem fixedSourceTailTestInputs_dense_supported (hR : 0 < R) (u : R²)
    (hu : ∀ᵐ x ∂volume, x ∉ ball 0 R → u x = 0) :
    u ∈ closure (fixedSourceTailTestInputs hR) := by
  classical
  let f : E → E := (closedBall 0 R).indicator (fun x ↦ u x)
  have hfu : f =ᵐ[volume] ⇑u := by
    filter_upwards [hu] with x hx
    by_cases hxR : x ∈ closedBall 0 R
    · simp [f, hxR]
    · have hxB : x ∉ ball 0 R := fun h ↦ hxR (ball_subset_closedBall h)
      simp [f, hxR, hx hxB]
  have hf : MemLp f 2 volume := (Lp.memLp u).ae_eq hfu.symm
  have hfs : tsupport f ⊆ closedBall 0 R := by
    apply closure_minimal _ isClosed_closedBall
    exact support_indicator_subset
  have hfc : HasCompactSupport f :=
    (isCompact_closedBall (0 : E) R).of_isClosed_subset (isClosed_tsupport f) hfs
  rw [EMetric.mem_closure_iff]
  intro ε hε
  obtain ⟨g, hg, hgc, hgV, hge⟩ := Mollification.exists_contDiff_approx_L2 volume
    hf hfc isOpen_interior
    (hfs.trans (closedBall_subset_fixedSourceTailTest_plateau hR)) hε
  have hgLp : MemLp g 2 volume := hg.continuous.memLp_of_hasCompactSupport hgc
  refine ⟨hgLp.toLp g, ⟨g, hg, hgc, hgV, hgLp.coeFn_toLp⟩, ?_⟩
  rw [edist_comm, Lp.edist_def, eLpNorm_congr_ae (hgLp.coeFn_toLp.sub hfu.symm)]
  exact hge

end JanetCartan.ContinuumNormal.FrozenImageComparison
