module

public import JanetCartan.Analysis.Microlocal.NormalComparison.MaskDerivative
public import JanetCartan.Analysis.Calculus.BufferedInverse
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Input geometry for uniform normal comparison

The data of `app:ch_osc:setup:osc-normal` in `paper.tex`. All estimates in
`UniformNormalData` concern the original phase and amplitude. In particular,
inverse regularity, inverse jets and transport coefficient bounds are not fields.
The finite input jets use operator norms of multilinear derivatives; in fixed
dimension these give the manuscript's coordinate jet bounds, and conversely.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff

namespace JanetCartan.NormalComparison

/-- The fixed sets, buffers, dimensions and determinant gap of
`app:ch_osc:setup:osc-normal`. These data do not depend on the phase or amplitude.
Positive dimension suffices for the normal estimates, including the
one-dimensional slices used by `app:ch_osc:prop:osc-channel`. -/
structure UniformNormalGeometry (n r : ℕ) where
  dimension_pos : 0 < n
  rank_pos : 1 ≤ r
  X : Set (Euclidean n)
  D : Set (Euclidean n)
  X₀ : Set (Euclidean n)
  D₀ : Set (Euclidean n)
  V : Set (Euclidean n)
  isOpen_X : IsOpen X
  isOpen_D : IsOpen D
  convex_X : Convex ℝ X
  convex_D : Convex ℝ D
  bounded_X : Bornology.IsBounded X
  bounded_D : Bornology.IsBounded D
  compact_X₀ : IsCompact X₀
  compact_D₀ : IsCompact D₀
  isOpen_V : IsOpen V
  compact_closure_V : IsCompact (closure V)
  ε₀ : ℝ
  spatialBuffer : ℝ
  inputBuffer : ℝ
  inverseBuffer : ℝ
  gap : ℝ
  ε₀_pos : 0 < ε₀
  spatialBuffer_pos : 0 < spatialBuffer
  inputBuffer_pos : 0 < inputBuffer
  inverseBuffer_pos : 0 < inverseBuffer
  gap_pos : 0 < gap
  spatial_buffer : cthickening spatialBuffer X₀ ⊆ X
  input_buffer : cthickening inputBuffer D₀ ⊆ D

/-- The input-only smooth family in `app:ch_osc:setup:osc-normal`.
The open extension domains encode smoothness across both parameter endpoints
and across the closures of the spatial boxes. The support and quantitative
bounds are imposed only for the manuscript's parameter interval. -/
structure UniformNormalData {n r : ℕ} (G : UniformNormalGeometry n r)
    (C : ℕ → ℝ) where
  phase : ℝ → Euclidean n → Euclidean n → ℝ
  amplitude : ℝ → Euclidean n → Euclidean n → Fin r → ℂ
  parameterDomain : Set ℝ
  extensionDomain : Set (Euclidean n × Euclidean n)
  isOpen_parameterDomain : IsOpen parameterDomain
  isOpen_extensionDomain : IsOpen extensionDomain
  parameter_subset : Icc 0 G.ε₀ ⊆ parameterDomain
  spatial_subset : closure G.X ×ˢ closure G.D ⊆ extensionDomain
  phase_smooth : ContDiffOn ℝ ∞ (fun q : ℝ × (Euclidean n × Euclidean n) ↦
    phase q.1 q.2.1 q.2.2) (parameterDomain ×ˢ extensionDomain)
  amplitude_smooth : ContDiffOn ℝ ∞ (fun q : ℝ × (Euclidean n × Euclidean n) ↦
    amplitude q.1 q.2.1 q.2.2) (parameterDomain ×ˢ extensionDomain)
  amplitude_support : ∀ ε ∈ Icc 0 G.ε₀,
    Function.support (Function.uncurry (amplitude ε)) ⊆ G.X₀ ×ˢ G.D₀
  input_jets : ∀ ε ∈ Icc 0 G.ε₀, ∀ z ∈ G.X ×ˢ G.D, ∀ k ≤ 20 * (n + 1),
    ‖iteratedFDeriv ℝ k (Function.uncurry (phase ε)) z‖ +
    ‖iteratedFDeriv ℝ k (Function.uncurry (amplitude ε)) z‖ +
    ‖deriv (fun t ↦ iteratedFDeriv ℝ k (Function.uncurry (phase t)) z) ε‖ +
    ‖deriv (fun t ↦ iteratedFDeriv ℝ k (Function.uncurry (amplitude t)) z) ε‖ ≤ C k
  gradient_injective : ∀ ε ∈ Icc 0 G.ε₀, ∀ x ∈ G.X, ∀ y ∈ G.X,
    InjOn (averagedGradient (phase ε) x y) G.D
  image_buffer : ∀ ε ∈ Icc 0 G.ε₀, ∀ x ∈ G.X, ∀ y ∈ G.X,
    cthickening G.inverseBuffer (averagedGradient (phase ε) x y '' G.D₀) ⊆ G.V
  chart_buffer : ∀ ε ∈ Icc 0 G.ε₀, ∀ x ∈ G.X, ∀ y ∈ G.X,
    cthickening G.inverseBuffer (closure G.V) ⊆ averagedGradient (phase ε) x y '' G.D
  jacobian_gap : ∀ ε ∈ Icc 0 G.ε₀, ∀ x ∈ G.X, ∀ y ∈ G.X, ∀ u ∈ G.D,
    G.gap ≤ |(fderiv ℝ (averagedGradient (phase ε) x y) u).det|

variable {n r : ℕ} {G : UniformNormalGeometry n r} {C : ℕ → ℝ}

/-- The physical support stays inside its open box
(`app:ch_osc:setup:osc-normal`). -/
theorem UniformNormalGeometry.X₀_subset (G : UniformNormalGeometry n r) : G.X₀ ⊆ G.X :=
  (self_subset_cthickening _).trans G.spatial_buffer

/-- The input support stays inside its open box
(`app:ch_osc:setup:osc-normal`). -/
theorem UniformNormalGeometry.D₀_subset (G : UniformNormalGeometry n r) : G.D₀ ⊆ G.D :=
  (self_subset_cthickening _).trans G.input_buffer

/-- Joint smoothness at each original spatial point, including parameter
endpoints (`app:ch_osc:setup:osc-normal`). -/
theorem UniformNormalData.phase_contDiffAt (F : UniformNormalData G C)
    {ε : ℝ} (hε : ε ∈ F.parameterDomain) {x u : Euclidean n}
    (hx : x ∈ G.X) (hu : u ∈ G.D) :
    ContDiffAt ℝ ∞ (fun q : ℝ × (Euclidean n × Euclidean n) ↦
      F.phase q.1 q.2.1 q.2.2) (ε, (x, u)) :=
  F.phase_smooth.contDiffAt ((F.isOpen_parameterDomain.prod F.isOpen_extensionDomain).mem_nhds
    ⟨hε, F.spatial_subset ⟨subset_closure hx, subset_closure hu⟩⟩)

/-- Smoothness of the physical phase slice on the convex box
(`app:ch_osc:setup:osc-normal`). -/
theorem UniformNormalData.phase_contDiffAt_left (F : UniformNormalData G C)
    {ε : ℝ} (hε : ε ∈ F.parameterDomain) {x u : Euclidean n}
    (hx : x ∈ G.X) (hu : u ∈ G.D) :
    ContDiffAt ℝ ∞ (fun z ↦ F.phase ε z u) x :=
  (F.phase_contDiffAt hε hx hu).comp x
    (contDiffAt_const.prodMk (contDiffAt_id.prodMk contDiffAt_const))

/-- Convexity and smoothness discharge the segment hypotheses of the exact
phase linearization in `app:ch_osc:prop:osc-normal`. -/
theorem UniformNormalData.phase_sub_eq_inner (F : UniformNormalData G C)
    {ε : ℝ} (hε : ε ∈ F.parameterDomain) {x y u : Euclidean n}
    (hx : x ∈ G.X) (hy : y ∈ G.X) (hu : u ∈ G.D) :
    F.phase ε x u - F.phase ε y u =
      inner ℝ (x - y) (averagedGradient (F.phase ε) x y u) := by
  have hseg (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) 1) : y + t • (x - y) ∈ G.X := by
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
    exact G.convex_X.add_smul_sub_mem hy hx ht'
  apply phase_sub_eq_inner_averagedGradient
  · intro t ht
    exact (F.phase_contDiffAt_left hε (hseg t ht) hu).differentiableAt (by simp)
  · apply ContinuousOn.intervalIntegrable
    intro t ht
    have hp : ContinuousAt (fun s : ℝ ↦ y + s • (x - y)) t :=
      continuousAt_const.add (continuousAt_id.smul continuousAt_const)
    have hc := (F.phase_contDiffAt_left hε (hseg t ht) hu).continuousAt_fderiv (by simp)
    have hcomp := hc.comp (f := fun s : ℝ ↦ y + s • (x - y)) hp
    exact hcomp.continuousWithinAt

end JanetCartan.NormalComparison
