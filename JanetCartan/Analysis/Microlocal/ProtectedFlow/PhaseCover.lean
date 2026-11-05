module

public import JanetCartan.Analysis.Microlocal.ProtectedFlow.PhaseCover.FiniteAssembly
public import JanetCartan.Analysis.Microlocal.ProtectedFlow.PhaseCover.FiniteGraphs
public import JanetCartan.Analysis.Microlocal.ProtectedFlow.PhaseCover.LocalConstruction

/-!
# Comparison-phase coverage of complete source products

The finite comparison-phase construction in `app:ch_regular:thm:no-return`.
The local Hamilton construction is instantiated at every frozen characteristic
source covector, and compactness selects finitely many charts. Quantitative
zero exclusion supplies coverage of all current characteristic source points.
The geometry, compact estimate set and positive constants precede the current
symbol. The actual phases, projection charts and source/target buffers are
retained, with smooth gradients and Hamilton tangency supplied by `ChartData`.

`PhaseCover.UniformRectangles` strengthens this construction with fixed finite
canonical centers, common widths and physical buffers chosen before the current
symbol. It is a separate leaf to avoid a cycle through the canonical-factor
consumer. The actual coefficient extension, carrier instantiation and final
factor assembly belong to the parent no-return construction.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff Topology

namespace JanetCartan.ProtectedFlow.PhaseCover

open HamiltonPhase

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Construct finitely many actual comparison phases for the complete compact
source product (`app:ch_regular:thm:no-return`, finite comparison-phase paragraph).

The hypotheses concern only the frozen degree-one scalar symbol, its open
smooth domain, and the compact source directions. In particular no local phase,
coverage or graph-image gap is assumed. Any compact symmetric annular source
satisfying these hypotheses is covered in its entirety, including antipodes.

One fixed scalar C³ threshold on a compact buffered estimate set controls all
charts. Their zero-energy parameter sets are compact and annular by
`ComparisonGeometry.isCompact_parameters` and
`ComparisonChart.exists_parameter_annulus`. Gradients are smooth, solve the
eikonal equation and are Hamilton tangent by the theorems in `ComparisonChart`.
The regular-image bounds hold on the whole outer physical ball, uniformly over
all admissible current symbols. The compact regular angular enclosure `A` and
its positive buffer are fixed before the current symbol. Coverage includes
current zeros that are not frozen zeros.

The compact `ComparisonGeometry.ParameterFamily g` and
`ComparisonChart.familyGradient` expose these graphs directly to
`ProtectedFlow.exists_uniform_characteristic_buffer`. -/
theorem exists_finite_comparison_cover
    (H₀ : HomogeneousSymbol E) {D : Set (E × E)} (hD : IsOpen D)
    (hDH₀ : D ⊆ H₀.domain) (hH₀ : ContDiffOn ℝ ∞ H₀.h D)
    (hhom₀ : H₀.ConicHomogeneous)
    (hfrozen : ∀ z ∈ D, H₀.h z = H₀.h (0, z.2))
    {Ω G M : Set E} (hΩ : IsCompact Ω)
    (hsource : ({0} : Set E) ×ˢ Ω ⊆ D)
    (hΩzero : ∀ p ∈ Ω, p ≠ 0)
    (htransverse : ∀ p ∈ Ω, H₀.h (0, p) = 0 → H₀.hp (0, p) ≠ 0)
    (hG : IsOpen G) (hM : IsClosed M)
    (hregular : ∀ p ∈ Ω, normalizedCovector p ∈ G \ M) :
    ∃ (s : Finset {p : E // p ∈ Ω ∧ H₀.h (0, p) = 0})
      (g : s → ComparisonGeometry E) (r δ c C ε : ℝ) (K : Set (E × E)) (A : Set E),
      0 < r ∧ 0 < δ ∧ 0 < c ∧ 0 < C ∧ 0 < ε ∧
      IsCompact K ∧ K ⊆ D ∧ closedBall (0 : E) (3 * r) ×ˢ Ω ⊆ K ∧
      (∀ i : s, 3 * r < (g i).radius) ∧
      IsCompact A ∧ A ⊆ G \ M ∧ (∀ q ∈ A, closedBall q ε ⊆ G \ M) ∧
      ∀ (H : HomogeneousSymbol E), D ⊆ H.domain → ContDiffOn ℝ ∞ H.h D →
        H.ConicHomogeneous → cNorm K 3 (fun z ↦ H.h z - H₀.h z) ≤ δ →
        ∃ charts : (i : s) → ComparisonChart H (g i),
          (∀ η : ComparisonGeometry.ParameterFamily g, ∀ x ∈ closedBall 0 (2 * r),
            c ≤ ‖ComparisonChart.familyGradient charts η x‖ ∧
              ‖ComparisonChart.familyGradient charts η x‖ ≤ C ∧
              normalizedCovector (ComparisonChart.familyGradient charts η x) ∈ A) ∧
          ∀ x ∈ closedBall 0 r, ∀ p ∈ Ω, H.h (x, p) = 0 →
            ∃ η : ComparisonGeometry.ParameterFamily g,
              p = ComparisonChart.familyGradient charts η x := by
  classical
  let F (p : {p : E // p ∈ Ω ∧ H₀.h (0, p) = 0}) :
      LocalComparisonFamily H₀ D G M p.1 :=
    Classical.choice (exists_localComparisonFamily H₀ hD hDH₀ hH₀ hhom₀
      (hΩzero p p.2.1) (hsource ⟨mem_singleton 0, p.2.1⟩) p.2.2
      (htransverse p p.2.1 p.2.2) hG hM (hregular p p.2.1))
  obtain ⟨s, r, δ, c, C, ε, K, hr, hδ, hc, hC, hε, hK, hKD, hsourceK,
    _hballs, hfamily⟩ :=
    exists_finite_comparison_cover_of_local H₀ hD hH₀ hfrozen hΩ hsource F
  have hzero : cNorm K 3 (fun z ↦ H₀.h z - H₀.h z) ≤ δ := by
    simp only [sub_self]
    exact (cNorm_zero K 3).le.trans hδ.le
  obtain ⟨_, hri, _, _⟩ := hfamily H₀ hDH₀ hH₀ hhom₀ hzero
  obtain ⟨A, hA, hAG, hAbuffer, hAcontains⟩ :=
    exists_compact_regular_directions (G := G) (M := M) hε
  refine ⟨s, fun i ↦ (F i.1).geometry, r, δ, c, C, ε / 2, K, A,
    hr, hδ, hc, hC, half_pos hε, hK, hKD, hsourceK, hri, hA, hAG, hAbuffer, ?_⟩
  intro H hHD hH hhom hsmall
  obtain ⟨charts, _, hbounds, hcover⟩ := hfamily H hHD hH hhom hsmall
  refine ⟨charts, ?_, ?_⟩
  · intro η x hx
    obtain ⟨hlo, hup, hbuf⟩ := hbounds η.1 x hx η.2.1 η.2.2
    refine ⟨hlo, hup, hAcontains _ ?_ hbuf⟩
    exact norm_smul_inv_norm (norm_pos_iff.mp (hc.trans_le hlo))
  · intro x hx p hp hz
    obtain ⟨i, η, hη, he⟩ := hcover x hx p hp hz
    exact ⟨⟨i, ⟨η, hη⟩⟩, he⟩

end JanetCartan.ProtectedFlow.PhaseCover
