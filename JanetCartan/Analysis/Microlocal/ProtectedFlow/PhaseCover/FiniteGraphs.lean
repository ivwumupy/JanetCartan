module

public import JanetCartan.Analysis.Microlocal.ProtectedFlow.PhaseCover.ChartData
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Compact families of actual comparison graphs

For `app:ch_regular:thm:no-return`, the finite comparison charts have different
transverse sections. Their disjoint union of compact zero-energy parameter
sets gives one compact parameter space for
`ProtectedFlow.exists_uniform_characteristic_buffer`. Joint continuity,
physical differentiability and Hamilton tangency follow from the actual charts.
The final lemma encloses all uniformly buffered directions in one fixed compact
regular angular set, as used by `exists_finite_comparison_cover`.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff Topology

namespace JanetCartan.ProtectedFlow.PhaseCover

open HamiltonPhase

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {I : Type*}

namespace ComparisonGeometry

/-- The disjoint union of the charts' actual compact zero-energy slices.
Use its entire space as `V` in `exists_uniform_characteristic_buffer`
(`app:ch_regular:thm:no-return`). -/
abbrev ParameterFamily (g : I → ComparisonGeometry E) := Σ i : I, (g i).parameters

/-- A finite family of compact parameter slices is one compact parameter
space for the complete graph family (`app:ch_regular:thm:no-return`). -/
theorem isCompact_parameterFamily [Finite I] (g : I → ComparisonGeometry E) :
    IsCompact (univ : Set (ParameterFamily g)) := by
  let (i : I) : CompactSpace (g i).parameters :=
    isCompact_iff_compactSpace.mp (g i).isCompact_parameters
  exact isCompact_univ

end ComparisonGeometry

namespace ComparisonChart

variable {H : HomogeneousSymbol E} {g : I → ComparisonGeometry E}
  (C : (i : I) → ComparisonChart H (g i))

/-- All actual phase gradients, indexed by the disjoint compact parameter
slices (`app:ch_regular:thm:no-return`). -/
def familyGradient (η : ComparisonGeometry.ParameterFamily g) (x : E) : E :=
  (C η.1).gradientMap η.2.1 x

/-- Joint continuity on the entire common outer physical ball and parameter
family. This supplies `hg` in `exists_uniform_characteristic_buffer`
(`app:ch_regular:thm:no-return`). -/
theorem continuousOn_familyGradient {r : ℝ} (hr : ∀ i, r ≤ (g i).radius) :
    ContinuousOn (fun z : E × ComparisonGeometry.ParameterFamily g ↦
      familyGradient C z.2 z.1) (closedBall 0 (2 * r) ×ˢ univ) := by
  have hb (i : I) : Continuous
      (fun z : (g i).parameters × closedBall (0 : E) (2 * r) ↦
        (C i).gradientMap z.1.1 z.2.1) := by
    apply (C i).gradient_smooth.continuousOn.comp_continuous
      (continuous_subtype_val.snd'.prodMk continuous_subtype_val.fst')
    intro z
    exact (g i).outer_product_subset_domain
      ⟨closedBall_subset_closedBall (by linarith [hr i]) z.2.2, z.1.2⟩
  have hall : Continuous
      (fun z : ComparisonGeometry.ParameterFamily g × closedBall (0 : E) (2 * r) ↦
        familyGradient C z.1 z.2.1) := by
    exact (continuous_sigma (f := fun z : Σ i : I,
      (g i).parameters × closedBall (0 : E) (2 * r) ↦
        (C z.1).gradientMap z.2.1.1 z.2.2.1) hb).comp
      (Homeomorph.sigmaProdDistrib (X := fun i ↦ (g i).parameters)
        (Y := closedBall (0 : E) (2 * r))).continuous
  rw [continuousOn_iff_continuous_domRestrict]
  exact hall.comp (continuous_subtype_val.snd.prodMk
    (continuous_subtype_val.fst.subtype_mk (fun z ↦ z.2.1)))

/-- Physical differentiability of every actual graph on the outer ball,
including its boundary. This supplies `hgraph` in
`exists_uniform_characteristic_buffer` (`app:ch_regular:thm:no-return`). -/
theorem hasFDerivAt_familyGradient {r : ℝ} (hr : ∀ i, r ≤ (g i).radius)
    (η : ComparisonGeometry.ParameterFamily g) {x : E} (hx : x ∈ closedBall 0 (2 * r)) :
    HasFDerivAt (familyGradient C η) (fderiv ℝ (familyGradient C η) x) x := by
  have hz := (g η.1).outer_product_subset_domain (a := (x, η.2.1))
    ⟨closedBall_subset_closedBall (by linarith [hr η.1]) hx, η.2.2⟩
  exact (((C η.1).gradient_smooth.contDiffAt ((g η.1).isOpen_domain.mem_nhds hz)).comp x
    (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp) |>.hasFDerivAt

/-- The whole parameter family solves the zero-energy equation on the outer
ball (`app:ch_regular:thm:no-return`). -/
theorem zero_energy_familyGradient {r : ℝ} (hr : ∀ i, r ≤ (g i).radius)
    (η : ComparisonGeometry.ParameterFamily g) {x : E} (hx : x ∈ closedBall 0 (2 * r)) :
    (x, familyGradient C η x) ∈ H.domain ∧ H.h (x, familyGradient C η x) = 0 :=
  (C η.1).zero_energy
    (closedBall_subset_closedBall (by linarith [hr η.1]) hx) η.2.2

/-- Tangency of every actual graph in the compact family. This supplies
`htangent` in `exists_uniform_characteristic_buffer`, using the proved
eikonal differentiation identity (`app:ch_regular:thm:no-return`). -/
theorem hamilton_tangent_familyGradient {r : ℝ} (hr : ∀ i, r ≤ (g i).radius)
    (η : ComparisonGeometry.ParameterFamily g) {x : E} (hx : x ∈ closedBall 0 (2 * r)) :
    -H.hx (x, familyGradient C η x) =
      (fderiv ℝ (familyGradient C η) x) (H.hp (x, familyGradient C η x)) :=
  (C η.1).hamilton_tangent ((g η.1).outer_product_subset_domain
    ⟨closedBall_subset_closedBall (by linarith [hr η.1]) hx, η.2.2⟩)

end ComparisonChart

/-- Enclose all unit directions with a given regular buffer in one compact
regular set, retaining half the buffer. Applied after finite selection, this
makes the angular enclosure independent of the current symbol in
`exists_finite_comparison_cover` (`app:ch_regular:thm:no-return`). -/
theorem exists_compact_regular_directions {G M : Set E} {ε : ℝ} (hε : 0 < ε) :
    ∃ A : Set E, IsCompact A ∧ A ⊆ G \ M ∧
      (∀ q ∈ A, closedBall q (ε / 2) ⊆ G \ M) ∧
      ∀ q, ‖q‖ = 1 → closedBall q ε ⊆ G \ M → q ∈ A := by
  let B : Set E := ⋂ (z : E) (_ : z ∉ G \ M), {q | ε ≤ dist z q}
  let A := sphere (0 : E) 1 ∩ B
  have hB : IsClosed B := isClosed_iInter fun z ↦ isClosed_iInter fun _ ↦
    isClosed_le continuous_const (continuous_const.dist continuous_id)
  have hbuffer : ∀ q ∈ A, closedBall q (ε / 2) ⊆ G \ M := by
    intro q hq z hz
    by_contra hout
    have hh : ε ≤ dist z q := mem_iInter.mp (mem_iInter.mp hq.2 z) hout
    rw [mem_closedBall] at hz
    linarith
  refine ⟨A, (isCompact_sphere 0 1).inter_right hB,
    fun q hq ↦ hbuffer q hq (mem_closedBall_self (by positivity)), hbuffer, ?_⟩
  intro q hq hball
  refine ⟨by simpa only [mem_sphere, dist_zero_right] using hq, ?_⟩
  apply mem_iInter.mpr
  intro z
  apply mem_iInter.mpr
  intro hz
  change ε ≤ dist z q
  exact le_of_not_gt (fun hlt ↦ hz (hball (mem_closedBall.mpr hlt.le)))

end JanetCartan.ProtectedFlow.PhaseCover
