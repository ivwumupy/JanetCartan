module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.Phase
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# Local inverse projection charts

For `app:lem:common-hamilton-phase`, the inverse function theorem constructs
an actual projection chart when the augmented projection has an invertible
derivative. This local construction does not assert common quantitative buffers
for a family of symbols.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace JanetCartan.HamiltonPhase

variable {E U : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  {H : HomogeneousSymbol E} (Φ : HamiltonFlow H U)

/-- Retain the canonical covector in the base projection
(`app:lem:common-hamilton-phase`). -/
def HamiltonFlow.augmentedProjection (q : ℝ × InitialData U) : E × (ℝ × U) :=
  (Φ.position q, q.2.2)

/-- The differential of the base projection with the covector retained
(`app:lem:common-hamilton-phase`). -/
theorem HamiltonFlow.hasFDerivAt_augmentedProjection
    {q : ℝ × InitialData U} (hq : q ∈ Φ.time ×ˢ Φ.parameters) :
    HasFDerivAt Φ.augmentedProjection
      ((flowDifferential (H.hp (Φ.position q, Φ.momentum q)) (Φ.positionVariation q)).prod
        ((ContinuousLinearMap.snd ℝ U (ℝ × U)).comp
          (ContinuousLinearMap.snd ℝ ℝ (InitialData U)))) q :=
  (Φ.position_derivative q.1 hq.1 q.2 hq.2).prodMk
    ((ContinuousLinearMap.snd ℝ U (ℝ × U)).hasFDerivAt.comp q
      (ContinuousLinearMap.snd ℝ ℝ (InitialData U)).hasFDerivAt)

/-- At the initial section, the base-projection derivative has columns
`h_ξ, j`: these are `h_ξ,e₂,…,eₙ` in the manuscript's coordinates
(`app:lem:common-hamilton-phase`). -/
theorem HamiltonFlow.hasFDerivAt_initialProjection
    {s : InitialData U} (hs : s ∈ Φ.parameters) :
    HasFDerivAt (fun q : ℝ × U ↦ Φ.position (q.1, (q.2, s.2)))
      (flowDifferential (H.hp (Φ.sectionMap s.1, Φ.momentum (0, s))) Φ.sectionMap)
      (0, s.1) := by
  have hc := (Φ.position_derivative 0 Φ.zero_mem_time s hs).comp (0, s.1)
    ((ContinuousLinearMap.fst ℝ ℝ U).hasFDerivAt.prodMk
      ((ContinuousLinearMap.snd ℝ ℝ U).hasFDerivAt.prodMk (hasFDerivAt_const s.2 _)))
  convert! hc using 1
  apply ContinuousLinearMap.ext
  intro q
  simp [flowDifferential, Φ.initial_variation s hs, Φ.initial_position s hs]

/-- Turning a differentiable inverse of the augmented projection into the
section/time chart used by the phase formula (`app:lem:common-hamilton-phase`). -/
def ProjectionChart.ofOpenPartialHomeomorph
    (e : OpenPartialHomeomorph (ℝ × InitialData U) (E × (ℝ × U)))
    (he : (e : (ℝ × InitialData U) → E × (ℝ × U)) = Φ.augmentedProjection)
    (hs : e.source ⊆ Φ.time ×ˢ Φ.parameters)
    (hd : ∀ z ∈ e.target, DifferentiableAt ℝ e.symm z) : ProjectionChart Φ := by
  let C : E × (ℝ × U) → ℝ × U := fun z ↦ ((e.symm z).1, (e.symm z).2.1)
  have hlift (z : E × (ℝ × U)) (hz : z ∈ e.target) : chartLift C z = e.symm z := by
    have hη := congrArg Prod.snd (e.right_inv hz)
    rw [he] at hη
    change (e.symm z).2.2 = z.2 at hη
    simp only [chartLift, C, ← hη]
  exact {
    source := e.source
    target := e.target
    isOpen_source := e.open_source
    isOpen_target := e.open_target
    coordinates := C
    derivative := fun z ↦ fderiv ℝ C z
    hasFDerivAt_coordinates := fun z hz ↦ ((hd z hz).fst.prodMk (hd z hz).snd.fst).hasFDerivAt
    source_admissible := fun q hq ↦ hs hq
    maps_to_source := fun z hz ↦ by rw [hlift z hz]; exact e.map_target hz
    maps_to_target := fun q hq ↦ by simpa only [he, HamiltonFlow.augmentedProjection] using e.map_source hq
    right_inverse := fun z hz ↦ by
      rw [hlift z hz]
      exact congrArg Prod.fst (show Φ.augmentedProjection (e.symm z) = z by
        rw [← he]; exact e.right_inv hz)
    left_inverse := fun q hq ↦ by
      change ((e.symm (Φ.augmentedProjection q)).1, (e.symm (Φ.augmentedProjection q)).2.1) = _
      rw [← he, e.left_inv hq] }

/-- The inverse function theorem supplies a nonempty local projection chart
from a smooth augmented projection and an invertible derivative at one point.
No inverse chart or phase identity is an input (`app:lem:common-hamilton-phase`). -/
theorem HamiltonFlow.exists_localProjectionChart [CompleteSpace U]
    {q : ℝ × InitialData U} (hq : q ∈ Φ.time ×ˢ Φ.parameters)
    (hc : ContDiffAt ℝ 1 Φ.augmentedProjection q)
    (A : (ℝ × InitialData U) ≃L[ℝ] (E × (ℝ × U)))
    (hA : HasFDerivAt Φ.augmentedProjection (A : _ →L[ℝ] _) q) :
    ∃ C : ProjectionChart Φ, q ∈ C.source ∧ Φ.augmentedProjection q ∈ C.target := by
  let e := hc.toOpenPartialHomeomorph Φ.augmentedProjection hA (by simp)
  have he : (e : (ℝ × InitialData U) → E × (ℝ × U)) = Φ.augmentedProjection := rfl
  have hdi : ContDiffAt ℝ 1 e.symm (Φ.augmentedProjection q) := hc.to_localInverse hA (by simp)
  obtain ⟨V, hVsub, hV, hqV⟩ := eventually_nhds_iff.mp (hdi.eventually (by simp))
  let e₁ := e.restrOpen (Φ.time ×ˢ Φ.parameters) (Φ.isOpen_time.prod Φ.isOpen_parameters)
  let e₂ := (e₁.symm.restrOpen V hV).symm
  have he₂ : (e₂ : (ℝ × InitialData U) → E × (ℝ × U)) = Φ.augmentedProjection := rfl
  have hs : e₂.source ⊆ Φ.time ×ˢ Φ.parameters := fun _ hx ↦ hx.1.2
  have hd : ∀ z ∈ e₂.target, DifferentiableAt ℝ e₂.symm z :=
    fun z hz ↦ (hVsub z hz.2).differentiableAt (by simp)
  have hq₂ : q ∈ e₂.source := ⟨⟨hc.mem_toOpenPartialHomeomorph_source hA (by simp), hq⟩, hqV⟩
  exact ⟨ProjectionChart.ofOpenPartialHomeomorph Φ e₂ he₂ hs hd, hq₂, e₂.map_source hq₂⟩

/-- A smooth forward projection has a smooth inverse on one open chart.
Openness of invertibility supplies a neighborhood on which the inverse function
theorem applies at every point (`app:lem:common-hamilton-phase`). -/
theorem HamiltonFlow.exists_smoothLocalProjectionChart [CompleteSpace U]
    {q : ℝ × InitialData U} (hq : q ∈ Φ.time ×ˢ Φ.parameters)
    (hc : ContDiffOn ℝ ∞ Φ.augmentedProjection (Φ.time ×ˢ Φ.parameters))
    (A : (ℝ × InitialData U) ≃L[ℝ] (E × (ℝ × U)))
    (hA : HasFDerivAt Φ.augmentedProjection (A : _ →L[ℝ] _) q) :
    ∃ C : ProjectionChart Φ, q ∈ C.source ∧ Φ.augmentedProjection q ∈ C.target ∧
      ContDiffOn ℝ ∞ C.coordinates C.target := by
  have hD := Φ.isOpen_time.prod Φ.isOpen_parameters
  have hcq := hc.contDiffAt (hD.mem_nhds hq)
  let e := hcq.toOpenPartialHomeomorph Φ.augmentedProjection hA (by simp)
  have he : (e : (ℝ × InitialData U) → E × (ℝ × U)) = Φ.augmentedProjection := rfl
  have hequiv : ∀ᶠ x in 𝓝 q, ∃ B : (ℝ × InitialData U) ≃L[ℝ] (E × (ℝ × U)),
      (B : _ →L[ℝ] _) = fderiv ℝ Φ.augmentedProjection x := by
    have hN := A.nhds
    rw [← hA.fderiv] at hN
    exact (hcq.continuousAt_fderiv (by simp)).tendsto.eventually hN
  obtain ⟨V, hVsub, hV, hqV⟩ := eventually_nhds_iff.mp
    (hequiv.and (hD.mem_nhds hq))
  let e₁ := e.restrOpen V hV
  have he₁ : (e₁ : (ℝ × InitialData U) → E × (ℝ × U)) = Φ.augmentedProjection := rfl
  have hs : e₁.source ⊆ Φ.time ×ˢ Φ.parameters := fun _ hx ↦ (hVsub _ hx.2).2
  have hd (z : E × (ℝ × U)) (hz : z ∈ e₁.target) : ContDiffAt ℝ ∞ e₁.symm z := by
    have hx := e₁.map_target hz
    obtain ⟨B, hB⟩ := (hVsub _ hx.2).1
    have hf := hc.contDiffAt (hD.mem_nhds (hs hx))
    apply e₁.contDiffAt_symm hz (f₀' := B)
    · rw [he₁, hB]
      exact (hf.differentiableAt (by simp)).hasFDerivAt
    · exact hf
  have hq₁ : q ∈ e₁.source := ⟨hcq.mem_toOpenPartialHomeomorph_source hA (by simp), hqV⟩
  let C := ProjectionChart.ofOpenPartialHomeomorph Φ e₁ he₁ hs
    (fun z hz ↦ (hd z hz).differentiableAt (by simp))
  refine ⟨C, hq₁, e₁.map_source hq₁, ?_⟩
  intro z hz
  exact ((hd z hz).fst.prodMk (hd z hz).snd.fst).contDiffWithinAt

end JanetCartan.HamiltonPhase
