module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.Flow
public import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# The Hamilton phase on an inverse projection chart

For `app:lem:common-hamilton-phase`, construct `S = e t + u' · η'` from a
Hamilton flow and an actual differentiable local inverse of its base projection.
The flow and inverse are inputs; their existence, uniform buffers, mixed-Hessian
bounds, and higher-order estimates are separate obligations.
-/

@[expose] public noncomputable section

open scoped InnerProductSpace Topology
open Filter

namespace JanetCartan.HamiltonPhase

variable {E U F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Pairing with `(e, η')` (or with `(t,u')`) in split canonical coordinates
(`app:lem:common-hamilton-phase`). -/
def canonicalCovector (q : ℝ × U) : ℝ × U →L[ℝ] ℝ :=
  q.1 • ContinuousLinearMap.fst ℝ ℝ U +
    (innerSL ℝ q.2).comp (ContinuousLinearMap.snd ℝ ℝ U)

@[simp] theorem canonicalCovector_apply (q v : ℝ × U) :
    canonicalCovector q v = q.1 * v.1 + ⟪q.2, v.2⟫_ℝ := rfl

/-- The phase formula in `app:lem:common-hamilton-phase`. -/
def phase (C : E × (ℝ × U) → ℝ × U) (z : E × (ℝ × U)) : ℝ :=
  z.2.1 * (C z).1 + ⟪(C z).2, z.2.2⟫_ℝ

/-- The differential `ξ · dx + t de + u' · dη'` from
`app:lem:common-hamilton-phase`. -/
def phaseDifferential (p : E) (q : ℝ × U) : E × (ℝ × U) →L[ℝ] ℝ :=
  (innerSL ℝ p).comp (ContinuousLinearMap.fst ℝ E (ℝ × U)) +
    (canonicalCovector q).comp (ContinuousLinearMap.snd ℝ E (ℝ × U))

@[simp] theorem phaseDifferential_apply (p : E) (q : ℝ × U) (v : E × (ℝ × U)) :
    phaseDifferential p q v = ⟪p, v.1⟫_ℝ + q.1 * v.2.1 + ⟪q.2, v.2.2⟫_ℝ := by
  simp [phaseDifferential, add_assoc]

/-- Differentiate the explicit phase formula before using Hamilton's equations. -/
theorem hasFDerivAt_phase_formula {C : E × (ℝ × U) → ℝ × U}
    {C' : E × (ℝ × U) →L[ℝ] ℝ × U} {z : E × (ℝ × U)}
    (hC : HasFDerivAt C C' z) :
    HasFDerivAt (phase C)
      ((canonicalCovector z.2).comp C' +
        (canonicalCovector (C z)).comp (ContinuousLinearMap.snd ℝ E (ℝ × U))) z := by
  have hη := (ContinuousLinearMap.snd ℝ E (ℝ × U)).hasFDerivAt (x := z)
  have hd := (hη.fst.mul hC.fst).add (hC.snd.inner ℝ hη.snd)
  convert! hd using 1
  apply ContinuousLinearMap.ext
  intro v
  simp [canonicalCovector, fderivInnerCLM_apply, real_inner_comm]
  ring

/-- Lift inverse coordinates back to time and initial data, retaining `η`. -/
def chartLift (C : E × (ℝ × U) → ℝ × U) (z : E × (ℝ × U)) : ℝ × InitialData U :=
  ((C z).1, ((C z).2, z.2))

/-- The differential of `chartLift`. -/
def chartLiftDifferential (C' : E × (ℝ × U) →L[ℝ] ℝ × U) :
    E × (ℝ × U) →L[ℝ] ℝ × InitialData U :=
  ((ContinuousLinearMap.fst ℝ ℝ U).comp C').prod
    (((ContinuousLinearMap.snd ℝ ℝ U).comp C').prod (ContinuousLinearMap.snd ℝ E (ℝ × U)))

/-- Differentiation of the inverse-coordinate lift. -/
theorem hasFDerivAt_chartLift {C : E × (ℝ × U) → ℝ × U}
    {C' : E × (ℝ × U) →L[ℝ] ℝ × U} {z : E × (ℝ × U)}
    (hC : HasFDerivAt C C' z) :
    HasFDerivAt (chartLift C) (chartLiftDifferential C') z :=
  hC.fst.prodMk (hC.snd.prodMk (ContinuousLinearMap.snd ℝ E (ℝ × U)).hasFDerivAt)

namespace HamiltonFlow

variable {H : HomogeneousSymbol E} (Φ : HamiltonFlow H U)

/-- Differentiating the actual inverse-projection identity and using the proved
Liouville identity gives the full phase differential
(`app:lem:common-hamilton-phase`). -/
theorem hasFDerivAt_phase {C : E × (ℝ × U) → ℝ × U}
    {C' : E × (ℝ × U) →L[ℝ] ℝ × U} {z : E × (ℝ × U)}
    (hC : HasFDerivAt C C' z)
    (ht : (C z).1 ∈ Φ.time) (hs : ((C z).2, z.2) ∈ Φ.parameters)
    (hinv : (fun w ↦ Φ.position (chartLift C w)) =ᶠ[𝓝 z] Prod.fst) :
    HasFDerivAt (phase C) (phaseDifferential (Φ.momentum (chartLift C z)) (C z)) z := by
  have hproj := (Φ.position_derivative _ ht _ hs).comp z (hasFDerivAt_chartLift hC)
  have hproj' := (hproj.congr_of_eventuallyEq hinv.symm).unique
    (ContinuousLinearMap.fst ℝ E (ℝ × U)).hasFDerivAt
  have hliouville (v : E × (ℝ × U)) :
      ⟪Φ.momentum (chartLift C z), v.1⟫_ℝ = canonicalCovector z.2 (C' v) := by
    have he := congrArg (fun L : E × (ℝ × U) →L[ℝ] E ↦ L v) hproj'
    have hl := Φ.liouville ht hs (chartLiftDifferential C' v)
    change _ = v.1 at he
    rw [← he]
    exact hl
  convert! hasFDerivAt_phase_formula hC using 1
  apply ContinuousLinearMap.ext
  intro v
  simp only [phaseDifferential, add_apply, ContinuousLinearMap.comp_apply]
  exact congrArg (fun a ↦ a + canonicalCovector (C z) v.2) (hliouville v)

/-- The physical derivative of the phase is the transported momentum
(`app:ch_regular_base:eq:actual-eikonal`). -/
theorem hasFDerivAt_phase_position {C : E × (ℝ × U) → ℝ × U}
    {C' : E × (ℝ × U) →L[ℝ] ℝ × U} {z : E × (ℝ × U)}
    (hC : HasFDerivAt C C' z)
    (ht : (C z).1 ∈ Φ.time) (hs : ((C z).2, z.2) ∈ Φ.parameters)
    (hinv : (fun w ↦ Φ.position (chartLift C w)) =ᶠ[𝓝 z] Prod.fst) :
    HasFDerivAt (fun x ↦ phase C (x, z.2)) (innerSL ℝ (Φ.momentum (chartLift C z))) z.1 := by
  have hi : HasFDerivAt (fun x : E ↦ (x, z.2))
      ((ContinuousLinearMap.id ℝ E).prod 0) z.1 :=
    (hasFDerivAt_id z.1).prodMk (hasFDerivAt_const z.2 z.1)
  have hd := (Φ.hasFDerivAt_phase hC ht hs hinv).comp z.1 hi
  convert! hd using 1
  apply ContinuousLinearMap.ext
  intro v
  simp [phaseDifferential, canonicalCovector]

/-- The canonical derivative is precisely `(t,u')` in split coordinates
(`app:lem:common-hamilton-phase`). -/
theorem hasFDerivAt_phase_parameter {C : E × (ℝ × U) → ℝ × U}
    {C' : E × (ℝ × U) →L[ℝ] ℝ × U} {z : E × (ℝ × U)}
    (hC : HasFDerivAt C C' z)
    (ht : (C z).1 ∈ Φ.time) (hs : ((C z).2, z.2) ∈ Φ.parameters)
    (hinv : (fun w ↦ Φ.position (chartLift C w)) =ᶠ[𝓝 z] Prod.fst) :
    HasFDerivAt (fun η ↦ phase C (z.1, η)) (canonicalCovector (C z)) z.2 := by
  have hi : HasFDerivAt (fun η : ℝ × U ↦ (z.1, η))
      ((0 : ℝ × U →L[ℝ] E).prod (ContinuousLinearMap.id ℝ (ℝ × U))) z.2 :=
    (hasFDerivAt_const z.1 z.2).prodMk (hasFDerivAt_id z.2)
  have hd := (Φ.hasFDerivAt_phase hC ht hs hinv).comp z.2 hi
  convert! hd using 1
  apply ContinuousLinearMap.ext
  intro v
  simp [phaseDifferential]

/-- Energy conservation gives the eikonal equation for the actual gradient of
`S` (`app:ch_regular_base:eq:actual-eikonal`). -/
theorem eikonal [CompleteSpace E] {C : E × (ℝ × U) → ℝ × U}
    {C' : E × (ℝ × U) →L[ℝ] ℝ × U} {z : E × (ℝ × U)}
    (hC : HasFDerivAt C C' z)
    (ht : (C z).1 ∈ Φ.time) (hs : ((C z).2, z.2) ∈ Φ.parameters)
    (hinv : (fun w ↦ Φ.position (chartLift C w)) =ᶠ[𝓝 z] Prod.fst) :
    H.h (z.1, gradient (fun x ↦ phase C (x, z.2)) z.1) = z.2.1 := by
  have hg : HasGradientAt (fun x ↦ phase C (x, z.2)) (Φ.momentum (chartLift C z)) z.1 :=
    Φ.hasFDerivAt_phase_position hC ht hs hinv
  rw [hg.gradient, ← hinv.eq_of_nhds]
  exact Φ.energy ht hs

end HamiltonFlow

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- The initial value follows when the inverse chart sends the section to
`(0,x')` (`app:ch_regular_base:eq:actual-eikonal`). -/
theorem phase_on_section {C : E × (ℝ × U) → ℝ × U} {j : U → E}
    {u : U} {η : ℝ × U} (hC : C (j u, η) = (0, u)) :
    phase C (j u, η) = ⟪u, η.2⟫_ℝ := by
  simp [phase, hC]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- Invariance of inverse base coordinates under positive covector scaling
implies degree-one homogeneity of the explicit phase
(`app:lem:common-hamilton-phase`). -/
theorem phase_smul {C : E × (ℝ × U) → ℝ × U} {x : E} {η : ℝ × U} {r : ℝ}
    (hC : C (x, r • η) = C (x, η)) :
    phase C (x, r • η) = r * phase C (x, η) := by
  simp [phase, hC, inner_smul_right, mul_add, mul_assoc]

/-- An actual inverse chart for the base projection, with the canonical
parameter retained. These are inverse-map inputs, not phase identities
(`app:lem:common-hamilton-phase`). -/
structure ProjectionChart {H : HomogeneousSymbol E} (Φ : HamiltonFlow H U) where
  source : Set (ℝ × InitialData U)
  target : Set (E × (ℝ × U))
  isOpen_source : IsOpen source
  isOpen_target : IsOpen target
  coordinates : E × (ℝ × U) → ℝ × U
  derivative : E × (ℝ × U) → (E × (ℝ × U) →L[ℝ] ℝ × U)
  hasFDerivAt_coordinates : ∀ z ∈ target, HasFDerivAt coordinates (derivative z) z
  source_admissible : ∀ q ∈ source, q.1 ∈ Φ.time ∧ q.2 ∈ Φ.parameters
  maps_to_source : ∀ z ∈ target, chartLift coordinates z ∈ source
  maps_to_target : ∀ q ∈ source, (Φ.position q, q.2.2) ∈ target
  right_inverse : ∀ z ∈ target, Φ.position (chartLift coordinates z) = z.1
  left_inverse : ∀ q ∈ source, coordinates (Φ.position q, q.2.2) = (q.1, q.2.1)

namespace ProjectionChart

variable {H : HomogeneousSymbol E} {Φ : HamiltonFlow H U} (C : ProjectionChart Φ)

/-- The phase differential throughout an inverse chart
(`app:lem:common-hamilton-phase`). -/
theorem hasFDerivAt_phase {z : E × (ℝ × U)} (hz : z ∈ C.target) :
    HasFDerivAt (phase C.coordinates)
      (phaseDifferential (Φ.momentum (chartLift C.coordinates z)) (C.coordinates z)) z := by
  have ha := C.source_admissible _ (C.maps_to_source z hz)
  exact Φ.hasFDerivAt_phase (C.hasFDerivAt_coordinates z hz) ha.1 ha.2
    (Filter.eventuallyEq_of_mem (C.isOpen_target.mem_nhds hz) (fun w hw ↦ C.right_inverse w hw))

/-- The eikonal equation on the whole supplied chart
(`app:ch_regular_base:eq:actual-eikonal`). -/
theorem eikonal [CompleteSpace E] {z : E × (ℝ × U)} (hz : z ∈ C.target) :
    H.h (z.1, gradient (fun x ↦ phase C.coordinates (x, z.2)) z.1) = z.2.1 := by
  have ha := C.source_admissible _ (C.maps_to_source z hz)
  exact Φ.eikonal (C.hasFDerivAt_coordinates z hz) ha.1 ha.2
    (Filter.eventuallyEq_of_mem (C.isOpen_target.mem_nhds hz) (fun w hw ↦ C.right_inverse w hw))

/-- The section value follows from the left inverse and the initial position
of the flow (`app:ch_regular_base:eq:actual-eikonal`). -/
theorem initial_value {u : U} {η : ℝ × U} (hs : (0, (u, η)) ∈ C.source) :
    phase C.coordinates (Φ.sectionMap u, η) = ⟪u, η.2⟫_ℝ := by
  have hc := C.left_inverse (0, (u, η)) hs
  have hi := Φ.initial_position (u, η) (C.source_admissible _ hs).2
  simp only [hi] at hc
  exact phase_on_section hc

/-- Base-flow scaling invariance transfers to the inverse coordinates. The
scaling law is explicit here; deriving it by ODE uniqueness is separate
(`app:lem:common-hamilton-phase`). -/
theorem coordinates_smul {x : E} {η : ℝ × U} {r : ℝ}
    (hz : (x, η) ∈ C.target)
    (hs : ((C.coordinates (x, η)).1, ((C.coordinates (x, η)).2, r • η)) ∈ C.source)
    (hscale : Φ.position ((C.coordinates (x, η)).1, ((C.coordinates (x, η)).2, r • η)) =
      Φ.position (chartLift C.coordinates (x, η))) :
    C.coordinates (x, r • η) = C.coordinates (x, η) := by
  have hc := C.left_inverse _ hs
  rw [hscale, C.right_inverse _ hz] at hc
  exact hc

/-- Degree-one phase scaling from the base-flow scaling law and the inverse
chart (`app:lem:common-hamilton-phase`). -/
theorem homogeneous {x : E} {η : ℝ × U} {r : ℝ}
    (hz : (x, η) ∈ C.target)
    (hs : ((C.coordinates (x, η)).1, ((C.coordinates (x, η)).2, r • η)) ∈ C.source)
    (hscale : Φ.position ((C.coordinates (x, η)).1, ((C.coordinates (x, η)).2, r • η)) =
      Φ.position (chartLift C.coordinates (x, η))) :
    phase C.coordinates (x, r • η) = r * phase C.coordinates (x, η) :=
  phase_smul (C.coordinates_smul hz hs hscale)

end ProjectionChart

end JanetCartan.HamiltonPhase
