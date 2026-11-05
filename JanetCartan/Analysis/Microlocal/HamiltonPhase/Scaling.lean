module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.LocalFlow
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.Phase
public import Mathlib.Analysis.ODE.ExistUnique

/-!
# Positive covector scaling of Hamilton flows

For `app:lem:common-hamilton-phase`, differentiating degree-one homogeneity
gives degree zero for the momentum gradient and degree one for the position
gradient. Local ODE uniqueness then propagates the initial momentum scaling
throughout the connected time strip. The inverse chart still requires actual
membership of the scaled lift in its source.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology InnerProductSpace

namespace JanetCartan.HamiltonPhase

variable {E U : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]

/-- Scaling only the covector in phase space (`app:lem:common-hamilton-phase`). -/
def covectorScaling (r : ℝ) : E × E →L[ℝ] E × E :=
  (ContinuousLinearMap.fst ℝ E E).prod (r • ContinuousLinearMap.snd ℝ E E)

@[simp] theorem covectorScaling_apply (r : ℝ) (z : E × E) :
    covectorScaling r z = (z.1, r • z.2) := rfl

namespace HomogeneousSymbol

variable (H : HomogeneousSymbol E)

/-- The conic-domain and degree-one symbol hypotheses used for arbitrary positive
scales in `app:lem:common-hamilton-phase`. Openness and the actual derivatives
are already part of `HomogeneousSymbol`; no flow identity is included here. -/
structure ConicHomogeneous : Prop where
  scale_mem : ∀ z ∈ H.domain, ∀ r : ℝ, 0 < r → (z.1, r • z.2) ∈ H.domain
  scale_symbol : ∀ z ∈ H.domain, ∀ r : ℝ, 0 < r → H.h (z.1, r • z.2) = r * H.h z

/-- The differential form of degree-one homogeneity
(`app:lem:common-hamilton-phase`). -/
theorem differential_smul (hH : H.ConicHomogeneous) {z : E × E}
    (hz : z ∈ H.domain) {r : ℝ} (hr : 0 < r) (v : E × E) :
    hamiltonDifferential (H.hx (z.1, r • z.2)) (H.hp (z.1, r • z.2))
      (v.1, r • v.2) = r * hamiltonDifferential (H.hx z) (H.hp z) v := by
  have hd := (H.hasFDerivAt_h _ (hH.scale_mem z hz r hr)).comp z
    (covectorScaling (E := E) r).hasFDerivAt
  have he : (fun w : E × E ↦ H.h (covectorScaling r w)) =ᶠ[𝓝 z]
      (fun w ↦ r * H.h w) :=
    eventuallyEq_of_mem (H.isOpen_domain.mem_nhds hz)
      (fun w hw ↦ hH.scale_symbol w hw r hr)
  have heq := (hd.congr_of_eventuallyEq he.symm).unique
    ((H.hasFDerivAt_h z hz).const_mul r)
  exact congrArg (fun L : E × E →L[ℝ] ℝ ↦ L v) heq

/-- The position gradient has degree one in the covector
(`app:lem:common-hamilton-phase`). -/
theorem hx_smul (hH : H.ConicHomogeneous) {z : E × E}
    (hz : z ∈ H.domain) {r : ℝ} (hr : 0 < r) :
    H.hx (z.1, r • z.2) = r • H.hx z := by
  apply ext_inner_right ℝ
  intro v
  simpa [hamiltonDifferential_apply, inner_smul_left] using
    H.differential_smul hH hz hr (v, 0)

/-- The momentum gradient has degree zero in the covector
(`app:lem:common-hamilton-phase`). -/
theorem hp_smul (hH : H.ConicHomogeneous) {z : E × E}
    (hz : z ∈ H.domain) {r : ℝ} (hr : 0 < r) :
    H.hp (z.1, r • z.2) = H.hp z := by
  apply ext_inner_right ℝ
  intro v
  have he := H.differential_smul hH hz hr (0, v)
  simp only [hamiltonDifferential_apply, inner_zero_right, zero_add, inner_smul_right] at he
  exact mul_left_cancel₀ (ne_of_gt hr) he

/-- The Hamilton vector field commutes with covector scaling
(`app:lem:common-hamilton-phase`). -/
theorem vectorField_smul (hH : H.ConicHomogeneous) {z : E × E}
    (hz : z ∈ H.domain) {r : ℝ} (hr : 0 < r) :
    H.vectorField (covectorScaling r z) = covectorScaling r (H.vectorField z) := by
  simp [vectorField, H.hp_smul hH hz hr, H.hx_smul hH hz hr]

end HomogeneousSymbol

/-- Local Lipschitz uniqueness extends over a connected open time strip. -/
private theorem solution_eqOn_of_contDiffOn
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : F → F} {D : Set F} (hD : IsOpen D) (hV : ContDiffOn ℝ 1 V D)
    {I : Set ℝ} (hI : IsOpen I) (hIc : IsPreconnected I)
    {f g : ℝ → F} (hf : ∀ t ∈ I, HasDerivAt f (V (f t)) t)
    (hg : ∀ t ∈ I, HasDerivAt g (V (g t)) t)
    (hfm : ∀ t ∈ I, f t ∈ D) {t₀ : ℝ} (ht₀ : t₀ ∈ I)
    (heq : f t₀ = g t₀) : EqOn f g I := by
  let S := {t | f t = g t} ∩ I
  have hlocal (t : ℝ) (ht : t ∈ S) : f =ᶠ[𝓝 t] g := by
    obtain ⟨K, B, hB, hVB⟩ :=
      ((hV (f t) (hfm t ht.2)).contDiffAt
        (hD.mem_nhds (hfm t ht.2))).exists_lipschitzOnWith
    have hfb : ∀ᶠ s in 𝓝 t, f s ∈ B := (hf t ht.2).continuousAt hB
    have hgb : ∀ᶠ s in 𝓝 t, g s ∈ B := (hg t ht.2).continuousAt (ht.1 ▸ hB)
    have htime : ∀ᶠ s in 𝓝 t, s ∈ I := hI.mem_nhds ht.2
    exact ODE_solution_unique_of_eventually (v := fun _ ↦ V) (s := fun _ ↦ B)
      (Eventually.of_forall (fun _ ↦ hVB))
      ((htime.and hfb).mono (fun s hs ↦ ⟨hf s hs.1, hs.2⟩))
      ((htime.and hgb).mono (fun s hs ↦ ⟨hg s hs.1, hs.2⟩)) ht.1
  have hSo : IsOpen S := isOpen_iff_mem_nhds.mpr fun t ht ↦
    (hlocal t ht).and (hI.mem_nhds ht.2)
  have hSc : closure S ∩ I ⊆ S := by
    intro t ht
    refine ⟨?_, ht.2⟩
    apply sub_eq_zero.mp
    exact ((hf t ht.2).continuousAt.sub (hg t ht.2).continuousAt).continuousWithinAt
      |>.eq_const_of_mem_closure ht.1 (fun y hy ↦ sub_eq_zero.mpr hy.1)
  have hsub := hIc.subset_of_closure_inter_subset hSo ⟨t₀, ht₀, heq, ht₀⟩ hSc
  exact fun t ht ↦ (hsub ht).1

namespace HamiltonFlow

variable {H : HomogeneousSymbol E} (Φ : HamiltonFlow H U)

/-- Positive covector scaling commutes with the full Hamilton flow throughout
its time strip (`app:lem:common-hamilton-phase`). Both initial data must be
admissible. The only scaling input about the solution is its momentum at time
zero; the section condition already fixes the initial base point. A `C¹`
Hamilton field on the open conic symbol domain suffices for uniqueness. -/
theorem state_smul (hH : H.ConicHomogeneous)
    (hfield : ContDiffOn ℝ 1 H.vectorField H.domain)
    {u : U} {η : ℝ × U} {r : ℝ} (hr : 0 < r)
    (hs : (u, η) ∈ Φ.parameters) (hrs : (u, r • η) ∈ Φ.parameters)
    (hinit : Φ.momentum (0, (u, r • η)) = r • Φ.momentum (0, (u, η)))
    {t : ℝ} (ht : t ∈ Φ.time) :
    (Φ.position (t, (u, r • η)), Φ.momentum (t, (u, r • η))) =
      (Φ.position (t, (u, η)), r • Φ.momentum (t, (u, η))) := by
  let f : ℝ → E × E := fun a ↦
    (Φ.position (a, (u, r • η)), Φ.momentum (a, (u, r • η)))
  let g : ℝ → E × E := fun a ↦
    covectorScaling r (Φ.position (a, (u, η)), Φ.momentum (a, (u, η)))
  have hf (a : ℝ) (ha : a ∈ Φ.time) : HasDerivAt f (H.vectorField (f a)) a :=
    (Φ.position_hasDerivAt ha hrs).prodMk (Φ.momentum_hasDerivAt ha hrs)
  have hg (a : ℝ) (ha : a ∈ Φ.time) : HasDerivAt g (H.vectorField (g a)) a := by
    have hd := (covectorScaling (E := E) r).hasFDerivAt.comp_hasDerivAt a
      ((Φ.position_hasDerivAt ha hs).prodMk (Φ.momentum_hasDerivAt ha hs))
    change HasDerivAt g (H.vectorField (covectorScaling r
      (Φ.position (a, (u, η)), Φ.momentum (a, (u, η))))) a
    rw [H.vectorField_smul hH (Φ.state_mem a ha (u, η) hs) hr]
    exact hd
  have hi : f 0 = g 0 := by
    apply Prod.ext
    · exact (Φ.initial_position _ hrs).trans (Φ.initial_position _ hs).symm
    · exact hinit
  exact solution_eqOn_of_contDiffOn H.isOpen_domain hfield Φ.isOpen_time
    Φ.isPreconnected_time hf hg (fun a ha ↦ Φ.state_mem a ha _ hrs)
    Φ.zero_mem_time hi ht

/-- The base flow is invariant under positive covector scaling
(`app:lem:common-hamilton-phase`). -/
theorem position_smul (hH : H.ConicHomogeneous)
    (hfield : ContDiffOn ℝ 1 H.vectorField H.domain)
    {u : U} {η : ℝ × U} {r : ℝ} (hr : 0 < r)
    (hs : (u, η) ∈ Φ.parameters) (hrs : (u, r • η) ∈ Φ.parameters)
    (hinit : Φ.momentum (0, (u, r • η)) = r • Φ.momentum (0, (u, η)))
    {t : ℝ} (ht : t ∈ Φ.time) :
    Φ.position (t, (u, r • η)) = Φ.position (t, (u, η)) :=
  congrArg Prod.fst (Φ.state_smul hH hfield hr hs hrs hinit ht)

/-- The transported momentum has degree one in its initial canonical covector
(`app:lem:common-hamilton-phase`). -/
theorem momentum_smul (hH : H.ConicHomogeneous)
    (hfield : ContDiffOn ℝ 1 H.vectorField H.domain)
    {u : U} {η : ℝ × U} {r : ℝ} (hr : 0 < r)
    (hs : (u, η) ∈ Φ.parameters) (hrs : (u, r • η) ∈ Φ.parameters)
    (hinit : Φ.momentum (0, (u, r • η)) = r • Φ.momentum (0, (u, η)))
    {t : ℝ} (ht : t ∈ Φ.time) :
    Φ.momentum (t, (u, r • η)) = r • Φ.momentum (t, (u, η)) :=
  congrArg Prod.snd (Φ.state_smul hH hfield hr hs hrs hinit ht)

end HamiltonFlow

namespace ProjectionChart

variable {H : HomogeneousSymbol E} {Φ : HamiltonFlow H U} (C : ProjectionChart Φ)

/-- The inverse base coordinates are invariant under positive covector scaling,
by Hamilton ODE uniqueness (`app:lem:common-hamilton-phase`). Membership of the
scaled lift in the actual chart source is essential for its left inverse. -/
theorem coordinates_smul_of_initial_momentum (hH : H.ConicHomogeneous)
    (hfield : ContDiffOn ℝ 1 H.vectorField H.domain)
    {x : E} {η : ℝ × U} {r : ℝ} (hr : 0 < r) (hz : (x, η) ∈ C.target)
    (hs : ((C.coordinates (x, η)).1, ((C.coordinates (x, η)).2, r • η)) ∈ C.source)
    (hinit : Φ.momentum (0, ((C.coordinates (x, η)).2, r • η)) =
      r • Φ.momentum (0, ((C.coordinates (x, η)).2, η))) :
    C.coordinates (x, r • η) = C.coordinates (x, η) := by
  have ha := C.source_admissible _ (C.maps_to_source _ hz)
  have hra := C.source_admissible _ hs
  exact C.coordinates_smul hz hs
    (Φ.position_smul hH hfield hr ha.2 hra.2 hinit ha.1)

/-- Degree-one homogeneity of the Hamilton phase, with the base-flow scaling
premise of `ProjectionChart.homogeneous` discharged by ODE uniqueness
(`app:lem:common-hamilton-phase`). The scaled-source membership and initial
momentum scaling are explicit inputs from the chart and section constructions. -/
theorem homogeneous_of_initial_momentum (hH : H.ConicHomogeneous)
    (hfield : ContDiffOn ℝ 1 H.vectorField H.domain)
    {x : E} {η : ℝ × U} {r : ℝ} (hr : 0 < r) (hz : (x, η) ∈ C.target)
    (hs : ((C.coordinates (x, η)).1, ((C.coordinates (x, η)).2, r • η)) ∈ C.source)
    (hinit : Φ.momentum (0, ((C.coordinates (x, η)).2, r • η)) =
      r • Φ.momentum (0, ((C.coordinates (x, η)).2, η))) :
    phase C.coordinates (x, r • η) = r * phase C.coordinates (x, η) := by
  have ha := C.source_admissible _ (C.maps_to_source _ hz)
  have hra := C.source_admissible _ hs
  exact C.homogeneous hz hs
    (Φ.position_smul hH hfield hr ha.2 hra.2 hinit ha.1)

end ProjectionChart

end JanetCartan.HamiltonPhase
