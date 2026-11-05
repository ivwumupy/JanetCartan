module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.Conservation

/-!
# Inputs and conservation laws for a local Hamilton flow

`app:lem:common-hamilton-phase`: the inputs below specify a Hamilton flow and
its first variational equation on a connected open time strip. They contain no
phase, eikonal equation, or conserved Liouville form. The `LocalFlow` module
constructs these inputs from a smooth Hamilton field and initial section data.
-/

@[expose] public noncomputable section

open scoped InnerProductSpace Topology
open Filter

namespace JanetCartan.HamiltonPhase

variable {E U F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The full differential of a flow from its velocity and initial-data variation
(`app:lem:common-hamilton-phase`). -/
def flowDifferential {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (v : V) (A : W →L[ℝ] V) : ℝ × W →L[ℝ] V :=
  (ContinuousLinearMap.fst ℝ ℝ W).smulRight v +
    A.comp (ContinuousLinearMap.snd ℝ ℝ W)

@[simp] theorem flowDifferential_apply {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (v : V) (A : W →L[ℝ] V) (w : ℝ × W) :
    flowDifferential v A w = w.1 • v + A w.2 := rfl

/-- Initial section point and canonical covector `(u', (e, η'))`. -/
abbrev InitialData (U : Type*) := U × (ℝ × U)

/-- A differentiable real degree-one Hamiltonian on an open phase-space domain
(`app:lem:common-hamilton-phase`). Only scaling factors near one are needed for
the differential identities, so truncated conic boxes are allowed. -/
structure HomogeneousSymbol (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  domain : Set (E × E)
  isOpen_domain : IsOpen domain
  h : E × E → ℝ
  hx : E × E → E
  hp : E × E → E
  hpDerivative : E × E → (E × E →L[ℝ] E)
  hasFDerivAt_h : ∀ z ∈ domain, HasFDerivAt h (hamiltonDifferential (hx z) (hp z)) z
  hasFDerivAt_hp : ∀ z ∈ domain, HasFDerivAt hp (hpDerivative z) z
  homogeneous : ∀ z ∈ domain, ∀ᶠ r : ℝ in 𝓝 1, h (z.1, r • z.2) = r * h z

/-- Euler identity for a locally degree-one symbol
(`app:lem:common-hamilton-phase`). -/
theorem HomogeneousSymbol.euler (H : HomogeneousSymbol E) {z : E × E} (hz : z ∈ H.domain) :
    ⟪z.2, H.hp z⟫_ℝ = H.h z :=
  euler_identity_of_local_homogeneity (H.hasFDerivAt_h z hz) (H.homogeneous z hz)

/-- A Hamilton flow with its genuine first derivatives and variational equation,
starting on the section at energy `e` and tangential momentum `η'`
(`app:lem:common-hamilton-phase`). -/
structure HamiltonFlow (H : HomogeneousSymbol E) (U : Type*)
    [NormedAddCommGroup U] [InnerProductSpace ℝ U] where
  time : Set ℝ
  isOpen_time : IsOpen time
  isPreconnected_time : IsPreconnected time
  zero_mem_time : 0 ∈ time
  parameters : Set (InitialData U)
  isOpen_parameters : IsOpen parameters
  sectionMap : U →L[ℝ] E
  position : ℝ × InitialData U → E
  momentum : ℝ × InitialData U → E
  positionVariation : ℝ × InitialData U → (InitialData U →L[ℝ] E)
  momentumVariation : ℝ × InitialData U → (InitialData U →L[ℝ] E)
  state_mem : ∀ t ∈ time, ∀ s ∈ parameters, (position (t, s), momentum (t, s)) ∈ H.domain
  position_derivative : ∀ t ∈ time, ∀ s ∈ parameters,
    HasFDerivAt position
      (flowDifferential (H.hp (position (t, s), momentum (t, s))) (positionVariation (t, s)))
      (t, s)
  momentum_derivative : ∀ t ∈ time, ∀ s ∈ parameters,
    HasFDerivAt momentum
      (flowDifferential (-H.hx (position (t, s), momentum (t, s))) (momentumVariation (t, s)))
      (t, s)
  variation_equation : ∀ t ∈ time, ∀ s ∈ parameters, ∀ v : InitialData U,
    HasDerivAt (fun r ↦ positionVariation (r, s) v)
      (H.hpDerivative (position (t, s), momentum (t, s))
        (positionVariation (t, s) v, momentumVariation (t, s) v)) t
  initial_position : ∀ s ∈ parameters, position (0, s) = sectionMap s.1
  initial_energy : ∀ s ∈ parameters, H.h (position (0, s), momentum (0, s)) = s.2.1
  initial_momentum : ∀ s ∈ parameters, ∀ v : U,
    ⟪momentum (0, s), sectionMap v⟫_ℝ = ⟪s.2.2, v⟫_ℝ

namespace HamiltonFlow

variable {H : HomogeneousSymbol E} (Φ : HamiltonFlow H U)

/-- The initial position variation is obtained by differentiating the actual
initial section condition (`app:lem:common-hamilton-phase`). -/
theorem initial_variation (s : InitialData U) (hs : s ∈ Φ.parameters)
    (v : InitialData U) : Φ.positionVariation (0, s) v = Φ.sectionMap v.1 := by
  have hi : HasFDerivAt (fun a : InitialData U ↦ ((0 : ℝ), a))
      ((0 : InitialData U →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (InitialData U))) s :=
    (hasFDerivAt_const (0 : ℝ) s).prodMk (hasFDerivAt_id s)
  have hd := (Φ.position_derivative 0 Φ.zero_mem_time s hs).comp s hi
  have heq : (fun a : InitialData U ↦ Φ.position (0, a)) =ᶠ[𝓝 s]
      (fun a ↦ Φ.sectionMap a.1) :=
    Filter.eventuallyEq_of_mem (Φ.isOpen_parameters.mem_nhds hs)
      (fun a ha ↦ Φ.initial_position a ha)
  have hd' := Φ.sectionMap.hasFDerivAt.comp s
    (ContinuousLinearMap.fst ℝ U (ℝ × U)).hasFDerivAt
  have he := (hd.congr_of_eventuallyEq heq.symm).unique hd'
  have hv := congrArg (fun L : InitialData U →L[ℝ] E ↦ L v) he
  simpa [flowDifferential] using hv

/-- The base component satisfies Hamilton's equation. -/
theorem position_hasDerivAt {t : ℝ} (ht : t ∈ Φ.time)
    {s : InitialData U} (hs : s ∈ Φ.parameters) :
    HasDerivAt (fun r ↦ Φ.position (r, s))
      (H.hp (Φ.position (t, s), Φ.momentum (t, s))) t := by
  have hd := (Φ.position_derivative t ht s hs).comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t s))
  simpa [flowDifferential, Function.comp_def] using hd

/-- The momentum component satisfies Hamilton's equation. -/
theorem momentum_hasDerivAt {t : ℝ} (ht : t ∈ Φ.time)
    {s : InitialData U} (hs : s ∈ Φ.parameters) :
    HasDerivAt (fun r ↦ Φ.momentum (r, s))
      (-H.hx (Φ.position (t, s), Φ.momentum (t, s))) t := by
  have hd := (Φ.momentum_derivative t ht s hs).comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t s))
  simpa [flowDifferential, Function.comp_def] using hd

/-- Energy equals the prescribed initial coordinate `e` throughout the strip
(`app:lem:common-hamilton-phase`). -/
theorem energy {t : ℝ} (ht : t ∈ Φ.time)
    {s : InitialData U} (hs : s ∈ Φ.parameters) :
    H.h (Φ.position (t, s), Φ.momentum (t, s)) = s.2.1 := by
  calc
    _ = H.h (Φ.position (0, s), Φ.momentum (0, s)) :=
      conserved_of_hasDerivAt_zero Φ.isOpen_time Φ.isPreconnected_time Φ.zero_mem_time
        (fun r hr ↦ hasDerivAt_energy_zero
          (H.hasFDerivAt_h _ (Φ.state_mem r hr s hs))
          (Φ.position_hasDerivAt hr hs) (Φ.momentum_hasDerivAt hr hs)) ht
    _ = _ := Φ.initial_energy s hs

/-- Conservation of `ξ · δx` for every initial-data variation, including
variations of `e` and `η'` (`app:lem:common-hamilton-phase`). -/
theorem liouville_variation {t : ℝ} (ht : t ∈ Φ.time)
    {s : InitialData U} (hs : s ∈ Φ.parameters) (v : InitialData U) :
    ⟪Φ.momentum (t, s), Φ.positionVariation (t, s) v⟫_ℝ = ⟪s.2.2, v.1⟫_ℝ := by
  have hc : ⟪Φ.momentum (t, s), Φ.positionVariation (t, s) v⟫_ℝ =
      ⟪Φ.momentum (0, s), Φ.positionVariation (0, s) v⟫_ℝ :=
    conserved_of_hasDerivAt_zero Φ.isOpen_time Φ.isPreconnected_time Φ.zero_mem_time
      (fun r hr ↦ hasDerivAt_liouville_zero (Φ.momentum_hasDerivAt hr hs)
        (Φ.variation_equation r hr s hs v)
        (differentiated_euler_identity
          (H.hasFDerivAt_h _ (Φ.state_mem r hr s hs))
          (H.hasFDerivAt_hp _ (Φ.state_mem r hr s hs))
          (Filter.eventuallyEq_of_mem (H.isOpen_domain.mem_nhds (Φ.state_mem r hr s hs))
            (fun z hz ↦ H.euler hz)))) ht
  rw [hc, Φ.initial_variation s hs v, Φ.initial_momentum s hs v.1]

/-- Allowing time to vary gives `ξ · dx = e dt + η' · du'`
(`app:lem:common-hamilton-phase`). -/
theorem liouville {t : ℝ} (ht : t ∈ Φ.time)
    {s : InitialData U} (hs : s ∈ Φ.parameters) (w : ℝ × InitialData U) :
    ⟪Φ.momentum (t, s),
      flowDifferential (H.hp (Φ.position (t, s), Φ.momentum (t, s)))
        (Φ.positionVariation (t, s)) w⟫_ℝ =
      s.2.1 * w.1 + ⟪s.2.2, w.2.1⟫_ℝ := by
  simp only [flowDifferential_apply, inner_add_right, inner_smul_right,
    H.euler (Φ.state_mem t ht s hs), Φ.energy ht hs, Φ.liouville_variation ht hs]
  ring

end HamiltonFlow
end JanetCartan.HamiltonPhase
