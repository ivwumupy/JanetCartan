module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.FiniteOrderContinuity.PhaseBounds
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.FiniteOrderContinuity.RootStability.BranchUniqueness
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.SymbolStability
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.FlowJetBounds
/-!
# Identifying independently constructed Hamilton charts

For `app:lem:common-hamilton-phase`, the conic, finite-order continuity, and
one-high constructions must refer to the same phase. Scalar-root uniqueness
on a common transverse cylinder identifies initial data. ODE uniqueness then
identifies the actual Hamilton trajectories. The normalized inverse gap
identifies inverse coordinates and all phase jets on a common open target.
These results preserve every cylinder, state-range and inverse-buffer condition;
the common-family assembly remains responsible for choosing their common domains.
-/

@[expose] public noncomputable section

open Set Metric Filter
open scoped ContDiff InnerProductSpace Topology NNReal
namespace JanetCartan.HamiltonPhase
variable {E U : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
local instance compatibilityNormedSpaceE : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance compatibilityNormedSpaceU : NormedSpace ℝ U := InnerProductSpace.toNormedSpace

namespace HamiltonFlow
variable {H : HomogeneousSymbol E} (Φ Ψ : HamiltonFlow H U)

/-- Actual Hamilton flows with equal initial states agree on the common
short strip (`app:lem:common-hamilton-phase`). Smoothness on the compact state
buffer supplies the Lipschitz bound; no flow equality is assumed. -/
theorem state_eq_of_initial_eq
    {D : Set (E × E)} (hD : IsOpen D) (hDH : D ⊆ H.domain)
    (hH : ContDiffOn ℝ ∞ H.h D) {w : E × E} {R T : ℝ}
    (hRD : closedBall w R ⊆ D) (hT : 0 < T)
    (htime : Ioo (-T) T ⊆ Φ.time) (htime' : Ioo (-T) T ⊆ Ψ.time)
    {s : InitialData U} (hs : s ∈ Φ.parameters) (hs' : s ∈ Ψ.parameters)
    (hrange : ∀ t ∈ Ioo (-T) T, (Φ.position (t, s), Φ.momentum (t, s)) ∈ closedBall w R)
    (hrange' : ∀ t ∈ Ioo (-T) T, (Ψ.position (t, s), Ψ.momentum (t, s)) ∈ closedBall w R)
    (hinit : (Φ.position (0, s), Φ.momentum (0, s)) =
      (Ψ.position (0, s), Ψ.momentum (0, s))) :
    ∀ t ∈ Ioo (-T) T, (Φ.position (t, s), Φ.momentum (t, s)) =
      (Ψ.position (t, s), Ψ.momentum (t, s)) := by
  let L : ℝ≥0 := ⟨cNorm (closedBall w R) 2 H.vectorField, cNorm_nonneg _ _ _⟩
  have hfield : ContDiffOn ℝ ∞ H.vectorField D :=
    H.contDiffOn_vectorField_of_subset hD hDH (by simpa using hH)
  have hlip := (ODE.field_and_fderiv_lipschitzOnWith_of_cNorm
    (K := L) hD hRD hfield le_rfl).1
  intro t ht
  have hseg : uIcc 0 t ⊆ Ioo (-T) T :=
    ordConnected_Ioo.uIcc_subset ⟨by linarith, hT⟩ ht
  have hdist := autonomousFlow_dist_le hlip
    (fun t ht ↦ (Φ.position_hasDerivAt (htime (hseg ht)) hs).prodMk
      (Φ.momentum_hasDerivAt (htime (hseg ht)) hs))
    (fun t ht ↦ (Ψ.position_hasDerivAt (htime' (hseg ht)) hs').prodMk
      (Ψ.momentum_hasDerivAt (htime' (hseg ht)) hs'))
    (fun t ht ↦ hrange t (hseg ht)) (fun t ht ↦ hrange' t (hseg ht))
  simpa only [hinit, dist_self, zero_mul, dist_le_zero] using hdist

/-- Identify independently constructed Hamilton flows by their transverse
energy section (`app:lem:common-hamilton-phase`). Root equations follow from
the flows' energy identities, scalar uniqueness identifies the roots, and ODE
uniqueness identifies the trajectories. This is the compatibility input for
combining `exists_commonConicHamiltonPhases` with the finite-order and one-high
estimates on common buffered subdomains. -/
theorem state_eq_of_common_section
    {D : Set (E × E)} (hD : IsOpen D) (hDH : D ⊆ H.domain)
    (hH : ContDiffOn ℝ ∞ H.h D) {w : E × E} {R T : ℝ}
    (hRD : closedBall w R ⊆ D) (hT : 0 < T)
    (htime : Ioo (-T) T ⊆ Φ.time) (htime' : Ioo (-T) T ⊆ Ψ.time)
    (j : U →ₗᵢ[ℝ] E) (ν : E) {P : Set (InitialData U)}
    (hP : P ⊆ Φ.parameters) (hP' : P ⊆ Ψ.parameters)
    {l u c : ℝ} (hc : 0 < c)
    (hcylinder : MapsTo (transverseSectionState j ν) (P ×ˢ Icc l u) D)
    (hgap : ∀ s ∈ P, ∀ τ ∈ Icc l u,
      c ≤ |⟪H.hp (transverseSectionState j ν (s, τ)), ν⟫_ℝ|)
    (g g' : InitialData U → ℝ)
    (hg : ∀ s ∈ P, g s ∈ Icc l u)
    (hg' : ∀ s ∈ P, g' s ∈ Icc l u)
    (hinit : ∀ s ∈ P, (Φ.position (0, s), Φ.momentum (0, s)) =
      transverseSectionState j ν (s, g s))
    (hinit' : ∀ s ∈ P, (Ψ.position (0, s), Ψ.momentum (0, s)) =
      transverseSectionState j ν (s, g' s))
    (hrange : ∀ q ∈ Ioo (-T) T ×ˢ P, (Φ.position q, Φ.momentum q) ∈ closedBall w R)
    (hrange' : ∀ q ∈ Ioo (-T) T ×ˢ P, (Ψ.position q, Ψ.momentum q) ∈ closedBall w R) :
    EqOn (fun q ↦ (Φ.position q, Φ.momentum q))
      (fun q ↦ (Ψ.position q, Ψ.momentum q)) (Ioo (-T) T ×ˢ P) := by
  have hroot : EqOn g g' P := by
    apply CharacteristicRoot.root_eqOn_of_gap (f := sectionEnergyEquation H j ν) hc
    · intro s hs τ hτ
      exact (((hH.contDiffAt (hD.mem_nhds (hcylinder ⟨hs, hτ⟩))).comp (s, τ)
        (contDiff_transverseSectionState j ν).contDiffAt).sub
          contDiff_fst.snd.fst.contDiffAt).differentiableAt (by simp)
    · intro s hs τ hτ
      simpa only [scalarDerivative_sectionEnergyEquation H j ν (w := (s, τ)) (hDH (hcylinder ⟨hs, hτ⟩))]
        using hgap s hs τ hτ
    · intro s hs
      refine ⟨hg s hs, ?_⟩
      rw [sectionEnergyEquation, ← hinit s hs, Φ.initial_energy s (hP hs), sub_self]
    · intro s hs
      refine ⟨hg' s hs, ?_⟩
      rw [sectionEnergyEquation, ← hinit' s hs, Ψ.initial_energy s (hP' hs), sub_self]
  intro q hq
  exact Φ.state_eq_of_initial_eq Ψ hD hDH hH hRD hT htime htime' (hP hq.2) (hP' hq.2)
    (fun t ht ↦ hrange (t, q.2) ⟨ht, hq.2⟩)
    (fun t ht ↦ hrange' (t, q.2) ⟨ht, hq.2⟩)
    (by rw [hinit q.2 hq.2, hinit' q.2 hq.2, hroot hq.2]) q.1 hq.1
end HamiltonFlow

namespace ProjectionChart
variable {H : HomogeneousSymbol E} {Φ Ψ : HamiltonFlow H U}

omit [FiniteDimensional ℝ E] in
/-- Transfer all coordinate and phase jets between independently chosen
inverse charts of equal Hamilton trajectories (`app:lem:common-hamilton-phase`).
The flow equality is supplied by `HamiltonFlow.state_eq_of_common_section`;
the inverse gap and common lift buffer give uniqueness of coordinates.
This allows finite-order continuity and one-high estimates to be transported
to the conic family's local chart without identifying construction choices
definitionally. -/
theorem phase_jets_eq_of_state_eq (C : ProjectionChart Φ) (C' : ProjectionChart Ψ)
    {D : Set (ℝ × InitialData U)} (hD : Convex ℝ D)
    (A : (ℝ × InitialData U) ≃L[ℝ] (E × (ℝ × U)))
    (hadm : D ⊆ Φ.time ×ˢ Φ.parameters)
    (hgap : ∀ q ∈ D,
      ‖(A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U)).comp
        (fderiv ℝ Φ.augmentedProjection q) -
        ContinuousLinearMap.id ℝ (ℝ × InitialData U)‖ ≤ 1 / 2)
    (hstate : EqOn (fun q ↦ (Φ.position q, Φ.momentum q))
      (fun q ↦ (Ψ.position q, Ψ.momentum q)) D)
    {V : Set (E × (ℝ × U))} (hV : IsOpen V)
    (hVC : V ⊆ C.target) (hVC' : V ⊆ C'.target)
    (hmap : MapsTo (chartLift C.coordinates) V D)
    (hmap' : MapsTo (chartLift C'.coordinates) V D) :
    EqOn C.coordinates C'.coordinates V ∧
      EqOn (phase C.coordinates) (phase C'.coordinates) V ∧
      ∀ n : ℕ, EqOn (iteratedFDeriv ℝ n C.coordinates)
        (iteratedFDeriv ℝ n C'.coordinates) V ∧
        EqOn (iteratedFDeriv ℝ n (phase C.coordinates))
          (iteratedFDeriv ℝ n (phase C'.coordinates)) V := by
  have hproj : EqOn Φ.augmentedProjection Ψ.augmentedProjection D := by
    intro q hq
    change (Φ.position q, q.2.2) = (Ψ.position q, q.2.2)
    exact Prod.ext (congrArg (fun z : E × E ↦ z.1) (hstate hq)) rfl
  have he : EqOn C.coordinates C'.coordinates V := fun z hz ↦
    C.coordinates_eq_of_projection_eq C' hD A hadm hgap hproj
      (hVC hz) (hVC' hz) (hmap hz) (hmap' hz)
  have hp : EqOn (phase C.coordinates) (phase C'.coordinates) V := by
    intro z hz
    simp only [phase, he hz]
  refine ⟨he, hp, fun n ↦ ⟨?_, ?_⟩⟩
  · intro z hz
    have hh : C.coordinates =ᶠ[𝓝 z] C'.coordinates :=
      eventuallyEq_of_mem (hV.mem_nhds hz) (fun w hw ↦ he hw)
    exact (hh.iteratedFDeriv ℝ n).eq_of_nhds
  · intro z hz
    have hh : phase C.coordinates =ᶠ[𝓝 z] phase C'.coordinates :=
      eventuallyEq_of_mem (hV.mem_nhds hz) (fun w hw ↦ hp hw)
    exact (hh.iteratedFDeriv ℝ n).eq_of_nhds
end ProjectionChart
end JanetCartan.HamiltonPhase
