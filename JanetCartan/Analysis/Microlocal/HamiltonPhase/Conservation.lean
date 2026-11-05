module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Conservation identities for homogeneous Hamilton flows

The calculation in `app:lem:common-hamilton-phase` is local in phase space.
These results assume actual Hamilton and variational equations; they do not
assert existence of their solutions.
-/

@[expose] public noncomputable section

open scoped InnerProductSpace Topology
open Filter

namespace JanetCartan.HamiltonPhase

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The differential of a real Hamiltonian, in position/momentum order
(`app:lem:common-hamilton-phase`). -/
def hamiltonDifferential (hx hp : E) : E × E →L[ℝ] ℝ :=
  (innerSL ℝ hx).comp (ContinuousLinearMap.fst ℝ E E) +
    (innerSL ℝ hp).comp (ContinuousLinearMap.snd ℝ E E)

@[simp] theorem hamiltonDifferential_apply (hx hp : E) (v : E × E) :
    hamiltonDifferential hx hp v = ⟪hx, v.1⟫_ℝ + ⟪hp, v.2⟫_ℝ := rfl

/-- Euler identity from degree-one homogeneity near scaling factor one
(`app:lem:common-hamilton-phase`). -/
theorem euler_identity_of_local_homogeneity {h : E × E → ℝ} {z : E × E} {hx hp : E}
    (hh : HasFDerivAt h (hamiltonDifferential hx hp) z)
    (hhom : ∀ᶠ r : ℝ in 𝓝 1, h (z.1, r • z.2) = r * h z) :
    ⟪z.2, hp⟫_ℝ = h z := by
  have hc : HasDerivAt (fun r : ℝ ↦ (z.1, r • z.2)) (0, z.2) 1 := by
    simpa using (hasDerivAt_const (1 : ℝ) z.1).prodMk ((hasDerivAt_id (1 : ℝ)).smul_const z.2)
  have hh' : HasFDerivAt h (hamiltonDifferential hx hp) (z.1, (1 : ℝ) • z.2) := by
    simpa using hh
  have hd := hh'.comp_hasDerivAt 1 hc
  have heq : (fun r : ℝ ↦ h (z.1, r • z.2)) =ᶠ[𝓝 1] (fun r ↦ r * h z) := hhom
  have he := (hd.congr_of_eventuallyEq heq.symm).unique
    ((hasDerivAt_id (1 : ℝ)).mul_const (h z))
  simpa [real_inner_comm] using he

/-- Differentiating Euler's degree-one identity gives the cancellation used in
`app:lem:common-hamilton-phase`, including variations in momentum. -/
theorem differentiated_euler_identity
    {h : E × E → ℝ} {hp : E × E → E} {z : E × E} {hx : E}
    {A : E × E →L[ℝ] E}
    (hh : HasFDerivAt h (hamiltonDifferential hx (hp z)) z)
    (hA : HasFDerivAt hp A z)
    (heuler : (fun w : E × E ↦ ⟪w.2, hp w⟫_ℝ) =ᶠ[𝓝 z] h)
    (v : E × E) : ⟪z.2, A v⟫_ℝ = ⟪hx, v.1⟫_ℝ := by
  have hi := ((ContinuousLinearMap.snd ℝ E E).hasFDerivAt.inner ℝ hA)
  have heq := (hi.congr_of_eventuallyEq heuler.symm).unique hh
  have hv := congrArg (fun L : E × E →L[ℝ] ℝ ↦ L v) heq
  simp only [ContinuousLinearMap.comp_apply, fderivInnerCLM_apply,
    ContinuousLinearMap.prod_apply, hamiltonDifferential_apply] at hv
  rw [real_inner_comm v.2 (hp z)] at hv
  exact add_right_cancel hv

/-- Hamilton's equations preserve energy (`app:lem:common-hamilton-phase`). -/
theorem hasDerivAt_energy_zero
    {h : E × E → ℝ} {x p : ℝ → E} {t : ℝ} {hx hp : E}
    (hh : HasFDerivAt h (hamiltonDifferential hx hp) (x t, p t))
    (hxt : HasDerivAt x hp t) (hpt : HasDerivAt p (-hx) t) :
    HasDerivAt (fun s ↦ h (x s, p s)) 0 t := by
  have hz : hamiltonDifferential hx hp (hp, -hx) = 0 := by
    simp [hamiltonDifferential, real_inner_comm]
  convert! hh.comp_hasDerivAt t (hxt.prodMk hpt) using 1
  simp [hz]

/-- The fixed-time Liouville pairing has zero time derivative, using the
linearized position equation and differentiated Euler identity
(`app:lem:common-hamilton-phase`). -/
theorem hasDerivAt_liouville_zero
    {p dx : ℝ → E} {t : ℝ} {hx dp : E} {A : E × E →L[ℝ] E}
    (hpt : HasDerivAt p (-hx) t)
    (hdxt : HasDerivAt dx (A (dx t, dp)) t)
    (heuler : ∀ v : E × E, ⟪p t, A v⟫_ℝ = ⟪hx, v.1⟫_ℝ) :
    HasDerivAt (fun s ↦ ⟪p s, dx s⟫_ℝ) 0 t := by
  convert hpt.inner ℝ hdxt using 1
  simp [heuler]

/-- Integrating a zero derivative on a connected open time strip. This also
allows negative Hamilton times (`app:lem:common-hamilton-phase`). -/
theorem conserved_of_hasDerivAt_zero {I : Set ℝ} (hI : IsOpen I)
    (hIc : IsPreconnected I) (h0 : 0 ∈ I) {f : ℝ → ℝ}
    (hf : ∀ t ∈ I, HasDerivAt f 0 t) {t : ℝ} (ht : t ∈ I) :
    f t = f 0 := by
  exact hI.is_const_of_deriv_eq_zero hIc
    (fun s hs ↦ (hf s hs).differentiableAt.differentiableWithinAt)
    (fun s hs ↦ (hf s hs).deriv) ht h0

end JanetCartan.HamiltonPhase
