module

public import JanetCartan.Analysis.Calculus.BufferedInverse
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The frozen full phase chart

The reference map in `app:ch_seed:prop:seed-phase-charts` is
`(z₁, η) ↦ (⟪v z₁, η⟫, η)`, where `v z₁ = ∇H₀(ζₐ(z))` and the
spectator coordinates are fixed. We compute its differential and construct its
inverse linear map from incidence transversality. These are reference-chart
results; the actual Hamilton phase comparison is a separate input.
-/

@[expose] public noncomputable section

open scoped InnerProductSpace Topology
open Set Filter

namespace JanetCartan.FullPhaseCharts

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The frozen map `Ψ₀ = (G, η)` in `app:ch_seed:prop:seed-phase-charts`. -/
def frozenChart (v : ℝ → E) (u : ℝ × E) : ℝ × E :=
  (⟪v u.1, u.2⟫_ℝ, u.2)

/-- Incidence at a nonzero direction forces a nonzero transverse component
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem transverse_ne_zero_of_incidence {v η : E} {ω : ℝ}
    (hk : (ω, η) ≠ (0, 0)) (hinc : ω = ⟪v, η⟫_ℝ) : η ≠ 0 := by
  intro hη
  apply hk
  simp_all

/-- The triangular derivative of the frozen map, with `a = ∂z₁G`
(`app:ch_seed:prop:seed-phase-charts`). -/
def triangularDifferential (a : ℝ) (v : E) : (ℝ × E) →L[ℝ] (ℝ × E) :=
  (a • ContinuousLinearMap.fst ℝ ℝ E +
    (innerSL ℝ v).comp (ContinuousLinearMap.snd ℝ ℝ E)).prod
      (ContinuousLinearMap.snd ℝ ℝ E)

@[simp] theorem triangularDifferential_apply (a : ℝ) (v : E) (w : ℝ × E) :
    triangularDifferential a v w = (a * w.1 + ⟪v, w.2⟫_ℝ, w.2) := rfl

/-- Differentiating the actual formula for `Ψ₀`
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem hasFDerivAt_frozenChart {v : ℝ → E} {v' : E} {u : ℝ × E}
    (hv : HasDerivAt v v' u.1) :
    HasFDerivAt (frozenChart v)
      (triangularDifferential ⟪v', u.2⟫_ℝ (v u.1)) u := by
  have h₁ := hv.hasFDerivAt.comp u
    (ContinuousLinearMap.fst ℝ ℝ E).hasFDerivAt
  have h₂ := (ContinuousLinearMap.snd ℝ ℝ E).hasFDerivAt (x := u)
  convert! (h₁.inner ℝ h₂).prodMk h₂ using 1
  apply ContinuousLinearMap.ext
  intro w
  simp [triangularDifferential, fderivInnerCLM_apply, real_inner_comm,
    inner_smul_right, mul_comm, add_comm]

/-- The explicit inverse derivative, valid whenever incidence is transverse
(`app:ch_seed:prop:seed-phase-charts`). -/
def triangularInverse (a : ℝ) (v : E) : (ℝ × E) →L[ℝ] (ℝ × E) :=
  (a⁻¹ • (ContinuousLinearMap.fst ℝ ℝ E -
    (innerSL ℝ v).comp (ContinuousLinearMap.snd ℝ ℝ E))).prod
      (ContinuousLinearMap.snd ℝ ℝ E)

@[simp] theorem triangularInverse_apply (a : ℝ) (v : E) (w : ℝ × E) :
    triangularInverse a v w = (a⁻¹ * (w.1 - ⟪v, w.2⟫_ℝ), w.2) := rfl

/-- Transversality supplies a continuous linear equivalence; invertibility is
proved from the triangular formula, not assumed as a chart field
(`app:ch_seed:prop:seed-phase-charts`). -/
def triangularEquiv (a : ℝ) (v : E) (ha : a ≠ 0) : (ℝ × E) ≃L[ℝ] (ℝ × E) :=
  ContinuousLinearEquiv.equivOfInverse (triangularDifferential a v)
    (triangularInverse a v)
    (by intro w; ext <;> simp [ha])
    (by intro w; ext <;> simp [ha])

@[simp] theorem triangularEquiv_coe (a : ℝ) (v : E) (ha : a ≠ 0) :
    (triangularEquiv a v ha : (ℝ × E) →L[ℝ] (ℝ × E)) =
      triangularDifferential a v := rfl

/-- Full rank of the frozen chart follows from the scalar incidence derivative
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem bijective_fderiv_frozenChart {v : ℝ → E} {v' : E} {u : ℝ × E}
    (hv : HasDerivAt v v' u.1) (hinc : ⟪v', u.2⟫_ℝ ≠ 0) :
    Function.Bijective (fderiv ℝ (frozenChart v) u) := by
  rw [(hasFDerivAt_frozenChart hv).fderiv]
  exact (triangularEquiv _ _ hinc).bijective

/-- A nonzero Jacobian determinant at the reference incidence point
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem det_fderiv_frozenChart_ne_zero [FiniteDimensional ℝ E]
    {v : ℝ → E} {v' : E} {u : ℝ × E}
    (hv : HasDerivAt v v' u.1) (hinc : ⟪v', u.2⟫_ℝ ≠ 0) :
    (fderiv ℝ (frozenChart v) u).det ≠ 0 := by
  rw [(hasFDerivAt_frozenChart hv).fderiv]
  exact (triangularEquiv _ (v u.1) hinc).toLinearEquiv.isUnit_det'.ne_zero

/-- Smoothness of the reference map, with arbitrary fixed spectators in `v`
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem contDiff_frozenChart {v : ℝ → E} {r : WithTop ℕ∞}
    (hv : ContDiff ℝ r v) : ContDiff ℝ r (frozenChart v) :=
  ((hv.comp contDiff_fst).inner ℝ contDiff_snd).prodMk contDiff_snd

/-- Local smoothness of the reference map on its construction domain
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem contDiffAt_frozenChart {v : ℝ → E} {r : WithTop ℕ∞} {u : ℝ × E}
    (hv : ContDiffAt ℝ r v u.1) : ContDiffAt ℝ r (frozenChart v) u :=
  ((hv.comp u contDiffAt_fst).inner ℝ contDiffAt_snd).prodMk contDiffAt_snd

/-- Shrinking around a transverse reference incidence makes the derivative
uniformly close to its central invertible matrix. This discharges the reference
quarter-gap hypothesis of `common_buffered_inverse_domains` on any smaller box
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem exists_frozen_derivative_gap {v : ℝ → E} {u : ℝ × E}
    (hv : ContDiffAt ℝ 1 v u.1) (hinc : ⟪deriv v u.1, u.2⟫_ℝ ≠ 0) :
    ∃ ρ > 0, ∀ w ∈ Metric.ball u ρ,
      ‖((triangularEquiv _ (v u.1) hinc).symm : (ℝ × E) →L[ℝ] (ℝ × E)).comp
        (fderiv ℝ (frozenChart v) w) - ContinuousLinearMap.id ℝ (ℝ × E)‖ ≤ 1 / 4 := by
  let G := triangularEquiv _ (v u.1) hinc
  have hd : fderiv ℝ (frozenChart v) u = (G : (ℝ × E) →L[ℝ] (ℝ × E)) :=
    (hasFDerivAt_frozenChart (hv.differentiableAt one_ne_zero).hasDerivAt).fderiv
  have hc := (contDiffAt_frozenChart hv).continuousAt_fderiv one_ne_zero
  have hn : ContinuousAt (fun w ↦
      ‖(G.symm : (ℝ × E) →L[ℝ] (ℝ × E)).comp (fderiv ℝ (frozenChart v) w) -
        ContinuousLinearMap.id ℝ (ℝ × E)‖) u :=
    ((continuousAt_const.clm_comp hc).sub continuousAt_const).norm
  have hzero : (G.symm : (ℝ × E) →L[ℝ] (ℝ × E)).comp
      (fderiv ℝ (frozenChart v) u) - ContinuousLinearMap.id ℝ (ℝ × E) = 0 := by
    rw [hd]
    apply ContinuousLinearMap.ext
    intro w
    simp
  have hnormzero : ‖(G.symm : (ℝ × E) →L[ℝ] (ℝ × E)).comp
      (fderiv ℝ (frozenChart v) u) - ContinuousLinearMap.id ℝ (ℝ × E)‖ = 0 := by
    exact (congrArg (fun L : (ℝ × E) →L[ℝ] (ℝ × E) ↦ ‖L‖) hzero).trans
      (norm_zero (E := (ℝ × E) →L[ℝ] (ℝ × E)))
  have hn' := hn.eventually (gt_mem_nhds (show
      ‖(G.symm : (ℝ × E) →L[ℝ] (ℝ × E)).comp (fderiv ℝ (frozenChart v) u) -
        ContinuousLinearMap.id ℝ (ℝ × E)‖ < (1 / 4 : ℝ) by
      exact hnormzero.trans_lt (by norm_num)))
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff_ball.mp hn'
  exact ⟨ρ, hρ, fun w hw ↦ (hball w hw).le⟩

/-- The reference transverse map is exactly the identity, so its derivative
has zero normalized gap (`app:ch_seed:prop:seed-phase-charts`). -/
theorem frozenChart_transverse (v : ℝ → E) (z : ℝ) :
    (fun η ↦ (frozenChart v (z, η)).2) = id := rfl

end JanetCartan.FullPhaseCharts
