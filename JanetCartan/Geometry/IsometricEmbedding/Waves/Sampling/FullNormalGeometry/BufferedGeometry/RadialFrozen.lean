module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.FullNormalGeometry.BufferedGeometry.RadialFrozen.Normalization
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.FrozenIncidence
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.ActualComparison.Neighborhoods

/-!
# The frozen derivative gap on the entire radial sampling domain

Primitive incidence and transversality for the retained quantitative patch
family give one invertible triangular normalization and a strict derivative
gap on the complete prescribed radial interval. Only the angular/incidence
radius is shrunk. This supplies the frozen input to buffered inverse stability
for `jc-sampling-full-radial-inverse`, as required by
`app:ch_seed:prop:seed-phase-charts`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff InnerProductSpace NNReal

namespace JanetCartan.Sampling.FullNormalGeometry
open HamiltonPhase ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ActualPhase ActualComparison
open ContinuumNormalReduction.ConicChart

variable {m : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- Primitive frozen incidence produces one strict normalized derivative gap
on the entire radial image of every sufficiently small doubled data box.
The same retained family, base covector and full radial interval are used
throughout. This is the reference input to the full radial buffered inverse
construction (`app:ch_seed:prop:seed-phase-charts`). -/
theorem exists_radial_frozen_derivative_gap {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    {k : Euclidean (m + 1)} (hk : k ≠ 0) (hinc : incidence k (P.toFun z₀) = 0)
    (hd : fderiv ℝ (fun w ↦ incidence k (P.toFun w)) z₀
      (EuclideanSpace.single 0 1) ≠ 0)
    {amin amax : ℝ} (hamin : 0 < amin) (ha : amin ≤ amax) :
    let ηb : Euclidean m := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
    let f₀ : (ℝ × Euclidean m) → (ℝ × Euclidean m) :=
      frozenChart (fun t ↦ gradient (dispersion T)
      (spatialCarrier T (spectatorCenter z₀, t)))
    ∃ r₀ > 0, ∃ G : (ℝ × Euclidean m) ≃L[ℝ] (ℝ × Euclidean m),
      ∃ q : ℝ≥0, q < 1 ∧ ∀ r, 0 < r → r ≤ r₀ →
        ∀ u ∈ (fun p : ℝ × (ℝ × Euclidean m) ↦ radialScale p.1 p.2) ''
            (Icc amin amax ×ˢ dataBox (n := m + 1) z₀ ηb (2 * r)),
          DifferentiableAt ℝ f₀ u ∧
          ‖(G.symm : (ℝ × Euclidean m) →L[ℝ] (ℝ × Euclidean m)).comp
              (fderiv ℝ f₀ u) - ContinuousLinearMap.id ℝ (ℝ × Euclidean m)‖ ≤ q := by
  let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
  have hηb : ηb ≠ 0 := FrozenIncidence.tangential_direction_ne_zero T hP hz₀ hk hinc
  have hzD := parameterCube_subset_doubledInterior hP.1 (fun i ↦ (hz₀ i).le)
  have hV : ContDiffAt ℝ ∞ (fun p ↦ gradient (dispersion T) (spatialCarrier T p))
      (spectatorCenter z₀, z₀ 0) :=
    (FrozenIncidence.carrier_gradient_smooth T hP).contDiffAt
      (((isOpen_parameterInterior _).preimage carrierParameters.continuous).mem_nhds
        (by
          change carrierParameters (spectatorCenter z₀, z₀ 0) ∈
            parameterInterior (2 * P.radius)
          rwa [carrierParameters_spectatorCenter]))
  have hv : ContDiffAt ℝ 1 (fun t ↦ gradient (dispersion T)
      (spatialCarrier T (spectatorCenter z₀, t))) (z₀ 0) :=
    (hV.comp (z₀ 0) (contDiffAt_const.prodMk contDiffAt_id)).of_le (by simp)
  obtain ⟨ρ, hρ, G, q, hq, hgap⟩ := RadialFrozen.exists_frozen_radial_neighborhood
    hv (FrozenIncidence.scalar_incidence_transverse T hP hz₀ hinc hd) hamin ha
  refine ⟨min (ρ / 4) (‖ηb‖ / 4),
    lt_min (by positivity) (div_pos (norm_pos_iff.mpr hηb) (by norm_num)), G, q, hq, ?_⟩
  rintro r _hr hr u ⟨⟨a, w⟩, ⟨ha', hw⟩, rfl⟩
  apply hgap w _ a ha'
  rw [mem_ball, Prod.dist_eq]
  have hsmall : 2 * r < ρ := by
    have := hr.trans (min_le_left (ρ / 4) (‖ηb‖ / 4))
    linarith
  exact max_lt ((mem_closedBall.mp hw.1).trans_lt hsmall)
    ((mem_closedBall.mp hw.2).trans_lt hsmall)

end JanetCartan.Sampling.FullNormalGeometry
