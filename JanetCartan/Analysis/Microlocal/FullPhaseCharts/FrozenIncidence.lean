module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.FrozenIncidence.Triangular

/-!
# Frozen incidence and the joint reference quarter-gap

This closes the frozen transversality paragraph of
`app:ch_seed:prop:seed-phase-charts` for the same `PatchQuantitativeFamily`
retained by `exists_constructed_carrier_phases`. The characteristic equation,
nonzero tangential direction and scalar transversality are derived in the
imported leaves. Here the actual triangular equivalence gives one normalized
quarter-gap jointly in the two spectators and data `(z₁,η)`.

The parent `exists_fullChart_inverseFamily` consumes this reference gap.
Current-chart comparison and inverse estimates are separate obligations.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff InnerProductSpace Topology

namespace JanetCartan.FullPhaseCharts.FrozenIncidence
open HamiltonPhase ActualCarriers ActualCarriers.FrozenPhaseReference
open ActualCarriers.CurrentFullPhase FrozenMenu ActualPhase

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- The data differential of the literal frozen chart is jointly continuous
in both spectators and data (`app:ch_seed:prop:seed-phase-charts`). -/
theorem frozen_data_derivative_continuousAt {c C : ℝ} (hP : P.IsValid c C)
    {q : Euclidean 2 × (ℝ × Euclidean (n - 1))}
    (hq : carrierParameters (q.1, q.2.1) ∈ parameterInterior (2 * P.radius)) :
    ContinuousAt (fun a : Euclidean 2 × (ℝ × Euclidean (n - 1)) ↦
      fderiv ℝ (frozenChart (fun t ↦ gradient (dispersion T)
        (spatialCarrier T (a.1, t)))) a.2) q := by
  have hV : ContDiffAt ℝ ∞ (fun p ↦ gradient (dispersion T) (spatialCarrier T p))
      (q.1, q.2.1) :=
    (carrier_gradient_smooth T hP).contDiffAt
      (((isOpen_parameterInterior _).preimage carrierParameters.continuous).mem_nhds hq)
  have hF : ContDiffAt ℝ ∞
      (Function.uncurry (fun (a : Euclidean 2 × (ℝ × Euclidean (n - 1)))
        (u : ℝ × Euclidean (n - 1)) ↦
          frozenChart (fun t ↦ gradient (dispersion T) (spatialCarrier T (a.1, t))) u))
      (q, q.2) :=
    ((hV.comp (q, q.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd.fst)).inner ℝ
      contDiffAt_snd.snd).prodMk contDiffAt_snd.snd
  exact (hF.fderiv (m := ∞) contDiffAt_snd (by simp)).continuousAt

/-- One central triangular equivalence controls the frozen data differential
throughout a joint neighborhood of the two spectators and data. The whole
neighborhood also stays in the original patch interior. This supplies the
reference quarter-gap to `exists_fullChart_inverseFamily`
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem exists_reference_quarter_gap {c C : ℝ} (hP : P.IsValid c C)
    {z : Euclidean 3} (hz : z ∈ parameterInterior P.radius)
    {k : Euclidean n} (hinc : incidence k (P.toFun z) = 0)
    (hd : fderiv ℝ (fun w ↦ incidence k (P.toFun w)) z
      (EuclideanSpace.single 0 1) ≠ 0) :
    ∃ ρ > 0, ∀ q ∈ ball
        (spectatorCenter z, (z 0, T.data.adapted.embedding.toContinuousLinearMap.adjoint k)) ρ,
      carrierParameters (q.1, q.2.1) ∈ parameterInterior P.radius ∧
      ‖((referenceEquiv T hP hz hinc hd).symm :
          (ℝ × Euclidean (n - 1)) →L[ℝ] (ℝ × Euclidean (n - 1))).comp
          (fderiv ℝ (frozenChart (fun t ↦ gradient (dispersion T)
            (spatialCarrier T (q.1, t)))) q.2) -
        ContinuousLinearMap.id ℝ (ℝ × Euclidean (n - 1))‖ ≤ 1 / 4 := by
  let q₀ : Euclidean 2 × (ℝ × Euclidean (n - 1)) :=
    (spectatorCenter z, (z 0, T.data.adapted.embedding.toContinuousLinearMap.adjoint k))
  let L := referenceEquiv T hP hz hinc hd
  let D := fun q : Euclidean 2 × (ℝ × Euclidean (n - 1)) ↦
    fderiv ℝ (frozenChart (fun t ↦ gradient (dispersion T)
      (spatialCarrier T (q.1, t)))) q.2
  have hD : ContinuousAt D q₀ := frozen_data_derivative_continuousAt T hP (by
    change carrierParameters (spectatorCenter z, z 0) ∈ parameterInterior (2 * P.radius)
    rw [carrierParameters_spectatorCenter]
    exact parameterCube_subset_doubledInterior hP.1 (fun i ↦ (hz i).le))
  have hn : ContinuousAt (fun q ↦
      ‖(L.symm : (ℝ × Euclidean (n - 1)) →L[ℝ] (ℝ × Euclidean (n - 1))).comp (D q) -
        ContinuousLinearMap.id ℝ (ℝ × Euclidean (n - 1))‖) q₀ :=
    ((continuousAt_const.clm_comp hD).sub continuousAt_const).norm
  have hcentral : D q₀ = (L :
      (ℝ × Euclidean (n - 1)) →L[ℝ] (ℝ × Euclidean (n - 1))) :=
    fderiv_eq_referenceEquiv T hP hz hinc hd
  have hzero : (L.symm : (ℝ × Euclidean (n - 1)) →L[ℝ] (ℝ × Euclidean (n - 1))).comp
      (D q₀) - ContinuousLinearMap.id ℝ (ℝ × Euclidean (n - 1)) = 0 := by
    rw [hcentral]
    apply ContinuousLinearMap.ext
    intro u
    simp
  have hgap : ∀ᶠ q in 𝓝 q₀,
      ‖(L.symm : (ℝ × Euclidean (n - 1)) →L[ℝ] (ℝ × Euclidean (n - 1))).comp (D q) -
        ContinuousLinearMap.id ℝ (ℝ × Euclidean (n - 1))‖ < 1 / 4 :=
    hn.eventually (gt_mem_nhds (by
      change ‖(L.symm : (ℝ × Euclidean (n - 1)) →L[ℝ] (ℝ × Euclidean (n - 1))).comp
        (D q₀) - ContinuousLinearMap.id ℝ (ℝ × Euclidean (n - 1))‖ < 1 / 4
      rw [hzero, norm_zero]
      norm_num))
  have hmem : ∀ᶠ q : Euclidean 2 × (ℝ × Euclidean (n - 1)) in 𝓝 q₀,
      carrierParameters (q.1, q.2.1) ∈ parameterInterior P.radius := by
    have hc : Continuous (fun q : Euclidean 2 × (ℝ × Euclidean (n - 1)) ↦
        carrierParameters (q.1, q.2.1)) :=
      carrierParameters.continuous.comp (continuous_fst.prodMk continuous_snd.fst)
    apply hc.continuousAt.preimage_mem_nhds
    change parameterInterior P.radius ∈ 𝓝 (carrierParameters (spectatorCenter z, z 0))
    rw [carrierParameters_spectatorCenter]
    exact (isOpen_parameterInterior _).mem_nhds hz
  obtain ⟨ρ, hρ, hb⟩ := Metric.eventually_nhds_iff_ball.mp (hmem.and hgap)
  exact ⟨ρ, hρ, fun q hq ↦ ⟨(hb q hq).1, (hb q hq).2.le⟩⟩

/-- Literal-cover assembly of the reference quarter-gap: its central
linear equivalence is obtained from primitive frozen incidence. Together
with `cover_dispersion_incidence`, this is the frozen input to the parent
inverse-family construction (`app:ch_seed:prop:seed-phase-charts`). -/
theorem cover_exists_reference_quarter_gap {D : CoverData n} {c C : ℝ}
    (hD : D.IsValid c C) (b : Fin D.chartCount) (a : Fin (D.patchCount b))
    (T : PatchQuantitativeFamily (D.patches b a) U hU)
    {k : Euclidean n} (hk : k ∈ D.domain b) :
    ∃ L : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1)),
      (L : (ℝ × Euclidean (n - 1)) →L[ℝ] (ℝ × Euclidean (n - 1))) =
        fderiv ℝ (frozenChart (fun t ↦ gradient (dispersion T)
          (spatialCarrier T (spectatorCenter (D.roots b a k), t))))
          (D.roots b a k 0, T.data.adapted.embedding.toContinuousLinearMap.adjoint k) ∧
      ∃ ρ > 0, ∀ q ∈ ball
          (spectatorCenter (D.roots b a k),
            (D.roots b a k 0, T.data.adapted.embedding.toContinuousLinearMap.adjoint k)) ρ,
        carrierParameters (q.1, q.2.1) ∈ parameterInterior (D.patches b a).radius ∧
        ‖(L.symm : (ℝ × Euclidean (n - 1)) →L[ℝ] (ℝ × Euclidean (n - 1))).comp
            (fderiv ℝ (frozenChart (fun t ↦ gradient (dispersion T)
              (spatialCarrier T (q.1, t)))) q.2) -
          ContinuousLinearMap.id ℝ (ℝ × Euclidean (n - 1))‖ ≤ 1 / 4 := by
  obtain ⟨hP, hsec⟩ := hD.2.2.2.2.1 b a
  have hz := (hsec.2.1 k hk).1
  have hi := (hsec.2.1 k hk).2.2.2
  have hd : fderiv ℝ (fun w ↦ incidence k ((D.patches b a).toFun w))
      (D.roots b a k) (EuclideanSpace.single 0 1) ≠ 0 :=
    abs_pos.mp (hD.1.trans_le (hsec.2.2 k hk _ (fun i ↦ (hz i).le)))
  exact ⟨referenceEquiv T hP hz hi hd, (fderiv_eq_referenceEquiv T hP hz hi hd).symm,
    exists_reference_quarter_gap T hP hz hi hd⟩

end JanetCartan.FullPhaseCharts.FrozenIncidence
