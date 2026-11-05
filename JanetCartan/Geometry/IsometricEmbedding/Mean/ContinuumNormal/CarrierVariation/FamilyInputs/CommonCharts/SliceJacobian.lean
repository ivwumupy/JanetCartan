module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.CommonCharts.LocalInverse
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.InverseJets.Jacobian.Differential

open Set Filter Metric
open scoped ContDiff Topology
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
open ContinuumNormalReduction.TransportSymbol FullPhaseCharts
variable {n : ℕ}

/-- Invertibility of the augmented differential forces positivity of the
literal slice Jacobian: a zero slice tangent gives a zero augmented tangent.
Consumer: the common `bg-jacobian` lower bound, not merely a determinant of a
normalized augmented map (`app:ch_osc:prop:osc-normal`, Step 4'). -/
theorem transportAbsoluteJacobian_pos_of_augmented_injective
    (c : TransportSliceCoordinates n)
    {Y : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1)}
    {p : InputVariables n}
    (hf : DifferentiableAt ℝ (augmentedTransportGradient Y) p)
    (hi : Function.Injective (fderiv ℝ (augmentedTransportGradient Y) p)) :
    0 < transportAbsoluteJacobian c Y p := by
  have hg : DifferentiableAt ℝ (transportAveragedGradient Y) p := hf.fst.snd.snd
  have hid := hasFDerivAt_id (𝕜 := ℝ) p
  have he := ((hid.fst.fst.prodMk (hid.fst.snd.prodMk hg.hasFDerivAt)).prodMk
    hid.snd.fst.snd).fderiv
  change fderiv ℝ (augmentedTransportGradient Y) p = _ at he
  have hzero : ∀ z, transportSliceDifferential c Y p z = 0 → z = 0 := by
    intro z hz
    have hd : fderiv ℝ (augmentedTransportGradient Y) p (transportSliceInsertion c z) = 0 := by
      rw [he, transportSliceDifferential_eq_restriction c Y hg] at *
      change ((0, 0, _), 0) = 0
      change (fderiv ℝ (transportAveragedGradient Y) p) (transportSliceInsertion c z) = 0 at hz
      exact Prod.ext (Prod.ext rfl (Prod.ext rfl hz)) rfl
    have hz' : transportSliceInsertion c z = 0 := hi (hd.trans (map_zero _).symm)
    apply c.equiv.injective
    apply Prod.ext
    · simpa [transportSliceInsertion] using congrArg (fun w : InputVariables n ↦ w.2.1.1) hz'
    · simpa [transportSliceInsertion] using congrArg (fun w : InputVariables n ↦ w.2.2) hz'
  apply abs_pos.mpr
  intro hdet
  exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hdet)
    (LinearMap.ker_eq_bot'.mpr hzero)


/-- Continuity of the literal Jacobian jointly in source scale and every
input variable follows from joint forward smoothness. No inverse or Jacobian
regularity is assumed (`app:ch_background:eq:bg-jacobian`). -/
theorem source_transportAbsoluteJacobian_continuousOn
    (c : TransportSliceCoordinates n)
    {Y : ℝ → Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1)}
    {I : Set ℝ} {W : Set (InputVariables n)} (hI : IsOpen I) (hW : IsOpen W)
    (hf : ContDiffOn ℝ ∞ (fun q : ℝ × InputVariables n ↦
      augmentedTransportGradient (Y q.1) q.2) (I ×ˢ W)) :
    ContinuousOn (fun q : ℝ × InputVariables n ↦ transportAbsoluteJacobian c (Y q.1) q.2)
      (I ×ˢ W) := by
  have hg : ContDiffOn ℝ ∞ (fun q : ℝ × InputVariables n ↦
      transportAveragedGradient (Y q.1) q.2) (I ×ˢ W) := hf.fst.snd.snd
  have hs : ContDiffOn ℝ ∞ (fun q : InputVariables n × ℝ ↦
      transportAveragedGradient (Y q.2) q.1) (W ×ˢ I) :=
    hg.comp (f := fun q : InputVariables n × ℝ ↦ (q.2, q.1))
      (contDiffOn_snd.prodMk contDiffOn_fst) (fun _ hq ↦ ⟨hq.2, hq.1⟩)
  have hd : ContDiffOn ℝ ∞ (fun q : ℝ × InputVariables n ↦
      fderiv ℝ (transportAveragedGradient (Y q.1)) q.2) (I ×ˢ W) :=
    (contDiffOn_parameterFDeriv hW hI hs).comp
      (f := fun q : ℝ × InputVariables n ↦ (q.2, q.1))
      (contDiffOn_snd.prodMk contDiffOn_fst) (fun _ hq ↦ ⟨hq.2, hq.1⟩)
  have hcont : ContinuousOn (fun q : ℝ × InputVariables n ↦
      |(transportDifferentialRestriction c (fderiv ℝ
        (transportAveragedGradient (Y q.1)) q.2)).det|) (I ×ˢ W) :=
    ((ContinuousLinearMap.continuous_det (𝕜 := ℝ) (E := Euclidean n)).comp_continuousOn
      ((transportDifferentialRestriction c).continuous.comp_continuousOn hd.continuousOn)).abs
  apply hcont.congr
  intro q hq
  have hslice : ContDiffOn ℝ ∞ (transportAveragedGradient (Y q.1)) W :=
    hg.comp (f := fun p : InputVariables n ↦ (q.1, p))
      (contDiffOn_const.prodMk contDiffOn_id) (fun _ hp ↦ ⟨hq.1, hp⟩)
  exact congrArg (fun L : Euclidean n →L[ℝ] Euclidean n ↦ |L.det|)
    (transportSliceDifferential_eq_restriction c (Y q.1)
      ((hslice.contDiffAt (hW.mem_nhds hq.2)).differentiableAt (by simp)))

/-- A single positive bound for the literal slice Jacobian on common
physical/scale neighborhoods follows from the seed augmented differential.
The equivalence is supplied by the frozen incidence producer. Consumer:
`exists_source_common_local_charts` (`bg-jacobian`). -/
theorem exists_local_positive_transport_jacobian
    (c : TransportSliceCoordinates n)
    {Y : ℝ → Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1)}
    {I : Set ℝ} {W : Set (InputVariables n)} {p₀ : InputVariables n}
    (hI : IsOpen I) (hW : IsOpen W) (h0 : (0 : ℝ) ∈ I) (hp₀ : p₀ ∈ W)
    (hf : ContDiffOn ℝ ∞ (fun q : ℝ × InputVariables n ↦
      augmentedTransportGradient (Y q.1) q.2) (I ×ˢ W))
    (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2)
    (hA : fderiv ℝ (augmentedTransportGradient (Y 0)) p₀ = A.toContinuousLinearMap) :
    ∃ ρ > (0 : ℝ), closedBall p₀ ρ ⊆ W ∧
    ∃ ε > (0 : ℝ), Ioo (-ε) ε ⊆ I ∧ ∃ cJ > (0 : ℝ),
      ∀ σ ∈ Ioo (-ε) ε, ∀ p ∈ closedBall p₀ ρ,
        cJ ≤ transportAbsoluteJacobian c (Y σ) p := by
  have hs : ContDiffOn ℝ ∞ (augmentedTransportGradient (Y 0)) W :=
    hf.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hp ↦ ⟨h0, hp⟩)
  have hpos : 0 < transportAbsoluteJacobian c (Y 0) p₀ :=
    transportAbsoluteJacobian_pos_of_augmented_injective c
      ((hs.contDiffAt (hW.mem_nhds hp₀)).differentiableAt (by simp)) (by rw [hA]; exact A.injective)
  let cJ := transportAbsoluteJacobian c (Y 0) p₀ / 2
  have hcJ : 0 < cJ := half_pos hpos
  have hj : ContinuousAt (fun q : ℝ × InputVariables n ↦
      transportAbsoluteJacobian c (Y q.1) q.2) (0, p₀) :=
    (source_transportAbsoluteJacobian_continuousOn c hI hW hf).continuousAt
    ((hI.prod hW).mem_nhds ⟨h0, hp₀⟩)
  have hprod : ∀ᶠ q : ℝ × InputVariables n in 𝓝 (0, p₀), q ∈ I ×ˢ W :=
    (hI.prod hW).mem_nhds ⟨h0, hp₀⟩
  have hnear : ∀ᶠ q : ℝ × InputVariables n in 𝓝 (0, p₀),
      q ∈ I ×ˢ W ∧ cJ < transportAbsoluteJacobian c (Y q.1) q.2 :=
    hprod.and (hj.eventually (lt_mem_nhds (half_lt_self hpos)))
  obtain ⟨d, hd, hb⟩ := Metric.eventually_nhds_iff_ball.mp hnear
  have hh (σ : ℝ) (hσ : σ ∈ Ioo (-(d / 2)) (d / 2))
      (p : InputVariables n) (hp : p ∈ closedBall p₀ (d / 2)) :
      (σ, p) ∈ I ×ˢ W ∧ cJ < transportAbsoluteJacobian c (Y σ) p :=
    hb (σ, p) (by
      rw [mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, sub_zero]
      exact ⟨(abs_lt.mpr hσ).trans (half_lt_self hd),
        (mem_closedBall.mp hp).trans_lt (half_lt_self hd)⟩)
  have hzero : (0 : ℝ) ∈ Ioo (-(d / 2)) (d / 2) := ⟨by linarith, by linarith⟩
  refine ⟨d / 2, half_pos hd, fun p hp ↦ (hh 0 hzero p hp).1.2,
    d / 2, half_pos hd, fun σ hσ ↦ (hh σ hσ p₀ (mem_closedBall_self (by linarith))).1.1,
    cJ, hcJ, fun σ hσ p hp ↦ (hh σ hσ p hp).2.le⟩

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
