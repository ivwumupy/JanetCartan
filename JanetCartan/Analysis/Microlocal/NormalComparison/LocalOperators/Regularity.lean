module

public import JanetCartan.Analysis.Microlocal.NormalComparison.UniformKernel
public import JanetCartan.Analysis.Microlocal.NormalComparison.KernelCalculus

/-!
# Compact kernels from the local normal data

Spatial regularity for the actual operator and scalar cutoff channel in
`app:ch_osc:prop:osc-normal`. The phase is used only on the open input boxes;
no smoothness or amplitude support outside the parameter interval is assumed.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace JanetCartan.NormalComparison
variable {n r : ℕ} {G : UniformNormalGeometry n r} {C : ℕ → ℝ}

/-- The original amplitude vanishes off its fixed compact carrier, for use in
constructing `uniformOscillatoryOperator` (`app:ch_osc:setup:osc-normal`). -/
theorem UniformNormalData.amplitude_eq_zero_off_carrier
    (F : UniformNormalData G C) {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀)
    {z : Euclidean n × Euclidean n} (hz : z ∉ G.X₀ ×ˢ G.D₀) :
    F.amplitude ε z.1 z.2 = 0 := by
  by_contra h
  exact hz (F.amplitude_support ε hε h)

/-- The normalized vector kernel has the manuscript's fixed compact carrier.
This supplies compactness for the full-space output construction in
`app:ch_osc:prop:osc-normal`. -/
theorem UniformNormalData.normalizedKernel_support_subset
    (F : UniformNormalData G C) {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀)
    (scale K : ℝ) (i : Fin r) :
    Function.support (Function.uncurry
      (normalizedOscillatoryKernel scale K (F.phase ε) (fun x u ↦ F.amplitude ε x u i))) ⊆
      G.X₀ ×ˢ G.D₀ := by
  intro z hz
  by_contra hout
  apply hz
  simp [Function.uncurry, normalizedOscillatoryKernel, F.amplitude_eq_zero_off_carrier hε hout]

/-- Local phase regularity suffices for global smoothness of each actual
vector kernel in `app:ch_osc:prop:osc-normal`. Outside the compact carrier the
kernel is locally zero. -/
theorem UniformNormalData.normalizedKernel_contDiff
    (F : UniformNormalData G C) {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀)
    (scale K : ℝ) (i : Fin r) :
    ContDiff ℝ ∞ (Function.uncurry
      (normalizedOscillatoryKernel scale K (F.phase ε) (fun x u ↦ F.amplitude ε x u i))) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z ∈ G.X₀ ×ˢ G.D₀
  · have hp := (F.phase_contDiffAt (F.parameter_subset hε)
      (G.X₀_subset hz.1) (G.D₀_subset hz.2)).comp z
      (contDiffAt_const.prodMk contDiffAt_id)
    have ha := (F.amplitude_contDiffAt (F.parameter_subset hε)
      (G.X₀_subset hz.1) (G.D₀_subset hz.2)).comp z
      (contDiffAt_const.prodMk contDiffAt_id)
    exact (contDiffAt_const.mul ((contDiffAt_const.mul
      (Complex.ofRealCLM.contDiff.contDiffAt.comp z (contDiffAt_const.mul hp))).cexp)).mul
      ((contDiffAt_pi.mp ha) i)
  · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [(G.compact_X₀.isClosed.prod G.compact_D₀.isClosed).isOpen_compl.mem_nhds hz]
      with w hw
    simp [Function.uncurry, normalizedOscillatoryKernel, F.amplitude_eq_zero_off_carrier hε hw]

/-- Compactness of each actual vector kernel, consumed by
`uniformOscillatoryOperator` (`app:ch_osc:prop:osc-normal`). -/
theorem UniformNormalData.normalizedKernel_hasCompactSupport
    (F : UniformNormalData G C) {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀)
    (scale K : ℝ) (i : Fin r) :
    HasCompactSupport (Function.uncurry
      (normalizedOscillatoryKernel scale K (F.phase ε) (fun x u ↦ F.amplitude ε x u i))) :=
  HasCompactSupport.of_support_subset_isCompact (G.compact_X₀.prod G.compact_D₀)
    (F.normalizedKernel_support_subset hε scale K i)

/-- The scalar channel kernel is globally smooth for any smooth cutoff whose
closed support is inside the original boxes. This supplies the literal kernel
in `fullNormalAmplitudeKernel` in Step 2 of `app:ch_osc:prop:osc-normal`. -/
theorem UniformNormalData.cutoffKernel_contDiff
    (F : UniformNormalData G C) {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀)
    (scale K : ℝ) {χ : Euclidean n → Euclidean n → ℂ}
    (hχ : ContDiff ℝ ∞ (Function.uncurry χ))
    (hs : tsupport (Function.uncurry χ) ⊆ G.X ×ˢ G.D) :
    ContDiff ℝ ∞ (Function.uncurry
      (normalizedOscillatoryKernel scale K (F.phase ε) χ)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z ∈ tsupport (Function.uncurry χ)
  · have hp := (F.phase_contDiffAt (F.parameter_subset hε)
      (hs hz).1 (hs hz).2).comp z (contDiffAt_const.prodMk contDiffAt_id)
    exact (contDiffAt_const.mul ((contDiffAt_const.mul
      (Complex.ofRealCLM.contDiff.contDiffAt.comp z (contDiffAt_const.mul hp))).cexp)).mul
      hχ.contDiffAt
  · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport (Function.uncurry χ)).isOpen_compl.mem_nhds hz]
      with w hw
    have hwχ : χ w.1 w.2 = 0 := by
      by_contra hn
      exact hw (subset_tsupport (Function.uncurry χ) hn)
    simp [Function.uncurry, normalizedOscillatoryKernel, hwχ]

/-- The scalar cutoff kernel has compact support, without any global phase
hypothesis (`app:ch_osc:prop:osc-normal`, Step 2). -/
theorem UniformNormalData.cutoffKernel_hasCompactSupport
    (F : UniformNormalData G C) (ε scale K : ℝ)
    {χ : Euclidean n → Euclidean n → ℂ}
    (hχ : HasCompactSupport (Function.uncurry χ)) :
    HasCompactSupport (Function.uncurry
      (normalizedOscillatoryKernel scale K (F.phase ε) χ)) :=
  hasCompactSupport_normalizedOscillatoryKernel scale K (F.phase ε) hχ

end JanetCartan.NormalComparison
