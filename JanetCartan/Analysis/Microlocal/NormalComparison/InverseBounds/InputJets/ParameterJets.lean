module

public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.InputJets.ParameterJets.Interchange

/-!
# Parameter derivatives of the original normal-comparison inputs

The mixed jet hypotheses of `app:ch_osc:setup:osc-normal` bound spatial jets of
the actual parameter derivatives, by interchange on the open extensions.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace JanetCartan.NormalComparison

variable {n r : ℕ} {G : UniformNormalGeometry n r} {C : ℕ → ℝ}

/-- The actual parameter derivative of the phase is spatially smooth, including
at the parameter endpoints (`app:ch_osc:setup:osc-normal`). -/
theorem UniformNormalData.phase_parameterDeriv_contDiffOn (F : UniformNormalData G C)
    {ε : ℝ} (hε : ε ∈ F.parameterDomain) :
    ContDiffOn ℝ ∞ (fun z : Euclidean n × Euclidean n ↦
      deriv (fun t ↦ F.phase t z.1 z.2) ε) (G.X ×ˢ G.D) := by
  intro z hz
  exact ((contDiffAt_parameter_deriv (F.phase_contDiffAt hε hz.1 hz.2)).comp z
    (contDiffAt_const.prodMk contDiffAt_id)).contDiffWithinAt

/-- The actual parameter derivative of the amplitude is spatially smooth,
including at the parameter endpoints (`app:ch_osc:setup:osc-normal`). -/
theorem UniformNormalData.amplitude_parameterDeriv_contDiffOn (F : UniformNormalData G C)
    {ε : ℝ} (hε : ε ∈ F.parameterDomain) :
    ContDiffOn ℝ ∞ (fun z : Euclidean n × Euclidean n ↦
      deriv (fun t ↦ F.amplitude t z.1 z.2) ε) (G.X ×ˢ G.D) := by
  intro z hz
  exact ((contDiffAt_parameter_deriv (F.amplitude_contDiffAt hε hz.1 hz.2)).comp z
    (contDiffAt_const.prodMk contDiffAt_id)).contDiffWithinAt

/-- Parameter/spatial interchange for the phase, at arbitrary spatial order
(`app:ch_osc:setup:osc-normal`). -/
theorem UniformNormalData.phase_iteratedFDeriv_parameterDeriv (F : UniformNormalData G C)
    {ε : ℝ} (hε : ε ∈ F.parameterDomain) {z : Euclidean n × Euclidean n}
    (hz : z ∈ G.X ×ˢ G.D) (k : ℕ) :
    iteratedFDeriv ℝ k (fun z : Euclidean n × Euclidean n ↦
      deriv (fun t ↦ F.phase t z.1 z.2) ε) z =
      deriv (fun t ↦ iteratedFDeriv ℝ k (Function.uncurry (F.phase t)) z) ε :=
  iteratedFDeriv_deriv_parameter F.isOpen_parameterDomain F.isOpen_extensionDomain
    F.phase_smooth hε (F.spatial_subset ⟨subset_closure hz.1, subset_closure hz.2⟩) k

/-- Parameter/spatial interchange for the amplitude, at arbitrary spatial order
(`app:ch_osc:setup:osc-normal`). -/
theorem UniformNormalData.amplitude_iteratedFDeriv_parameterDeriv (F : UniformNormalData G C)
    {ε : ℝ} (hε : ε ∈ F.parameterDomain) {z : Euclidean n × Euclidean n}
    (hz : z ∈ G.X ×ˢ G.D) (k : ℕ) :
    iteratedFDeriv ℝ k (fun z : Euclidean n × Euclidean n ↦
      deriv (fun t ↦ F.amplitude t z.1 z.2) ε) z =
      deriv (fun t ↦ iteratedFDeriv ℝ k (Function.uncurry (F.amplitude t)) z) ε :=
  iteratedFDeriv_deriv_parameter F.isOpen_parameterDomain F.isOpen_extensionDomain
    F.amplitude_smooth hε (F.spatial_subset ⟨subset_closure hz.1, subset_closure hz.2⟩) k

/-- The original input constants bound spatial jets of the actual phase
parameter derivative (`app:ch_osc:setup:osc-normal`). -/
theorem UniformNormalData.norm_phase_parameterDeriv_jet_le (F : UniformNormalData G C)
    {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀) {z : Euclidean n × Euclidean n}
    (hz : z ∈ G.X ×ˢ G.D) {k : ℕ} (hk : k ≤ 20 * (n + 1)) :
    ‖iteratedFDeriv ℝ k (fun z : Euclidean n × Euclidean n ↦
      deriv (fun t ↦ F.phase t z.1 z.2) ε) z‖ ≤ C k := by
  rw [F.phase_iteratedFDeriv_parameterDeriv (F.parameter_subset hε) hz k]
  exact (F.input_jet_bounds hε hz hk).2.2.1

/-- The original input constants bound spatial jets of the actual amplitude
parameter derivative (`app:ch_osc:setup:osc-normal`). -/
theorem UniformNormalData.norm_amplitude_parameterDeriv_jet_le (F : UniformNormalData G C)
    {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀) {z : Euclidean n × Euclidean n}
    (hz : z ∈ G.X ×ˢ G.D) {k : ℕ} (hk : k ≤ 20 * (n + 1)) :
    ‖iteratedFDeriv ℝ k (fun z : Euclidean n × Euclidean n ↦
      deriv (fun t ↦ F.amplitude t z.1 z.2) ε) z‖ ≤ C k := by
  rw [F.amplitude_iteratedFDeriv_parameterDeriv (F.parameter_subset hε) hz k]
  exact (F.input_jet_bounds hε hz hk).2.2.2

/-- Differentiating the actual averaged gradient gives the averaged gradient of
the actual parameter derivative (`app:ch_osc:prop:osc-normal`, Step 2).
Convexity keeps the compact segment in the original box. The open parameter
extension includes both endpoints of the manuscript's parameter interval. -/
theorem UniformNormalData.deriv_averagedGradient (F : UniformNormalData G C)
    {ε : ℝ} (hε : ε ∈ F.parameterDomain) {x y u : Euclidean n}
    (hx : x ∈ G.X) (hy : y ∈ G.X) (hu : u ∈ G.D) :
    deriv (fun t ↦ averagedGradient (F.phase t) x y u) ε =
      averagedGradient (fun x u ↦ deriv (fun t ↦ F.phase t x u) ε) x y u := by
  let H : ℝ × ℝ → Euclidean n →L[ℝ] ℝ := fun q ↦
    fderiv ℝ (fun z ↦ F.phase q.2 z u) (y + q.1 • (x - y))
  have hseg (s : ℝ) (hs : s ∈ uIcc (0 : ℝ) 1) : y + s • (x - y) ∈ G.X :=
    G.convex_X.add_smul_sub_mem hy hx (by simpa using hs)
  have hH : ∀ q ∈ uIcc (0 : ℝ) 1 ×ˢ F.parameterDomain, ContDiffAt ℝ ∞ H q := by
    intro q hq
    have hp := F.phase_contDiffAt hq.2 (hseg q.1 hq.1) hu
    have hh : ContDiffAt ℝ ∞
        (fun w : (ℝ × ℝ) × Euclidean n ↦ F.phase w.1.2 w.2 u)
        (q, y + q.1 • (x - y)) :=
      hp.comp (q, y + q.1 • (x - y))
        (contDiffAt_fst.snd.prodMk (contDiffAt_snd.prodMk contDiffAt_const))
    exact hh.fderiv (contDiffAt_const.add (contDiffAt_fst.smul contDiffAt_const)) (by simp)
  let J : ℝ → ℝ →L[ℝ] (Euclidean n →L[ℝ] ℝ) := fun s ↦
    (fderiv ℝ H (s, ε)).comp (ContinuousLinearMap.inr ℝ ℝ ℝ)
  -- Fix the normed structure before forming the operator-valued integral.
  let : NormedAddCommGroup (ℝ →L[ℝ] (Euclidean n →L[ℝ] ℝ)) := inferInstance
  have hJ : IntervalIntegrable (fun s ↦ J s) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    intro s hs
    have hd := ((hH (s, ε) ⟨hs, hε⟩).fderiv_right (m := ∞) (by simp)).continuousAt
    exact ((hd.comp (f := fun t : ℝ ↦ (t, ε)) (continuousAt_id.prodMk continuousAt_const)).clm_comp
      continuousAt_const).continuousWithinAt
  have hInt := (hasFDerivAt_fixedIntervalIntegral F.isOpen_parameterDomain hH hε).hasDerivAt
  have hvalue : (∫ s in (0 : ℝ)..1, J s) 1 =
      ∫ s in (0 : ℝ)..1, fderiv ℝ (fun z ↦ deriv (fun t ↦ F.phase t z u) ε)
        (y + s • (x - y)) := by
    rw [ContinuousLinearMap.intervalIntegral_apply hJ]
    apply intervalIntegral.integral_congr
    intro s hs
    have hh := ((hH (s, ε) ⟨hs, hε⟩).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt ε
      ((hasDerivAt_const ε s).prodMk (hasDerivAt_id ε))
    have hf : ContDiffOn ℝ ∞ (fun p : ℝ × Euclidean n ↦ F.phase p.1 p.2 u)
        (F.parameterDomain ×ˢ G.X) := by
      intro p hp
      exact ((F.phase_contDiffAt hp.1 hp.2 hu).comp p
        (contDiffAt_fst.prodMk (contDiffAt_snd.prodMk contDiffAt_const))).contDiffWithinAt
    have hi := fderiv_deriv_parameter F.isOpen_parameterDomain G.isOpen_X hf hε (hseg s hs)
    exact hh.deriv.symm.trans hi.symm
  have hh : HasDerivAt (fun t ↦ ∫ s in (0 : ℝ)..1, H (s, t))
      (∫ s in (0 : ℝ)..1, fderiv ℝ (fun z ↦ deriv (fun t ↦ F.phase t z u) ε)
        (y + s • (x - y))) ε := by
    rw [← hvalue]
    exact hInt
  let L := (InnerProductSpace.toDual ℝ (Euclidean n)).symm.toContinuousLinearEquiv
  exact (L.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt ε hh).deriv

end JanetCartan.NormalComparison
