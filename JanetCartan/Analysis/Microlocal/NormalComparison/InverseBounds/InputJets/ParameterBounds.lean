module

public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.InputJets.Amplitude
public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.InputJets.AveragedGradient
public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.InputJets.ParameterJets

/-!
# Quantitative jets of the actual parameter derivatives

The input estimates for the velocity and transport coefficients in Step 2 of
`app:ch_osc:prop:osc-normal`. Spatial differentiation of the averaged gradient
costs one phase derivative; its parameter derivative has the same bound.
The parameter derivative of the full normal amplitude has twice the spatial
amplitude bound, in the Frobenius norm. All constants depend only on the
dimensions and the finite original input jets, and precede the family.
-/

@[expose] public noncomputable section

open Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.NormalComparison

variable {n r : ℕ} {G : UniformNormalGeometry n r} {C : ℕ → ℝ}

local instance (r : ℕ) : TopologicalSpace (Matrix (Fin r) (Fin r) ℂ) :=
  (Matrix.frobeniusNormedAddCommGroup (m := Fin r) (n := Fin r)
    (α := ℂ)).toUniformSpace.toTopologicalSpace

/-- The two differentiated outer products give this family-independent
constant for `∂ε A`, used in `normalTransportCoefficient`
(`app:ch_osc:prop:osc-normal`, Step 2). -/
def normalAmplitudeParameterJetBound (r : ℕ) (C : ℕ → ℝ) (k : ℕ) : ℝ :=
  2 * normalAmplitudeJetBound r C k

/-- Nonnegativity of the parameter-amplitude bound
(`app:ch_osc:prop:osc-normal`). -/
theorem normalAmplitudeParameterJetBound_nonneg (r : ℕ) (C : ℕ → ℝ) (k : ℕ) :
    0 ≤ normalAmplitudeParameterJetBound r C k :=
  mul_nonneg (by norm_num) (normalAmplitudeJetBound_nonneg r C k)

/-- The actual parameter derivative of the averaged gradient is spatially
smooth across the parameter endpoints (`app:ch_osc:setup:osc-normal`). -/
theorem UniformNormalData.averagedGradient_parameterDeriv_contDiffOn
    (F : UniformNormalData G C) {ε : ℝ} (hε : ε ∈ F.parameterDomain) :
    ContDiffOn ℝ ∞ (fun q : Euclidean n × (Euclidean n × Euclidean n) ↦
      deriv (fun t ↦ averagedGradient (F.phase t) q.1 q.2.1 q.2.2) ε)
      (G.X ×ˢ (G.X ×ˢ G.D)) := by
  intro q hq
  have hj := F.averagedGradient_contDiffOn.contDiffAt (x := (ε, q))
    ((F.isOpen_parameterDomain.prod (G.isOpen_X.prod (G.isOpen_X.prod G.isOpen_D))).mem_nhds
      ⟨hε, hq⟩)
  exact ((contDiffAt_parameter_deriv hj).comp q
    (contDiffAt_const.prodMk contDiffAt_id)).contDiffWithinAt

/-- Quantitative jets of the actual `∂ε Ψ`, used by `transportVelocity`.
Interchange reduces this to the original `∂ε D^j φ` input bounds, with
exactly one spatial derivative lost (`app:ch_osc:prop:osc-normal`, Step 2). -/
theorem UniformNormalData.averagedGradient_parameter_jet_bound
    (F : UniformNormalData G C) {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀)
    {k : ℕ} (hk : k + 1 ≤ 20 * (n + 1))
    {q : Euclidean n × (Euclidean n × Euclidean n)} (hq : q ∈ G.X ×ˢ (G.X ×ˢ G.D)) :
    ‖iteratedFDeriv ℝ k (fun w : Euclidean n × (Euclidean n × Euclidean n) ↦
      deriv (fun t ↦ averagedGradient (F.phase t) w.1 w.2.1 w.2.2) ε) q‖ ≤
      averagedGradientJetBound C k := by
  have heq : (fun w : Euclidean n × (Euclidean n × Euclidean n) ↦
      deriv (fun t ↦ averagedGradient (F.phase t) w.1 w.2.1 w.2.2) ε) =ᶠ[𝓝 q]
      (fun w ↦ averagedGradient (fun x u ↦ deriv (fun t ↦ F.phase t x u) ε)
        w.1 w.2.1 w.2.2) := by
    filter_upwards [(G.isOpen_X.prod (G.isOpen_X.prod G.isOpen_D)).mem_nhds hq] with w hw
    exact F.deriv_averagedGradient (F.parameter_subset hε) hw.1 hw.2.1 hw.2.2
  rw [(heq.iteratedFDeriv ℝ k).eq_of_nhds]
  exact norm_iteratedFDeriv_averagedGradient_le
    (φ := fun x u ↦ deriv (fun t ↦ F.phase t x u) ε) G.isOpen_X G.isOpen_D G.convex_X
    (F.phase_parameterDeriv_contDiffOn (F.parameter_subset hε))
    (fun _ hj _ hz ↦ F.norm_phase_parameterDeriv_jet_le hε hz hj) hk hq

/-- The actual parameter derivative of the normal amplitude is spatially
smooth, including at both parameter endpoints (`app:ch_osc:setup:osc-normal`). -/
theorem UniformNormalData.normalAmplitude_parameterDeriv_contDiffOn
    (F : UniformNormalData G C) {ε : ℝ} (hε : ε ∈ F.parameterDomain) :
    ContDiffOn ℝ ∞ (fun q : Euclidean n × (Euclidean n × Euclidean n) ↦
      deriv (fun t ↦ normalAmplitude (F.amplitude t) q.1 q.2.1 q.2.2) ε)
      (G.X ×ˢ (G.X ×ˢ G.D)) := by
  intro q hq
  have hj := F.normalAmplitude_contDiffOn_joint.contDiffAt (x := (ε, q))
    ((F.isOpen_parameterDomain.prod (G.isOpen_X.prod (G.isOpen_X.prod G.isOpen_D))).mem_nhds
      ⟨hε, hq⟩)
  exact ((contDiffAt_parameter_deriv hj).comp q
    (contDiffAt_const.prodMk contDiffAt_id)).contDiffWithinAt

-- Each differentiated outer product is bounded by the same binomial sum.
private theorem norm_iteratedFDeriv_normalAmplitudeBilinear_le
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {a b : H → Fin r → ℂ} {U : Set H} (hU : IsOpen U)
    (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U)
    {q : H} (hq : q ∈ U) {k : ℕ}
    (haj : ∀ j ≤ k, ‖iteratedFDeriv ℝ j a q‖ ≤ |C j|)
    (hbj : ∀ j ≤ k, ‖iteratedFDeriv ℝ j b q‖ ≤ |C j|) :
    ‖iteratedFDeriv ℝ k (fun z ↦ normalAmplitudeBilinear r (a z) (b z)) q‖ ≤
      normalAmplitudeJetBound r C k := by
  have h := (normalAmplitudeBilinear r).norm_iteratedFDerivWithin_le_of_bilinear
    ha hb hU.uniqueDiffOn hq (n := k) (by simp)
  simp only [iteratedFDerivWithin_of_isOpen _ hU hq] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg (normalAmplitudeBilinear r)))
  apply Finset.sum_le_sum
  intro j hj
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (haj j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
      (Nat.cast_nonneg _)) (hbj (k - j) (Nat.sub_le k j))
    (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _))

/-- Full Frobenius spatial jets of the actual parameter derivative of the
normal amplitude, supplying the `∂ε A` term in `normalTransportCoefficient`.
The proof uses the original mixed input jets, after derivative interchange
(`app:ch_osc:prop:osc-normal`, Step 2). -/
theorem UniformNormalData.norm_iteratedFDeriv_normalAmplitude_parameterDeriv_le
    (F : UniformNormalData G C) {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀)
    {q : Euclidean n × (Euclidean n × Euclidean n)} (hq : q ∈ G.X ×ˢ (G.X ×ˢ G.D))
    {k : ℕ} (hk : k ≤ 20 * (n + 1)) :
    ‖iteratedFDeriv ℝ k (fun z : Euclidean n × (Euclidean n × Euclidean n) ↦
      deriv (fun t ↦ normalAmplitude (F.amplitude t) z.1 z.2.1 z.2.2) ε) q‖ ≤
      normalAmplitudeParameterJetBound r C k := by
  let U := G.X ×ˢ (G.X ×ˢ G.D)
  have hU : IsOpen U := G.isOpen_X.prod (G.isOpen_X.prod G.isOpen_D)
  let a := Function.uncurry (F.amplitude ε)
  let da := fun z : Euclidean n × Euclidean n ↦ deriv (fun t ↦ F.amplitude t z.1 z.2) ε
  have ha : ContDiffOn ℝ ∞ a (G.X ×ˢ G.D) :=
    F.amplitude_contDiffOn_spatial (F.parameter_subset hε)
  have hda : ContDiffOn ℝ ∞ da (G.X ×ˢ G.D) :=
    F.amplitude_parameterDeriv_contDiffOn (F.parameter_subset hε)
  have hdal (L : (Euclidean n × (Euclidean n × Euclidean n)) →L[ℝ]
      (Euclidean n × Euclidean n)) (hL : ‖L‖ ≤ 1)
      {z : Euclidean n × (Euclidean n × Euclidean n)}
      (hz : L z ∈ G.X ×ˢ G.D) {j : ℕ} (hj : j ≤ 20 * (n + 1)) :
      ‖iteratedFDeriv ℝ j (da ∘ L) z‖ ≤ |C j| := by
    apply (norm_iteratedFDeriv_comp_linear_on_open_le L (G.isOpen_X.prod G.isOpen_D)
      hda hz j).trans
    calc
      _ ≤ ‖iteratedFDeriv ℝ j da (L z)‖ * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hL) (norm_nonneg _)
      _ ≤ |C j| := by
        rw [mul_one]
        exact (F.norm_amplitude_parameterDeriv_jet_le hε hz hj).trans (le_abs_self _)
  have hal : ContDiffOn ℝ ∞ (a ∘ normalLeftInput n) U :=
    ha.comp (normalLeftInput n).contDiff.contDiffOn (fun _ hz ↦ ⟨hz.1, hz.2.2⟩)
  have har : ContDiffOn ℝ ∞ (a ∘ normalRightInput n) U :=
    ha.comp (normalRightInput n).contDiff.contDiffOn (fun _ hz ↦ hz.2)
  have hdal' : ContDiffOn ℝ ∞ (da ∘ normalLeftInput n) U :=
    hda.comp (normalLeftInput n).contDiff.contDiffOn (fun _ hz ↦ ⟨hz.1, hz.2.2⟩)
  have hdar : ContDiffOn ℝ ∞ (da ∘ normalRightInput n) U :=
    hda.comp (normalRightInput n).contDiff.contDiffOn (fun _ hz ↦ hz.2)
  let f := fun z ↦ normalAmplitudeBilinear r (a (normalLeftInput n z)) (da (normalRightInput n z))
  let g := fun z ↦ normalAmplitudeBilinear r (da (normalLeftInput n z)) (a (normalRightInput n z))
  have hf : ContDiffOn ℝ ∞ f U :=
    ((normalAmplitudeBilinear r).contDiff.comp_contDiffOn hal).clm_apply hdar
  have hg : ContDiffOn ℝ ∞ g U :=
    ((normalAmplitudeBilinear r).contDiff.comp_contDiffOn hdal').clm_apply har
  have hfj : ‖iteratedFDeriv ℝ k f q‖ ≤ normalAmplitudeJetBound r C k :=
    norm_iteratedFDeriv_normalAmplitudeBilinear_le hU hal hdar hq
      (fun _ hj ↦ F.norm_amplitude_comp_linear_le (normalLeftInput n) (norm_normalLeftInput_le n)
        hε ⟨hq.1, hq.2.2⟩ (hj.trans hk))
      (fun _ hj ↦ hdal (normalRightInput n) (norm_normalRightInput_le n) hq.2 (hj.trans hk))
  have hgj : ‖iteratedFDeriv ℝ k g q‖ ≤ normalAmplitudeJetBound r C k :=
    norm_iteratedFDeriv_normalAmplitudeBilinear_le hU hdal' har hq
      (fun _ hj ↦ hdal (normalLeftInput n) (norm_normalLeftInput_le n) ⟨hq.1, hq.2.2⟩ (hj.trans hk))
      (fun _ hj ↦ F.norm_amplitude_comp_linear_le (normalRightInput n) (norm_normalRightInput_le n)
        hε hq.2 (hj.trans hk))
  have heq : (fun z : Euclidean n × (Euclidean n × Euclidean n) ↦
      deriv (fun t ↦ normalAmplitude (F.amplitude t) z.1 z.2.1 z.2.2) ε) =ᶠ[𝓝 q]
      (fun z ↦ f z + g z) := by
    filter_upwards [hU.mem_nhds hq] with z hz
    exact F.deriv_normalAmplitude (F.parameter_subset hε) hz.1 hz.2.1 hz.2.2
  rw [(heq.iteratedFDeriv ℝ k).eq_of_nhds,
    fun_iteratedFDeriv_add_apply ((hf.contDiffAt (hU.mem_nhds hq)).of_le (by simp))
      ((hg.contDiffAt (hU.mem_nhds hq)).of_le (by simp))]
  exact (norm_add_le _ _).trans ((add_le_add hfj hgj).trans_eq (by
    simp [normalAmplitudeParameterJetBound, two_mul]))

end JanetCartan.NormalComparison
