module

public import JanetCartan.Analysis.Microlocal.NormalComparison.CutoffGeometry.Construction
public import JanetCartan.Analysis.ContDiff.Norm.Basic

/-!
# The fixed scalar cutoff channel

Step 2 of `app:ch_osc:prop:osc-normal` applies the mask-free norm theorem to
the original phase with amplitude `χx χu`. This module constructs that input
data, including the uniformly buffered enlarged support and all finite jets.
`fixedScalarNormalCutoffs G C` is chosen before the family; its `inputBounds`
likewise depend only on the geometry, original jet budget and fixed cutoffs.
No operator estimate is assumed or asserted here.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff

namespace JanetCartan.NormalComparison

variable {n r : ℕ} {G : UniformNormalGeometry n r} {C : ℕ → ℝ}

/-- The literal single-component amplitude in Step 2 of
`app:ch_osc:prop:osc-normal`. -/
def ScalarNormalCutoffs.amplitude (χ : ScalarNormalCutoffs G C)
    (z : Euclidean n × Euclidean n) (_ : Fin 1) : ℂ := (χ.χx z.1 : ℂ) * (χ.χu z.2 : ℂ)

/-- Global smoothness of the fixed scalar amplitude
(`app:ch_osc:prop:osc-normal`, Step 2). -/
theorem ScalarNormalCutoffs.amplitude_contDiff (χ : ScalarNormalCutoffs G C) :
    ContDiff ℝ ∞ χ.amplitude := by
  apply contDiff_pi.mpr
  intro i
  exact (Complex.ofRealCLM.contDiff.comp (χ.smooth_x.comp contDiff_fst)).mul
    (Complex.ofRealCLM.contDiff.comp (χ.smooth_u.comp contDiff_snd))

/-- Support of the fixed scalar amplitude in the enlarged compact boxes
(`app:ch_osc:prop:osc-normal`, Step 2). -/
theorem ScalarNormalCutoffs.amplitude_support (χ : ScalarNormalCutoffs G C) :
    Function.support χ.amplitude ⊆
      (G.scalarCutoffGeometry C).X₀ ×ˢ (G.scalarCutoffGeometry C).D₀ := by
  intro z hz
  have hx : χ.χx z.1 ≠ 0 := by
    intro h
    apply hz
    ext i
    simp [ScalarNormalCutoffs.amplitude, h]
  have hu : χ.χu z.2 ≠ 0 := by
    intro h
    apply hz
    ext i
    simp [ScalarNormalCutoffs.amplitude, h]
  exact ⟨χ.support_x (subset_tsupport _ hx), χ.support_u (subset_tsupport _ hu)⟩

/-- Fixed finite input bounds for the scalar channel of
`app:ch_osc:prop:osc-normal`. The compact-set seminorm is computed for the
chosen cutoff alone; no phase family, frequency, parameter or mask enters it. -/
def ScalarNormalCutoffs.inputBounds (χ : ScalarNormalCutoffs G C) (k : ℕ) : ℝ :=
  C k + cNorm (closure G.X ×ˢ closure G.D) k χ.amplitude

/-- The added cutoff jet is bounded on the original open boxes
(`app:ch_osc:prop:osc-normal`, Step 2). -/
theorem ScalarNormalCutoffs.amplitude_jet_bound (χ : ScalarNormalCutoffs G C)
    (k : ℕ) {z : Euclidean n × Euclidean n} (hz : z ∈ G.X ×ˢ G.D) :
    ‖iteratedFDeriv ℝ k χ.amplitude z‖ ≤
      cNorm (closure G.X ×ˢ closure G.D) k χ.amplitude := by
  apply norm_iteratedFDeriv_le_cNorm
    (G.bounded_X.isCompact_closure.prod G.bounded_D.isCompact_closure)
    (χ.amplitude_contDiff.of_le (by simp))
    ⟨subset_closure hz.1, subset_closure hz.2⟩ le_rfl

/-- The actual rank-one input family for the mask-free scalar norm estimate
in `app:ch_osc:prop:osc-normal`, Step 2. Every geometric and quantitative field
is proved from the original input and the fixed cutoff construction. -/
def ScalarNormalCutoffs.toUniformNormalData (χ : ScalarNormalCutoffs G C)
    (F : UniformNormalData G C) : UniformNormalData (G.scalarCutoffGeometry C) χ.inputBounds where
  phase := F.phase
  amplitude := fun _ x u ↦ χ.amplitude (x, u)
  parameterDomain := F.parameterDomain
  extensionDomain := F.extensionDomain
  isOpen_parameterDomain := F.isOpen_parameterDomain
  isOpen_extensionDomain := F.isOpen_extensionDomain
  parameter_subset := F.parameter_subset
  spatial_subset := F.spatial_subset
  phase_smooth := F.phase_smooth
  amplitude_smooth := (χ.amplitude_contDiff.comp contDiff_snd).contDiffOn
  amplitude_support := fun _ _ ↦ χ.amplitude_support
  input_jets := by
    intro ε hε z hz k hk
    have h := F.input_jets ε hε z hz k hk
    have hA := norm_nonneg (iteratedFDeriv ℝ k (Function.uncurry (F.amplitude ε)) z)
    have hdA := norm_nonneg
      (deriv (fun t ↦ iteratedFDeriv ℝ k (Function.uncurry (F.amplitude t)) z) ε)
    have hb := χ.amplitude_jet_bound k hz
    change ‖iteratedFDeriv ℝ k (Function.uncurry (F.phase ε)) z‖ +
      ‖iteratedFDeriv ℝ k χ.amplitude z‖ +
      ‖deriv (fun t ↦ iteratedFDeriv ℝ k (Function.uncurry (F.phase t)) z) ε‖ +
      ‖deriv (fun _ : ℝ ↦ iteratedFDeriv ℝ k χ.amplitude z) ε‖ ≤ _
    simp only [deriv_const, norm_zero, add_zero, ScalarNormalCutoffs.inputBounds]
    linarith
  gradient_injective := F.gradient_injective
  image_buffer := fun _ hε _ hx _ hy ↦ F.cutoff_image_buffer hε hx hy
  chart_buffer := by
    intro ε hε x hx y hy
    apply (cthickening_mono (show G.inverseBuffer / 2 ≤ G.inverseBuffer from
      half_le_self G.inverseBuffer_pos.le) _).trans
    exact F.chart_buffer ε hε x hx y hy
  jacobian_gap := F.jacobian_gap

/-- The scalar channel retains the phase literally
(`app:ch_osc:prop:osc-normal`, Step 2). -/
@[simp] theorem ScalarNormalCutoffs.toUniformNormalData_phase (χ : ScalarNormalCutoffs G C)
    (F : UniformNormalData G C) : (χ.toUniformNormalData F).phase = F.phase := rfl

/-- The literal scalar amplitude identity consumed by the local operator
construction in `app:ch_osc:prop:osc-normal`, Step 2. -/
@[simp] theorem ScalarNormalCutoffs.toUniformNormalData_amplitude
    (χ : ScalarNormalCutoffs G C) (F : UniformNormalData G C)
    (ε : ℝ) (x u : Euclidean n) (i : Fin 1) :
    (χ.toUniformNormalData F).amplitude ε x u i = (χ.χx x : ℂ) * (χ.χu u : ℂ) := rfl

/-- The channel is identically one on the product of the exposed open
plateaus containing the original supports (`app:ch_osc:prop:osc-normal`). -/
theorem ScalarNormalCutoffs.amplitude_eq_one_on_plateau (χ : ScalarNormalCutoffs G C)
    {x u : Euclidean n} (hx : x ∈ interior {x | χ.χx x = 1})
    (hu : u ∈ interior {u | χ.χu u = 1}) (i : Fin 1) : χ.amplitude (x, u) i = 1 := by
  have hx' := interior_subset hx
  have hu' := interior_subset hu
  change χ.χx x = 1 at hx'
  change χ.χu u = 1 at hu'
  simp [ScalarNormalCutoffs.amplitude, hx', hu']

end JanetCartan.NormalComparison
