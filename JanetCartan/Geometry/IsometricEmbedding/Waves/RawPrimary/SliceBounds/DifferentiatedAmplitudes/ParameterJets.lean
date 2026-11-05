module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.DifferentiatedAmplitudes.Bounds
public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.InputJets.ParameterJets.Interchange

/-!
# Normalization and the parameter jet in the slice input

The extra derivative in `UniformNormalData.input_jets` is an actual parameter
derivative of the spatial jet. It is bounded here by one further joint jet,
using the proved mixed derivative interchange. This is the parameter part of
`app:ch_waves:eq:individual-raw-slice`, including the endpoint epsilon zero
in an open smooth extension.
-/

@[expose] public noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace JanetCartan.RawPrimary.SliceBounds

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Freezing the parameter contracts the joint jets on the same open product
chart (`app:ch_waves:eq:individual-raw-slice`). -/
theorem norm_iteratedFDeriv_slice_le_joint {I : Set ℝ} {U : Set E}
    (hI : IsOpen I) (hU : IsOpen U) {f : ℝ × E → F}
    (hf : ContDiffOn ℝ ∞ f (I ×ˢ U)) {ε : ℝ} (hε : ε ∈ I)
    {z : E} (hz : z ∈ U) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun y ↦ f (ε, y)) z‖ ≤
      ‖iteratedFDeriv ℝ k f (ε, z)‖ := by
  let T : E →L[ℝ] ℝ × E := ContinuousLinearMap.inr ℝ ℝ E
  let g : ℝ × E → F := fun q ↦ f ((ε, 0) + q)
  let W : Set (ℝ × E) := (fun q ↦ (ε, 0) + q) ⁻¹' (I ×ˢ U)
  have hW : IsOpen W := (hI.prod hU).preimage (by fun_prop)
  have hg : ContDiffOn ℝ ∞ g W :=
    hf.comp (contDiffOn_const.add contDiffOn_id) (fun _ h ↦ h)
  have hT : ‖T‖ ≤ 1 := by
    apply T.opNorm_le_bound zero_le_one
    intro y
    simp [T]
  have hmem : T z ∈ W := by simpa [W, T] using And.intro hε hz
  have hh := NormalComparison.norm_iteratedFDeriv_comp_linear_on_open_le T hW hg hmem k
  have he : (fun y ↦ f (ε, y)) = g ∘ T := by ext y; simp [g, T]
  rw [he]
  apply hh.trans
  apply (mul_le_of_le_one_right (norm_nonneg _)
    (pow_le_one₀ (norm_nonneg _) hT)).trans_eq
  simp only [g, iteratedFDeriv_comp_add_left]
  simp [T]

/-- The parameter derivative required by `UniformNormalData.input_jets`
costs exactly one joint derivative; it is derived, not supplied as an
amplitude-jet premise (`app:ch_waves:eq:individual-raw-slice`). -/
theorem norm_deriv_sliceJet_le_joint {I : Set ℝ} {U : Set E}
    (hI : IsOpen I) (hU : IsOpen U) {f : ℝ × E → F}
    (hf : ContDiffOn ℝ ∞ f (I ×ˢ U)) {ε : ℝ} (hε : ε ∈ I)
    {z : E} (hz : z ∈ U) (k : ℕ) :
    ‖deriv (fun t ↦ iteratedFDeriv ℝ k (fun y ↦ f (t, y)) z) ε‖ ≤
      ‖iteratedFDeriv ℝ (k + 1) f (ε, z)‖ := by
  rw [← NormalComparison.iteratedFDeriv_deriv_parameter hI hU hf hε hz k]
  let g : ℝ × E → F := fun q ↦ fderiv ℝ f q (1, 0)
  have hg : ContDiffOn ℝ ∞ g (I ×ˢ U) :=
    (hf.fderiv_of_isOpen (hI.prod hU) (m := ∞) (by simp)).clm_apply contDiffOn_const
  have heq : (fun y ↦ deriv (fun t ↦ f (t, y)) ε) =ᶠ[𝓝 z]
      (fun y ↦ g (ε, y)) := by
    filter_upwards [hU.mem_nhds hz] with y hy
    exact (((hf.contDiffAt ((hI.prod hU).mem_nhds ⟨hε, hy⟩)).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt ε
        ((hasDerivAt_id ε).prodMk (hasDerivAt_const ε y))).deriv
  rw [(heq.iteratedFDeriv (𝕜 := ℝ) (n := k)).eq_of_nhds]
  apply (norm_iteratedFDeriv_slice_le_joint hI hU hg hε hz k).trans
  have hd := (hf.contDiffAt ((hI.prod hU).mem_nhds
    (show (ε, z) ∈ I ×ˢ U from ⟨hε, hz⟩))).fderiv_right
    (m := ∞) (by simp)
  have hh := norm_iteratedFDeriv_clm_apply_const (c := ((1 : ℝ), (0 : E))) hd
    (by simp : (k : ℕ∞ω) ≤ ∞)
  simpa only [g, Prod.norm_def, norm_one, norm_zero, max_eq_left zero_le_one,
    one_mul, norm_iteratedFDeriv_fderiv] using hh

/-- Removing the exact `L^(s-q)` physical cost from a branch leaves the
amplitude used by the order-zero single-channel estimate
(`app:ch_waves:eq:individual-raw-slice`). -/
def normalizedSliceDerivativeAmplitude (φ : E → ℝ) (A : E → F)
    {s : ℕ} (v : Fin s → E) (b : SliceDerivativeBranch s) (L : ℝ) : E → F :=
  fun x ↦ (L ^ (s - b.phaseCount))⁻¹ • sliceDerivativeAmplitude φ A v b x

/-- Normalization preserves joint smoothness on the original chart
(`app:ch_waves:eq:individual-raw-slice`). -/
theorem contDiffOn_normalizedSliceDerivativeAmplitude {U : Set E} (hU : IsOpen U)
    {φ : E → ℝ} {A : E → F} (hφ : ContDiffOn ℝ ∞ φ U)
    (hA : ContDiffOn ℝ ∞ A U) {s : ℕ} (v : Fin s → E)
    (b : SliceDerivativeBranch s) (L : ℝ) :
    ContDiffOn ℝ ∞ (normalizedSliceDerivativeAmplitude φ A v b L) U :=
  (contDiffOn_sliceDerivativeAmplitude hU hφ hA v b).const_smul _

/-- Reconstruction restores the exact physical scale and changes neither
the branch nor the phase (`app:ch_waves:eq:individual-raw-slice`). -/
theorem scale_normalizedSliceDerivativeAmplitude {φ : E → ℝ} {A : E → F}
    {s : ℕ} (v : Fin s → E) (b : SliceDerivativeBranch s) {L : ℝ} (hL : 0 < L) (x : E) :
    L ^ (s - b.phaseCount) • normalizedSliceDerivativeAmplitude φ A v b L x =
      sliceDerivativeAmplitude φ A v b x := by
  simp only [normalizedSliceDerivativeAmplitude, smul_smul,
    mul_inv_cancel₀ (pow_ne_zero _ hL.ne'), one_smul]

/-- Every required normalized joint jet is independent of the scale. The
only quantitative inputs are the primitive phase/amplitude grades at orders
through `s+k`, with the same fixed reserve
(`app:ch_waves:eq:individual-raw-slice`). -/
theorem norm_iteratedFDeriv_normalizedSliceDerivativeAmplitude_le
    {U : Set E} (hU : IsOpen U) {φ : E → ℝ} {A : E → F}
    (hφ : ContDiffOn ℝ ∞ φ U) (hA : ContDiffOn ℝ ∞ A U)
    {n Dpr s k : ℕ} (hk : k ≤ rawSliceJetOrder n + 1)
    (v : Fin s → E) (b : SliceDerivativeBranch s) (hv : ∀ i, ‖v i‖ ≤ 1)
    {L : ℝ} (hL : 1 ≤ L) {a p : ℕ → ℝ}
    (ha : ∀ j ≤ s + k, 0 ≤ a j)
    (hp : ∀ j, 1 ≤ j → j ≤ s + k → 0 ≤ p j)
    {x : E} (hx : x ∈ U)
    (hAj : ∀ j ≤ s + k, ‖iteratedFDeriv ℝ j A x‖ ≤
      a j * L ^ (j + Dpr - rawSlicePrimitiveReserve n Dpr))
    (hφj : ∀ j, 1 ≤ j → j ≤ s + k → ‖iteratedFDeriv ℝ j φ x‖ ≤
      p j * L ^ (j - 1 + Dpr - rawSlicePrimitiveReserve n Dpr)) :
    ‖iteratedFDeriv ℝ k (normalizedSliceDerivativeAmplitude φ A v b L) x‖ ≤
      sliceDerivativeJetConstant a p b k := by
  have hpos : 0 < L ^ (s - b.phaseCount) := pow_pos (lt_of_lt_of_le zero_lt_one hL) _
  have hs := contDiffOn_sliceDerivativeAmplitude hU hφ hA v b
  change ‖iteratedFDeriv ℝ k
    (fun y ↦ (L ^ (s - b.phaseCount))⁻¹ • sliceDerivativeAmplitude φ A v b y) x‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply'
    ((hs.contDiffAt (hU.mem_nhds hx)).of_le (by simp)), norm_smul,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)]
  apply (mul_le_mul_of_nonneg_left
    (norm_iteratedFDeriv_sliceDerivativeAmplitude_le_fixedReserve hU hφ hA hk
      v b hv hL ha hp hx hAj hφj) (inv_nonneg.mpr hpos.le)).trans_eq
  field_simp

end JanetCartan.RawPrimary.SliceBounds
