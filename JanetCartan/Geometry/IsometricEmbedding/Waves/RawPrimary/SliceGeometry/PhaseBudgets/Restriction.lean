module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceGeometry.Domains
public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.InputJets.ParameterJets.Interchange

/-!
# Restricting the joint slice phase jets

Freezing physical time and epsilon costs no jet norm. The actual epsilon
derivative of a spatial jet costs one additional joint derivative, including
at epsilon zero (`app:ch_seed:eq:seed-quotient-integral`). These are the
restrictions needed by `UniformNormalData.input_jets`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.RawPrimary.SliceGeometry
open ActualCarriers FrozenMenu CurrentFullPhase SliceBounds
open FullPhaseCharts.ActualPhase

section RealRestriction
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Freezing the parameter contracts the joint jets on the same open product
chart (`app:ch_waves:eq:individual-raw-slice`). -/
private theorem norm_iteratedFDeriv_realSlice_le_joint {I : Set ℝ} {U : Set E}
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
private theorem norm_deriv_realSliceJet_le_joint {I : Set ℝ} {U : Set E}
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
  apply (norm_iteratedFDeriv_realSlice_le_joint hI hU hg hε hz k).trans
  have hd := (hf.contDiffAt ((hI.prod hU).mem_nhds
    (show (ε, z) ∈ I ×ˢ U from ⟨hε, hz⟩))).fderiv_right
    (m := ∞) (by simp)
  have hh := norm_iteratedFDeriv_clm_apply_const (c := ((1 : ℝ), (0 : E))) hd
    (by simp : (k : ℕ∞ω) ≤ ∞)
  simpa only [g, Prod.norm_def, norm_one, norm_zero, max_eq_left zero_le_one,
    one_mul, norm_iteratedFDeriv_fderiv] using hh

end RealRestriction

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

local notation "E" => Euclidean (n - 1)

private theorem norm_iteratedFDeriv_canonicalSlicePhase_joint_le (Q : _) (z : Euclidean 3)
    {a e b t ε : ℝ} (ha : 0 < a) (ha' : 4 * a < T.family.radius)
    (he : 0 < e) (heb : 16 * e < b)
    (hb : ball (T.reference.spatialPatch z) b ⊆
      ball (covectorCenter T) (min T.family.radius (3 * T.family.sourceRadius)))
    (ht : t ∈ Ioo (-a) a) (hε : ε ∈ sliceParameterDomain e)
    {w : E × E} (hw : w ∈ sliceExtensionDomain n a) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun q : ℝ × (E × E) ↦
      canonicalSlicePhase T Q z t q.1 q.2.1 q.2.2) (ε, w)‖ ≤
      ‖iteratedFDeriv ℝ k
        (rawSlicePhaseExtension (canonicalBasePhase T Q) (T.reference.spatialPatch z))
        (ε, (t, w.1), w.2)‖ := by
  let L : (ℝ × (E × E)) →L[ℝ] (ℝ × (ℝ × E) × E) :=
    (ContinuousLinearMap.fst ℝ _ _).prod
      (((0 : (ℝ × (E × E)) →L[ℝ] ℝ).prod
        ((ContinuousLinearMap.fst ℝ E E).comp (ContinuousLinearMap.snd ℝ _ _))).prod
        ((ContinuousLinearMap.snd ℝ E E).comp (ContinuousLinearMap.snd ℝ _ _)))
  have hL : ‖L‖ ≤ 1 := by
    apply L.opNorm_le_bound zero_le_one
    intro q
    simp [L, Prod.norm_def]
  let f := rawSlicePhaseExtension (canonicalBasePhase T Q) (T.reference.spatialPatch z)
  let v : ℝ × (ℝ × E) × E := (0, (t, 0), 0)
  let g := fun q ↦ f (v + q)
  let W := (fun q ↦ v + q) ⁻¹' sliceShiftDomain T a e
  have hW : IsOpen W := (isOpen_sliceShiftDomain T a e).preimage (by fun_prop)
  have hg : ContDiffOn ℝ ∞ g W :=
    (canonicalSlicePhase_smooth_on_shiftDomain T Q z ha' he heb hb).comp
      (contDiffOn_const.add contDiffOn_id) (fun _ h ↦ h)
  have hmem : L (ε, w) ∈ W := by
    have hh : (ε, (t, w.1), w.2) ∈ sliceShiftDomain T a e :=
      sliceExtensionDomain_mapsTo_shiftDomain T (e := e) ha ht
        (show (ε, w) ∈ sliceParameterDomain e ×ˢ sliceExtensionDomain n a from ⟨hε, hw⟩)
    simpa [L, W, v] using hh
  have heq : (fun q : ℝ × (E × E) ↦ canonicalSlicePhase T Q z t q.1 q.2.1 q.2.2) =
      g ∘ L := by
    ext q
    simp [canonicalSlicePhase, g, f, L, v]
  rw [heq]
  apply (NormalComparison.norm_iteratedFDeriv_comp_linear_on_open_le L hW hg hmem k).trans
  apply (mul_le_of_le_one_right (norm_nonneg _)
    (pow_le_one₀ (norm_nonneg _) hL)).trans_eq
  simp only [g, iteratedFDeriv_comp_add_left]
  simp [L, v, f]

/-- The spatial jet and its actual epsilon derivative are bounded by joint
raw-quotient orders `k` and `k+1`. Both endpoints are taken in the proved open
extension. Hence phase order `k+2` suffices for `UniformNormalData.input_jets`
(`app:ch_seed:eq:seed-quotient-integral`, `app:ch_waves:setup:oscillatory`). -/
theorem canonicalSlicePhase_inputJets_le_joint (Q : _) (z : Euclidean 3)
    {a e b t ε : ℝ} (ha : 0 < a) (ha' : 4 * a < T.family.radius)
    (he : 0 < e) (heb : 16 * e < b)
    (hb : ball (T.reference.spatialPatch z) b ⊆
      ball (covectorCenter T) (min T.family.radius (3 * T.family.sourceRadius)))
    (ht : t ∈ Ioo (-a) a) (hε : ε ∈ Icc 0 e)
    {w : E × E} (hw : w ∈ sliceSpatialDomain n a ×ˢ sliceInputDomain n) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (Function.uncurry (canonicalSlicePhase T Q z t ε)) w‖ +
      ‖deriv (fun ε' ↦ iteratedFDeriv ℝ k
        (Function.uncurry (canonicalSlicePhase T Q z t ε')) w) ε‖ ≤
      ‖iteratedFDeriv ℝ k
        (rawSlicePhaseExtension (canonicalBasePhase T Q) (T.reference.spatialPatch z))
        (ε, (t, w.1), w.2)‖ +
      ‖iteratedFDeriv ℝ (k + 1)
        (rawSlicePhaseExtension (canonicalBasePhase T Q) (T.reference.spatialPatch z))
        (ε, (t, w.1), w.2)‖ := by
  have hs := canonicalSlicePhase_smooth T Q z ha ha' he heb hb ht
  have hε' := sliceParameterDomain_contains he hε
  have hw' := sliceExtensionDomain_contains ha ⟨subset_closure hw.1, subset_closure hw.2⟩
  have hzero := (norm_iteratedFDeriv_realSlice_le_joint isOpen_Ioo
    (isOpen_ball.prod isOpen_ball) hs hε' hw' k).trans
      (norm_iteratedFDeriv_canonicalSlicePhase_joint_le T Q z ha ha' he heb hb ht hε' hw' k)
  have hone := (norm_deriv_realSliceJet_le_joint isOpen_Ioo
    (isOpen_ball.prod isOpen_ball) hs hε' hw' k).trans
      (norm_iteratedFDeriv_canonicalSlicePhase_joint_le T Q z ha ha' he heb hb ht hε' hw' (k + 1))
  exact add_le_add hzero hone

end JanetCartan.RawPrimary.SliceGeometry
