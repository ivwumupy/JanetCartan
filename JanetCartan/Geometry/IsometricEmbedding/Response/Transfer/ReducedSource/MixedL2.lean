module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.ReducedSource.JointJets
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.LowEnvelope.CompactSobolev

/-!
# Mixed L² tensors of the literal reduced source

The original physical cutoff supplies a fixed compact support for every
joint derivative. Its volume is independent of the source and history; no
Sobolev embedding or extra derivative is used in the datum bounds for
`app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.ResponseTransfer.ReducedSource
open Sampling.BackgroundModulation ResponseSourceExtension
variable {n d : ℕ}
local notation "E" => Euclidean n
local notation "Par" => Euclidean 3 × Euclidean d
local notation "Tensor" => Matrix (Fin n) (Fin n) ℂ

private theorem norm_toLp_jet_le_of_support_bound
    {F : Type*} [NormedAddCommGroup F] {f : E → F} (hf : MemLp f 2 volume)
    {S : Set E} (hS : IsCompact S) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ x, ‖f x‖ ≤ B) (hz : ∀ x, x ∉ S → f x = 0) :
    ‖hf.toLp f‖ ≤ B * Real.sqrt (volume.real S) := by
  have h : ‖hf.toLp f‖ ≤ ‖indicatorConstLp (μ := volume) 2 hS.measurableSet hS.measure_ne_top (B : ℝ)‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hf.coeFn_toLp, indicatorConstLp_coeFn (μ := volume) (p := 2)
      (hs := hS.measurableSet) (hμs := hS.measure_ne_top) (c := B)] with x hx hi
    rw [hx, hi]
    by_cases hxs : x ∈ S
    · simpa only [Set.indicator_of_mem hxs, Real.norm_eq_abs, abs_of_nonneg hB] using hb x
    · simp only [Set.indicator_of_notMem hxs, hz x hxs, norm_zero, le_refl]
  convert h using 1
  rw [norm_indicatorConstLp (by norm_num) (by norm_num)]
  simp [Real.norm_eq_abs, abs_of_nonneg hB, Real.sqrt_eq_rpow]

/-- Mixed L² tensors of the literal reduced source, with the same support and
no derivative loss. This supplies the actual datum input of both full-source
envelopes (`app:ch_response:eq:response-graded-reduced`). -/
theorem exists_cutoff_reducedSource_mixedL2_constants
    {core chart : Set E} (χ : OutputCutoff core chart) (hchart : IsOpen chart)
    (η : E → ℝ) (hη : ContDiff ℝ ∞ η)
    (AQ Ca : ℕ → ℝ) (hAQ : ∀ j, 0 ≤ AQ j) (hCa : ∀ j, 0 ≤ Ca j) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ (V : Set Par), IsOpen V →
      ∀ (Q : E → Fin n → MetricTensor n) (a : E × Par → Tensor) (A L : ℝ),
      0 ≤ A → 1 ≤ L → ContDiffOn ℝ ∞ Q chart → ContDiffOn ℝ ∞ a (chart ×ˢ V) →
      (∀ x ∈ tsupport χ.toFun, ∀ j, ‖iteratedFDeriv ℝ j Q x‖ ≤ AQ j * L ^ j) →
      (∀ w ∈ chart ×ˢ V, ∀ j, ‖iteratedFDeriv ℝ j a w‖ ≤ Ca j * A * L ^ j) →
      let b := fun w : E × Par ↦ χ.toFun w.1 •
        (η w.1 • ((1 / 2 : ℝ) • complexStressContraction (Q w.1) (a w)))
      ContDiffOn ℝ ∞ b (univ ×ˢ V) ∧
        ∀ c ∈ V, ∀ j, ∃ hm : MemLp (fun x : E ↦ iteratedFDeriv ℝ j b (x,c)) 2 volume,
          ‖hm.toLp (fun x : E ↦ iteratedFDeriv ℝ j b (x,c))‖ ≤ C j * A * L ^ j := by
  obtain ⟨C, hC, hj⟩ := exists_cutoff_reducedSource_joint_jet_constants χ hchart η hη AQ Ca hAQ hCa
  refine ⟨fun j ↦ C j * Real.sqrt (volume.real (tsupport χ.toFun)),
    fun j ↦ mul_nonneg (hC j) (Real.sqrt_nonneg _), ?_⟩
  intro V hV Q a A L hA hL hQ ha hQb hab b
  obtain ⟨hb, hbj⟩ := hj V hV Q a A L hA hL hQ ha hQb hab
  refine ⟨hb, ?_⟩
  intro c hc j
  let g := fun x : E ↦ iteratedFDeriv ℝ j b (x,c)
  have hgc : Continuous g := continuous_iff_continuousAt.mpr fun x ↦
    (((hb.contDiffAt ((isOpen_univ.prod hV).mem_nhds ⟨mem_univ x,hc⟩)).iteratedFDeriv_right (m := ∞)
      (by simp)).comp x (contDiffAt_id.prodMk contDiffAt_const)).continuousAt
  have hz (x : E) (hx : x ∉ tsupport χ.toFun) : g x = 0 := by
    have he : b =ᶠ[𝓝 (x,c)] 0 := by
      have hx' := (notMem_tsupport_iff_eventuallyEq.mp hx).comp_tendsto
        (continuous_fst.tendsto (x,c))
      filter_upwards [hx'] with w hw
      change χ.toFun w.1 = 0 at hw
      simp only [b, hw, zero_smul, Pi.zero_apply]
    change iteratedFDeriv ℝ j b (x,c) = 0
    rw [(he.iteratedFDeriv ℝ j).self_of_nhds]
    simp
  have hm : MemLp g 2 volume := hgc.memLp_of_hasCompactSupport (HasCompactSupport.intro χ.compact hz)
  refine ⟨hm, ?_⟩
  exact (norm_toLp_jet_le_of_support_bound hm χ.compact
    (mul_nonneg (mul_nonneg (hC j) hA) (pow_nonneg (zero_le_one.trans hL) _))
    (fun x ↦ hbj (x,c) ⟨mem_univ _,hc⟩ j) hz).trans_eq (by ring)

end JanetCartan.ResponseTransfer.ReducedSource
