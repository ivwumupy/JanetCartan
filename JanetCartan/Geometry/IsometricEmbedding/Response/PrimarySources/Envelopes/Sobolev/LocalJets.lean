module

public import JanetCartan.Geometry.IsometricEmbedding.Response.PrimarySources.Envelopes.Extension
public import JanetCartan.Analysis.Sobolev.Local.Smooth.FiniteOrder.SmoothEstimate.Jets
public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.InputJets.Base

/-!
# Local jets of the fixed primary source extension

The local input to `app:ch_response:eq:response-graded-source` is a joint
pointwise grade. Restriction to spatial slices and multiplication by the
already selected output cutoff preserve its scale power. Constants are chosen
before the amplitude, its size, its scale, and the carrier.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Topology

namespace JanetCartan.ResponsePrimarySources

variable {E P F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem iteratedFDeriv_affine_restrict
    (L : E →L[ℝ] P) (b : P) {U : Set P} (hU : IsOpen U)
    {f : P → F} (hf : ContDiffOn ℝ ∞ f U) {x : E} (hx : b + L x ∈ U) (j : ℕ) :
    iteratedFDeriv ℝ j (fun y ↦ f (b + L y)) x =
      (iteratedFDeriv ℝ j f (b + L x)).compContinuousLinearMap (fun _ ↦ L) := by
  let W := (fun z ↦ b + z) ⁻¹' U
  have hW : IsOpen W := hU.preimage (by fun_prop)
  have hg : ContDiffOn ℝ ∞ (fun z ↦ f (b + z)) W :=
    hf.comp (by fun_prop) (fun _ h ↦ h)
  have h := L.iteratedFDerivWithin_comp_right hg hW.uniqueDiffOn
    (hW.preimage L.continuous).uniqueDiffOn hx (i := j) (by simp)
  rw [iteratedFDerivWithin_of_isOpen _ (hW.preimage L.continuous) hx,
    iteratedFDerivWithin_of_isOpen _ hW hx, iteratedFDeriv_comp_add_left] at h
  exact h

/-- Freezing the carrier costs no joint derivative order or norm constant.
Consumer: the primary strain envelope in `app:ch_response:cor:current-atoms`. -/
theorem norm_iteratedFDeriv_primary_spatialSlice_le
    {U : Set E} {V : Set P} (hU : IsOpen U) (hV : IsOpen V)
    {a : E × P → F} (ha : ContDiffOn ℝ ∞ a (U ×ˢ V))
    {x : E} (hx : x ∈ U) {c : P} (hc : c ∈ V) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun y ↦ a (y, c)) x‖ ≤
      ‖iteratedFDeriv ℝ j a (x, c)‖ := by
  let L : E →L[ℝ] E × P := ContinuousLinearMap.inl ℝ E P
  have he := iteratedFDeriv_affine_restrict L (0, c) (hU.prod hV) ha
    (x := x) (by simpa [L] using And.intro hx hc) j
  simp only [L, ContinuousLinearMap.inl_apply, Prod.mk_add_mk, zero_add, add_zero] at he
  rw [he]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  have hL : ‖ContinuousLinearMap.inl ℝ E P‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by intro y; simp)
  simpa using mul_le_of_le_one_right (norm_nonneg (iteratedFDeriv ℝ j a (x, c)))
    (pow_le_one₀ (norm_nonneg _) hL)

/-- Carrier derivatives are evaluations of the same joint jet, on the original
open chart (`app:ch_response:cor:current-atoms`). -/
theorem primary_carrier_derivative_eq_joint
    {U : Set E} {V : Set P} (hU : IsOpen U) (hV : IsOpen V)
    {a : E × P → F} (ha : ContDiffOn ℝ ∞ a (U ×ˢ V))
    {x : E} (hx : x ∈ U) {c : P} (hc : c ∈ V) (k : ℕ) (v : Fin k → P) :
    iteratedFDeriv ℝ k (fun d ↦ a (x, d)) c v =
      iteratedFDeriv ℝ k a (x, c) (fun i ↦ (0, v i)) := by
  have he := iteratedFDeriv_affine_restrict (ContinuousLinearMap.inr ℝ E P)
    (x, 0) (hU.prod hV) ha (x := c) (by simpa using And.intro hx hc) k
  simpa using congrArg (fun t ↦ t v) he

/-- Spatial derivatives of evaluated carrier jets use exactly the total order
`j+k`. Unit directions cost no extra power of the scale. Consumer:
`app:ch_response:eq:response-graded-source` for each prescribed carrier jet. -/
theorem primary_carrier_derivative_spatial_bounds
    {U : Set E} {V : Set P} (hU : IsOpen U) (hV : IsOpen V)
    {a : E × P → F} (ha : ContDiffOn ℝ ∞ a (U ×ˢ V))
    (k : ℕ) (v : Fin k → P) (hv : ∀ i, ‖v i‖ ≤ 1) {c : P} (hc : c ∈ V) :
    ContDiffOn ℝ ∞ (fun x ↦ iteratedFDeriv ℝ k (fun d ↦ a (x, d)) c v) U ∧
    ∀ x ∈ U, ∀ j,
      ‖iteratedFDeriv ℝ j (fun y ↦ iteratedFDeriv ℝ k (fun d ↦ a (y, d)) c v) x‖ ≤
        ‖iteratedFDeriv ℝ (j + k) a (x, c)‖ := by
  let ev := ContinuousMultilinearMap.apply ℝ (fun _ : Fin k ↦ E × P) F
    (fun i ↦ (0, v i))
  have hev : ‖ev‖ ≤ 1 := by
    apply ev.opNorm_le_bound zero_le_one
    intro t
    apply (t.le_opNorm (fun i ↦ (0, v i))).trans
    simpa only [one_mul] using mul_le_of_le_one_right (norm_nonneg t)
      (Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _) (fun i _ ↦ by simpa using hv i))
  have hj : ContDiffOn ℝ ∞ (iteratedFDeriv ℝ k a) (U ×ˢ V) := fun z hz ↦
    ((ha.contDiffAt ((hU.prod hV).mem_nhds hz)).iteratedFDeriv_right (by simp)).contDiffWithinAt
  have he : EqOn (fun x ↦ iteratedFDeriv ℝ k (fun d ↦ a (x, d)) c v)
      (fun x ↦ ev (iteratedFDeriv ℝ k a (x, c))) U :=
    fun x hx ↦ primary_carrier_derivative_eq_joint hU hV ha hx hc k v
  refine ⟨((ev.contDiff.comp_contDiffOn hj).comp
    (contDiffOn_id.prodMk contDiffOn_const) (fun _ hx ↦ ⟨hx, hc⟩)).congr he, ?_⟩
  intro x hx j
  have he' := he.eventuallyEq_of_mem (hU.mem_nhds hx)
  rw [(he'.iteratedFDeriv ℝ j).self_of_nhds]
  apply (norm_iteratedFDeriv_primary_spatialSlice_le hU hV
    (ev.contDiff.comp_contDiffOn hj) hx hc j).trans
  apply (ev.norm_iteratedFDeriv_comp_left
    (hj.contDiffAt ((hU.prod hV).mem_nhds ⟨hx, hc⟩)) (by simp)).trans
  apply (mul_le_of_le_one_left (norm_nonneg _) hev).trans_eq
  rw [LocalSobolev.FiniteOrder.norm_iteratedFDeriv_iteratedFDeriv, Nat.add_comm]

variable {n : ℕ} {core chart : Set (Euclidean n)}

/-- Fixed-cutoff Leibniz constants for the primary source. The actual amplitude
is quantified after the constants; only orders through the requested order
are used (`app:ch_response:eq:response-graded-source`). -/
theorem exists_primary_zeroExtend_jet_constants (χ : ResponseSourceExtension.OutputCutoff core chart)
    (hchart : IsOpen chart) (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) :
    ∃ J : ℕ → ℝ, (∀ j, 0 ≤ J j) ∧
      ∀ (f : Euclidean n → F) (A L : ℝ), 0 ≤ A → 1 ≤ L →
      ContDiffOn ℝ ∞ f chart →
      (∀ x ∈ chart, ∀ j, ‖iteratedFDeriv ℝ j f x‖ ≤ B j * A * L ^ j) →
      ∀ x j, ‖iteratedFDeriv ℝ j (χ.zeroExtend (fun y : chart ↦ f y)) x‖ ≤
        J j * A * L ^ j := by
  have hX (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ tsupport χ.toFun,
      ‖iteratedFDeriv ℝ j χ.toFun x‖ ≤ C := by
    obtain ⟨C, hC⟩ := χ.compact.exists_bound_of_continuousOn
      (χ.smooth.continuous_iteratedFDeriv (by simp)).continuousOn
    exact ⟨max 0 C, le_max_left _ _, fun x hx ↦ (hC x hx).trans (le_max_right _ _)⟩
  choose X hX hXbound using hX
  let J := fun j ↦ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * X i * B (j - i)
  have hJ : ∀ j, 0 ≤ J j := fun j ↦ Finset.sum_nonneg fun i _ ↦
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hX i)) (hB _)
  refine ⟨J, hJ, ?_⟩
  intro f A L hA hL hf hb x j
  by_cases hx : x ∈ tsupport χ.toFun
  · rw [χ.zeroExtend_restrict]
    have hxchart := χ.support_chart hx
    have ht := norm_iteratedFDerivWithin_smul_le χ.smooth.contDiffOn hf
      hchart.uniqueDiffOn hxchart (by simp : (j : ℕ∞ω) ≤ ∞)
    simp only [iteratedFDerivWithin_of_isOpen _ hchart hxchart] at ht
    apply ht.trans
    simp only [J, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    calc
      _ ≤ (j.choose i : ℝ) * X i * (B (j - i) * A * L ^ (j - i)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hXbound i x hx) (Nat.cast_nonneg _))
          (hb x hxchart _) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hX i))
      _ = ((j.choose i : ℝ) * X i * B (j - i)) * A * L ^ (j - i) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (Nat.sub_le _ _))
        (mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hX i)) (hB _)) hA)
  · have hz : χ.zeroExtend (fun y : chart ↦ f y) =ᶠ[𝓝 x] 0 := by
      rw [χ.zeroExtend_restrict]
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      simp [hy]
    rw [(hz.iteratedFDeriv ℝ j).self_of_nhds]
    simp only [iteratedFDeriv_zero, Pi.zero_apply, norm_zero]
    exact mul_nonneg (mul_nonneg (hJ j) hA) (pow_nonneg (zero_le_one.trans hL) _)

end JanetCartan.ResponsePrimarySources
