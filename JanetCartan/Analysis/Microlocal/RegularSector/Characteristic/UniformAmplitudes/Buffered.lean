module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformAmplitudes.Construction
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ResidualCoordinates.BufferedMatrices
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ConicAmplitude.CollaredBounds

/-!
# Buffered matrices on the same uniform chart

The source-flowout inclusion from `exists_uniform_pencilAmplitudes` puts the
entire smaller transported box inside its local amplitude buffer. The literal
zero extension from `ResidualCoordinates` is therefore smooth, including for
the local matrix `PW₁`. Its seminorm is controlled by the original local jets
and the fixed time cutoff, without any additional derivative reserve.

Consumer: supported conic amplitudes in `EvolutionIntegral`, for
`app:ch_regular_base:eq:energy-complete-residual` of `paper-v2.tex`.
The buffered local `PW₁` agrees with the derivative of the buffered correction
on the time plateau; outside it a cutoff commutator must still be retained.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.UniformAmplitudes
open AmplitudeBounds ResidualCoordinates
variable {d : ℕ}
local notation "T" => TwoTimePoint (Euclidean d)
local notation "Mat" => Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ

/-- The existing buffered amplitude in the characteristic joint coordinates.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
def bufferedMatrix (V : Set T) (κ : ℝ → ℝ) (f : T → Mat) : T → Mat :=
  fun q ↦ bufferedAmplitude V κ (curryCharacteristicMatrix f)
    q.1 q.2.1 q.2.2.1 q.2.2.2

/-- The actual source-flowout radius controls the whole smaller transported
box, not just the nonzero source support (`characteristic-kernel`). -/
theorem transported_small_box_subset
    (C : OpenPartialHomeomorph T T) (z : RootState (Euclidean d))
    {src ρ : ℝ} (hsrc : 0 ≤ src)
    (hflow : MapsTo C (closedBall (z.1, z) src) (closedBall (z.1, z) (ρ / 2))) :
    C.target ∩ C.symm ⁻¹' (ball z.1 (src / 2) ×ˢ
      (ball z.1 (src / 2) ×ˢ ball z.2 (src / 2))) ⊆ closedBall (z.1, z) (ρ / 2) := by
  intro q hq
  have hp : C.symm q ∈ closedBall (z.1, z) src := by
    apply closedBall_subset_closedBall (show src / 2 ≤ src by linarith)
    apply ball_subset_closedBall
    simpa only [mem_preimage, mem_prod, mem_ball, Prod.dist_eq, max_lt_iff] using hq.2
  simpa only [C.right_inv hq.1] using hflow hp

private theorem bufferedMatrix_germ {V : Set T} (hV : IsOpen V)
    (κ : ℝ → ℝ) (f : T → Mat) {q : T} (hq : q ∈ V) :
    bufferedMatrix V κ f =ᶠ[𝓝 q] fun p ↦ (κ p.1 : ℂ) • f p := by
  filter_upwards [hV.mem_nhds hq] with p hp
  simp [bufferedMatrix, bufferedAmplitude, curryCharacteristicMatrix, hp]

private theorem bufferedMatrix_regular
    (C : OpenPartialHomeomorph T T)
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    (hC : (C : T → T) = twoTimeProjection Φ)
    {I : Set ℝ} {U : Set (Euclidean d × Euclidean d)}
    (hI : IsOpen I) (hU : IsOpen U) (hbox : I ×ˢ (I ×ˢ U) ⊆ C.source)
    {κ : ℝ → ℝ} (hκ : ContDiff ℝ ∞ κ) (hcκ : HasCompactSupport κ)
    (hκI : tsupport κ ⊆ I)
    {σ : RootState (Euclidean d) → ℝ} (hcσ : HasCompactSupport σ)
    (hσI : tsupport σ ⊆ I ×ˢ U)
    {f : T → Mat}
    (hf : ContDiffOn ℝ ∞ f (C.target ∩ C.symm ⁻¹' (I ×ˢ (I ×ˢ U))))
    (hz : ∀ p ∈ C.target, (C.symm p).2 ∉ tsupport σ → f p = 0) :
    let V := C.target ∩ C.symm ⁻¹' (I ×ˢ (I ×ˢ U))
    ContDiff ℝ ∞ (bufferedMatrix V κ f) ∧
      HasCompactSupport (bufferedMatrix V κ f) ∧
      tsupport (bufferedMatrix V κ f) ⊆ V := by
  let V := C.target ∩ C.symm ⁻¹' (I ×ˢ (I ×ˢ U))
  have hV : IsOpen V := C.symm.continuousOn.isOpen_inter_preimage
    C.open_target (hI.prod (hI.prod hU))
  have hprod : tsupport κ ×ˢ tsupport σ ⊆ C.source :=
    fun _ hp ↦ hbox ⟨hκI hp.1, hσI hp.2⟩
  have hK : IsCompact (C '' (tsupport κ ×ˢ tsupport σ)) :=
    (hcκ.prod hcσ).image_of_continuousOn (C.continuousOn.mono hprod)
  have hKV : C '' (tsupport κ ×ˢ tsupport σ) ⊆ V := by
    rintro p ⟨q, hq, rfl⟩
    refine ⟨C.map_source (hprod hq), ?_⟩
    change C.symm (C q) ∈ I ×ˢ (I ×ˢ U)
    rw [C.left_inv (hprod hq)]
    exact ⟨hκI hq.1, hσI hq.2⟩
  have hs : Function.support (bufferedMatrix V κ f) ⊆ C '' (tsupport κ ×ˢ tsupport σ) := by
    intro p hp
    have hpV : p ∈ V := by
      by_contra hn
      exact hp (by simp [bufferedMatrix, bufferedAmplitude, hn])
    have hκp : κ p.1 ≠ 0 := by
      intro hk
      exact hp (by simp [bufferedMatrix, bufferedAmplitude, hpV, hk])
    have hσp : (C.symm p).2 ∈ tsupport σ := by
      by_contra hn
      exact hp (by simp [bufferedMatrix, bufferedAmplitude, curryCharacteristicMatrix,
        hpV, hz p hpV.1 hn])
    refine ⟨C.symm p, ⟨?_, hσp⟩, C.right_inv hpV.1⟩
    rw [(twoTimeChart_inverse_coordinates hC hpV.1).1]
    exact subset_tsupport κ hκp
  have ht := closure_minimal hs hK.isClosed
  refine ⟨?_, hK.of_isClosed_subset (isClosed_tsupport _) ht, ht.trans hKV⟩
  apply Localization.contDiff_of_contDiffOn_support_neighborhood hV _ (ht.trans hKV)
  intro p hp
  exact ((((Complex.ofRealCLM.contDiff.comp (hκ.comp contDiff_fst)).contDiffAt).smul
    (hf.contDiffAt (hV.mem_nhds hp))).congr_of_eventuallyEq
      (bufferedMatrix_germ hV κ f hp)).contDiffWithinAt

/-- Zero extension has no derivative cost when its actual closed support
is inside the transported open box. This estimate concerns the existing
buffered amplitude, retaining its output-time multiplier (`retarded-kernel`). -/
theorem cNorm_bufferedMatrix_le {V U : Set T} (hV : IsOpen V)
    {J : Set T} (hJ : IsCompact J) (hU : IsOpen U) (hJU : J ⊆ U)
    {κ : ℝ → ℝ} (hκ : ContDiff ℝ ∞ κ) {f : T → Mat}
    (hf : ContDiffOn ℝ ∞ f U) (hs : tsupport (bufferedMatrix V κ f) ⊆ V)
    (m : ℕ) :
    cNorm J m (bufferedMatrix V κ f) ≤
      ((m + 1 : ℝ) * 2 ^ m * cNorm J m (fun p : T ↦ (κ p.1 : ℂ))) * cNorm J m f := by
  have hg := (Complex.ofRealCLM.contDiff.comp (hκ.comp contDiff_fst)).contDiffOn.smul hf
  have hnorm : cNorm J m (bufferedMatrix V κ f) ≤
      cNorm J m (fun p : T ↦ (κ p.1 : ℂ) • f p) := by
    apply cNorm_le_sum_of_bounds (fun k _ ↦ sSup_norm_iteratedFDeriv_nonneg J k _)
    intro k hk p hp
    by_cases hpV : p ∈ V
    · rw [(bufferedMatrix_germ hV κ f hpV).iteratedFDeriv ℝ k |>.eq_of_nhds]
      exact le_csSup (bddAbove_norm_iteratedFDeriv_of_contDiffAt hJ
        (fun q hq ↦ (hg.contDiffAt (hU.mem_nhds (hJU hq))).of_le (by simp)) hk)
        (mem_image_of_mem _ hp)
    · have hz := (notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ hpV (hs h))).iteratedFDeriv ℝ k
      rw [hz.eq_of_nhds]
      simpa using sSup_norm_iteratedFDeriv_nonneg J k (fun p : T ↦ (κ p.1 : ℂ) • f p)
  exact hnorm.trans (EvolutionIntegral.SymbolBudgets.cNorm_smul_on_open_le hJ hU hJU
    (Complex.ofRealCLM.contDiff.comp (hκ.comp contDiff_fst)).contDiffOn hf m)

/-- The three literal matrices, indexed only to use one supported estimate:
`W₀`, `W₁=i·correction`, and the full `PW₁`, respectively.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
def pencilAmplitudeFamily
    (i : Fin (d + 1))
    (Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1))
    (B : Euclidean (d + 1) → MetricTensor (d + 1))
    (h : RootState (Euclidean d) → ℝ)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (C : OpenPartialHomeomorph T T) (r c : Fin (d + 1))
    (σ : RootState (Euclidean d) → ℝ) : Fin 3 → T → Mat :=
  ![pencilLeadingComplexMatrix (coordinateSplit i) Q B h Φ C r c σ,
    pencilCorrectionComplexMatrix (coordinateSplit i) Q B h Φ C r c σ,
    pencilCorrectionResidualComplexMatrix (coordinateSplit i) Q B h Φ C r c σ]

private theorem pencilAmplitudeFamily_zero
    (i : Fin (d + 1))
    (Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1))
    (B : Euclidean (d + 1) → MetricTensor (d + 1))
    (h : RootState (Euclidean d) → ℝ)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (C : OpenPartialHomeomorph T T) (hC : (C : T → T) = twoTimeProjection Φ)
    (r c : Fin (d + 1)) (σ : RootState (Euclidean d) → ℝ)
    {q : T} (hq : q ∈ C.target) (hσ : (C.symm q).2 ∉ tsupport σ) (j : Fin 3) :
    pencilAmplitudeFamily i Q B h Φ C r c σ j q = 0 := by
  have hz k := columns_eventuallyEq_zero_of_sourceMask
    (coordinateSplit i) Q B h Φ C hC r c σ hq hσ k
  have hd k : fderiv ℝ (pencilCorrectionColumn (coordinateSplit i) Q B h Φ C r c σ k) q = 0 := by
    simpa using (hz k).2.fderiv (𝕜 := ℝ) |>.eq_of_nhds
  fin_cases j <;> ext a k <;>
    simp [pencilAmplitudeFamily, pencilLeadingComplexMatrix, pencilCorrectionComplexMatrix,
      pencilCorrectionResidualComplexMatrix, complexColumnMatrix, adaptedPencilApply,
      (hz k).1.eq_of_nhds, (hz k).2.eq_of_nhds, hd k]

/-- Apply the literal supported extension to the original uniform outputs.
The whole transported source box is inside their proved smoothness domain;
all three matrices, including the full local residual, have actual compact
support and zero-cost derivative bounds. No supported matrix bound is an
input. Source: `app:ch_regular_base:lem:characteristic-kernel`. -/
theorem buffered_pencilAmplitudeFamily_of_uniform_outputs
    (i : Fin (d + 1))
    (Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1))
    (B : Euclidean (d + 1) → MetricTensor (d + 1))
    (h : RootState (Euclidean d) → ℝ)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (C : OpenPartialHomeomorph T T) (hC : (C : T → T) = twoTimeProjection Φ)
    (r c : Fin (d + 1)) (z : RootState (Euclidean d))
    {a src ρ ρo : ℝ} (hsrc : 0 < src) (hsrca : src < a)
    (hρ : 0 < ρ) (hρo : ρ < ρo) (hsource : C.source = ball (z.1, z) a)
    (hflow : MapsTo C (closedBall (z.1, z) src) (closedBall (z.1, z) (ρ / 2)))
    {σ : RootState (Euclidean d) → ℝ} {κ : ℝ → ℝ}
    (hκ : ContDiff ℝ ∞ κ) (hcκ : HasCompactSupport κ)
    (hκs : tsupport κ ⊆ ball z.1 (src / 2))
    (hcσ : HasCompactSupport σ) (hσs : tsupport σ ⊆ ball z (src / 2))
    (hf : ∀ j, ContDiffOn ℝ ∞ (pencilAmplitudeFamily i Q B h Φ C r c σ j)
      (ball (z.1, z) ρo)) :
    let V := C.target ∩ C.symm ⁻¹' (ball z.1 (src / 2) ×ˢ
      (ball z.1 (src / 2) ×ˢ ball z.2 (src / 2)))
    ∀ j,
      let f := pencilAmplitudeFamily i Q B h Φ C r c σ j
      ContDiff ℝ ∞ (bufferedMatrix V κ f) ∧
      HasCompactSupport (bufferedMatrix V κ f) ∧
      tsupport (bufferedMatrix V κ f) ⊆ V ∧
      tsupport (bufferedMatrix V κ f) ⊆ closedBall (z.1, z) (ρ / 2) ∧
      (∀ q : T, q.2.1 ≤ z.1 - src → bufferedMatrix V κ f q = 0) ∧
      (∀ m, cNorm (closedBall (z.1, z) ρ) m (bufferedMatrix V κ f) ≤
        ((m + 1 : ℝ) * 2 ^ m * cNorm (closedBall (z.1, z) ρ) m
          (fun p : T ↦ (κ p.1 : ℂ))) * cNorm (closedBall (z.1, z) ρ) m f) ∧
      (∀ q ∈ V, κ =ᶠ[𝓝 q.1] (fun _ ↦ 1) → bufferedMatrix V κ f =ᶠ[𝓝 q] f) := by
  let V := C.target ∩ C.symm ⁻¹' (ball z.1 (src / 2) ×ˢ
    (ball z.1 (src / 2) ×ˢ ball z.2 (src / 2)))
  have hV : IsOpen V := C.symm.continuousOn.isOpen_inter_preimage
    C.open_target (isOpen_ball.prod (isOpen_ball.prod isOpen_ball))
  have hVρ := transported_small_box_subset C z hsrc.le hflow
  have hVρo : V ⊆ ball (z.1, z) ρo :=
    hVρ.trans (closedBall_subset_ball (by linarith : ρ / 2 < ρo))
  have hbox : ball z.1 (src / 2) ×ˢ (ball z.1 (src / 2) ×ˢ ball z.2 (src / 2)) ⊆ C.source := by
    rw [hsource]
    intro q hq
    apply ball_subset_ball (show src / 2 ≤ a by linarith)
    simpa only [mem_prod, mem_ball, Prod.dist_eq, max_lt_iff] using hq
  have hσbox : tsupport σ ⊆ ball z.1 (src / 2) ×ˢ ball z.2 (src / 2) := by
    intro w hw
    simpa only [mem_prod, mem_ball, Prod.dist_eq, max_lt_iff] using hσs hw
  change ∀ j : Fin 3, _
  intro j f
  obtain ⟨hreg, hcomp, hs⟩ := bufferedMatrix_regular C hC isOpen_ball isOpen_ball
    hbox hκ hcκ hκs hcσ hσbox ((hf j).mono hVρo)
    (fun p hp hn ↦ pencilAmplitudeFamily_zero i Q B h Φ C hC r c σ hp hn j)
  refine ⟨hreg, hcomp, hs, hs.trans hVρ, ?_, ?_, ?_⟩
  · intro q hq
    change bufferedMatrix V κ f q = 0
    by_cases hqV : q ∈ V
    · have hn : (C.symm q).2 ∉ tsupport σ := by
        intro hm
        have ht : dist (C.symm q).2.1 z.1 < src / 2 :=
          (le_max_left _ _).trans_lt (hσs hm)
        rw [(twoTimeChart_inverse_coordinates hC hqV.1).2.1] at ht
        have hl := (abs_lt.mp (show |q.2.1 - z.1| < src / 2 from ht)).1
        linarith
      have hz := pencilAmplitudeFamily_zero i Q B h Φ C hC r c σ hqV.1 hn j
      change f q = 0 at hz
      simpa only [hz, smul_zero] using (bufferedMatrix_germ hV κ f hqV).eq_of_nhds
    · simp [bufferedMatrix, bufferedAmplitude, hqV]
  · intro m
    exact cNorm_bufferedMatrix_le hV (isCompact_closedBall _ _) isOpen_ball
      (closedBall_subset_ball hρo) hκ (hf j) hs m
  · intro q hq hk
    filter_upwards [bufferedMatrix_germ hV κ f hq,
      hk.comp_tendsto continuous_fst.continuousAt] with p hp hkp
    change κ p.1 = 1 at hkp
    simpa only [hkp, Complex.ofReal_one, one_smul] using hp

end JanetCartan.RegularSector.Characteristic.UniformAmplitudes
