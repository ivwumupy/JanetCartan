module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualFlow.BufferedFootpoint
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseEstimates.FiberBounds
/-!
# Joint one-high bounds for forwards and backwards characteristics

For `app:ch_waves:eq:joint-tame`, both characteristic maps are fixed linear
restrictions of the SAME autonomous flow. The genuine ODE estimate constructs
its variational equations and closes every forcing input. Constants precede
the field and flow, and depend only on the low bound and fixed buffers.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff
namespace JanetCartan.NullTransport.ActualFlow
open FullPhaseCharts.InverseEstimates
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Fixed restriction to the adapted initial section (`app:ch_waves:eq:joint-tame`). -/
def forwardLiftInput : (ℝ × E) →L[ℝ] (ℝ × E) × ℝ :=
  ((0 : (ℝ × E) →L[ℝ] ℝ).prod (ContinuousLinearMap.snd ℝ ℝ E)).prod
    (ContinuousLinearMap.fst ℝ ℝ E)

/-- Fixed substitution for the backwards footpoint formula (`app:ch_waves:eq:joint-tame`). -/
def backwardLiftInput : (ℝ × E) →L[ℝ] (ℝ × E) × ℝ :=
  (ContinuousLinearMap.id ℝ (ℝ × E)).prod (-(ContinuousLinearMap.fst ℝ ℝ E))

/-- Forward restriction is a contraction (`app:ch_waves:eq:joint-tame`). -/
theorem norm_forwardLiftInput_le : ‖forwardLiftInput (E := E)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro q
  simp [forwardLiftInput, Prod.norm_def, max_comm]

/-- Backwards substitution is a contraction (`app:ch_waves:eq:joint-tame`). -/
theorem norm_backwardLiftInput_le : ‖backwardLiftInput (E := E)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro q
  change max ‖q‖ ‖-q.1‖ ≤ 1 * ‖q‖
  simp only [norm_neg, one_mul]
  exact max_le le_rfl (le_max_left _ _)

variable [FiniteDimensional ℝ E]

/-- Both characteristic maps inherit joint bounds from the same autonomous
flow on fixed compact boxes (`app:ch_waves:eq:joint-tame`). -/
theorem cNorm_characteristics_le_flow {Ψ : (ℝ × E) × ℝ → ℝ × E}
    {p₀ : E} {R ε τ : ℝ} (hR : 0 < R) (_hε : 0 < ε)
    (_hτ : 0 ≤ τ) (hτε : τ < ε) (hτR : τ ≤ R / 4)
    (hΨ : ContDiffOn ℝ ∞ Ψ (ball (0, p₀) (R / 2) ×ˢ Ioo (-ε) ε)) (k : ℕ) :
    cNorm (Icc (-τ) τ ×ˢ closedBall p₀ (R / 8)) k (forwardFromLift Ψ) +
      cNorm (Icc (-τ) τ ×ˢ closedBall p₀ (R / 8)) k (footpointFromLift Ψ) ≤
      (2 * (k + 1 : ℝ)) *
        cNorm (closedBall (0, p₀) (R / 4) ×ˢ Icc (-τ) τ) k Ψ := by
  let S := Icc (-τ) τ ×ˢ closedBall p₀ (R / 8)
  let J := closedBall ((0 : ℝ), p₀) (R / 4) ×ˢ Icc (-τ) τ
  let W := ball ((0 : ℝ), p₀) (R / 2) ×ˢ Ioo (-ε) ε
  have hJ : IsCompact J := (isCompact_closedBall _ _).prod isCompact_Icc
  have hW : IsOpen W := isOpen_ball.prod isOpen_Ioo
  have hJW : J ⊆ W := by
    rintro ⟨q, t⟩ ⟨hq, ht⟩
    exact ⟨closedBall_subset_ball (by linarith) hq, by
      constructor <;> linarith [ht.1, ht.2]⟩
  have hF : MapsTo (forwardLiftInput (E := E)) S J := by
    rintro ⟨t, p⟩ ⟨ht, hp⟩
    refine ⟨?_, ht⟩
    change ((0 : ℝ), p) ∈ closedBall (0, p₀) (R / 4)
    simpa using (closedBall_subset_closedBall (by linarith : R / 8 ≤ R / 4) hp)
  have hB : MapsTo (backwardLiftInput (E := E)) S J := by
    rintro ⟨t, p⟩ ⟨ht, hp⟩
    refine ⟨?_, ?_⟩
    · change (t, p) ∈ closedBall (0, p₀) (R / 4)
      rw [mem_closedBall, Prod.dist_eq, max_le_iff]
      exact ⟨by simpa only [Real.dist_eq, sub_zero] using (abs_le.mpr ht).trans hτR,
        hp.trans (by linarith)⟩
    · change -τ ≤ -t ∧ -t ≤ τ
      constructor <;> linarith [ht.1, ht.2]
  have hproj (L : (ℝ × E) →L[ℝ] (ℝ × E) × ℝ)
      (hL : ‖L‖ ≤ 1) (hm : MapsTo L S J) :
      cNorm S k (fun q ↦ (Ψ (L q)).2) ≤ (k + 1 : ℝ) * cNorm J k Ψ := by
    have hf : ContDiffOn ℝ ∞ (Ψ ∘ L) (L ⁻¹' W) :=
      hΨ.comp L.contDiff.contDiffOn (fun _ h ↦ h)
    have hpost := cNorm_postLinear_le_on (isCompact_Icc.prod (isCompact_closedBall _ _))
      k (ContinuousLinearMap.snd ℝ ℝ E)
      (fun q hq ↦ (hf.contDiffAt ((hW.preimage L.continuous).mem_nhds (hJW (hm hq)))).of_le
        (by simp))
    apply hpost.trans
    apply (mul_le_of_le_one_left (cNorm_nonneg S k (Ψ ∘ L)) ?_).trans
      (cNorm_comp_contraction_le_on L hL hJ hW hJW hΨ hm k)
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro q
    simpa using norm_snd_le q
  have h₁ := hproj forwardLiftInput norm_forwardLiftInput_le hF
  have h₂ := hproj backwardLiftInput norm_backwardLiftInput_le hB
  change cNorm S k (forwardFromLift Ψ) + cNorm S k (footpointFromLift Ψ) ≤ _
  exact (add_le_add h₁ h₂).trans_eq (by ring)

/-- A joint one-high bound for both maps from the genuine ODE and its
field norm. Constants precede the field and flow. The actual null flow
construction discharges the ODE, initial identity and range hypotheses;
no variational identity or flow bound is an input (`app:ch_waves:eq:joint-tame`). -/
theorem exists_buffered_flow_cNorm_bound (p₀ : E) {R ε M : ℝ}
    (hR : 0 < R) (hε : 0 < ε) (hM : 0 ≤ M) (hεR : ε ≤ R)
    {Ω : Set (ℝ × E)} (hΩ : IsOpen Ω) (hbuffer : closedBall (0, p₀) R ⊆ Ω) (k : ℕ) :
    ∃ C > (0 : ℝ), ∀ (V : ℝ × E → ℝ × E) (Ψ : (ℝ × E) × ℝ → ℝ × E),
      ContDiffOn ℝ ∞ V Ω →
      ContDiffOn ℝ ∞ Ψ (ball (0, p₀) (R / 2) ×ˢ Ioo (-ε) ε) →
      cNorm (closedBall (0, p₀) R) 1 V ≤ M →
      (∀ q ∈ ball (0, p₀) (R / 2), Ψ (q, 0) = q) →
      (∀ q ∈ ball (0, p₀) (R / 2), ∀ t ∈ Ioo (-ε) ε,
        HasDerivAt (fun s ↦ Ψ (q, s)) (V (Ψ (q, t))) t) →
      (∀ q ∈ closedBall (0, p₀) (R / 4), ∀ t ∈ Ioo (-ε) ε,
        Ψ (q, t) ∈ closedBall (0, p₀) R) →
      cNorm (Icc (-(ε / 4)) (ε / 4) ×ˢ closedBall p₀ (R / 8)) k (forwardFromLift Ψ) +
        cNorm (Icc (-(ε / 4)) (ε / 4) ×ˢ closedBall p₀ (R / 8)) k (footpointFromLift Ψ) ≤
        C * (1 + cNorm (closedBall (0, p₀) R) k V) := by
  let l := ε / R
  let J := closedBall ((0 : ℝ), p₀) (R / 4)
  have hl : 0 < l := div_pos hε hR
  have houter : l * 2 * (R / 2) = ε := by dsimp [l]; field_simp
  have hinner : l * (R / 4) = ε / 4 := by dsimp [l]; field_simp
  obtain ⟨A, hA, hb⟩ := HamiltonPhase.exists_autonomousFlow_joint_cNorm_bound
    ((0 : ℝ), p₀) ((0 : ℝ), p₀) (by linarith : 0 < R / 4)
    (by linarith : R / 4 < R / 2) hR hl (by norm_num : (1 : ℝ) < 2)
    hΩ hbuffer 0 hM (cNorm_nonneg J 1 (id : ℝ × E → ℝ × E)) k
  let N := cNorm J k (id : ℝ × E → ℝ × E)
  have hN : 0 ≤ N := cNorm_nonneg _ _ _
  refine ⟨(2 * (k + 1 : ℝ)) * A * (1 + N), by positivity, ?_⟩
  intro V Ψ hV hΨ hVM hi hd hr
  have hf := hb V id Ψ hV contDiff_id.contDiffOn
    (by simpa only [houter, zero_sub, zero_add] using hΨ) hVM le_rfl hi
    (by simpa only [houter, zero_sub, zero_add] using hd)
    (by simpa only [houter, zero_sub, zero_add] using hr)
  simp only [hinner, zero_sub, zero_add] at hf
  have hc := cNorm_characteristics_le_flow hR hε (by positivity : 0 ≤ ε / 4)
    (by linarith : ε / 4 < ε) (by linarith : ε / 4 ≤ R / 4) hΨ k
  apply hc.trans
  have hv := cNorm_nonneg (closedBall ((0 : ℝ), p₀) R) k V
  have hhigh : 1 + cNorm (closedBall ((0 : ℝ), p₀) R) k V + N ≤
      (1 + N) * (1 + cNorm (closedBall ((0 : ℝ), p₀) R) k V) := by nlinarith
  calc
    _ ≤ (2 * (k + 1 : ℝ)) * (A * (1 + cNorm (closedBall (0, p₀) R) k V + N)) :=
      mul_le_mul_of_nonneg_left hf (by positivity)
    _ ≤ (2 * (k + 1 : ℝ)) * (A * ((1 + N) * (1 + cNorm (closedBall (0, p₀) R) k V))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hhigh hA.le) (by positivity)
    _ = _ := by ring
end JanetCartan.NullTransport.ActualFlow
