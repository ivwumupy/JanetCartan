module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.FiniteOrderContinuity.FlowFamily
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.FamilyConstruction

/-!
# Buffered charts retaining finite-order forward continuity

For `app:lem:common-hamilton-phase`, apply the buffered inverse construction to
the finite-order Hamilton-flow family. The `m = 1` estimate fixes the common
`C³` neighborhood; higher comparisons remain available on the same domains.
The consumer is the final symbol-to-inverse and symbol-to-phase theorem.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff InnerProductSpace
namespace JanetCartan.HamiltonPhase

variable {E U : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]

/-- `app:lem:common-hamilton-phase`: actual compatible buffered charts with
finite-order forward-projection continuity from scalar-symbol order `m + 1`.
The reference chart is built from the same reference flow used in the estimates.
All gap, range and regularity premises of finite-order inverse stability are
produced here; no inverse comparison is assumed. State containment and source
admissibility are retained for the root/ODE comparison with the tame family. -/
theorem exists_common_finiteOrder_bufferedCharts
    (H₀ : HomogeneousSymbol E) {D : Set (E × E)} (hD : IsOpen D)
    (hDH₀ : D ⊆ H₀.domain) (hH₀ : ContDiffOn ℝ ∞ H₀.h D)
    (j : U →ₗᵢ[ℝ] E) (ν : E) (horth : ∀ v : U, ⟪ν, j v⟫_ℝ = 0)
    (hspan : ∀ x : E, ⟪ν, x⟫_ℝ = 0 → ∃ u : U, j u = x)
    {s₀ : InitialData U} {τ₀ R : ℝ} (hR : 0 < R)
    (hRD : closedBall (transverseSectionState j ν (s₀, τ₀)) R ⊆ D)
    (henergy : H₀.h (transverseSectionState j ν (s₀, τ₀)) = s₀.2.1)
    (htrans : ⟪H₀.hp (transverseSectionState j ν (s₀, τ₀)), ν⟫_ℝ ≠ 0) :
    let z₀ := transverseSectionState j ν (s₀, τ₀)
    ∃ (r b δ : ℝ) (d : (m : ℕ) → (ε : ℝ) → 0 < ε → ℝ)
      (Φ₀ : HamiltonFlow H₀ U) (C₀ : ProjectionChart Φ₀)
      (A : (ℝ × InitialData U) ≃L[ℝ] (E × (ℝ × U))) (V : Set (E × (ℝ × U))),
      0 < r ∧ 0 < b ∧ 0 < δ ∧ (∀ m ε hε, 0 < d m ε hε) ∧
      IsOpen V ∧ IsCompact (closure V) ∧ (j s₀.1, s₀.2) ∈ V ∧
      C₀.target = V ∧ C₀.source ⊆ ball ((0 : ℝ), s₀) (2 * r) ∧
      ContDiffOn ℝ ∞ C₀.coordinates V ∧
      ContDiffOn ℝ ∞ Φ₀.augmentedProjection (ball ((0 : ℝ), s₀) (3 * r)) ∧
      ∀ H : HomogeneousSymbol E, D ⊆ H.domain → ContDiffOn ℝ ∞ H.h D →
        cNorm (closedBall z₀ R) 3 (fun z ↦ H.h z - H₀.h z) ≤ δ →
        ∃ (Φ : HamiltonFlow H U) (C : ProjectionChart Φ),
          Φ.time = Φ₀.time ∧ Φ.parameters = Φ₀.parameters ∧
          Φ.sectionMap = j.toContinuousLinearMap ∧
          C.target = V ∧ C.source = ball ((0 : ℝ), s₀) (3 * r) ∩ Φ.augmentedProjection ⁻¹' V ∧
          C.source ⊆ ball ((0 : ℝ), s₀) (2 * r) ∧
          ContDiffOn ℝ ∞ C.coordinates V ∧
          ContDiffOn ℝ ∞ Φ.augmentedProjection (ball ((0 : ℝ), s₀) (3 * r)) ∧
          cthickening b (Φ.augmentedProjection '' closure (ball ((0 : ℝ), s₀) r)) ⊆ V ∧
          cthickening b (closure V) ⊆ Φ.augmentedProjection '' ball ((0 : ℝ), s₀) (2 * r) ∧
          (∀ q ∈ ball ((0 : ℝ), s₀) (3 * r),
            ‖(A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U)).comp
              (fderiv ℝ Φ.augmentedProjection q) - ContinuousLinearMap.id ℝ (ℝ × InitialData U)‖ ≤ 1 / 2) ∧
          (∀ m ε hε, cNorm (closedBall z₀ R) (m + 1) (fun z ↦ H.h z - H₀.h z) < d m ε hε →
            cNorm (closedBall ((0 : ℝ), s₀) (2 * r)) m
              (Φ.augmentedProjection - Φ₀.augmentedProjection) < ε) ∧
          ball ((0 : ℝ), s₀) (3 * r) ⊆ Φ.time ×ˢ Φ.parameters ∧
          (∀ q ∈ Φ.time ×ˢ Φ.parameters,
            (Φ.position q, Φ.momentum q) ∈ closedBall z₀ R) := by
  let z₀ := transverseSectionState j ν (s₀, τ₀)
  obtain ⟨r₀, T, δ₀, d, Φ₀, hr₀, hT, hδ₀, hd, ht₀, hp₀, hj₀,
      hm₀, hc₀, hq₀, hfamily⟩ :=
    exists_common_finiteOrder_hamiltonFlows H₀ hD hDH₀ hH₀ j ν horth hR hRD henergy htrans
  let Q := Icc (-T) T ×ˢ closedBall s₀ r₀
  have hQ : IsCompact Q := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hdomQ : Φ₀.time ×ˢ Φ₀.parameters ⊆ Q := by
    rw [ht₀, hp₀]
    exact prod_mono Ioo_subset_Icc_self ball_subset_closedBall
  have hs₀ : s₀ ∈ Φ₀.parameters := hp₀.symm ▸ mem_ball_self hr₀
  have hv : ⟪ν, H₀.hp (j s₀.1, Φ₀.momentum (0, s₀))⟫_ℝ ≠ 0 := by
    rw [hm₀, real_inner_comm]
    exact htrans
  obtain ⟨A, _hA, r, hr, _hk₁, _hk₂, _hk₃, hinnerouter, _hmidouter, hadm,
      hconv, hgap, ε, hε, b, hb, V, hV, hVc, hzV, hstable⟩ :=
    Φ₀.exists_bufferedProjection_domains j hj₀ ν horth hspan hs₀ hv
      ((hc₀.contDiffAt ((Φ₀.isOpen_time.prod Φ₀.isOpen_parameters).mem_nhds
        ⟨Φ₀.zero_mem_time, hs₀⟩)).of_le (by simp))
  have hballadm : ball ((0 : ℝ), s₀) (3 * r) ⊆ Φ₀.time ×ˢ Φ₀.parameters := subset_closure.trans hadm
  have hballQ := hballadm.trans hdomQ
  have hmidQ : closedBall ((0 : ℝ), s₀) (2 * r) ⊆ Q :=
    (closedBall_subset_ball (by linarith : 2 * r < 3 * r)).trans hballQ
  let N := ‖(A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U))‖
  have hN : 0 ≤ N := by
    exact norm_nonneg (A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U))
  let η := min ε (1 / (4 * (N + 1)))
  have hη : 0 < η := lt_min hε (by positivity)
  have hNη : N * η ≤ 1 / 4 := by
    have hh := (le_div_iff₀ (show 0 < 4 * (N + 1) by positivity)).mp (min_le_right ε (1 / (4 * (N + 1))))
    change η * (4 * (N + 1)) ≤ 1 at hh
    nlinarith [hη.le]
  have hcharts (H : HomogeneousSymbol E) (Φ : HamiltonFlow H U)
      (ht : Φ.time = Φ₀.time) (hp : Φ.parameters = Φ₀.parameters)
      (hc : ContDiffOn ℝ ∞ Φ.position (Φ.time ×ˢ Φ.parameters))
      (hq : ∀ q ∈ Q, ContDiffAt ℝ ∞ Φ.augmentedProjection q)
      (hclose : cNorm Q 1 (Φ.augmentedProjection - Φ₀.augmentedProjection) < η) :
      ∃ C : ProjectionChart Φ,
        C.target = V ∧ C.source = ball ((0 : ℝ), s₀) (3 * r) ∩ Φ.augmentedProjection ⁻¹' V ∧
        C.source ⊆ ball ((0 : ℝ), s₀) (2 * r) ∧ ContDiffOn ℝ ∞ C.coordinates V ∧
        ContDiffOn ℝ ∞ Φ.augmentedProjection (ball ((0 : ℝ), s₀) (3 * r)) ∧
        cthickening b (Φ.augmentedProjection '' closure (ball ((0 : ℝ), s₀) r)) ⊆ V ∧
        cthickening b (closure V) ⊆ Φ.augmentedProjection '' ball ((0 : ℝ), s₀) (2 * r) ∧
        (∀ q ∈ ball ((0 : ℝ), s₀) (3 * r),
          ‖(A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U)).comp
            (fderiv ℝ Φ.augmentedProjection q) - ContinuousLinearMap.id ℝ (ℝ × InitialData U)‖ ≤ 1 / 2) := by
    have hvalue (q : ℝ × InitialData U) (hqQ : q ∈ Q) :
        ‖Φ.augmentedProjection q - Φ₀.augmentedProjection q‖ ≤ η := by
      have hh := norm_iteratedFDeriv_le_cNorm_of_contDiffAt
        (f := Φ.augmentedProjection - Φ₀.augmentedProjection) hQ
        (fun q hqQ ↦ ((hq q hqQ).sub (hq₀ q hqQ)).of_le (by simp)) hqQ (by omega : 0 ≤ 1)
      apply le_trans ?_ hclose.le
      simpa only [norm_iteratedFDeriv_zero, Pi.sub_apply] using hh
    have hderiv (q : ℝ × InitialData U) (hqQ : q ∈ Q) :
        ‖fderiv ℝ Φ.augmentedProjection q - fderiv ℝ Φ₀.augmentedProjection q‖ ≤ η := by
      have hh := norm_iteratedFDeriv_le_cNorm_of_contDiffAt
        (f := Φ.augmentedProjection - Φ₀.augmentedProjection) hQ
        (fun q hqQ ↦ ((hq q hqQ).sub (hq₀ q hqQ)).of_le (by simp)) hqQ (by omega : 1 ≤ 1)
      have he := fderiv_sub ((hq q hqQ).differentiableAt (by simp))
        ((hq₀ q hqQ).differentiableAt (by simp))
      rw [norm_iteratedFDeriv_one, he] at hh
      exact hh.trans hclose.le
    have hadm' : ball ((0 : ℝ), s₀) (3 * r) ⊆ Φ.time ×ˢ Φ.parameters := by
      simpa only [ht, hp] using hballadm
    have hdiff : ∀ q ∈ ball ((0 : ℝ), s₀) (3 * r), DifferentiableAt ℝ Φ.augmentedProjection q :=
      fun q hqB ↦ (hq q (hballQ hqB)).differentiableAt (by simp)
    obtain ⟨_hi, _hlip, _hk, hinner, htarget, hpre, _hpre'⟩ := hstable Φ.augmentedProjection hdiff
      (fun q hqB ↦ (hderiv q (hballQ hqB)).trans (min_le_left _ _))
      (fun q hqB ↦ (hvalue q (hballQ (ball_subset_ball (by linarith) (hinnerouter hqB)))).trans (min_le_left _ _))
    have hhalf : ∀ q ∈ ball ((0 : ℝ), s₀) (3 * r),
        ‖(A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U)).comp
          (fderiv ℝ Φ.augmentedProjection q) - ContinuousLinearMap.id ℝ (ℝ × InitialData U)‖ ≤ 1 / 2 := by
      intro q hqB
      apply normalized_derivative_gap_of_perturbation A (A := fderiv ℝ Φ₀.augmentedProjection q)
      · have he : (A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U)).comp
            (fderiv ℝ Φ₀.augmentedProjection q - (A : _ →L[ℝ] _)) =
            (A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U)).comp
              (fderiv ℝ Φ₀.augmentedProjection q) - ContinuousLinearMap.id ℝ (ℝ × InitialData U) := by
          apply ContinuousLinearMap.ext
          intro v
          simp
        exact he ▸ hgap q hqB
      · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          ((mul_le_mul_of_nonneg_left (hderiv q (hballQ hqB)) hN).trans hNη)
    have himage : V ⊆ Φ.augmentedProjection '' ball ((0 : ℝ), s₀) (3 * r) := by
      intro z hz
      exact image_mono (ball_subset_ball (by linarith))
        (htarget (self_subset_cthickening _ (subset_closure hz)))
    obtain ⟨C, hCt, hCs, hC⟩ :=
      Φ.exists_smoothBufferedProjectionChart isOpen_ball hconv hV hadm' himage hc A hhalf
    refine ⟨C, hCt, hCs, ?_, hC,
      (fun q hqB ↦ (hq q (hballQ hqB)).contDiffWithinAt), hinner, htarget, hhalf⟩
    intro q hqC
    rw [hCs] at hqC
    exact hpre ⟨self_subset_cthickening _ (subset_closure hqC.2), hqC.1⟩
  obtain ⟨C₀, hC₀t, _hC₀s, hC₀buffer, hC₀, hΦ₀, _hinner₀, _htarget₀, _hhalf₀⟩ :=
    hcharts H₀ Φ₀ rfl rfl hc₀ hq₀ (by simpa only [sub_self, cNorm_zero] using hη)
  refine ⟨r, b, min δ₀ (d 1 η hη / 2), d, Φ₀, C₀, A, V, hr, hb,
    lt_min hδ₀ (half_pos (hd 1 η hη)), hd, hV, hVc, hzV, hC₀t, hC₀buffer, hC₀, hΦ₀, ?_⟩
  intro H hDH hH hsmall
  obtain ⟨Φ, ht, hp, hj, hc, _hmc, _hrange, hq, hcompare⟩ :=
    hfamily H hDH hH (hsmall.trans (min_le_left _ _))
  have hlow : cNorm (closedBall z₀ R) (1 + 1) (fun z ↦ H.h z - H₀.h z) < d 1 η hη :=
    ((cNorm_mono_order (by omega : 1 + 1 ≤ 3)).trans
      (hsmall.trans (min_le_right _ _))).trans_lt (half_lt_self (hd 1 η hη))
  obtain ⟨C, hCt, hCs, hbuffer, hC, hΦ, hinner, htarget, hhalf⟩ :=
    hcharts H Φ ht hp hc hq (hcompare 1 η hη hlow)
  refine ⟨Φ, C, ht, hp, hj, hCt, hCs, hbuffer, hC, hΦ, hinner, htarget, hhalf,
    ?_, (by simpa only [ht, hp] using hballadm), _hrange⟩
  intro m ε hε hn
  exact (cNorm_mono_set_of_contDiffAt hmidQ hQ
    (fun q hqQ ↦ ((hq q hqQ).sub (hq₀ q hqQ)).of_le (by simp))).trans_lt
      (hcompare m ε hε hn)

end JanetCartan.HamiltonPhase
