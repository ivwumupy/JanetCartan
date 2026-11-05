module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading.HamiltonComparison.FlowJets

/-!
# Joint comparison with the original varying initial sections

For `app:lem:common-hamilton-phase`, autonomous time augmentation converts the
spatial comparison with varying initial jets into joint comparison. The input
orders of the vector field and initial section remain exactly the output order.
The intended consumer is the retained Hamilton forward-projection comparison;
`exists_retained_initialState_compact_tolerance` supplies its initial section
and symbol differentiation supplies its vector field. `ForwardRegularity`
and `ForwardComparison` discharge smoothness and instantiate this estimate
for the actual retained flow.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff Topology

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading
open JanetCartan.ODE
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

private theorem rescaling_buffers {r T ρ τ : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hτ : 0 < τ) (hτT : τ < T) :
    ∃ l Rp q : ℝ, 0 < l ∧ ρ < Rp ∧ Rp < r ∧ 1 < q ∧
      l * ρ = τ ∧ l * q * Rp < T := by
  let l := τ / ρ
  have hl : 0 < l := div_pos hτ hρ
  have hlρ : l * ρ = τ := div_mul_cancel₀ _ hρ.ne'
  have hρT : ρ < T / l := (lt_div_iff₀ hl).mpr (by nlinarith)
  obtain ⟨Rp, hρRp, hRp⟩ := exists_between (lt_min hρr hρT)
  have hRp0 : 0 < Rp := hρ.trans hρRp
  have hlRp : l * Rp < T := by
    have := (lt_div_iff₀ hl).mp (lt_of_lt_of_le hRp (min_le_right _ _))
    nlinarith
  have hq : 1 < T / (l * Rp) := (lt_div_iff₀ (mul_pos hl hRp0)).mpr (by simpa)
  obtain ⟨q, hq1, hqT⟩ := exists_between hq
  refine ⟨l, Rp, q, hl, hρRp, hRp.trans_le (min_le_left _ _), hq1, hlρ, ?_⟩
  have := (lt_div_iff₀ (mul_pos hl hRp0)).mp hqT
  nlinarith

omit [FiniteDimensional ℝ E] in
private theorem exists_augmented_initial_sub_bound (z : P) (ρ l c : ℝ) (m : ℕ) :
    ∃ C > (0 : ℝ), ∀ (Φ Φ₀ : P × ℝ → E),
      (∀ p ∈ closedBall z ρ, ContDiffAt ℝ m (fun p ↦ Φ (p, 0) - Φ₀ (p, 0)) p) →
      cNorm (closedBall (z, (0 : ℝ)) ρ) m
        (fun p ↦ TimeRescaling.flow 0 l c Φ (p, 0) - TimeRescaling.flow 0 l c Φ₀ (p, 0)) ≤
        C * cNorm (closedBall z ρ) m (fun p ↦ Φ (p, 0) - Φ₀ (p, 0)) := by
  let π : P × ℝ → P := Prod.fst
  let K := closedBall (z, (0 : ℝ)) ρ
  let D := compositionMultiplicity m * (1 + cNorm K m π) ^ m
  have hD : 0 ≤ D := by
    dsimp [D, compositionMultiplicity]
    exact mul_nonneg (Finset.sum_nonneg (fun _ _ ↦ Nat.cast_nonneg _))
      (pow_nonneg (by linarith [cNorm_nonneg K m π]) _)
  let V := ContinuousLinearMap.inl ℝ E ℝ
  let C := (m + 1 : ℝ) * ‖V‖ * D
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C + 1, by positivity, ?_⟩
  intro Φ Φ₀ hf
  let f : P → E := fun p ↦ Φ (p, 0) - Φ₀ (p, 0)
  have hmap : MapsTo π K (closedBall z ρ) := by
    intro p hp
    exact (show dist p.1 z ≤ dist p (z, 0) by
      rw [Prod.dist_eq]; exact le_max_left _ _).trans hp
  have hu : ∀ p ∈ K, ContDiffAt ℝ m (f ∘ π) p :=
    fun p hp ↦ (hf _ (hmap hp)).comp p contDiff_fst.contDiffAt
  have hcomp : cNorm K m (f ∘ π) ≤ D * cNorm (closedBall z ρ) m f := by
    have hπ : ContDiff ℝ m π := contDiff_fst
    have hh := cNorm_comp_le_polynomial
      (fun _ _ ↦ hπ.contDiffAt) (fun p hp ↦ hf _ (hmap hp))
      (fun i hi ↦ bddAbove_norm_iteratedFDeriv (isCompact_closedBall _ _) hπ hi)
      (cNorm_nonneg (closedBall z ρ) m f)
      (fun i hi p hp ↦ norm_iteratedFDeriv_le_cNorm_of_contDiffAt
        (isCompact_closedBall _ _) hf (hmap hp) hi)
    simpa only [D, mul_right_comm] using hh
  have heq : (fun p ↦ TimeRescaling.flow 0 l c Φ (p, 0) -
      TimeRescaling.flow 0 l c Φ₀ (p, 0)) = V ∘ (f ∘ π) := by
    funext p
    simp [TimeRescaling.flow, V, f, π]
  rw [heq]
  have hb : cNorm K m (V ∘ (f ∘ π)) ≤ (m + 1 : ℝ) * (‖V‖ * cNorm K m (f ∘ π)) := by
    apply (cNorm_le_sum_of_bounds (C := fun _ ↦ ‖V‖ * cNorm K m (f ∘ π))
      (fun _ _ ↦ mul_nonneg (norm_nonneg _) (cNorm_nonneg _ _ _)) ?_).trans_eq (by simp)
    intro i hi p hp
    exact (V.norm_iteratedFDeriv_comp_left (hu p hp) (by exact_mod_cast hi)).trans
      (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_le_cNorm_of_contDiffAt
        (isCompact_closedBall _ _) hu hp hi) (norm_nonneg _))
  calc
    _ ≤ (m + 1 : ℝ) * (‖V‖ * cNorm K m (f ∘ π)) := hb
    _ ≤ (m + 1 : ℝ) * (‖V‖ * (D * cNorm (closedBall z ρ) m f)) := by gcongr
    _ = C * cNorm (closedBall z ρ) m f := by dsimp [C]; ring
    _ ≤ (C + 1) * cNorm (closedBall z ρ) m f :=
      mul_le_mul_of_nonneg_right (by linarith) (cNorm_nonneg _ _ _)

/-- Joint finite-order comparison of actual solutions with varying initial
sections. The same order `m` of the field and initial section controls the full
space-time order `m`; neither a higher perturbation derivative nor a perturbed
flow-jet bound is assumed. The retained Hamilton instantiation in
`ForwardComparison` proves smoothness and the actual ODE/range properties
(`app:lem:common-hamilton-phase`). -/
theorem exists_retained_joint_flow_tolerance
    {W : Set E} {w : E} {z : P} {R r T ρ τ : ℝ} {V₀ : E → E} {Φ₀ : P × ℝ → E}
    (hW : IsOpen W) (hR : 0 < R) (hRW : closedBall w R ⊆ W)
    (hV₀ : ContDiffOn ℝ ∞ V₀ W)
    (hΦ₀ : ContDiffOn ℝ ∞ Φ₀ (ball z r ×ˢ Ioo (-T) T))
    (hode₀ : ∀ p ∈ ball z r, ∀ t ∈ Ioo (-T) T,
      HasDerivAt (fun s ↦ Φ₀ (p, s)) (V₀ (Φ₀ (p, t))) t)
    (hrange₀ : ∀ p ∈ closedBall z ρ, ∀ t ∈ Ioo (-T) T, Φ₀ (p, t) ∈ closedBall w R)
    (hρ : 0 < ρ) (hρr : ρ < r) (hτ : 0 < τ) (hτT : τ < T)
    (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ (V : E → E) (Φ : P × ℝ → E),
      ContDiffOn ℝ ∞ V W → ContDiffOn ℝ ∞ Φ (ball z r ×ˢ Ioo (-T) T) →
      (∀ p ∈ ball z r, ∀ t ∈ Ioo (-T) T,
        HasDerivAt (fun s ↦ Φ (p, s)) (V (Φ (p, t))) t) →
      (∀ p ∈ closedBall z ρ, ∀ t ∈ Ioo (-T) T, Φ (p, t) ∈ closedBall w R) →
      cNorm (closedBall w R) m (V - V₀) +
        cNorm (closedBall z ρ) m (fun p ↦ Φ (p, 0) - Φ₀ (p, 0)) < δ →
      cNorm (closedBall z ρ ×ˢ Icc (-τ) τ) m (Φ - Φ₀) < ε := by
  obtain ⟨l, Rp, q, hl, hρRp, hRpr, hq, hlρ, hlqRp⟩ :=
    rescaling_buffers hρ hρr hτ hτT
  let c := R / ρ
  have hc : 0 < c := div_pos hR hρ
  have hcρ : c * ρ ≤ R := (div_mul_cancel₀ R hρ.ne').le
  have hq0 : 0 < q := zero_lt_one.trans hq
  have htime : Ioo (0 - l * q * Rp) (0 + l * q * Rp) ⊆ Ioo (-T) T := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hsmooth {Φ : P × ℝ → E}
      (hΦ : ContDiffOn ℝ ∞ Φ (ball z r ×ˢ Ioo (-T) T)) :
      ContDiffOn ℝ ∞ Φ (ball z Rp ×ˢ Ioo (0 - l * q * Rp) (0 + l * q * Rp)) :=
    hΦ.mono (prod_mono (ball_subset_ball hRpr.le) htime)
  have hode {V : E → E} {Φ : P × ℝ → E}
      (hΦ : ∀ p ∈ ball z r, ∀ t ∈ Ioo (-T) T,
        HasDerivAt (fun s ↦ Φ (p, s)) (V (Φ (p, t))) t) :
      ∀ p ∈ ball (z, (0 : ℝ)) Rp, ∀ u ∈ Ioo (-q) q,
        HasDerivAt (fun v ↦ TimeRescaling.flow 0 l c Φ (p, v))
          (TimeRescaling.field l c V (TimeRescaling.flow 0 l c Φ (p, u))) u := by
    apply TimeRescaling.hasDerivAt_flow hl hq0 hc.ne'
    intro p hp t ht
    exact hΦ p (ball_subset_ball hRpr.le hp) t (htime ht)
  have hrange {Φ : P × ℝ → E}
      (hΦ : ∀ p ∈ closedBall z ρ, ∀ t ∈ Ioo (-T) T, Φ (p, t) ∈ closedBall w R) :
      ∀ p ∈ closedBall (z, (0 : ℝ)) ρ, ∀ u ∈ Ioo (-q) q,
        TimeRescaling.flow 0 l c Φ (p, u) ∈ closedBall (w, 0) R := by
    apply TimeRescaling.flow_mem_closedBall hρRp hl hq0 hc.le hcρ
    intro p hp t ht
    exact hΦ p hp t (htime ht)
  have hSW : closedBall (w, (0 : ℝ)) R ⊆ W ×ˢ univ := by
    intro p hp
    refine ⟨hRW ?_, mem_univ _⟩
    exact (show dist p.1 w ≤ dist p (w, 0) by
      rw [Prod.dist_eq]; exact le_max_left _ _).trans hp
  let A : ℝ := (max 1 |l⁻¹|) ^ m
  have hA : 0 < A := pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) _
  obtain ⟨d, hd, hstable⟩ := exists_retained_spatial_flow_tolerance
    (isCompact_closedBall (z, (0 : ℝ)) ρ) isOpen_ball (closedBall_subset_ball hρRp)
    (isCompact_closedBall (w, (0 : ℝ)) R) (convex_closedBall (w, (0 : ℝ)) R)
    (hW.prod isOpen_univ) hSW zero_lt_one hq (TimeRescaling.contDiffOn_field hV₀ l c)
    (TimeRescaling.contDiffOn_flow hl hq0 (hsmooth hΦ₀)) (hode hode₀) (hrange hrange₀)
    m (div_pos hε hA)
  obtain ⟨Cf, hCf, hfield⟩ := TimeRescaling.exists_cNorm_field_sub_bound w hR l c m
  obtain ⟨Ci, hCi, hinitial⟩ := exists_augmented_initial_sub_bound (E := E) z ρ l c m
  refine ⟨d / (Cf + Ci), div_pos hd (add_pos hCf hCi), ?_⟩
  intro V Φ hV hΦ hΦode hΦrange hsmall
  have hinitSmooth : ∀ p ∈ closedBall z ρ,
      ContDiffAt ℝ m (fun p ↦ Φ (p, 0) - Φ₀ (p, 0)) p := by
    intro p hp
    have ht : 0 ∈ Ioo (-T) T := by constructor <;> linarith
    exact (((hΦ.sub hΦ₀).contDiffAt ((isOpen_ball.prod isOpen_Ioo).mem_nhds
      ⟨closedBall_subset_ball hρr hp, ht⟩)).comp p
      (contDiffAt_id.prodMk contDiffAt_const)).of_le (by simp)
  have hsmall' : cNorm (closedBall (w, (0 : ℝ)) R) m
      (TimeRescaling.field l c V - TimeRescaling.field l c V₀) +
      cNorm (closedBall (z, (0 : ℝ)) ρ) m
        (fun p ↦ TimeRescaling.flow 0 l c Φ (p, 0) -
          TimeRescaling.flow 0 l c Φ₀ (p, 0)) < d := by
    have hf := hfield V V₀ W hW hRW hV hV₀
    have hi := hinitial Φ Φ₀ hinitSmooth
    have hh := (lt_div_iff₀ (add_pos hCf hCi)).mp hsmall
    nlinarith [cNorm_nonneg (closedBall w R) m (V - V₀),
      cNorm_nonneg (closedBall z ρ) m (fun p ↦ Φ (p, 0) - Φ₀ (p, 0))]
  have haux := hstable (TimeRescaling.field l c V) (TimeRescaling.flow 0 l c Φ)
    (TimeRescaling.contDiffOn_field hV l c)
    (TimeRescaling.contDiffOn_flow hl hq0 (hsmooth hΦ))
    (hode hΦode) (hrange hΦrange) hsmall' 1 (by constructor <;> norm_num)
  have hrec := TimeRescaling.cNorm_flow_sub_recover_le z hρ hρRp hq hl 0 c m
    (hsmooth hΦ) (hsmooth hΦ₀)
  simp only [zero_sub, zero_add, hlρ] at hrec
  apply hrec.trans_lt
  exact (mul_lt_mul_of_pos_left haux hA).trans_eq (mul_div_cancel₀ ε hA.ne')

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading
