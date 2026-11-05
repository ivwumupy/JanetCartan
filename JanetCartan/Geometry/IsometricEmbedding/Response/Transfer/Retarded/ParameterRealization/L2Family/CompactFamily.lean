module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Retarded.ParameterRealization.ClassicalFields
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Smooth families in the uniform norm on a compact set

The uniform mean-value argument used by the Lebesgue-L2 parameter lifting in
`app:ch_response:thm:response-literal-transfer`.
-/

open Set Filter
open scoped Topology ContDiff
@[expose] public noncomputable section
namespace JanetCartan.ResponseTransfer.ParameterRealization.L2Family

variable {P F Y : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace Y] [CompactSpace Y]
/-- Curry a continuous field of linear maps, with its uniform operator bound.
Used by the parameter lifting in `app:ch_response:thm:response-literal-transfer`. -/
def compactLinearFlip : C(Y, P →L[ℝ] F) →L[ℝ] P →L[ℝ] C(Y, F) :=
  LinearMap.mkContinuous
    { toFun := fun (f : C(Y, P →L[ℝ] F)) ↦ LinearMap.mkContinuous
        { toFun := fun (v : P) ↦ (⟨fun y ↦ f y v, f.continuous.clm_apply continuous_const⟩ : C(Y, F))
          map_add' := by intros; ext; simp
          map_smul' := by intros; ext; simp }
        ‖f‖ (fun v ↦ (ContinuousMap.norm_le _ (by positivity)).mpr fun y ↦
          (f y).le_opNorm v |>.trans (mul_le_mul_of_nonneg_right
            (ContinuousMap.norm_coe_le_norm f y) (norm_nonneg v)))
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
    1 (fun f ↦ by
      simp only [one_mul]
      apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f)
      intro v
      exact (ContinuousMap.norm_le _ (by positivity)).mpr fun y ↦
        (f y).le_opNorm v |>.trans (mul_le_mul_of_nonneg_right
          (ContinuousMap.norm_coe_le_norm f y) (norm_nonneg v)))

/-- Uniform continuity of the derivative and the mean-value inequality yield
norm differentiability (`app:ch_response:thm:response-literal-transfer`). -/
lemma hasFDerivAt_of_pointwise {U : Set P} (hU : IsOpen U) {f : P → C(Y, F)}
    {df : P → C(Y, P →L[ℝ] F)} (hd : ContinuousOn df U)
    (hf : ∀ c ∈ U, ∀ y, HasFDerivAt (fun a ↦ f a y) (df c y) c)
    {c : P} (hc : c ∈ U) : HasFDerivAt f (compactLinearFlip (df c)) c := by
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  have he : ∀ᶠ a in 𝓝 c, ‖df a - df c‖ < ε := by
    have ht1 : ContinuousAt df c := hd.continuousAt (hU.mem_nhds hc)
    have ht2 : ContinuousAt (fun a ↦ df a - df c) c := ht1.sub continuousAt_const
    have ht : ContinuousAt (fun a ↦ ‖df a - df c‖) c :=
      ContinuousAt.norm (E := C(Y, P →L[ℝ] F)) ht2
    have hh : ‖df c - df c‖ < ε := by
      simpa only [sub_self, @norm_zero C(Y, P →L[ℝ] F) _] using hε
    exact ht (gt_mem_nhds hh)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem (hU.mem_nhds hc) he)
  filter_upwards [Metric.ball_mem_nhds c hr] with a ha
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro y
  change ‖f a y - f c y - df c y (a - c)‖ ≤ ε * ‖a-c‖
  apply Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (f := fun b ↦ f b y) (f' := fun b ↦ df b y) (φ := df c y)
    (x := c) (y := a) (C := ε) (s := Metric.ball c r)
  · intro b hb
    exact (hf b (hball hb).1 y).hasFDerivWithinAt
  · intro b hb
    exact (ContinuousMap.norm_coe_le_norm (df b - df c) y).trans (hball hb).2.le
  · exact convex_ball c r
  · exact Metric.mem_ball_self hr
  · exact ha

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {K : Set X} [CompactSpace K]
/-- Restrict a classical family to a compact set; use zero when the slice is
not continuous. Only its values on the open parameter domain are used in
`app:ch_response:thm:response-literal-transfer`. -/
def compactFamily (g : P → X → F) : P → C(K, F) :=
  fun c ↦ ContinuousMap.mkD (fun x : K ↦ g c x) 0


omit [CompactSpace K] in
/-- The restriction agrees pointwise on the smooth parameter domain
(`app:ch_response:thm:response-literal-transfer`). -/
lemma compactFamily_apply {U : Set P} {g : P → X → F}
    (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (U ×ˢ univ))
    {c : P} (hc : c ∈ U) (x : K) : compactFamily g c x = g c x := by
  apply ContinuousMap.mkD_apply_of_continuous
  exact (hg.continuousOn.comp_continuous (continuous_const.prodMk continuous_subtype_val)
    (fun _ ↦ ⟨hc, mem_univ _⟩))


omit [CompactSpace K] in
/-- Joint continuity yields uniform continuity in the parameter on the compact
spatial set (`app:ch_response:thm:response-literal-transfer`). -/
lemma compactFamily_continuousOn {U : Set P} {g : P → X → F}
    (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (U ×ˢ univ)) :
    ContinuousOn (compactFamily (K := K) g) U := by
  apply ContinuousMap.continuousOn_mkD_of_uncurry
  exact hg.continuousOn.comp (continuous_id.prodMap continuous_subtype_val).continuousOn
    (fun z hz ↦ ⟨hz.1, mem_univ _⟩)

/-- Joint smoothness of the first parameter differential, used in the induction
for `app:ch_response:thm:response-literal-transfer`. -/
lemma contDiffOn_parameterFDeriv {U : Set P} (hU : IsOpen U) {g : P → X → F}
    (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (U ×ˢ univ)) :
    ContDiffOn ℝ ∞ (fun z : P × X ↦ fderiv ℝ (fun a ↦ g a z.2) z.1)
      (U ×ˢ univ) := by
  intro z hz
  have hh : ContDiffAt ℝ ∞ (fun w : (P × X) × P ↦ g w.2 w.1.2) (z, z.1) :=
    (hg.contDiffAt ((hU.prod isOpen_univ).mem_nhds hz)).comp (z, z.1)
      (contDiffAt_snd.prodMk (contDiffAt_snd.comp (z, z.1) contDiffAt_fst))
  exact (hh.fderiv (f := fun (w : P × X) a ↦ g a w.2) (g := Prod.fst)
    contDiffAt_fst (m := ∞) (by simp)).contDiffWithinAt

/-- The compact restriction has the actual pointwise parameter differential
as its norm derivative (`app:ch_response:thm:response-literal-transfer`). -/
lemma compactFamily_hasFDerivAt {U : Set P} (hU : IsOpen U) {g : P → X → F}
    (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (U ×ˢ univ))
    {c : P} (hc : c ∈ U) :
    HasFDerivAt (compactFamily (K := K) g)
      (compactLinearFlip (compactFamily (fun a x ↦ fderiv ℝ (fun b ↦ g b x) a) c)) c := by
  apply hasFDerivAt_of_pointwise hU (compactFamily_continuousOn (contDiffOn_parameterFDeriv hU hg)) _ hc
  intro a ha x
  rw [compactFamily_apply (contDiffOn_parameterFDeriv hU hg) ha]
  have ht : ContDiffAt ℝ ∞ (fun b ↦ g b x) a :=
    (hg.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨ha, mem_univ _⟩)).comp a
      (contDiffAt_id.prodMk contDiffAt_const)
  apply ht.differentiableAt (by simp) |>.hasFDerivAt.congr_of_eventuallyEq
  filter_upwards [hU.mem_nhds ha] with b hb
  exact compactFamily_apply hg hb x

/-- Every finite order of smoothness holds in the uniform norm. This discharges
the norm differentiability input of the L2 lifting for
`app:ch_response:thm:response-literal-transfer`. -/
lemma compactFamily_contDiffAt (n : ℕ) {U : Set P} (hU : IsOpen U)
    {g : P → X → F} (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (U ×ˢ univ))
    {c : P} (hc : c ∈ U) : ContDiffAt ℝ n (compactFamily (K := K) g) c := by
  induction n generalizing F with
  | zero => exact contDiffAt_zero.mpr ⟨U, hU.mem_nhds hc, compactFamily_continuousOn hg⟩
  | succ n ih =>
    apply contDiffAt_succ_iff_hasFDerivAt.mpr
    refine ⟨fun a ↦ compactLinearFlip (compactFamily (fun b x ↦ fderiv ℝ (fun e ↦ g e x) b) a),
      ⟨U, hU.mem_nhds hc, fun a ha ↦ compactFamily_hasFDerivAt hU hg ha⟩, ?_⟩
    exact (compactLinearFlip (P := P) (Y := K) (F := F)).contDiff.contDiffAt.comp c
      (ih (F := P →L[ℝ] F) (g := fun a x ↦ fderiv ℝ (fun b ↦ g b x) a)
        (contDiffOn_parameterFDeriv hU hg))

end JanetCartan.ResponseTransfer.ParameterRealization.L2Family
