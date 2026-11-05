module

public import JanetCartan.Analysis.ODE.TimeRescaling.Construction
public import JanetCartan.Analysis.ContDiff.Norm.Basic
public import JanetCartan.Analysis.ContDiff.Norm.Composition
public import JanetCartan.Analysis.ContDiff.Norm.Products
public import Mathlib.Analysis.Normed.Operator.Prod
public import JanetCartan.Geometry.IsometricEmbedding.Normal.Profile.SecondJet
public import JanetCartan.Geometry.IsometricEmbedding.Reference.StressFrame.LocalComposition.SmoothExtension

/-!
# Seminorm transfer for autonomous time augmentation

Zero-loss bounds for the construction in `app:ch_regular_base:lem:buffered-interpolation`.
The consumer is the joint autonomous-flow estimate for `app:lem:common-hamilton-phase`.
Constants are chosen before the variable field and initial section.
-/

@[expose] public noncomputable section

open scoped ContDiff Topology
open Set Metric

namespace JanetCartan.TimeRescaling

variable {D P E F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem cNorm_postLinear {s : Set D} (hs : IsCompact s) (n : ℕ)
    (L : E →L[ℝ] F) {f : D → E} (hf : ContDiff ℝ n f) :
    cNorm s n (L ∘ f) ≤ ‖L‖ * cNorm s n f := by
  simp only [cNorm, Finset.mul_sum]
  apply cNorm_le_sum_of_bounds
    (fun j _ ↦ mul_nonneg (norm_nonneg _) (sSup_norm_iteratedFDeriv_nonneg s j f))
  intro j hj x hx
  apply (L.norm_iteratedFDeriv_comp_left hf.contDiffAt (by exact_mod_cast hj)).trans
  exact mul_le_mul_of_nonneg_left
    (le_csSup (bddAbove_norm_iteratedFDeriv hs hf hj) (mem_image_of_mem _ hx)) (norm_nonneg _)

private theorem cNorm_preAffine {s : Set D} {t : Set E} (ht : IsCompact t) (n : ℕ)
    (L : D →L[ℝ] E) (b : E) {K : ℝ} (hK : 1 ≤ K) (hLK : ‖L‖ ≤ K)
    {f : E → F} (hf : ContDiff ℝ n f) (hst : MapsTo (fun x ↦ L x + b) s t) :
    cNorm s n (fun x ↦ f (L x + b)) ≤ K ^ n * cNorm t n f := by
  simp only [cNorm, Finset.mul_sum]
  apply cNorm_le_sum_of_bounds
    (fun j _ ↦ mul_nonneg (pow_nonneg (zero_le_one.trans hK) _)
      (sSup_norm_iteratedFDeriv_nonneg t j f))
  intro j hj x hx
  have hg : ContDiff ℝ n (fun y ↦ f (y + b)) := hf.comp (contDiff_id.add contDiff_const)
  change ‖iteratedFDeriv ℝ j ((fun y ↦ f (y + b)) ∘ L) x‖ ≤ _
  rw [L.iteratedFDeriv_comp_right hg x (by exact_mod_cast hj),
    iteratedFDeriv_comp_add_right]
  apply ((iteratedFDeriv ℝ j f (L x + b)).norm_compContinuousLinearMap_le (fun _ ↦ L)).trans
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hb := le_csSup (bddAbove_norm_iteratedFDeriv ht hf hj) (mem_image_of_mem _ (hst hx))
  have hk : ‖L‖ ^ j ≤ K ^ n := (pow_le_pow_left₀ (norm_nonneg _) hLK j).trans
    (pow_le_pow_right₀ hK hj)
  exact (mul_le_mul hb hk (pow_nonneg (norm_nonneg _) _)
    (sSup_norm_iteratedFDeriv_nonneg t j f)).trans_eq (mul_comm _ _)

private theorem cNorm_pair {s : Set D} (hs : IsCompact s) (n : ℕ)
    {f : D → E} {g : D → F} (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    cNorm s n (fun x ↦ (f x, g x)) ≤ cNorm s n f + cNorm s n g := by
  simp only [cNorm, ← Finset.sum_add_distrib]
  apply cNorm_le_sum_of_bounds
    (fun j _ ↦ add_nonneg (sSup_norm_iteratedFDeriv_nonneg s j f)
      (sSup_norm_iteratedFDeriv_nonneg s j g))
  intro j hj x hx
  rw [iteratedFDeriv_prodMk hf.contDiffAt hg.contDiffAt (by exact_mod_cast hj),
    ContinuousMultilinearMap.opNorm_prod]
  have hf' := le_csSup (bddAbove_norm_iteratedFDeriv hs hf hj) (mem_image_of_mem _ hx)
  have hg' := le_csSup (bddAbove_norm_iteratedFDeriv hs hg hj) (mem_image_of_mem _ hx)
  exact max_le (by linarith [sSup_norm_iteratedFDeriv_nonneg s j g])
    (by linarith [sSup_norm_iteratedFDeriv_nonneg s j f])

omit [NormedSpace ℝ E] in
private theorem fst_mapsTo_closedBall (w : E) (τ : ℝ) :
    MapsTo (fun x : E × ℝ ↦ x.1) (closedBall (w, 0) τ) (closedBall w τ) := by
  intro x hx
  exact (show dist x.1 w ≤ dist x (w, 0) by
    rw [Prod.dist_eq]; exact le_max_left _ _).trans hx

/-- `app:ch_regular_base:lem:buffered-interpolation`: the augmented vector field
has a zero-loss linear seminorm bound at every order, including order one.
Only smoothness on a buffered open neighborhood of the state ball is required. -/
theorem exists_cNorm_field_bound [FiniteDimensional ℝ E]
    (w : E) {τ : ℝ} (hτ : 0 < τ) (l c : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : E → E) (W : Set E), IsOpen W →
      closedBall w τ ⊆ W → ContDiffOn ℝ ∞ V W →
      cNorm (closedBall (w, 0) τ) n (field l c V) ≤
        C * (1 + cNorm (closedBall w τ) n V) := by
  let s := closedBall (w, (0 : ℝ)) τ
  let a : E × ℝ → ℝ := fun x ↦ l / c * x.2
  let A := (2 : ℝ) ^ n * cNorm s n a
  have hA : 0 ≤ A := mul_nonneg (by positivity) (cNorm_nonneg _ _ _)
  refine ⟨1 + A, by positivity, ?_⟩
  intro V W hW hball hV
  obtain ⟨f, hf, _, _, hfg⟩ :=
    ProjectedStressFrame.exists_contDiff_extension_eq_near_closedBall w hτ hW hball hV
  have hnorm := GeometricProfile.cNorm_eq_of_eventuallyEq hfg n
  have heq : cNorm s n (field l c f) = cNorm s n (field l c V) := by
    apply GeometricProfile.cNorm_eq_of_eventuallyEq
    intro x hx
    filter_upwards [(hfg x.1 (fst_mapsTo_closedBall w τ hx)).comp_tendsto
      continuous_fst.continuousAt] with y hy
    change f y.1 = V y.1 at hy
    simp only [field, hy]
  have hf' : ContDiff ℝ n f := hf.of_le (by simp)
  have hfst : cNorm s n (fun x : E × ℝ ↦ f x.1) ≤ cNorm (closedBall w τ) n f := by
    simpa using cNorm_preAffine (s := s) (isCompact_closedBall w τ) n
      (ContinuousLinearMap.fst ℝ E ℝ) 0 (le_refl 1)
      (ContinuousLinearMap.norm_fst_le ..) hf' (by simpa using fst_mapsTo_closedBall w τ)
  have ha : ContDiff ℝ n a := contDiff_const.mul contDiff_snd
  have hpair := cNorm_pair (isCompact_closedBall (w, (0 : ℝ)) τ) n
    (ha.smul (hf'.comp contDiff_fst)) (contDiff_const (c := (0 : ℝ)))
  have hprod := cNorm_smul_le (isCompact_closedBall (w, (0 : ℝ)) τ)
    ha (hf'.comp contDiff_fst)
  have hb : cNorm s n (field l c f) ≤ A * cNorm (closedBall w τ) n f := by
    calc
      _ ≤ cNorm s n (fun x ↦ a x • f x.1) := by
        change cNorm s n (field l c f) ≤ cNorm s n (fun x ↦ a x • f x.1) +
          cNorm s n (0 : E × ℝ → ℝ) at hpair
        simpa only [cNorm_zero, add_zero] using hpair
      _ ≤ A * cNorm s n (fun x : E × ℝ ↦ f x.1) := hprod
      _ ≤ _ := mul_le_mul_of_nonneg_left hfst hA
  rw [heq, hnorm] at hb
  exact hb.trans (by nlinarith [cNorm_nonneg (closedBall w τ) n V])

/-- `app:ch_regular_base:lem:buffered-interpolation`: the augmented initial section
has a zero-loss bound with constant fixed before the section, also at order one. -/
theorem exists_cNorm_sectionMap_bound [FiniteDimensional ℝ P]
    (z : P) {ρ : ℝ} (hρ : 0 < ρ) (c : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ : P → E) (U : Set P), IsOpen U →
      closedBall z ρ ⊆ U → ContDiffOn ℝ ∞ σ U →
      cNorm (closedBall (z, 0) ρ) n (sectionMap c σ) ≤
        C * (1 + cNorm (closedBall z ρ) n σ) := by
  let s := closedBall (z, (0 : ℝ)) ρ
  let a : P × ℝ → ℝ := fun x ↦ c * x.2
  let A := cNorm s n a
  have hA : 0 ≤ A := cNorm_nonneg _ _ _
  refine ⟨1 + A, by positivity, ?_⟩
  intro σ U hU hball hσ
  obtain ⟨f, hf, _, _, hfg⟩ :=
    ProjectedStressFrame.exists_contDiff_extension_eq_near_closedBall z hρ hU hball hσ
  have hnorm := GeometricProfile.cNorm_eq_of_eventuallyEq hfg n
  have heq : cNorm s n (sectionMap c f) = cNorm s n (sectionMap c σ) := by
    apply GeometricProfile.cNorm_eq_of_eventuallyEq
    intro x hx
    filter_upwards [(hfg x.1 (fst_mapsTo_closedBall z ρ hx)).comp_tendsto
      continuous_fst.continuousAt] with y hy
    change f y.1 = σ y.1 at hy
    simp only [sectionMap, hy]
  have hf' : ContDiff ℝ n f := hf.of_le (by simp)
  have hfst : cNorm s n (fun x : P × ℝ ↦ f x.1) ≤ cNorm (closedBall z ρ) n f := by
    simpa using cNorm_preAffine (s := s) (isCompact_closedBall z ρ) n
      (ContinuousLinearMap.fst ℝ P ℝ) 0 (le_refl 1)
      (ContinuousLinearMap.norm_fst_le ..) hf' (by simpa using fst_mapsTo_closedBall z ρ)
  have hb := cNorm_pair (isCompact_closedBall (z, (0 : ℝ)) ρ) n
    (hf'.comp contDiff_fst) (show ContDiff ℝ n a from contDiff_const.mul contDiff_snd)
  change cNorm s n (sectionMap c f) ≤ cNorm s n (fun x : P × ℝ ↦ f x.1) + A at hb
  have hb' := hb.trans (add_le_add hfst (le_refl A))
  rw [heq, hnorm] at hb'
  exact hb'.trans (by nlinarith [cNorm_nonneg (closedBall z ρ) n σ])

/-- `app:lem:common-hamilton-phase`: the affine parameter map for recovery at
auxiliary time one. -/
def pullback (t₀ l : ℝ) (p : P × ℝ) : P × ℝ := (p.1, (p.2 - t₀) / l)

/-- `app:ch_regular_base:lem:buffered-interpolation`: the recovery map is smooth. -/
theorem contDiff_pullback (t₀ l : ℝ) : ContDiff ℝ ∞ (pullback (P := P) t₀ l) :=
  contDiff_fst.prodMk ((contDiff_snd.sub contDiff_const).div_const l)

omit [NormedSpace ℝ P] in
/-- `app:lem:common-hamilton-phase`: the working space-time rectangle pulls
back into the augmented closed parameter ball. -/
theorem pullback_mapsTo {l : ℝ} (hl : 0 < l) (z : P) (ρ t₀ : ℝ) :
    MapsTo (pullback t₀ l) (closedBall z ρ ×ˢ Icc (t₀ - l * ρ) (t₀ + l * ρ))
      (closedBall (z, 0) ρ) := by
  intro p hp
  simp only [pullback, mem_closedBall, Prod.dist_eq, Real.dist_eq, sub_zero, max_le_iff]
  refine ⟨hp.1, ?_⟩
  rw [abs_div, abs_of_pos hl, div_le_iff₀ hl, abs_le]
  constructor <;> linarith [hp.2.1, hp.2.2]

/-- `app:ch_regular_base:lem:buffered-interpolation` and
`app:lem:common-hamilton-phase`: affine pullback and output projection cost no
derivatives. The explicit constant depends only on `n` and the time scale `l`.
The smooth map is arbitrary on an open neighborhood of the augmented ball. -/
theorem cNorm_pullback_fst_le [FiniteDimensional ℝ P]
    (z : P) {ρ l : ℝ} (hρ : 0 < ρ) (hl : 0 < l) (t₀ : ℝ) (n : ℕ)
    {U : Set (P × ℝ)} (hU : IsOpen U) (hball : closedBall (z, 0) ρ ⊆ U)
    {f : P × ℝ → E × ℝ} (hf : ContDiffOn ℝ ∞ f U) :
    cNorm (closedBall z ρ ×ˢ Icc (t₀ - l * ρ) (t₀ + l * ρ)) n
      (fun p ↦ (f (pullback t₀ l p)).1) ≤
        (max 1 |l⁻¹|) ^ n * cNorm (closedBall (z, 0) ρ) n f := by
  let s := closedBall z ρ ×ˢ Icc (t₀ - l * ρ) (t₀ + l * ρ)
  let t := closedBall (z, (0 : ℝ)) ρ
  let K := max 1 |l⁻¹|
  let L : (P × ℝ) →L[ℝ] (P × ℝ) :=
    (ContinuousLinearMap.fst ℝ P ℝ).prod (l⁻¹ • ContinuousLinearMap.snd ℝ P ℝ)
  let b : P × ℝ := (0, -t₀ / l)
  have hK : 1 ≤ K := le_max_left _ _
  have hLK : ‖L‖ ≤ K := by
    apply L.opNorm_le_bound (zero_le_one.trans hK)
    intro x
    change max ‖x.1‖ ‖l⁻¹ * x.2‖ ≤ K * ‖x‖
    apply max_le
    · exact (norm_fst_le x).trans (le_mul_of_one_le_left (norm_nonneg _) hK)
    · rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul (le_max_right _ _) (norm_snd_le x) (norm_nonneg _)
        (zero_le_one.trans hK)
  have hL : ∀ x, L x + b = pullback t₀ l x := by
    intro x
    ext <;> simp [L, b, pullback]
    ring
  obtain ⟨g, hg, _, _, hgf⟩ :=
    ProjectedStressFrame.exists_contDiff_extension_eq_near_closedBall (z, (0 : ℝ))
      hρ hU hball hf
  have hnorm := GeometricProfile.cNorm_eq_of_eventuallyEq hgf n
  have heq : cNorm s n (fun x ↦ (g (pullback t₀ l x)).1) =
      cNorm s n (fun x ↦ (f (pullback t₀ l x)).1) := by
    apply GeometricProfile.cNorm_eq_of_eventuallyEq
    intro x hx
    filter_upwards [(hgf _ (pullback_mapsTo hl z ρ t₀ hx)).comp_tendsto
      (contDiff_pullback t₀ l).continuous.continuousAt] with y hy
    exact congrArg Prod.fst hy
  have hg' : ContDiff ℝ n g := hg.of_le (by simp)
  have hpre := cNorm_preAffine (s := s) (t := t) (isCompact_closedBall (z, (0 : ℝ)) ρ)
    n L b hK hLK hg'.fst (by simpa only [hL] using pullback_mapsTo hl z ρ t₀)
  have hpost : cNorm t n (fun x ↦ (g x).1) ≤ cNorm t n g := by
    apply (cNorm_postLinear (isCompact_closedBall (z, (0 : ℝ)) ρ) n
      (ContinuousLinearMap.fst ℝ E ℝ) hg').trans
    exact (mul_le_mul_of_nonneg_right (ContinuousLinearMap.norm_fst_le ..)
      (cNorm_nonneg t n g)).trans_eq (one_mul _)
  simp only [hL] at hpre
  have hb := hpre.trans (mul_le_mul_of_nonneg_left hpost
    (pow_nonneg (zero_le_one.trans hK) _))
  rw [heq, hnorm] at hb
  exact hb

/-- `app:lem:common-hamilton-phase`: the original joint flow seminorm is bounded
by the spatial seminorm of the constructed augmented flow at auxiliary time one.
This is the direct consumer of the parent's spatial autonomous-flow estimate. -/
theorem cNorm_flow_recover_le [FiniteDimensional ℝ P]
    (z : P) {ρ R q l : ℝ} (hρ : 0 < ρ) (hρR : ρ < R) (hq : 1 < q)
    (hl : 0 < l) (t₀ c : ℝ) (n : ℕ) {Φ : P × ℝ → E}
    (hΦ : ContDiffOn ℝ ∞ Φ
      (ball z R ×ˢ Ioo (t₀ - l * q * R) (t₀ + l * q * R))) :
    cNorm (closedBall z ρ ×ˢ Icc (t₀ - l * ρ) (t₀ + l * ρ)) n Φ ≤
      (max 1 |l⁻¹|) ^ n *
        cNorm (closedBall (z, 0) ρ) n (fun p ↦ flow t₀ l c Φ (p, 1)) := by
  have hs : ContDiffOn ℝ ∞ (fun p ↦ flow t₀ l c Φ (p, 1)) (ball (z, 0) R) := by
    apply (contDiffOn_flow hl (zero_lt_one.trans hq) hΦ).comp
      (contDiffOn_id.prodMk contDiffOn_const)
    intro p hp
    exact ⟨hp, by constructor <;> linarith⟩
  have hb := cNorm_pullback_fst_le z hρ hl t₀ n isOpen_ball
    (closedBall_subset_ball hρR) hs
  simpa only [pullback, flow_recover t₀ c hl.ne' Φ] using hb

end JanetCartan.TimeRescaling
