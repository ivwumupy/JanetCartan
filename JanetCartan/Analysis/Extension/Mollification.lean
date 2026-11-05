module

public import JanetCartan.Analysis.ContDiff.Norm.Defs
public import JanetCartan.Analysis.Extension.Mollification.LpContraction
public import JanetCartan.Analysis.Extension.Mollification.WeakContraction

/-!
# Compactly supported mollification

Analytic ingredients for the density paragraph in the proof of
`app:ch_regular_base:lem:ball-extension` (Appendix B of `paper.tex`).
The mollifier is a normalized real bump and works for Banach-valued functions on
any finite-dimensional real normed space. All support radii are physical radii.

We prove compact support buffers, commutation with every finite classical derivative,
uniform approximation of finite jets, and quantitative Cᵐ and Lᵖ derivative-error
bounds. Contraction and a cutoff give smooth density for Cᵐ functions on a
closed ball, with uniform approximation of the intrinsic boundary derivatives
and support in any prescribed open neighborhood. For arbitrary L² data we prove
that normalized mollification is a contraction, converges in L², and gives smooth
L² density on closed balls with controlled support. Weak derivatives are defined
by integration by parts against compactly supported smooth tests. Mollification
commutes with every order of a weak jet wherever the translated kernel stays in
the weak domain. Contraction followed by mollification proves smooth density for
arbitrary weak Hᵐ data on a positive-radius ball, in every L² derivative norm,
with support in any prescribed open neighborhood of the closed ball. Agreement
of completed extension operators is a downstream application of these estimates.
-/

@[expose] public noncomputable section

open MeasureTheory Metric Set Function Filter ContinuousLinearMap
open scoped Convolution Topology ContDiff Pointwise ENNReal

namespace JanetCartan
namespace Mollification

universe u

variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (μ : Measure E) [μ.IsAddHaarMeasure]

/-- Appendix B, ball-extension density paragraph: normalized bump convolution. -/
def mollify (φ : ContDiffBump (0 : E)) (f : E → F) : E → F :=
  φ.normed μ ⋆[lsmul ℝ ℝ, μ] f

/-- Appendix B, ball-extension density paragraph: mollification is smooth. -/
theorem contDiff_mollify (φ : ContDiffBump (0 : E)) {f : E → F}
    (hf : LocallyIntegrable f μ) : ContDiff ℝ ∞ (mollify μ φ f) :=
  φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed hf

/-- Appendix B, ball-extension density paragraph: compact support is preserved. -/
theorem hasCompactSupport_mollify (φ : ContDiffBump (0 : E)) {f : E → F}
    (hf : HasCompactSupport f) : HasCompactSupport (mollify μ φ f) :=
  φ.hasCompactSupport_normed.convolution _ hf

/-- Appendix B, ball-extension density paragraph: the support grows by at most
 the outer radius of the bump. -/
theorem tsupport_mollify_subset (φ : ContDiffBump (0 : E)) {f : E → F}
    {K : Set E} (hK : IsCompact K) (hf : tsupport f ⊆ K) :
    tsupport (mollify μ φ f) ⊆ closedBall (0 : E) φ.rOut + K := by
  apply closure_minimal _ ((isCompact_closedBall _ _).add hK).isClosed
  exact (support_convolution_subset _).trans
    (add_subset_add (by rw [φ.support_normed_eq]; exact ball_subset_closedBall)
      ((subset_tsupport f).trans hf))

/-- Appendix B, ball-extension density paragraph: explicit support buffer for balls. -/
theorem tsupport_mollify_subset_closedBall (φ : ContDiffBump (0 : E)) {f : E → F}
    {c : E} {R : ℝ} (hf : tsupport f ⊆ closedBall c R) :
    tsupport (mollify μ φ f) ⊆ closedBall c (R + φ.rOut) := by
  intro x hx
  obtain ⟨y, hy, z, hz, rfl⟩ :=
    tsupport_mollify_subset μ φ (isCompact_closedBall c R) hf hx
  rw [mem_closedBall, dist_eq_norm] at *
  calc
    ‖y + z - c‖ = ‖y + (z - c)‖ := by rw [add_sub_assoc]
    _ ≤ ‖y‖ + ‖z - c‖ := norm_add_le _ _
    _ ≤ φ.rOut + R := add_le_add (by simpa using hy) hz
    _ = R + φ.rOut := add_comm _ _

/-- Appendix B, ball-extension density paragraph: a compact support inside an open
set admits one positive buffer for all sufficiently small mollifiers. -/
theorem exists_support_buffer {f : E → F} (hf : HasCompactSupport f)
    {V : Set E} (hV : IsOpen V) (hfV : tsupport f ⊆ V) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ φ : ContDiffBump (0 : E), φ.rOut ≤ δ →
      tsupport (mollify μ φ f) ⊆ V := by
  obtain ⟨δ, hδ, hδV⟩ := hf.isCompact.exists_cthickening_subset_open hV hfV
  refine ⟨δ, hδ, fun φ hφ x hx ↦ hδV ?_⟩
  obtain ⟨y, hy, z, hz, rfl⟩ := tsupport_mollify_subset μ φ hf.isCompact Subset.rfl hx
  apply mem_cthickening_of_dist_le _ z _ _ hz
  simpa using (mem_closedBall_zero_iff.mp hy).trans hφ

variable [CompleteSpace F]

/-- Appendix B, ball-extension density paragraph: the local modulus of continuity
bounds the mollification error with constant one. -/
theorem dist_mollify_le (φ : ContDiffBump (0 : E)) {f : E → F} {x : E} {ε : ℝ}
    (hf : AEStronglyMeasurable f μ)
    (hε : ∀ y ∈ ball x φ.rOut, dist (f y) (f x) ≤ ε) :
    dist (mollify μ φ f x) (f x) ≤ ε :=
  φ.dist_normed_convolution_le hf hε

omit [CompleteSpace F] in
/-- Appendix B, ball-extension density paragraph: first derivatives commute with
mollification for compactly supported C¹ functions. -/
theorem fderiv_mollify (φ : ContDiffBump (0 : E)) {f : E → F}
    (hc : HasCompactSupport f) (hf : ContDiff ℝ 1 f) :
    fderiv ℝ (mollify μ φ f) = mollify μ φ (fderiv ℝ f) := by
  ext x v
  exact congrArg (fun L : E →L[ℝ] F ↦ L v)
    (hc.hasFDerivAt_convolution_right (lsmul ℝ ℝ)
      (φ.contDiff_normed (n := 1)).continuous.locallyIntegrable hf x).fderiv

omit [BorelSpace E] [CompleteSpace F] [μ.IsAddHaarMeasure] in
/-- Appendix B, ball-extension density paragraph: mollification commutes with
continuous linear changes of the target, in particular the derivative currying maps. -/
theorem mollify_continuousLinearEquiv {G : Type u} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [CompleteSpace G] (L : F ≃L[ℝ] G)
    (φ : ContDiffBump (0 : E)) (f : E → F) :
    mollify μ φ (L ∘ f) = L ∘ mollify μ φ f := by
  ext x
  simp only [mollify, convolution, lsmul_apply, comp_apply]
  simp_rw [← L.map_smul]
  exact L.integral_comp_comm _

/-- Appendix B, ball-extension density paragraph: every finite derivative commutes
with mollification of a compactly supported Cⁿ function. -/
theorem iteratedFDeriv_mollify (φ : ContDiffBump (0 : E)) (n : ℕ) {f : E → F}
    (hc : HasCompactSupport f) (hf : ContDiff ℝ n f) :
    iteratedFDeriv ℝ n (mollify μ φ f) = mollify μ φ (iteratedFDeriv ℝ n f) := by
  induction n generalizing F with
  | zero =>
    rw [iteratedFDeriv_zero_eq_comp, iteratedFDeriv_zero_eq_comp]
    exact (mollify_continuousLinearEquiv μ
      (continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv φ f).symm
  | succ n ih =>
    have hf1 : ContDiff ℝ 1 f := hf.of_le (by exact_mod_cast Nat.succ_pos n)
    have hfd : ContDiff ℝ n (fderiv ℝ f) := hf.fderiv_right (by simp)
    funext x
    rw [iteratedFDeriv_succ_eq_comp_right, fderiv_mollify μ φ hc hf1,
      ih (hc.fderiv ℝ) hfd]
    have heq : iteratedFDeriv ℝ (n + 1) f =
        (continuousMultilinearCurryRightEquiv' ℝ n E F).symm ∘
          iteratedFDeriv ℝ n (fderiv ℝ f) := by
      funext y
      exact iteratedFDeriv_succ_eq_comp_right
    rw [heq]
    exact congrFun (mollify_continuousLinearEquiv
      (F := E [×n]→L[ℝ] (E →L[ℝ] F)) (G := E [×(n + 1)]→L[ℝ] F) μ
      (continuousMultilinearCurryRightEquiv' ℝ n E F).symm.toContinuousLinearEquiv
      φ (iteratedFDeriv ℝ n (fderiv ℝ f))).symm x


/-- Appendix B, ball-extension density paragraph: shrinking mollifiers converge
uniformly on each compact set for continuous input. -/
theorem tendstoUniformlyOn_mollify {ι : Type*} {l : Filter ι} {φ : ι → ContDiffBump (0 : E)}
    (hφ : Tendsto (fun i ↦ (φ i).rOut) l (𝓝 0)) {f : E → F}
    (hf : Continuous f) {K : Set E} (hK : IsCompact K) :
    TendstoUniformlyOn (fun i ↦ mollify μ (φ i) f) f l K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hu : UniformContinuousOn f (cthickening 1 K) :=
    hK.cthickening.uniformContinuousOn_of_continuous hf.continuousOn
  obtain ⟨δ, hδ, hδf⟩ := Metric.uniformContinuousOn_iff.mp hu (ε / 2) (half_pos hε)
  filter_upwards [hφ.eventually (gt_mem_nhds (lt_min one_pos hδ))] with i hi
  intro x hx
  rw [dist_comm]
  apply (dist_mollify_le μ (φ i) hf.aestronglyMeasurable ?_).trans_lt (half_lt_self hε)
  intro y hy
  have hy' : dist y x < min 1 δ := (mem_ball.mp hy).trans hi
  exact (hδf y (mem_cthickening_of_dist_le _ x _ _ hx (lt_min_iff.mp hy').1.le)
    x (self_subset_cthickening _ hx) (lt_min_iff.mp hy').2).le

/-- Appendix B, ball-extension density paragraph: uniform approximation of a
uniformly continuous field by shrinking mollifiers. -/
theorem tendstoUniformly_mollify {ι : Type*} {l : Filter ι} {φ : ι → ContDiffBump (0 : E)}
    (hφ : Tendsto (fun i ↦ (φ i).rOut) l (𝓝 0)) {f : E → F}
    (hf : UniformContinuous f) :
    TendstoUniformly (fun i ↦ mollify μ (φ i) f) f l := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδf⟩ := Metric.uniformContinuous_iff.mp hf (ε / 2) (half_pos hε)
  filter_upwards [hφ.eventually (gt_mem_nhds hδ)] with i hi x
  rw [dist_comm]
  apply (dist_mollify_le μ (φ i) hf.continuous.aestronglyMeasurable ?_).trans_lt
    (half_lt_self hε)
  intro y hy
  exact (hδf ((mem_ball.mp hy).trans hi)).le

/-- Appendix B, ball-extension density paragraph: uniform approximation of each
finite derivative of a compactly supported Cᵐ field. -/
theorem tendstoUniformly_iteratedFDeriv_mollify {ι : Type*} {l : Filter ι} {φ : ι → ContDiffBump (0 : E)}
    (hφ : Tendsto (fun i ↦ (φ i).rOut) l (𝓝 0)) {f : E → F} (m : ℕ)
    (hc : HasCompactSupport f) (hf : ContDiff ℝ m f) :
    TendstoUniformly (fun i ↦ iteratedFDeriv ℝ m (mollify μ (φ i) f))
      (iteratedFDeriv ℝ m f) l := by
  simp_rw [iteratedFDeriv_mollify μ _ m hc hf]
  exact tendstoUniformly_mollify μ hφ
    ((hc.iteratedFDeriv m).uniformContinuous_of_continuous hf.continuous_iteratedFDeriv')

include μ in
/-- Appendix B, ball-extension density paragraph: simultaneous uniform approximation
of the finite jet, preserving compact support inside the prescribed open set.
The input here is a whole-space compactly supported Cᵐ function. -/
theorem exists_contDiff_approx_jet {f : E → F} (m : ℕ) (hc : HasCompactSupport f) (hf : ContDiff ℝ m f)
    {V : Set E} (hV : IsOpen V) (hfV : tsupport f ⊆ V) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → F, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ tsupport g ⊆ V ∧
      ∀ j ≤ m, ∀ x, dist (iteratedFDeriv ℝ j g x) (iteratedFDeriv ℝ j f x) < ε := by
  let φ : ℕ → ContDiffBump (0 : E) := fun k ↦
    ⟨(1 / ((k : ℝ) + 1)) / 2, 1 / ((k : ℝ) + 1), by positivity,
      half_lt_self (by positivity)⟩
  have hφ : Tendsto (fun i ↦ (φ i).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨δ, hδ, hδV⟩ := exists_support_buffer μ hc hV hfV
  have he : ∀ᶠ i in atTop, ∀ j ∈ Finset.range (m + 1), ∀ x,
      dist (iteratedFDeriv ℝ j (mollify μ (φ i) f) x) (iteratedFDeriv ℝ j f x) < ε := by
    apply (eventually_all_finite (Finset.range (m + 1)).finite_toSet).mpr
    intro j hj
    have hjm : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hu := tendstoUniformly_iteratedFDeriv_mollify μ hφ j hc (hf.of_le (by exact_mod_cast hjm))
    simpa only [dist_comm] using Metric.tendstoUniformly_iff.mp hu ε hε
  obtain ⟨i, hiδ, hie⟩ := ((hφ.eventually (gt_mem_nhds hδ)).and he).exists
  refine ⟨mollify μ (φ i) f, contDiff_mollify μ _ hf.continuous.locallyIntegrable,
    hasCompactSupport_mollify μ _ hc, hδV _ hiδ.le, ?_⟩
  intro j hj x
  exact hie j (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)) x

/-- Appendix B, ball-extension density paragraph: the local modulus of the nth
derivative controls its mollification error without loss of derivatives. -/
theorem dist_iteratedFDeriv_mollify_le (φ : ContDiffBump (0 : E)) (n : ℕ) {f : E → F}
    (hc : HasCompactSupport f) (hf : ContDiff ℝ n f) {x : E} {ε : ℝ}
    (hε : ∀ y ∈ ball x φ.rOut,
      dist (iteratedFDeriv ℝ n f y) (iteratedFDeriv ℝ n f x) ≤ ε) :
    dist (iteratedFDeriv ℝ n (mollify μ φ f) x) (iteratedFDeriv ℝ n f x) ≤ ε := by
  rw [iteratedFDeriv_mollify μ φ n hc hf]
  exact dist_mollify_le μ φ hf.continuous_iteratedFDeriv'.aestronglyMeasurable hε

/-- Appendix B, ball-extension density paragraph: the project Cᵐ seminorm of the
error is bounded by the sum of the finite-jet moduli of continuity. -/
theorem cNorm_mollify_sub_le (φ : ContDiffBump (0 : E)) (m : ℕ) {f : E → F}
    (hc : HasCompactSupport f) (hf : ContDiff ℝ m f) {K : Set E} (hK : K.Nonempty)
    {ε : ℝ} (hε : ∀ j ≤ m, ∀ x ∈ K, ∀ y ∈ ball x φ.rOut,
      dist (iteratedFDeriv ℝ j f y) (iteratedFDeriv ℝ j f x) ≤ ε) :
    cNorm K m (mollify μ φ f - f) ≤ (m + 1) * ε := by
  unfold cNorm
  calc
    _ ≤ ∑ _j ∈ Finset.range (m + 1), ε := by
      apply Finset.sum_le_sum
      intro j hj
      have hjm : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      have hfj : ContDiff ℝ j f := hf.of_le (by exact_mod_cast hjm)
      apply csSup_le (hK.image _)
      rintro _ ⟨x, hx, rfl⟩
      change ‖iteratedFDeriv ℝ j (mollify μ φ f - f) x‖ ≤ ε
      rw [iteratedFDeriv_sub (contDiff_mollify μ φ hf.continuous.locallyIntegrable |>.of_le
        (by simp)) hfj, Pi.sub_apply, ← dist_eq_norm]
      exact dist_iteratedFDeriv_mollify_le μ φ j hc hfj (hε j hjm x hx)
    _ = (m + 1) * ε := by simp [Nat.cast_add, Nat.cast_one]

/-- Appendix B, ball-extension density paragraph: an Lᵖ bound for the error in
each classical derivative, with the explicit volume of the buffered support.
This is an estimate for Cⁿ input, not a weak-derivative density assertion. -/
theorem eLpNorm_iteratedFDeriv_mollify_sub_le (φ : ContDiffBump (0 : E)) (n : ℕ) {f : E → F}
    (hc : HasCompactSupport f) (hf : ContDiff ℝ n f) {p : ℝ≥0∞} (hp : p ≠ ⊤)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hmod : ∀ x y, y ∈ ball x φ.rOut →
      dist (iteratedFDeriv ℝ n f y) (iteratedFDeriv ℝ n f x) ≤ ε) :
    eLpNorm (iteratedFDeriv ℝ n (mollify μ φ f) - iteratedFDeriv ℝ n f) p μ ≤
      ENNReal.ofReal ε * μ (closedBall (0 : E) φ.rOut + tsupport f) ^ (1 / p.toReal) := by
  have hD : tsupport (iteratedFDeriv ℝ n f) ⊆ tsupport f := tsupport_iteratedFDeriv_subset n
  have hbuffer := (isCompact_closedBall (0 : E) φ.rOut).add hc.isCompact
  apply eLpNorm_sub_le_of_dist_bdd μ hp hbuffer.measurableSet.nullMeasurableSet hε
  · exact ((contDiff_mollify μ φ hf.continuous.locallyIntegrable).continuous_iteratedFDeriv
      (by simp) |>.sub hf.continuous_iteratedFDeriv').aestronglyMeasurable
  · intro x
    exact dist_iteratedFDeriv_mollify_le μ φ n hc hf (hmod x)
  · rw [iteratedFDeriv_mollify μ φ n hc hf]
    exact subset_tsupport _ |>.trans (tsupport_mollify_subset μ φ hc.isCompact hD)
  · intro x hx
    exact ⟨0, by simp [φ.rOut_pos.le], x, hD (subset_tsupport _ hx), zero_add x⟩

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
/-- Appendix B, `app:ch_regular_base:lem:ball-extension`: a Cᵐ function on
an open ball has a compactly supported Cᵐ representative agreeing with it on
a neighborhood of any smaller positive-radius closed ball. -/
theorem exists_compactlySupported_eq_near_closedBall {c : E} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) {f : E → F} {n : ℕ∞}
    (hf : ContDiffOn ℝ n f (ball c R)) :
    ∃ g : E → F, ContDiff ℝ n g ∧ HasCompactSupport g ∧
      tsupport g ⊆ ball c R ∧ ∀ x ∈ closedBall c r, g =ᶠ[𝓝 x] f := by
  obtain ⟨r₁, hr₁, hr₁R⟩ := exists_between hrR
  obtain ⟨r₂, hr₂, hr₂R⟩ := exists_between hr₁R
  let φ : ContDiffBump c := ⟨r₁, r₂, hr.trans hr₁, hr₂⟩
  have hφ : tsupport φ ⊆ ball c R := by
    rw [φ.tsupport_eq]
    exact closedBall_subset_ball hr₂R
  refine ⟨fun x ↦ φ x • f x, ?_, φ.hasCompactSupport.smul_right, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport φ
    · exact φ.contDiffAt.smul (hf.contDiffAt (isOpen_ball.mem_nhds (hφ hx)))
    · apply (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      simp [hy]
  · exact (tsupport_smul_subset_left φ f).trans hφ
  · intro x hx
    have hxφ : x ∈ ball c φ.rIn := (closedBall_subset_ball hr₁) hx
    filter_upwards [φ.eventuallyEq_one_of_mem_ball hxφ] with y hy
    simp [hy]

include μ in
/-- Appendix B, `app:ch_regular_base:lem:ball-extension`: smooth density in Cᵐ
on a positive-radius closed ball. All derivatives through order m are approximated
uniformly, including their intrinsic boundary values. The approximants have compact
support in the prescribed open neighborhood. Only Cᵐ regularity within the closed
ball is assumed; no pre-existing extension is needed. -/
theorem exists_contDiff_approx_jet_closedBall {c : E} {R : ℝ} (hR : 0 < R)
    {f : E → F} (m : ℕ) (hf : ContDiffOn ℝ m f (closedBall c R))
    {V : Set E} (hV : IsOpen V) (hRV : closedBall c R ⊆ V)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → F, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ tsupport g ⊆ V ∧
      ∀ j ≤ m, ∀ x ∈ closedBall c R,
        dist (iteratedFDeriv ℝ j g x)
          (iteratedFDerivWithin ℝ j f (closedBall c R) x) < ε := by
  have he : ∀ᶠ a in 𝓝[Ioo (0 : ℝ) 1] 1, ∀ j ∈ Finset.range (m + 1),
      ∀ x ∈ closedBall c R, dist (iteratedFDeriv ℝ j (f ∘ contract c a) x)
        (iteratedFDerivWithin ℝ j f (closedBall c R) x) < ε / 2 := by
    apply (eventually_all_finite (Finset.range (m + 1)).finite_toSet).mpr
    intro j hj
    have hjm : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hu := tendstoUniformlyOn_iteratedFDeriv_comp_contract hR j
      (hf.of_le (by exact_mod_cast hjm))
    simpa only [dist_comm] using Metric.tendstoUniformlyOn_iff.mp hu (ε / 2) (half_pos hε)
  have : (𝓝[Ioo (0 : ℝ) 1] 1).NeBot := by
    rw [nhdsWithin_Ioo_eq_nhdsLT (by norm_num : (0 : ℝ) < 1)]
    infer_instance
  obtain ⟨a, hea, ha⟩ := (he.and self_mem_nhdsWithin).exists
  have hRa : R < R / a := (lt_div_iff₀ ha.1).mpr (mul_lt_of_lt_one_right hR ha.2)
  obtain ⟨δ, hδ, hδV⟩ :=
    (isCompact_closedBall c R).exists_cthickening_subset_open hV hRV
  rw [cthickening_closedBall hδ.le hR.le, add_comm δ R] at hδV
  let S := min (R / a) (R + δ)
  have hRS : R < S := lt_min hRa (lt_add_of_pos_right R hδ)
  have hfS : ContDiffOn ℝ m (f ∘ contract c a) (ball c S) :=
    (contDiffOn_comp_contract ha.1 hf).mono (ball_subset_ball (min_le_left _ _))
  obtain ⟨u, hu, huc, huS, hueq⟩ := exists_compactlySupported_eq_near_closedBall hR hRS hfS
  have huV : tsupport u ⊆ V := huS.trans
    ((ball_subset_closedBall.trans (closedBall_subset_closedBall (min_le_right _ _))).trans hδV)
  obtain ⟨g, hg, hgc, hgV, hge⟩ := exists_contDiff_approx_jet μ m huc hu hV huV (half_pos hε)
  refine ⟨g, hg, hgc, hgV, fun j hj x hx ↦ ?_⟩
  have heq := ((hueq x hx).iteratedFDeriv ℝ j).eq_of_nhds
  calc
    dist (iteratedFDeriv ℝ j g x) (iteratedFDerivWithin ℝ j f (closedBall c R) x) ≤
        dist (iteratedFDeriv ℝ j g x) (iteratedFDeriv ℝ j u x) +
        dist (iteratedFDeriv ℝ j u x) (iteratedFDerivWithin ℝ j f (closedBall c R) x) :=
      dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hge j hj x)
      (heq ▸ hea j (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)) x hx)
    _ = ε := add_halves ε

omit [CompleteSpace F] [μ.IsAddHaarMeasure] in
/-- Appendix B, `app:ch_regular_base:lem:ball-extension`: a uniform error in
one classical derivative on a closed ball bounds its Lᵖ error by the explicit
volume factor. Combined with `exists_contDiff_approx_jet_closedBall`, this gives
simultaneous uniform and Lᵖ approximation for Cᵐ input; it does not assert density
for general weak-Sobolev input. -/
theorem eLpNorm_jet_sub_le_closedBall {c : E} {R : ℝ} (hR : 0 < R)
    {f g : E → F} (n : ℕ) (hf : ContDiffOn ℝ n f (closedBall c R))
    (hg : ContDiff ℝ n g) (p : ℝ≥0∞) {ε : ℝ}
    (hε : ∀ x ∈ closedBall c R,
      dist (iteratedFDeriv ℝ n g x) (iteratedFDerivWithin ℝ n f (closedBall c R) x) ≤ ε) :
    eLpNorm (iteratedFDeriv ℝ n g - iteratedFDerivWithin ℝ n f (closedBall c R))
      p (μ.restrict (closedBall c R)) ≤
      ENNReal.ofReal ε * μ (closedBall c R) ^ (1 / p.toReal) := by
  have hcont : ContinuousOn
      (iteratedFDeriv ℝ n g - iteratedFDerivWithin ℝ n f (closedBall c R)) (closedBall c R) :=
    hg.continuous_iteratedFDeriv'.continuousOn.sub
      (hf.continuousOn_iteratedFDerivWithin le_rfl (uniqueDiffOn_closedBall_of_pos c hR))
  have hmeas := hcont.aestronglyMeasurable_of_isCompact (isCompact_closedBall c R)
    measurableSet_closedBall (μ := μ)
  have hbound : ∀ᵐ x ∂μ.restrict (closedBall c R),
      ‖(iteratedFDeriv ℝ n g - iteratedFDerivWithin ℝ n f (closedBall c R)) x‖ ≤ ε := by
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
    simpa only [Pi.sub_apply, ← dist_eq_norm] using hε x hx
  simpa [Measure.restrict_apply_univ, one_div, mul_comm] using
    (eLpNorm_le_of_ae_bound (p := p) hmeas hbound)

omit [CompleteSpace F] in
/-- Appendix B, ball-extension density: normalized mollification contracts L²
for an arbitrary measurable representative of an L² function. -/
theorem eLpNorm_mollify_le (φ : ContDiffBump (0 : E)) {f : E → F}
    (hf : MemLp f 2 μ) : eLpNorm (mollify μ φ f) 2 μ ≤ eLpNorm f 2 μ := by
  have hconv : mollify μ φ (hf.toLp f) = mollify μ φ f :=
    convolution_congr (lsmul ℝ ℝ) Filter.EventuallyEq.rfl hf.coeFn_toLp
  rw [← hconv, ← eLpNorm_congr_ae hf.coeFn_toLp]
  exact eLpNorm_two_convolution_le μ φ (hf.toLp f)

omit [CompleteSpace F] in
/-- Appendix B, ball-extension density: mollification preserves L² membership. -/
theorem memLp_mollify (φ : ContDiffBump (0 : E)) {f : E → F}
    (hf : MemLp f 2 μ) : MemLp (mollify μ φ f) 2 μ :=
  (eLpNorm_mollify_le μ φ hf).trans_lt hf.eLpNorm_lt_top

/-- Appendix B, ball-extension density: mollification converges in L² for any
L² representative, including nonsmooth input. -/
theorem tendsto_eLpNorm_mollify_sub {ι : Type*} {l : Filter ι}
    {φ : ι → ContDiffBump (0 : E)}
    (hφ : Tendsto (fun i ↦ (φ i).rOut) l (𝓝 0)) {f : E → F} (hf : MemLp f 2 μ) :
    Tendsto (fun i ↦ eLpNorm (mollify μ (φ i) f - f) 2 μ) l (𝓝 0) := by
  have heq : ∀ i, eLpNorm (mollify μ (φ i) f - f) 2 μ =
      eLpNorm (mollify μ (φ i) (hf.toLp f) - (hf.toLp f : E → F)) 2 μ := by
    intro i
    rw [show mollify μ (φ i) (hf.toLp f) = mollify μ (φ i) f from
      convolution_congr (lsmul ℝ ℝ) Filter.EventuallyEq.rfl hf.coeFn_toLp]
    exact eLpNorm_congr_ae (Filter.EventuallyEq.rfl.sub hf.coeFn_toLp.symm)
  simp_rw [heq]
  exact tendsto_eLpNorm_two_convolution_sub μ hφ (hf.toLp f)

include μ in
/-- Appendix B, ball-extension density: a compactly supported L² function can be
approximated in L² by smooth functions whose compact supports stay inside any
prescribed open neighborhood of the original support. -/
theorem exists_contDiff_approx_L2 {f : E → F} (hf : MemLp f 2 μ)
    (hc : HasCompactSupport f) {V : Set E} (hV : IsOpen V) (hfV : tsupport f ⊆ V)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ g : E → F, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ tsupport g ⊆ V ∧
      eLpNorm (g - f) 2 μ < ε := by
  let φ : ℕ → ContDiffBump (0 : E) := fun k ↦
    ⟨(1 / ((k : ℝ) + 1)) / 2, 1 / ((k : ℝ) + 1), by positivity,
      half_lt_self (by positivity)⟩
  have hφ : Tendsto (fun i ↦ (φ i).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨δ, hδ, hδV⟩ := exists_support_buffer μ hc hV hfV
  obtain ⟨i, hiδ, hi⟩ := ((hφ.eventually (gt_mem_nhds hδ)).and
    ((tendsto_eLpNorm_mollify_sub μ hφ hf).eventually (gt_mem_nhds hε))).exists
  exact ⟨mollify μ (φ i) f, contDiff_mollify μ _ (hf.locallyIntegrable (by norm_num)),
    hasCompactSupport_mollify μ _ hc, hδV _ hiδ.le, hi⟩

include μ in
/-- Appendix B, `app:ch_regular_base:lem:ball-extension`: smooth L² density on
closed balls, with compact support in any prescribed open neighborhood. No
regularity of the input beyond L² on the ball is required. -/
theorem exists_contDiff_approx_L2_closedBall {c : E} {R : ℝ} {f : E → F}
    (hf : MemLp f 2 (μ.restrict (closedBall c R)))
    {V : Set E} (hV : IsOpen V) (hRV : closedBall c R ⊆ V)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ g : E → F, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ tsupport g ⊆ V ∧
      eLpNorm (g - f) 2 (μ.restrict (closedBall c R)) < ε := by
  let u := (closedBall c R).indicator f
  have hu : MemLp u 2 μ :=
    (memLp_indicator_iff_restrict measurableSet_closedBall.nullMeasurableSet).mpr hf
  have hs : tsupport u ⊆ closedBall c R := by
    apply closure_minimal _ isClosed_closedBall
    intro x hx
    by_contra hxS
    exact hx (by simp [u, hxS])
  have hc : HasCompactSupport u :=
    (isCompact_closedBall c R).of_isClosed_subset (isClosed_tsupport u) hs
  obtain ⟨g, hg, hgc, hgV, hge⟩ := exists_contDiff_approx_L2 μ hu hc hV (hs.trans hRV) hε
  refine ⟨g, hg, hgc, hgV, ?_⟩
  have heq : g - f =ᵐ[μ.restrict (closedBall c R)] g - u := by
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
    simp [u, hx]
  rw [eLpNorm_congr_ae heq]
  exact (eLpNorm_mono_measure _ Measure.restrict_le_self).trans_lt hge

omit [CompleteSpace F] in
/-- Appendix B, ball-extension density: weak and classical differentiation
commute with mollification when the closed kernel ball lies inside the domain. -/
theorem HasWeakFDerivOn.fderiv_mollify {f : E → F} {f' : E → E →L[ℝ] F}
    {U : Set E} (hw : HasWeakFDerivOn μ f f' U)
    (hf : LocallyIntegrable f μ) (hf' : LocallyIntegrable f' μ)
    (φ : ContDiffBump (0 : E)) (x : E) (hx : closedBall x φ.rOut ⊆ U) :
    fderiv ℝ (mollify μ φ f) x = mollify μ φ f' x := by
  apply hw.fderiv_convolution μ hf hf' φ.contDiff_normed φ.hasCompactSupport_normed x
  intro y hy
  have ht := tsupport_comp_subset_preimage (φ.normed μ)
    (continuous_const.sub continuous_id) hy
  rw [mem_preimage, φ.tsupport_normed_eq] at ht
  apply hx
  simpa [mem_closedBall, dist_eq_norm, norm_sub_rev] using ht

omit [CompleteSpace F] in
/-- Appendix B, ball-extension density: global weak derivatives commute with
mollification without any classical differentiability assumption on the input. -/
theorem HasWeakFDerivOn.fderiv_mollify_univ {f : E → F} {f' : E → E →L[ℝ] F}
    (hw : HasWeakFDerivOn μ f f' univ) (φ : ContDiffBump (0 : E)) :
    fderiv ℝ (mollify μ φ f) = mollify μ φ f' := by
  funext x
  exact hw.fderiv_mollify μ (locallyIntegrableOn_univ.mp hw.1)
    (locallyIntegrableOn_univ.mp hw.2.1) φ x (subset_univ _)

omit [CompleteSpace F] in
/-- Appendix B, ball-extension density: smoothing contracts the L² norm of a
weak first derivative, with constant one. -/
theorem HasWeakFDerivOn.eLpNorm_fderiv_mollify_le {f : E → F} {f' : E → E →L[ℝ] F}
    (hw : HasWeakFDerivOn μ f f' univ) (hf' : MemLp f' 2 μ)
    (φ : ContDiffBump (0 : E)) :
    eLpNorm (fderiv ℝ (mollify μ φ f)) 2 μ ≤ eLpNorm f' 2 μ := by
  rw [hw.fderiv_mollify_univ μ φ]
  exact eLpNorm_mollify_le μ φ hf'

/-- Appendix B, ball-extension density: the classical derivatives of the smooth
approximants converge in L² to the weak first derivative of the input. -/
theorem HasWeakFDerivOn.tendsto_eLpNorm_fderiv_mollify_sub {ι : Type*} {l : Filter ι}
    {φ : ι → ContDiffBump (0 : E)} (hφ : Tendsto (fun i ↦ (φ i).rOut) l (𝓝 0))
    {f : E → F} {f' : E → E →L[ℝ] F} (hw : HasWeakFDerivOn μ f f' univ)
    (hf' : MemLp f' 2 μ) :
    Tendsto (fun i ↦ eLpNorm (fderiv ℝ (mollify μ (φ i) f) - f') 2 μ) l (𝓝 0) := by
  simp_rw [hw.fderiv_mollify_univ μ]
  exact tendsto_eLpNorm_mollify_sub μ hφ hf'

include μ in
/-- Appendix B, ball-extension density: compactly supported H¹ data admit smooth
compactly supported approximants in both L² and the L² norm of the weak derivative.
The supports remain inside any prescribed open neighborhood of the original support. -/
theorem exists_contDiff_approx_weakH1 {f : E → F} {f' : E → E →L[ℝ] F}
    (hw : HasWeakFDerivOn μ f f' univ) (hf : MemLp f 2 μ) (hf' : MemLp f' 2 μ)
    (hc : HasCompactSupport f) {V : Set E} (hV : IsOpen V) (hfV : tsupport f ⊆ V)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ g : E → F, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ tsupport g ⊆ V ∧
      eLpNorm (g - f) 2 μ < ε ∧ eLpNorm (fderiv ℝ g - f') 2 μ < ε := by
  let φ : ℕ → ContDiffBump (0 : E) := fun k ↦
    ⟨(1 / ((k : ℝ) + 1)) / 2, 1 / ((k : ℝ) + 1), by positivity,
      half_lt_self (by positivity)⟩
  have hφ : Tendsto (fun i ↦ (φ i).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨δ, hδ, hδV⟩ := exists_support_buffer μ hc hV hfV
  have h₀ := (tendsto_eLpNorm_mollify_sub μ hφ hf).eventually (gt_mem_nhds hε)
  have h₁ := (hw.tendsto_eLpNorm_fderiv_mollify_sub μ hφ hf').eventually (gt_mem_nhds hε)
  obtain ⟨i, hiδ, hi₀, hi₁⟩ := ((hφ.eventually (gt_mem_nhds hδ)).and (h₀.and h₁)).exists
  exact ⟨mollify μ (φ i) f, contDiff_mollify μ _ (hf.locallyIntegrable (by norm_num)),
    hasCompactSupport_mollify μ _ hc, hδV _ hiδ.le, hi₀, hi₁⟩

/-- Appendix B, ball-extension density: every order of a global weak jet
commutes with mollification, producing the classical jet of the smooth function. -/
theorem HasWeakJetOn.iteratedFDeriv_mollify {f : E → F}
    {J : (j : ℕ) → E → E [×j]→L[ℝ] F} {m : ℕ}
    (hw : HasWeakJetOn μ f J univ m) (φ : ContDiffBump (0 : E))
    (j : ℕ) (hj : j ≤ m) :
    iteratedFDeriv ℝ j (mollify μ φ f) = mollify μ φ (J j) := by
  induction j with
  | zero =>
    rw [hw.1, iteratedFDeriv_zero_eq_comp, iteratedFDeriv_zero_eq_comp]
    exact (mollify_continuousLinearEquiv μ
      (continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv φ f).symm
  | succ j ih =>
    rw [iteratedFDeriv_succ_eq_comp_left, ih (by omega),
      (hw.2 j (by omega)).fderiv_mollify_univ μ φ]
    let L := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ E) F
    have h := mollify_continuousLinearEquiv (F := E →L[ℝ] E [×j]→L[ℝ] F)
      (G := E [×(j + 1)]→L[ℝ] F) μ L.symm.toContinuousLinearEquiv φ (L ∘ J (j + 1))
    simpa only [comp_def, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      LinearIsometryEquiv.symm_apply_apply] using h.symm

/-- Appendix B, ball-extension density: mollification contracts the L² norm
at every order of a global weak jet, with constant one. -/
theorem HasWeakJetOn.eLpNorm_iteratedFDeriv_mollify_le {f : E → F}
    {J : (j : ℕ) → E → E [×j]→L[ℝ] F} {m : ℕ}
    (hw : HasWeakJetOn μ f J univ m) (φ : ContDiffBump (0 : E))
    (j : ℕ) (hj : j ≤ m) (hJ : MemLp (J j) 2 μ) :
    eLpNorm (iteratedFDeriv ℝ j (mollify μ φ f)) 2 μ ≤ eLpNorm (J j) 2 μ := by
  rw [hw.iteratedFDeriv_mollify μ φ j hj]
  exact eLpNorm_mollify_le μ φ hJ

/-- Appendix B, ball-extension density: each weak derivative of L² class is
approximated in L² by the corresponding classical derivative of the mollification. -/
theorem HasWeakJetOn.tendsto_eLpNorm_iteratedFDeriv_mollify_sub
    {ι : Type*} {l : Filter ι} {φ : ι → ContDiffBump (0 : E)}
    (hφ : Tendsto (fun i ↦ (φ i).rOut) l (𝓝 0)) {f : E → F}
    {J : (j : ℕ) → E → E [×j]→L[ℝ] F} {m : ℕ}
    (hw : HasWeakJetOn μ f J univ m) (j : ℕ) (hj : j ≤ m) (hJ : MemLp (J j) 2 μ) :
    Tendsto (fun i ↦ eLpNorm (iteratedFDeriv ℝ j (mollify μ (φ i) f) - J j) 2 μ)
      l (𝓝 0) := by
  simp_rw [hw.iteratedFDeriv_mollify μ _ j hj]
  exact tendsto_eLpNorm_mollify_sub μ hφ hJ

include μ in
/-- Appendix B, ball-extension density: smooth compactly supported approximation
of every finite global weak Hᵐ jet. All derivatives through order m converge in
L², and the support lies in any prescribed open neighborhood of the input support. -/
theorem exists_contDiff_approx_weakJet {f : E → F}
    {J : (j : ℕ) → E → E [×j]→L[ℝ] F} {m : ℕ}
    (hw : HasWeakJetOn μ f J univ m) (hf : MemLp f 2 μ)
    (hJ : ∀ j ≤ m, MemLp (J j) 2 μ)
    (hc : HasCompactSupport f) {V : Set E} (hV : IsOpen V) (hfV : tsupport f ⊆ V)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ g : E → F, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ tsupport g ⊆ V ∧
      ∀ j ≤ m, eLpNorm (iteratedFDeriv ℝ j g - J j) 2 μ < ε := by
  let φ : ℕ → ContDiffBump (0 : E) := fun k ↦
    ⟨(1 / ((k : ℝ) + 1)) / 2, 1 / ((k : ℝ) + 1), by positivity,
      half_lt_self (by positivity)⟩
  have hφ : Tendsto (fun i ↦ (φ i).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨δ, hδ, hδV⟩ := exists_support_buffer μ hc hV hfV
  have he : ∀ᶠ i in atTop, ∀ j ∈ Finset.range (m + 1),
      eLpNorm (iteratedFDeriv ℝ j (mollify μ (φ i) f) - J j) 2 μ < ε := by
    apply (eventually_all_finite (Finset.range (m + 1)).finite_toSet).mpr
    intro j hj
    have hjm : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    exact (hw.tendsto_eLpNorm_iteratedFDeriv_mollify_sub μ hφ j hjm (hJ j hjm)).eventually
      (gt_mem_nhds hε)
  obtain ⟨i, hiδ, hi⟩ := ((hφ.eventually (gt_mem_nhds hδ)).and he).exists
  refine ⟨mollify μ (φ i) f, contDiff_mollify μ _ (hf.locallyIntegrable (by norm_num)),
    hasCompactSupport_mollify μ _ hc, hδV _ hiδ.le, fun j hj ↦ ?_⟩
  exact hi j (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))

/-- Appendix B, `app:ch_regular_base:lem:ball-extension`: each weak derivative
commutes with mollification on an open region whose translated closed kernel balls
lie inside the weak domain. The L² hypotheses provide global local integrability. -/
theorem HasWeakJetOn.iteratedFDeriv_mollify_on {f : E → F}
    {J : (j : ℕ) → E → E [×j]→L[ℝ] F} {m : ℕ} {U W : Set E}
    (hw : HasWeakJetOn μ f J U m) (hJ : ∀ j ≤ m, MemLp (J j) 2 μ)
    (φ : ContDiffBump (0 : E)) (hW : IsOpen W)
    (hWU : ∀ x ∈ W, closedBall x φ.rOut ⊆ U) (j : ℕ) (hj : j ≤ m) :
    EqOn (iteratedFDeriv ℝ j (mollify μ φ f)) (mollify μ φ (J j)) W := by
  induction j with
  | zero =>
    have heq : iteratedFDeriv ℝ 0 (mollify μ φ f) = mollify μ φ (J 0) := by
      rw [hw.1, iteratedFDeriv_zero_eq_comp, iteratedFDeriv_zero_eq_comp]
      exact (mollify_continuousLinearEquiv μ
        (continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv φ f).symm
    exact fun x _ ↦ congrFun heq x
  | succ j ih =>
    intro x hx
    have heq : iteratedFDeriv ℝ j (mollify μ φ f) =ᶠ[𝓝 x] mollify μ φ (J j) :=
      Filter.eventuallyEq_of_mem (hW.mem_nhds hx) (ih (by omega))
    let : NormedAddCommGroup (E →L[ℝ] E [×j]→L[ℝ] F) := inferInstance
    let L : (E [×(j + 1)]→L[ℝ] F) ≃ₗᵢ[ℝ] (E →L[ℝ] E [×j]→L[ℝ] F) :=
      continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ E) F
    have hL : MemLp (L ∘ J (j + 1)) 2 μ := by
      apply (hJ (j + 1) hj).of_le
        (L.continuous.comp_aestronglyMeasurable (hJ (j + 1) hj).aestronglyMeasurable)
      filter_upwards [] with y
      exact (L.norm_map (J (j + 1) y)).le
    have hd := (hw.2 j (by omega)).fderiv_mollify μ
      ((hJ j (by omega)).locallyIntegrable (by norm_num))
      (hL.locallyIntegrable (by norm_num)) φ x (hWU x hx)
    rw [iteratedFDeriv_succ_eq_comp_left]
    change L.symm (fderiv ℝ (iteratedFDeriv ℝ j (mollify μ φ f)) x) = _
    rw [heq.fderiv_eq, hd]
    have h := mollify_continuousLinearEquiv (F := E →L[ℝ] E [×j]→L[ℝ] F)
      (G := E [×(j + 1)]→L[ℝ] F) μ L.symm.toContinuousLinearEquiv φ (L ∘ J (j + 1))
    simpa only [comp_def, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      LinearIsometryEquiv.symm_apply_apply] using congrFun h.symm x

/-- Appendix B, `app:ch_regular_base:lem:ball-extension`: a weak jet on a larger
ball can be approximated in every L² derivative norm on a smaller closed ball.
Only local weak identities are needed; the globally L² representatives and the
compact support supply the convolutions and control their supports. -/
theorem exists_contDiff_approx_weakJet_bufferedBall {f : E → F}
    {J : (j : ℕ) → E → E [×j]→L[ℝ] F} {m : ℕ} {c : E} {R S : ℝ}
    (hRS : R < S) (hw : HasWeakJetOn μ f J (ball c S) m)
    (hf : MemLp f 2 μ) (hJ : ∀ j ≤ m, MemLp (J j) 2 μ)
    (hc : HasCompactSupport f) {V : Set E} (hV : IsOpen V) (hfV : tsupport f ⊆ V)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ g : E → F, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ tsupport g ⊆ V ∧
      ∀ j ≤ m, eLpNorm (iteratedFDeriv ℝ j g - J j) 2
        (μ.restrict (closedBall c R)) < ε := by
  let φ : ℕ → ContDiffBump (0 : E) := fun k ↦
    ⟨(1 / ((k : ℝ) + 1)) / 2, 1 / ((k : ℝ) + 1), by positivity,
      half_lt_self (by positivity)⟩
  have hφ : Tendsto (fun i ↦ (φ i).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨δ, hδ, hδV⟩ := exists_support_buffer μ hc hV hfV
  have he : ∀ᶠ i in atTop, ∀ j ∈ Finset.range (m + 1),
      eLpNorm (mollify μ (φ i) (J j) - J j) 2 μ < ε := by
    apply (eventually_all_finite (Finset.range (m + 1)).finite_toSet).mpr
    intro j hj
    exact (tendsto_eLpNorm_mollify_sub μ hφ
      (hJ j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))).eventually (gt_mem_nhds hε)
  obtain ⟨i, hiδ, hiS, hi⟩ := ((hφ.eventually (gt_mem_nhds hδ)).and
    ((hφ.eventually (gt_mem_nhds (sub_pos.mpr hRS))).and he)).exists
  refine ⟨mollify μ (φ i) f, contDiff_mollify μ _ (hf.locallyIntegrable (by norm_num)),
    hasCompactSupport_mollify μ _ hc, hδV _ hiδ.le, fun j hj ↦ ?_⟩
  have hd := hw.iteratedFDeriv_mollify_on μ hJ (φ i)
    (W := ball c (S - (φ i).rOut)) isOpen_ball (fun x hx y hy ↦ ?_) j hj
  · have heq : iteratedFDeriv ℝ j (mollify μ (φ i) f) - J j =ᵐ[μ.restrict (closedBall c R)]
        mollify μ (φ i) (J j) - J j := by
      filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
      simp only [Pi.sub_apply, hd ((closedBall_subset_ball (by linarith : R < S - (φ i).rOut)) hx)]
    rw [eLpNorm_congr_ae heq]
    exact (eLpNorm_mono_measure _ Measure.restrict_le_self).trans_lt
      (hi j (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)))
  · rw [mem_ball] at hx ⊢
    rw [mem_closedBall] at hy
    exact (dist_triangle y x c).trans_lt (by linarith)

/-- Appendix B, `app:ch_regular_base:lem:ball-extension`: smooth density for an
arbitrary finite weak Hᵐ jet on a positive-radius ball. All derivatives through
order m are approximated in L² on the closed ball, and the smooth approximant has
compact support in any prescribed open neighborhood. Contraction creates the
buffer needed for local mollification; no global weak extension is assumed. -/
theorem exists_contDiff_approx_weakJet_closedBall {f : E → F}
    {J : (j : ℕ) → E → E [×j]→L[ℝ] F} {m : ℕ} {c : E} {R : ℝ}
    (hR : 0 < R) (hw : HasWeakJetOn μ f J (ball c R) m)
    (hf : MemLp f 2 (μ.restrict (closedBall c R)))
    (hJ : ∀ j ≤ m, MemLp (J j) 2 (μ.restrict (closedBall c R)))
    {V : Set E} (hV : IsOpen V) (hRV : closedBall c R ⊆ V)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ g : E → F, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ tsupport g ⊆ V ∧
      ∀ j ≤ m, eLpNorm (iteratedFDeriv ℝ j g - J j) 2
        (μ.restrict (closedBall c R)) < ε := by
  obtain ⟨η, hη, hηε⟩ := ENNReal.exists_nnreal_pos_mul_lt
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hε.ne'
  have hη' : (0 : ℝ≥0∞) < η := ENNReal.coe_pos.mpr hη
  obtain ⟨δ, hδ, hδV⟩ :=
    (isCompact_closedBall c R).exists_cthickening_subset_open hV hRV
  rw [cthickening_closedBall hδ.le hR.le, add_comm δ R] at hδV
  have he : ∀ᶠ a in 𝓝[Ioo (0 : ℝ) 1] 1, ∀ j ∈ Finset.range (m + 1),
      eLpNorm (fun x ↦ a ^ j • J j (contract c a x) - J j x) 2
        (μ.restrict (closedBall c R)) < η := by
    apply (eventually_all_finite (Finset.range (m + 1)).finite_toSet).mpr
    intro j hj
    exact (tendsto_eLpNorm_two_scaled_comp_contract_sub μ
      (hJ j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))) hR j).eventually
        (gt_mem_nhds hη')
  have hdiv : Tendsto (fun a : ℝ ↦ R / a) (𝓝[Ioo (0 : ℝ) 1] 1) (𝓝 R) := by
    have ht : ContinuousAt (fun a : ℝ ↦ R / a) 1 := by fun_prop (disch := norm_num)
    simpa only [div_one] using ht.tendsto.mono_left nhdsWithin_le_nhds
  have : (𝓝[Ioo (0 : ℝ) 1] 1).NeBot := by
    rw [nhdsWithin_Ioo_eq_nhdsLT (by norm_num : (0 : ℝ) < 1)]
    infer_instance
  obtain ⟨a, hea, haS, ha⟩ := (he.and
    ((hdiv.eventually (gt_mem_nhds (lt_add_of_pos_right R hδ))).and
      self_mem_nhdsWithin)).exists
  let u : E → F := (closedBall c R).indicator f ∘ contract c a
  let K : (j : ℕ) → E → E [×j]→L[ℝ] F :=
    fun j x ↦ a ^ j • (closedBall c R).indicator (J j) (contract c a x)
  have hpre : contract c a ⁻¹' ball c R = ball c (R / a) := by
    ext x
    simp only [mem_preimage, mem_ball, dist_contract_center, abs_of_pos ha.1]
    rw [lt_div_iff₀ ha.1, mul_comm]
  have hwu : HasWeakJetOn μ u K (ball c (R / a)) m := by
    simpa only [hpre] using (hw.indicator_closedBall.comp_contract isOpen_ball c ha.1)
  have hu : MemLp u 2 μ := memLp_comp_contract μ
    ((memLp_indicator_iff_restrict measurableSet_closedBall.nullMeasurableSet).mpr hf) c ha.1
  have hK (j : ℕ) (hj : j ≤ m) : MemLp (K j) 2 μ :=
    (memLp_comp_contract μ
      ((memLp_indicator_iff_restrict measurableSet_closedBall.nullMeasurableSet).mpr (hJ j hj))
      c ha.1).const_smul (a ^ j)
  have hs : tsupport u ⊆ closedBall c (R / a) :=
    tsupport_comp_contract_subset_closedBall support_indicator_subset ha.1
  have hc : HasCompactSupport u :=
    (isCompact_closedBall c (R / a)).of_isClosed_subset (isClosed_tsupport u) hs
  have hRa : R < R / a := (lt_div_iff₀ ha.1).mpr (mul_lt_of_lt_one_right hR ha.2)
  obtain ⟨g, hg, hgc, hgV, hge⟩ := exists_contDiff_approx_weakJet_bufferedBall μ
    hRa hwu hu hK hc hV (hs.trans ((closedBall_subset_closedBall haS.le).trans hδV)) hη'
  refine ⟨g, hg, hgc, hgV, fun j hj ↦ ?_⟩
  have hKeq : K j - J j =ᵐ[μ.restrict (closedBall c R)]
      (fun x ↦ a ^ j • J j (contract c a x) - J j x) := by
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
    simp [K, contract_mem_closedBall ⟨ha.1.le, ha.2.le⟩ hx]
  calc
    _ = eLpNorm ((iteratedFDeriv ℝ j g - K j) + (K j - J j)) 2
        (μ.restrict (closedBall c R)) := by rw [sub_add_sub_cancel]
    _ ≤ eLpNorm (iteratedFDeriv ℝ j g - K j) 2 (μ.restrict (closedBall c R)) +
        eLpNorm (K j - J j) 2 (μ.restrict (closedBall c R)) :=
      eLpNorm_add_le (μ := μ.restrict (closedBall c R)) (p := 2)
          (f := iteratedFDeriv ℝ j g - K j) (g := K j - J j) (by norm_num)
    _ ≤ (η : ℝ≥0∞) + η := add_le_add (hge j hj).le (by
      rw [eLpNorm_congr_ae hKeq]
      exact (hea j (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))).le)
    _ < ε := by simpa only [mul_two] using hηε

end Mollification
end JanetCartan
