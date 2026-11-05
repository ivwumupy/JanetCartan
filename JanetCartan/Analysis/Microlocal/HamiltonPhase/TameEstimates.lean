module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.SectionJetBounds
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.FlowJetBounds
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.InverseJetBounds
/-!
# One-high Hamilton phase estimates from scalar-symbol bounds

For `app:lem:common-hamilton-phase`, combine the proved implicit-root, joint
ODE, and inverse estimates on the same root, Hamilton flow, and projection
chart. The scalar symbol is used through order `n + 1`, with constants fixed
before the symbol, root, flow, and chart. No high root, flow, or inverse norm
is assumed. The remaining geometric inputs are the transverse cylinder, state
containment, source/target buffers, and normalized projection gap; the common
family construction must still instantiate them on compatible charts.

The order `n + 1` is separate from the larger combined derivative reserve:
a scalar-symbol bound at coefficient order `k + 2` therefore gives the phase
bound at coefficient order `n + 3`, as required by `FullPhaseCharts`.
-/

@[expose] public noncomputable section

open Set Metric Filter
open scoped ContDiff InnerProductSpace Topology
namespace JanetCartan.HamiltonPhase
variable {E U : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]

local instance tameEstimatesNormedSpaceE : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance tameEstimatesNormedSpaceU : NormedSpace ℝ U := InnerProductSpace.toNormedSpace

/-- Each Hamilton-field jet costs one scalar-symbol derivative
(`app:lem:common-hamilton-phase`). The consumer is the joint flow estimate. -/
theorem norm_iteratedFDeriv_vectorField_le
    (H : HomogeneousSymbol E) {D : Set (E × E)} (hD : IsOpen D)
    (hDH : D ⊆ H.domain) {n : ℕ} (hH : ContDiffOn ℝ (n + 1) H.h D)
    {z : E × E} (hz : z ∈ D) :
    ‖iteratedFDeriv ℝ n H.vectorField z‖ ≤ ‖iteratedFDeriv ℝ (n + 1) H.h z‖ := by
  have he : H.vectorField =ᶠ[𝓝 z] hamiltonFieldOfDifferential ∘ fderiv ℝ H.h := by
    filter_upwards [hD.mem_nhds hz] with w hw
    exact H.vectorField_eq_differential (hDH hw)
  rw [(he.iteratedFDeriv ℝ n).eq_of_nhds]
  have hd : ContDiffAt ℝ n (fderiv ℝ H.h) z :=
    (hH.fderiv_of_isOpen hD (by simp)).contDiffAt (hD.mem_nhds hz)
  calc
    _ ≤ ‖hamiltonFieldOfDifferential (E := E)‖ *
        ‖iteratedFDeriv ℝ n (fderiv ℝ H.h) z‖ :=
      (hamiltonFieldOfDifferential (E := E)).norm_iteratedFDeriv_comp_left hd le_rfl
    _ ≤ 1 * ‖iteratedFDeriv ℝ n (fderiv ℝ H.h) z‖ :=
      mul_le_mul_of_nonneg_right norm_hamiltonFieldOfDifferential_le (norm_nonneg _)
    _ = _ := by rw [one_mul, norm_iteratedFDeriv_fderiv]

/-- The scalar-symbol budget for the actual Hamilton field, with precisely
one derivative of loss (`app:lem:common-hamilton-phase`). -/
theorem cNorm_vectorField_le
    (H : HomogeneousSymbol E) {D K : Set (E × E)} (hD : IsOpen D)
    (hDH : D ⊆ H.domain) (hK : IsCompact K) (hKD : K ⊆ D)
    (n : ℕ) (hH : ContDiffOn ℝ (n + 1) H.h D) :
    cNorm K n H.vectorField ≤ (n + 1 : ℝ) * cNorm K (n + 1) H.h := by
  apply (cNorm_le_sum_of_bounds (C := fun _ ↦ cNorm K (n + 1) H.h)
    (fun _ _ ↦ cNorm_nonneg _ _ _) ?_).trans_eq (by simp)
  intro k hk z hz
  have hkn : (k + 1 : ℕ∞ω) ≤ n + 1 := by exact_mod_cast Nat.add_le_add_right hk 1
  exact (norm_iteratedFDeriv_vectorField_le H hD hDH (hH.of_le hkn) (hKD hz)).trans
    (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
      (fun z hz ↦ hH.contDiffAt (hD.mem_nhds (hKD hz))) hz (Nat.add_le_add_right hk 1))

/-- One-high joint time/parameter bounds for an actual root-initialized
Hamilton flow (`app:lem:common-hamilton-phase`). The implicit root's derivatives
and its low budget are derived from its energy equation and transverse gap.
The constant precedes the varying symbol, root and flow. The parent supplies
only the actual root, domain containment and fixed scalar `C²` budget. -/
theorem exists_hamiltonFlow_state_cNorm_bound
    (j : U →ₗᵢ[ℝ] E) (ν : E) (s₀ : InitialData U) (τ₀ : ℝ) (w : E × E)
    {r a c R M : ℝ} (hr : 0 < r) (ha : 0 < a) (hc : 0 < c) (hR : 0 < R)
    (hM : 0 ≤ M) {D : Set (E × E)} (hD : IsOpen D)
    (hRD : closedBall w R ⊆ D)
    (hmap : MapsTo (transverseSectionState j ν)
      (closedBall s₀ (2 * r) ×ˢ Icc (τ₀ - a) (τ₀ + a)) (closedBall w R)) (n : ℕ) :
    ∃ B > (0 : ℝ), ∀ (H : HomogeneousSymbol E) (g : InitialData U → ℝ)
      (Φ : HamiltonFlow H U),
      D ⊆ H.domain → ContDiffOn ℝ ∞ H.h D → cNorm (closedBall w R) 2 H.h ≤ M →
      ContDiffOn ℝ ∞ g (ball s₀ (2 * r)) →
      (∀ s ∈ ball s₀ (2 * r), g s ∈ Icc (τ₀ - a) (τ₀ + a) ∧
        H.h (transverseSectionState j ν (s, g s)) = s.2.1 ∧
        c ≤ |⟪H.hp (transverseSectionState j ν (s, g s)), ν⟫_ℝ|) →
      ball s₀ (2 * r) ⊆ Φ.parameters → Ioo (-(4 * r)) (4 * r) ⊆ Φ.time →
      ContDiffOn ℝ ∞ Φ.position (Φ.time ×ˢ Φ.parameters) →
      ContDiffOn ℝ ∞ Φ.momentum (Φ.time ×ˢ Φ.parameters) →
      (∀ s ∈ ball s₀ (2 * r),
        (Φ.position (0, s), Φ.momentum (0, s)) = transverseSectionState j ν (s, g s)) →
      (∀ s ∈ closedBall s₀ r, ∀ t ∈ Ioo (-(4 * r)) (4 * r),
        (Φ.position (t, s), Φ.momentum (t, s)) ∈ closedBall w R) →
      cNorm (closedBall s₀ r ×ˢ Icc (-r) r) n
        (fun q ↦ (Φ.position (q.2, q.1), Φ.momentum (q.2, q.1))) ≤
          B * (1 + cNorm (closedBall w R) (n + 1) H.h) := by
  have hK := isCompact_closedBall w R
  obtain ⟨A₁, hA₁, hroot₁⟩ := exists_sectionRoot_and_state_cNorm_bound_all
    j ν s₀ τ₀ hr ha hc hM hD hK hRD hmap 1
  obtain ⟨A, hA, hrootn⟩ := exists_sectionRoot_and_state_cNorm_bound_all
    j ν s₀ τ₀ hr ha hc hM hD hK hRD hmap n
  obtain ⟨B, hB, hflow⟩ := exists_autonomousFlow_joint_cNorm_bound
    s₀ w hr (by linarith : r < 2 * r) hR (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (1 : ℝ) < 2) hD hRD 0
    (by positivity : 0 ≤ 2 * M) (by positivity : 0 ≤ A₁ * (1 + M)) n
  refine ⟨B * (1 + (n + 1 : ℝ) + A), by positivity, ?_⟩
  intro H g Φ hDH hH hlow hg hroot hparams htime hx hp hinit hrange
  have hlow₁ := (cNorm_mono_order (by norm_num : 1 ≤ 2)).trans hlow
  have hsmooth : ContDiffOn ℝ ∞ (fun s ↦ transverseSectionState j ν (s, g s))
      (ball s₀ (2 * r)) :=
    (contDiff_transverseSectionState j ν).comp_contDiffOn (contDiffOn_id.prodMk hg)
  have hstate₁ := hroot₁ H g hDH hH hlow₁ hg hroot
  have hstaten := hrootn H g hDH hH hlow₁ hg hroot
  have hfield₁ := cNorm_vectorField_le H hD hDH hK hRD 1 (hH.of_le (by simp))
  have hfieldn := cNorm_vectorField_le H hD hDH hK hRD n (hH.of_le (by simp))
  have hswap : ContDiffOn ℝ ∞
      (fun q : InitialData U × ℝ ↦ (Φ.position (q.2, q.1), Φ.momentum (q.2, q.1)))
      (ball s₀ (2 * r) ×ˢ Ioo (-(4 * r)) (4 * r)) :=
    (hx.prodMk hp).comp (contDiff_snd.prodMk contDiff_fst).contDiffOn (fun _ hq ↦ ⟨htime hq.2, hparams hq.1⟩)
  have hb := hflow H.vectorField (fun s ↦ transverseSectionState j ν (s, g s))
    (fun q ↦ (Φ.position (q.2, q.1), Φ.momentum (q.2, q.1)))
    (H.contDiffOn_vectorField_of_subset hD hDH (n := ∞) (by simpa using hH))
    hsmooth (by convert hswap using 1 ; congr 2 <;> ring)
    (by norm_num at hfield₁; linarith)
    (by nlinarith [cNorm_nonneg (closedBall s₀ r) 1 g]) hinit
    (by
      intro s hs t ht
      have ht' : t ∈ Ioo (-(4 * r)) (4 * r) := by convert ht using 1 ; congr 1 <;> ring
      exact (Φ.position_hasDerivAt (htime ht') (hparams hs)).prodMk
        (Φ.momentum_hasDerivAt (htime ht') (hparams hs)))
    (by
      intro s hs t ht
      apply hrange s hs t
      convert ht using 1 ; congr 1 <;> ring)
  simp only [one_mul, zero_sub, zero_add] at hb
  have hn := cNorm_mono_order (s := closedBall w R) (f := H.h) (Nat.le_succ n)
  have hg0 := cNorm_nonneg (closedBall s₀ r) n g
  have hs0 := cNorm_nonneg (closedBall w R) (n + 1) H.h
  have hbudget : 1 + cNorm (closedBall w R) n H.vectorField +
      cNorm (closedBall s₀ r) n (fun s ↦ transverseSectionState j ν (s, g s)) ≤
      (1 + (n + 1 : ℝ) + A) * (1 + cNorm (closedBall w R) (n + 1) H.h) := by
    nlinarith
  exact hb.trans ((mul_le_mul_of_nonneg_left hbudget hB.le).trans_eq (by ring))


omit [FiniteDimensional ℝ E] in
/-- Transfer the joint state budget to the augmented projection on its source ball
(`app:lem:common-hamilton-phase`). The consumer is the actual tame flow family. -/
theorem exists_augmentedProjection_cNorm_bound_from_state
    (s₀ : InitialData U) {r : ℝ} (hr : 0 < r) (n : ℕ) :
    ∃ B > (0 : ℝ), ∀ (H : HomogeneousSymbol E) (Φ : HamiltonFlow H U),
      ball s₀ (2 * r) ⊆ Φ.parameters → Ioo (-(4 * r)) (4 * r) ⊆ Φ.time →
      ContDiffOn ℝ ∞ Φ.position (Φ.time ×ˢ Φ.parameters) →
      ContDiffOn ℝ ∞ Φ.momentum (Φ.time ×ˢ Φ.parameters) →
      cNorm (closedBall ((0 : ℝ), s₀) r) n Φ.augmentedProjection ≤
        B * (1 + cNorm (closedBall s₀ r ×ˢ Icc (-r) r) n
          (fun q ↦ (Φ.position (q.2, q.1), Φ.momentum (q.2, q.1)))) := by
  let K := closedBall ((0 : ℝ), s₀) r
  let L := closedBall s₀ r ×ˢ Icc (-r) r
  let S : ℝ × InitialData U → InitialData U × ℝ := Prod.swap
  let P : (E × E) →L[ℝ] E × (ℝ × U) := (ContinuousLinearMap.fst ℝ E E).prod 0
  let Q : ℝ × InitialData U → E × (ℝ × U) := fun q ↦ (0, q.2.2)
  have hK : IsCompact K := isCompact_closedBall _ _
  have hL : IsCompact L := (isCompact_closedBall _ _).prod isCompact_Icc
  have hS : ContDiff ℝ n S := contDiff_snd.prodMk contDiff_fst
  have hQ : ContDiff ℝ n Q := contDiff_const.prodMk contDiff_snd.snd
  have hP : ‖P‖ ≤ 1 := by
    apply P.opNorm_le_bound zero_le_one
    intro z
    simpa [P] using norm_fst_le z
  have hmap : MapsTo S K L := by
    intro q hq
    have hdist := mem_closedBall.mp hq
    rw [Prod.dist_eq, dist_zero_right, Real.norm_eq_abs, max_le_iff] at hdist
    exact ⟨hdist.2, abs_le.mp hdist.1⟩
  let A := compositionMultiplicity n * (1 + cNorm K n S) ^ n
  let N := cNorm K n Q
  have hN : 0 ≤ N := cNorm_nonneg K n Q
  have hA : 0 ≤ (n + 1 : ℝ) * |A| := by positivity
  refine ⟨1 + (n + 1 : ℝ) * |A| + N, by positivity, ?_⟩
  intro H Φ hparams htime hx hp
  let f : InitialData U × ℝ → E × E :=
    fun q ↦ (Φ.position (q.2, q.1), Φ.momentum (q.2, q.1))
  have hf : ∀ q ∈ L, ContDiffAt ℝ n f q := by
    intro q hq
    have ht : q.2 ∈ Φ.time := htime ⟨by linarith [hq.2.1], by linarith [hq.2.2]⟩
    have hs : q.1 ∈ Φ.parameters := hparams (closedBall_subset_ball (by linarith) hq.1)
    exact (((hx.prodMk hp).contDiffAt
      ((Φ.isOpen_time.prod Φ.isOpen_parameters).mem_nhds ⟨ht, hs⟩)).comp q
      (contDiff_snd.prodMk contDiff_fst).contDiffAt).of_le (by simp)
  have hcomp := cNorm_comp_le_polynomial (s := K) (r := n)
    (fun _ _ ↦ hS.contDiffAt) (fun q hq ↦ hf _ (hmap hq))
    (fun k hk ↦ bddAbove_norm_iteratedFDeriv hK hS hk)
    (cNorm_nonneg L n f)
    (fun k hk q hq ↦ norm_iteratedFDeriv_le_cNorm_of_contDiffAt hL hf (hmap hq) hk)
  have hcomp' : cNorm K n (f ∘ S) ≤ |A| * cNorm L n f := by
    calc
      _ ≤ A * cNorm L n f := by convert hcomp using 1; dsimp [A]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_abs_self A) (cNorm_nonneg L n f)
  have hpost : cNorm K n (P ∘ (f ∘ S)) ≤ (n + 1 : ℝ) * cNorm K n (f ∘ S) := by
    apply (cNorm_le_sum_of_bounds (C := fun _ ↦ cNorm K n (f ∘ S))
      (fun _ _ ↦ cNorm_nonneg _ _ _) ?_).trans_eq (by simp)
    intro k hk q hq
    have hfs := (hf _ (hmap hq)).comp q hS.contDiffAt
    calc
      _ ≤ ‖P‖ * ‖iteratedFDeriv ℝ k (f ∘ S) q‖ :=
        P.norm_iteratedFDeriv_comp_left hfs (by exact_mod_cast hk)
      _ ≤ 1 * cNorm K n (f ∘ S) := mul_le_mul hP
        (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
          (fun q hq ↦ (hf _ (hmap hq)).comp q hS.contDiffAt) hq hk)
        (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  have hadd := cNorm_add_le_of_contDiffAt hK
    (fun q hq ↦ P.contDiff.contDiffAt.comp q ((hf _ (hmap hq)).comp q hS.contDiffAt))
    (fun _ _ ↦ hQ.contDiffAt)
  have he : (P ∘ (f ∘ S)) + Q = Φ.augmentedProjection := by
    funext q
    simp [P, Q, f, S, HamiltonFlow.augmentedProjection]
  rw [he] at hadd
  have hmain := hadd.trans (add_le_add hpost le_rfl)
  have hmain' := hmain.trans (add_le_add
    (mul_le_mul_of_nonneg_left hcomp' (by positivity)) le_rfl)
  change cNorm K n Φ.augmentedProjection ≤
    (1 + (n + 1 : ℝ) * |A| + N) * (1 + cNorm L n f)
  dsimp only [N] at *
  nlinarith [cNorm_nonneg L n f, mul_nonneg (cNorm_nonneg K n Q) (cNorm_nonneg L n f)]
/-- Sharp scalar-symbol estimate for the inverse coordinates and explicit
phase of the same Hamilton flow (`app:lem:common-hamilton-phase`). The right side
uses symbol order `n + 1`; neither inverse nor projection derivative budgets
are premises. Combined with a scalar-symbol coefficient shift of two, this is
the separate phase estimate at coefficient order `n + 3` consumed by
`FullPhaseCharts`. The common-family producer must instantiate the retained
root cylinder, state containment, inverse buffer and normalized half gap. -/
theorem exists_hamiltonPhase_cNorm_bound_from_symbol
    (j : U →ₗᵢ[ℝ] E) (ν : E) (s₀ : InitialData U) (τ₀ : ℝ) (w : E × E)
    {r a c R M : ℝ} (hr : 0 < r) (ha : 0 < a) (hc : 0 < c) (hR : 0 < R)
    (hM : 0 ≤ M) {D : Set (E × E)} (hD : IsOpen D)
    (hRD : closedBall w R ⊆ D)
    (hmap : MapsTo (transverseSectionState j ν)
      (closedBall s₀ (2 * r) ×ˢ Icc (τ₀ - a) (τ₀ + a)) (closedBall w R))
    {K : Set (E × (ℝ × U))} (hK : IsCompact K)
    (A : (ℝ × InitialData U) ≃L[ℝ] (E × (ℝ × U))) (n : ℕ) :
    ∃ B > (0 : ℝ), ∀ (H : HomogeneousSymbol E) (g : InitialData U → ℝ)
      (Φ : HamiltonFlow H U) (C : ProjectionChart Φ),
      D ⊆ H.domain → ContDiffOn ℝ ∞ H.h D → cNorm (closedBall w R) 2 H.h ≤ M →
      ContDiffOn ℝ ∞ g (ball s₀ (2 * r)) →
      (∀ s ∈ ball s₀ (2 * r), g s ∈ Icc (τ₀ - a) (τ₀ + a) ∧
        H.h (transverseSectionState j ν (s, g s)) = s.2.1 ∧
        c ≤ |⟪H.hp (transverseSectionState j ν (s, g s)), ν⟫_ℝ|) →
      ball s₀ (2 * r) ⊆ Φ.parameters → Ioo (-(4 * r)) (4 * r) ⊆ Φ.time →
      ContDiffOn ℝ ∞ Φ.position (Φ.time ×ˢ Φ.parameters) →
      ContDiffOn ℝ ∞ Φ.momentum (Φ.time ×ˢ Φ.parameters) →
      (∀ s ∈ ball s₀ (2 * r),
        (Φ.position (0, s), Φ.momentum (0, s)) = transverseSectionState j ν (s, g s)) →
      (∀ s ∈ closedBall s₀ r, ∀ t ∈ Ioo (-(4 * r)) (4 * r),
        (Φ.position (t, s), Φ.momentum (t, s)) ∈ closedBall w R) →
      K ⊆ C.target → ContDiffOn ℝ ∞ C.coordinates C.target →
      MapsTo (chartLift C.coordinates) K (closedBall ((0 : ℝ), s₀) r) →
      (∀ q ∈ closedBall ((0 : ℝ), s₀) r,
        ‖(A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U)).comp
          (fderiv ℝ Φ.augmentedProjection q) -
          ContinuousLinearMap.id ℝ (ℝ × InitialData U)‖ ≤ 1 / 2) →
      cNorm K n (chartLift C.coordinates) + cNorm K n C.coordinates +
        cNorm K n (phase C.coordinates) ≤
          B * (1 + cNorm (closedBall w R) (n + 1) H.h) := by
  obtain ⟨F₁, hF₁, hflow₁⟩ := exists_hamiltonFlow_state_cNorm_bound
    j ν s₀ τ₀ w hr ha hc hR hM hD hRD hmap 1
  obtain ⟨F, hF, hflow⟩ := exists_hamiltonFlow_state_cNorm_bound
    j ν s₀ τ₀ w hr ha hc hR hM hD hRD hmap n
  obtain ⟨P₁, hP₁, hproj₁⟩ := exists_augmentedProjection_cNorm_bound_from_state (E := E) s₀ hr 1
  obtain ⟨P, hP, hproj⟩ := exists_augmentedProjection_cNorm_bound_from_state (E := E) s₀ hr n
  let W := Ioo (-(4 * r)) (4 * r) ×ˢ ball s₀ (2 * r)
  have hW : IsOpen W := isOpen_Ioo.prod isOpen_ball
  have hball : closedBall ((0 : ℝ), s₀) r ⊆ W := by
    intro q hq
    have hh := mem_closedBall.mp hq
    rw [Prod.dist_eq, dist_zero_right, Real.norm_eq_abs, max_le_iff] at hh
    have ht := abs_le.mp hh.1
    exact ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩,
      closedBall_subset_ball (by linarith) hh.2⟩
  obtain ⟨I, hI, hinverse⟩ := exists_coordinates_phase_cNorm_bound
    ((0 : ℝ), s₀) hr hW hball hK A
    (by positivity : 0 ≤ P₁ * (1 + F₁ * (1 + M))) n
  refine ⟨I * (1 + P * (1 + F)), by positivity, ?_⟩
  intro H g Φ C hDH hH hlow hg hroot hparams htime hx hp hinit hrange hKC hC hmaps hgap
  have hf₁ := hflow₁ H g Φ hDH hH hlow hg hroot hparams htime hx hp hinit hrange
  have hf := hflow H g Φ hDH hH hlow hg hroot hparams htime hx hp hinit hrange
  have hp₁ := hproj₁ H Φ hparams htime hx hp
  have hpn := hproj H Φ hparams htime hx hp
  have hlowproj : cNorm (closedBall ((0 : ℝ), s₀) r) 1 Φ.augmentedProjection ≤
      P₁ * (1 + F₁ * (1 + M)) := by
    apply hp₁.trans
    apply mul_le_mul_of_nonneg_left _ hP₁.le
    exact add_le_add le_rfl
      (hf₁.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hlow) hF₁.le))
  have hprojhigh : cNorm (closedBall ((0 : ℝ), s₀) r) n Φ.augmentedProjection ≤
      P * (1 + F) * (1 + cNorm (closedBall w R) (n + 1) H.h) := by
    apply hpn.trans
    have hnorm := cNorm_nonneg (closedBall w R) (n + 1) H.h
    have hstep : 1 + cNorm (closedBall s₀ r ×ˢ Icc (-r) r) n
        (fun q ↦ (Φ.position (q.2, q.1), Φ.momentum (q.2, q.1))) ≤
        (1 + F) * (1 + cNorm (closedBall w R) (n + 1) H.h) := by nlinarith
    exact (mul_le_mul_of_nonneg_left hstep hP.le).trans_eq (by ring)
  have hΦ : ContDiffOn ℝ ∞ Φ.augmentedProjection W :=
    (hx.prodMk contDiff_snd.snd.contDiffOn).mono (fun _ hq ↦ ⟨htime hq.1, hparams hq.2⟩)
  have hi := hinverse H Φ C hKC hΦ hC hlowproj hmaps hgap
  have hbudget : 1 + cNorm (closedBall ((0 : ℝ), s₀) r) n Φ.augmentedProjection ≤
      (1 + P * (1 + F)) * (1 + cNorm (closedBall w R) (n + 1) H.h) := by
    nlinarith [cNorm_nonneg (closedBall w R) (n + 1) H.h]
  exact hi.trans ((mul_le_mul_of_nonneg_left hbudget hI.le).trans_eq (by ring))

end JanetCartan.HamiltonPhase
