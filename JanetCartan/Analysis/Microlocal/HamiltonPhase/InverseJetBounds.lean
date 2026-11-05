module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.SmoothBufferedChart
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.FiniteOrderContinuity.PhaseBounds
public import JanetCartan.Analysis.ContDiff.Norm.Composition.FlowForcing
public import JanetCartan.Analysis.ODE.HigherVariational.Partitions

/-!
# One-high inverse-coordinate and Hamilton-phase bounds

For `app:ch_regular_base:lem:buffered-interpolation` and
`app:lem:common-hamilton-phase` of paper.tex, differentiate the normalized
inverse equation and isolate its top derivative. The half gap absorbs the
linear term; baseline-one interpolation bounds the partition remainder.
Strong induction supplies every lower inverse jet, with no inverse-jet
budget among the hypotheses.

`exists_coordinates_phase_cNorm_bound` is the concrete transfer needed by
`exists_commonBufferedHamiltonPhases`: the parent supplies the joint forward
projection budget from the flow construction and the stated source/target
containments. The source working ball lies in an open smoothness domain;
the compact inner target lies in the open chart target and its lifted inverse
lies in that source ball. Constants precede the symbol, flow, and chart.
The high projection norm enters linearly at the requested order, with loss zero.
These estimates concern an actual smooth chart, not existence of that chart.
-/

open Set Filter Metric
open scoped ContDiff Topology
@[expose] public noncomputable section
namespace JanetCartan.HamiltonPhase
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
private theorem norm_le_twice_comp_of_half_gap (B : X →L[ℝ] X)
    (hB : ‖B - ContinuousLinearMap.id ℝ X‖ ≤ 1 / 2)
    {n : ℕ} (T : Y [×n]→L[ℝ] X) :
    ‖T‖ ≤ 2 * ‖B.compContinuousMultilinearMap T‖ := by
  have he : T = B.compContinuousMultilinearMap T -
      (B - ContinuousLinearMap.id ℝ X).compContinuousMultilinearMap T := by
    ext v
    simp
  have h := norm_sub_le (B.compContinuousMultilinearMap T)
    ((B - ContinuousLinearMap.id ℝ X).compContinuousMultilinearMap T)
  rw [← he] at h
  have hb := ((B - ContinuousLinearMap.id ℝ X).norm_compContinuousMultilinearMap_le T).trans
    (mul_le_mul_of_nonneg_right hB (norm_nonneg T))
  linarith

private theorem norm_linear_jet_le (L : Y →L[ℝ] X) {n : ℕ} (hn : 0 < n) (y : Y) :
    ‖iteratedFDeriv ℝ n L y‖ ≤ ‖L‖ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [← norm_iteratedFDeriv_fderiv]
  rw [show fderiv ℝ (L : Y → X) = (fun _ ↦ L) from funext fun x ↦ L.fderiv]
  cases k with
  | zero => simp
  | succ k => simp [iteratedFDeriv_succ_const]

/-- Differentiation of the normalized inverse equation, used in the inverse
jet induction of `app:ch_regular_base:lem:buffered-interpolation`. -/
theorem normalized_inverse_jet_identity {V : X → X} {g : Y → X} {y : Y}
    (L : Y →L[ℝ] X) {n : ℕ} (hn : 0 < n)
    (hV : ContDiffAt ℝ n V (g y)) (hg : ContDiffAt ℝ n g y)
    (heq : V ∘ g =ᶠ[𝓝 y] L) :
    (fderiv ℝ V (g y)).compContinuousMultilinearMap (iteratedFDeriv ℝ n g y) =
      iteratedFDeriv ℝ n L y - ODE.jetPartitionRemainder n V g y := by
  have h := ODE.iteratedFDeriv_comp_eq_top_add_jetPartitionRemainder hn hV hg
  rw [(heq.iteratedFDeriv ℝ n).eq_of_nhds] at h
  exact eq_sub_of_add_eq h.symm

variable [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y]
/-- `app:ch_regular_base:lem:buffered-interpolation`: normalized inverse jets
have a one-high bound with no derivative loss. All lower jets are derived by
strong induction from the inverse equation and the half gap. -/
theorem exists_normalized_inverse_jet_bound (a : X) {ρ : ℝ} (hρ : 0 < ρ)
    {W : Set X} (hW : IsOpen W) (hball : closedBall a ρ ⊆ W)
    (L : Y →L[ℝ] X) {M : ℝ} (hM : 0 ≤ M) (n : ℕ) :
    ∃ C > (0 : ℝ), ∀ (V : X → X) (g : Y → X) (y : Y),
      ContDiffOn ℝ ∞ V W → ContDiffAt ℝ ∞ g y →
      cNorm (closedBall a ρ) 1 V ≤ M → g y ∈ closedBall a ρ →
      ‖fderiv ℝ V (g y) - ContinuousLinearMap.id ℝ X‖ ≤ 1 / 2 →
      V ∘ g =ᶠ[𝓝 y] L →
      ‖iteratedFDeriv ℝ n g y‖ ≤ C * (1 + cNorm (closedBall a ρ) n V) := by
  classical
  induction n using Nat.strong_induction_on with | h n ih =>
  by_cases hn0 : n = 0
  · subst n
    refine ⟨1 + ‖a‖ + ρ, by positivity, ?_⟩
    intro V g y _ _ _ hy _ _
    rw [norm_iteratedFDeriv_zero]
    have hb : ‖g y‖ ≤ ‖a‖ + ρ := by
      have h := norm_le_insert a (g y)
      rw [← dist_eq_norm, dist_comm] at h
      exact h.trans (add_le_add_right hy _)
    nlinarith [cNorm_nonneg (closedBall a ρ) 0 V, norm_nonneg a]
  have hn : 0 < n := Nat.pos_of_ne_zero hn0
  choose A hA hAb using fun j : Fin n ↦ ih j j.isLt
  let A' : ℕ → ℝ := fun j ↦ if hj : j < n then A ⟨j, hj⟩ else 0
  have hA' (j : ℕ) : 0 ≤ A' j := by
    dsimp [A']; split_ifs with hj
    · exact (hA ⟨j, hj⟩).le
    · exact le_rfl
  have hforce : ∃ ε : ℝ, 0 ≤ ε ∧ ∀ (V : X → X) (g : Y → X) (y : Y),
      ContDiffOn ℝ ∞ V W → cNorm (closedBall a ρ) 1 V ≤ M →
      g y ∈ closedBall a ρ →
      (∀ j, 1 ≤ j → j < n → ‖iteratedFDeriv ℝ j g y‖ ≤
        A' j * (1 + cNorm (closedBall a ρ) j V)) →
      ‖ODE.jetPartitionRemainder n V g y‖ ≤
        ε * (1 + cNorm (closedBall a ρ) n V) := by
    by_cases hn1 : n = 1
    · subst n
      exact ⟨0, le_rfl, fun _ _ _ _ _ _ _ ↦ by
        simp only [ODE.jetPartitionRemainder_one, norm_zero, zero_mul, le_refl]⟩
    obtain ⟨ε, hε, hb⟩ := FlowForcing.exists_forcingSum_le_closedBall_on
      (0 : Y) a (by norm_num : (0 : ℝ) < 1) hρ isOpen_univ hW
      (subset_univ _) hball (by omega : 2 ≤ n) hM (le_refl (0 : ℝ)) A' hA'
    refine ⟨ε, hε.le, ?_⟩
    intro V g y hV hVM hy hj
    have hh := hb V (0 : Y → X) hV contDiffOn_const hVM (by simp)
      g y hy (by simpa using hj)
    exact (ODE.norm_jetPartitionRemainder_le n V g y).trans (by simpa [FlowForcing.forcingSum] using hh)
  obtain ⟨ε, hε, hforce⟩ := hforce
  refine ⟨1 + 2 * (‖L‖ + ε), by positivity, ?_⟩
  intro V g y hV hg hVM hy hgap heq
  have hrem := hforce V g y hV hVM hy (by
    intro j _ hj
    simpa only [A', dite_eq_left hj] using
      hAb ⟨j, hj⟩ V g y hV hg hVM hy hgap heq)
  have hid := normalized_inverse_jet_identity L hn
    ((hV.contDiffAt (hW.mem_nhds (hball hy))).of_le (by simp))
    (hg.of_le (by simp)) heq
  have hb := norm_le_twice_comp_of_half_gap (fderiv ℝ V (g y)) hgap
    (iteratedFDeriv ℝ n g y)
  rw [hid] at hb
  have ht := (norm_sub_le (iteratedFDeriv ℝ n L y) _).trans
    (add_le_add (norm_linear_jet_le L hn y) hrem)
  have hH := cNorm_nonneg (closedBall a ρ) n V
  nlinarith [norm_nonneg L]

private theorem cNorm_postLinear_of_contDiffAt
    {P F G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {K : Set P} (hK : IsCompact K) (n : ℕ) (L : F →L[ℝ] G)
    {f : P → F} (hf : ∀ x ∈ K, ContDiffAt ℝ n f x) :
    cNorm K n (L ∘ f) ≤ ‖L‖ * cNorm K n f := by
  simp only [cNorm, Finset.mul_sum]
  apply cNorm_le_sum_of_bounds
    (fun k _ ↦ mul_nonneg (norm_nonneg _) (sSup_norm_iteratedFDeriv_nonneg K k f))
  intro k hk x hx
  apply (L.norm_iteratedFDeriv_comp_left (hf x hx) (by exact_mod_cast hk)).trans
  exact mul_le_mul_of_nonneg_left
    (le_csSup (bddAbove_norm_iteratedFDeriv_of_contDiffAt hK hf hk)
      (mem_image_of_mem _ hx)) (norm_nonneg _)

/-- `app:ch_regular_base:lem:buffered-interpolation`: a smooth inverse on an
open target has a one-high `Cⁿ` bound, of loss zero, on any inner target
whose inverse image lies in the fixed source ball. The source ball has an
explicit open smoothness buffer. The constant is independent of both maps.
This is the transfer used for the augmented Hamilton projection. -/
theorem exists_inverse_cNorm_bound (a : X) {ρ : ℝ} (hρ : 0 < ρ)
    {W : Set X} (hW : IsOpen W) (hball : closedBall a ρ ⊆ W)
    (A : X ≃L[ℝ] Y) {M : ℝ} (hM : 0 ≤ M) (n : ℕ) :
    ∃ C > (0 : ℝ), ∀ (f : X → Y) (g : Y → X) (V K : Set Y),
      IsOpen V → K ⊆ V → ContDiffOn ℝ ∞ f W → ContDiffOn ℝ ∞ g V →
      cNorm (closedBall a ρ) 1 f ≤ M → MapsTo g K (closedBall a ρ) →
      (∀ x ∈ closedBall a ρ,
        ‖(A.symm : Y →L[ℝ] X).comp (fderiv ℝ f x) -
          ContinuousLinearMap.id ℝ X‖ ≤ 1 / 2) →
      EqOn (f ∘ g) id V →
      cNorm K n g ≤ C * (1 + cNorm (closedBall a ρ) n f) := by
  let L : Y →L[ℝ] X := A.symm
  choose C hC hbound using exists_normalized_inverse_jet_bound a hρ hW hball L
    (M := ‖L‖ * M) (mul_nonneg (norm_nonneg L) hM)
  let D := ∑ j ∈ Finset.range (n + 1), C j
  have hD : 0 ≤ D := Finset.sum_nonneg fun j _ ↦ (hC j).le
  refine ⟨(1 + D) * (1 + ‖L‖), by positivity, ?_⟩
  intro f g V K hV hKV hf hg hfM hrange hgap heq
  have hnorm (j : ℕ) : cNorm (closedBall a ρ) j (L ∘ f) ≤
      ‖L‖ * cNorm (closedBall a ρ) j f :=
    cNorm_postLinear_of_contDiffAt (isCompact_closedBall a ρ) j L
      (fun x hx ↦ (hf.contDiffAt (hW.mem_nhds (hball hx))).of_le (by simp))
  have hlow := (hnorm 1).trans (mul_le_mul_of_nonneg_left hfM (norm_nonneg L))
  have hjets (j : ℕ) (y : Y) (hy : y ∈ K) :
      ‖iteratedFDeriv ℝ j g y‖ ≤ C j * (1 + cNorm (closedBall a ρ) j (L ∘ f)) := by
    apply hbound j (L ∘ f) g y (hf.continuousLinearMap_comp L)
      (hg.contDiffAt (hV.mem_nhds (hKV hy))) hlow (hrange hy)
    · rw [(L.hasFDerivAt.comp (g y)
        ((hf.contDiffAt (hW.mem_nhds (hball (hrange hy)))).differentiableAt
          (by simp)).hasFDerivAt).fderiv]
      exact hgap _ (hrange hy)
    · exact Filter.eventuallyEq_of_mem (hV.mem_nhds (hKV hy)) (fun z hz ↦
        congrArg L (heq hz))
  have hH : 0 ≤ 1 + cNorm (closedBall a ρ) n (L ∘ f) := by
    linarith [cNorm_nonneg (closedBall a ρ) n (L ∘ f)]
  calc
    _ ≤ ∑ j ∈ Finset.range (n + 1), C j *
        (1 + cNorm (closedBall a ρ) n (L ∘ f)) := by
      apply CompositionBounds.cNorm_le_sum (fun j _ ↦ mul_nonneg (hC j).le hH)
      intro j hj y hy
      exact (hjets j y hy).trans (mul_le_mul_of_nonneg_left
        (add_le_add (le_refl 1) (cNorm_mono_order hj)) (hC j).le)
    _ = D * (1 + cNorm (closedBall a ρ) n (L ∘ f)) := (Finset.sum_mul ..).symm
    _ ≤ D * (1 + ‖L‖ * cNorm (closedBall a ρ) n f) :=
      mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) (hnorm n)) hD
    _ ≤ ((1 + D) * (1 + ‖L‖)) * (1 + cNorm (closedBall a ρ) n f) := by
      have h := cNorm_nonneg (closedBall a ρ) n f
      nlinarith [norm_nonneg L, mul_nonneg hD (norm_nonneg L),
        mul_nonneg hD h, mul_nonneg (norm_nonneg L) h]

section HamiltonChart
variable {E U : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ U]

/-- `app:lem:common-hamilton-phase`: transfer the augmented projection budget
to its actual inverse coordinates and the explicit phase `S = e t + u' · η'`.
The constant precedes the symbol, flow, and chart; it depends only on the order,
source ball and open buffer, compact target, central equivalence, and fixed
`C¹` projection bound. There is no derivative loss. The parent construction
must place the lifted compact target in the source ball, place that ball in
the open forward smoothness domain, and place the compact target in the open
chart target. No bounds on inverse jets are assumed. -/
theorem exists_coordinates_phase_cNorm_bound
    (a : ℝ × InitialData U) {ρ : ℝ} (hρ : 0 < ρ)
    {W : Set (ℝ × InitialData U)} (hW : IsOpen W) (hball : closedBall a ρ ⊆ W)
    {K : Set (E × (ℝ × U))} (hK : IsCompact K)
    (A : (ℝ × InitialData U) ≃L[ℝ] (E × (ℝ × U)))
    {M : ℝ} (hM : 0 ≤ M) (n : ℕ) :
    ∃ B > (0 : ℝ), ∀ (H : HomogeneousSymbol E) (Φ : HamiltonFlow H U)
      (C : ProjectionChart Φ),
      K ⊆ C.target → ContDiffOn ℝ ∞ Φ.augmentedProjection W →
      ContDiffOn ℝ ∞ C.coordinates C.target →
      cNorm (closedBall a ρ) 1 Φ.augmentedProjection ≤ M →
      MapsTo (chartLift C.coordinates) K (closedBall a ρ) →
      (∀ q ∈ closedBall a ρ,
        ‖(A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U)).comp
          (fderiv ℝ Φ.augmentedProjection q) -
          ContinuousLinearMap.id ℝ (ℝ × InitialData U)‖ ≤ 1 / 2) →
      cNorm K n (chartLift C.coordinates) + cNorm K n C.coordinates +
        cNorm K n (phase C.coordinates) ≤
          B * (1 + cNorm (closedBall a ρ) n Φ.augmentedProjection) := by
  let P : (ℝ × InitialData U) →L[ℝ] (ℝ × U) :=
    (ContinuousLinearMap.fst ℝ ℝ (InitialData U)).prod
      ((ContinuousLinearMap.fst ℝ U (ℝ × U)).comp
        (ContinuousLinearMap.snd ℝ ℝ (InitialData U)))
  obtain ⟨D, hD, hinv⟩ := exists_inverse_cNorm_bound a hρ hW hball A hM n
  obtain ⟨F, hF, hphase⟩ := exists_phase_finiteOrder_bound hK n
  refine ⟨(1 + (1 + F) * ‖P‖) * D, by positivity, ?_⟩
  intro H Φ C hKC hΦ hC hM' hrange hgap
  have hg : ContDiffOn ℝ ∞ (chartLift C.coordinates) C.target :=
    hC.fst.prodMk (hC.snd.prodMk contDiff_snd.contDiffOn)
  have hi := hinv Φ.augmentedProjection (chartLift C.coordinates) C.target K
    C.isOpen_target hKC hΦ hg hM' hrange hgap (by
      intro z hz
      exact Prod.ext (C.right_inverse z hz) rfl)
  have hc : cNorm K n C.coordinates ≤ ‖P‖ * cNorm K n (chartLift C.coordinates) := by
    have he : P ∘ chartLift C.coordinates = C.coordinates := by
      funext z
      simp [P, chartLift]
    rw [← he]
    apply cNorm_postLinear_of_contDiffAt hK n P
    exact fun z hz ↦ (hg.contDiffAt (C.isOpen_target.mem_nhds (hKC hz))).of_le (by simp)
  have hp : cNorm K n (phase C.coordinates) ≤ F * cNorm K n C.coordinates := by
    have hh := hphase C.target C.coordinates (fun _ ↦ (0 : ℝ × U))
      C.isOpen_target hKC (hC.of_le (by simp)) contDiffOn_const
    change cNorm K n (fun z ↦ z.2.1 * (C.coordinates z).1 +
      inner ℝ (C.coordinates z).2 z.2.2) ≤ _
    simpa [phase] using hh
  calc
    _ ≤ (1 + (1 + F) * ‖P‖) * cNorm K n (chartLift C.coordinates) := by
      nlinarith [mul_le_mul_of_nonneg_left hc hF.le]
    _ ≤ (1 + (1 + F) * ‖P‖) *
        (D * (1 + cNorm (closedBall a ρ) n Φ.augmentedProjection)) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by ring
end HamiltonChart
end JanetCartan.HamiltonPhase
