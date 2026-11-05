module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.InverseJetBounds

/-!
# Inverse jets from a differential lower bound

For the parameter-augmented charts in `app:ch_seed:prop:seed-phase-charts`,
a data-Jacobian half gap need not be a joint-Jacobian half gap. This leaf uses
the Hamilton inverse partition identity and its interpolation remainder with
a general fixed differential lower bound. The consumer `FiberBounds` derives
that lower bound from the data gap and the primitive forward `C¹` bound.
No inverse derivative is an input, and this does not construct an inverse.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Metric
open scoped ContDiff Topology
namespace JanetCartan.FullPhaseCharts.InverseEstimates
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

private theorem norm_multilinear_le_of_lower_bound (B : X →L[ℝ] X)
    {J : ℝ} (hJ : 0 ≤ J) (hB : ∀ v, ‖v‖ ≤ J * ‖B v‖)
    {n : ℕ} (T : Y [×n]→L[ℝ] X) :
    ‖T‖ ≤ J * ‖B.compContinuousMultilinearMap T‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  exact (hB (T v)).trans (by
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left
      ((B.compContinuousMultilinearMap T).le_opNorm v) hJ)

private theorem norm_linear_jet_le (L : Y →L[ℝ] X) {n : ℕ} (hn : 0 < n) (y : Y) :
    ‖iteratedFDeriv ℝ n L y‖ ≤ ‖L‖ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [← norm_iteratedFDeriv_fderiv]
  rw [show fderiv ℝ (L : Y → X) = (fun _ ↦ L) from funext fun x ↦ L.fderiv]
  cases k with
  | zero => simp
  | succ k => simp [iteratedFDeriv_succ_const]

variable [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y]
/-- The partition induction for `app:ch_seed:prop:seed-phase-charts`, with
an arbitrary fixed differential lower bound. This permits parameter augmentation
without assuming small physical or epsilon derivatives. The one-high estimate
has loss zero, with a constant chosen before either map. -/
theorem exists_inverse_jet_bound_of_lower_bound (a : X) {ρ : ℝ} (hρ : 0 < ρ)
    {W : Set X} (hW : IsOpen W) (hball : closedBall a ρ ⊆ W)
    (L : Y →L[ℝ] X) {M J : ℝ} (hM : 0 ≤ M) (hJ : 0 ≤ J) (n : ℕ) :
    ∃ C > (0 : ℝ), ∀ (V : X → X) (g : Y → X) (y : Y),
      ContDiffOn ℝ ∞ V W → ContDiffAt ℝ ∞ g y →
      cNorm (closedBall a ρ) 1 V ≤ M → g y ∈ closedBall a ρ →
      (∀ v, ‖v‖ ≤ J * ‖fderiv ℝ V (g y) v‖) →
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
  refine ⟨1 + J * (‖L‖ + ε), by positivity, ?_⟩
  intro V g y hV hg hVM hy hgap heq
  have hrem := hforce V g y hV hVM hy (by
    intro j _ hj
    simpa only [A', dite_eq_left hj] using
      hAb ⟨j, hj⟩ V g y hV hg hVM hy hgap heq)
  have hid := HamiltonPhase.normalized_inverse_jet_identity L hn
    ((hV.contDiffAt (hW.mem_nhds (hball hy))).of_le (by simp))
    (hg.of_le (by simp)) heq
  have hb := norm_multilinear_le_of_lower_bound (fderiv ℝ V (g y)) hJ hgap
    (iteratedFDeriv ℝ n g y)
  rw [hid] at hb
  have ht := (norm_sub_le (iteratedFDeriv ℝ n L y) _).trans
    (add_le_add (norm_linear_jet_le L hn y) hrem)
  have hH := cNorm_nonneg (closedBall a ρ) n V
  nlinarith [norm_nonneg L, mul_nonneg hJ (norm_nonneg L),
    mul_le_mul_of_nonneg_left ht hJ]

/-- The joint inverse `Cⁿ` bound used for the parameter augmentation in
`app:ch_seed:prop:seed-phase-charts`. Smoothness, the actual inverse equation,
source-ball containment and the forward differential lower bound are the only
analytic inputs. The constant is independent of both maps and their high norms. -/
theorem exists_inverse_cNorm_bound_of_lower_bound (a : X) {ρ : ℝ} (hρ : 0 < ρ)
    {W : Set X} (hW : IsOpen W) (hball : closedBall a ρ ⊆ W)
    {M J : ℝ} (hM : 0 ≤ M) (hJ : 0 ≤ J) (n : ℕ) :
    ∃ C > (0 : ℝ), ∀ (f g : X → X) (V K : Set X),
      IsOpen V → K ⊆ V → ContDiffOn ℝ ∞ f W → ContDiffOn ℝ ∞ g V →
      cNorm (closedBall a ρ) 1 f ≤ M → MapsTo g K (closedBall a ρ) →
      (∀ x ∈ closedBall a ρ, ∀ v, ‖v‖ ≤ J * ‖fderiv ℝ f x v‖) →
      EqOn (f ∘ g) id V →
      cNorm K n g ≤ C * (1 + cNorm (closedBall a ρ) n f) := by
  choose C hC hb using exists_inverse_jet_bound_of_lower_bound
    a hρ hW hball (ContinuousLinearMap.id ℝ X) hM hJ
  let D := ∑ j ∈ Finset.range (n + 1), C j
  have hD : 0 ≤ D := Finset.sum_nonneg fun j _ ↦ (hC j).le
  refine ⟨1 + D, by positivity, ?_⟩
  intro f g V K hV hKV hf hg hlow hrange hlower heq
  have hH : 0 ≤ 1 + cNorm (closedBall a ρ) n f := by
    linarith [cNorm_nonneg (closedBall a ρ) n f]
  calc
    _ ≤ ∑ j ∈ Finset.range (n + 1), C j *
        (1 + cNorm (closedBall a ρ) n f) := by
      apply cNorm_le_sum_of_bounds (fun j _ ↦ mul_nonneg (hC j).le hH)
      intro j hj y hy
      apply (hb j f g y hf (hg.contDiffAt (hV.mem_nhds (hKV hy)))
        hlow (hrange hy) (hlower _ (hrange hy))
        (Filter.eventuallyEq_of_mem (hV.mem_nhds (hKV hy)) (fun z hz ↦ heq hz))).trans
      exact mul_le_mul_of_nonneg_left
        (add_le_add (le_refl 1) (cNorm_mono_order hj)) (hC j).le
    _ = D * (1 + cNorm (closedBall a ρ) n f) := (Finset.sum_mul ..).symm
    _ ≤ (1 + D) * (1 + cNorm (closedBall a ρ) n f) := by nlinarith

end JanetCartan.FullPhaseCharts.InverseEstimates
