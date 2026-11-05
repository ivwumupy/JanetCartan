module

public import JanetCartan.Analysis.ODE.SmoothDependence
public import JanetCartan.Analysis.ODE.DerivativeBounds
public import JanetCartan.Analysis.ContDiff.Norm.Basic
public import JanetCartan.Analysis.ContDiff.Norm.Composition
public import JanetCartan.Analysis.ContDiff.Norm.Products
public import JanetCartan.Analysis.ODE.HigherVariational
public import JanetCartan.Analysis.ODE.TimeRescaling
public import JanetCartan.Analysis.ContDiff.Norm.Composition.FlowForcing

/-!
# Quantitative bounds for genuine autonomous flows

The spatial and joint time/parameter estimates of `app:ch_regular_base:lem:buffered-interpolation` and
`app:lem:common-hamilton-phase`. The estimates below follow from the actual
autonomous ODE on a buffered time interval, including variable initial sections.
The constants use only bounds for the vector field, its Lipschitz constant and
the initial section. Both signs of time are allowed.

The arbitrary-order spatial estimates derive the variational identities from
the genuine ODE and discharge the baseline-one forcing inputs by strong induction.
Their constants are chosen before the field and initial section, and their
high norms have derivative-order shift zero. Time rescaling gives the same
zero-loss bound for joint time/parameter derivatives on compact inner boxes.
The augmented field, section and flow are constructed from the genuine ODE;
no higher variational identity or forcing budget is a hypothesis of the bounds.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff Topology NNReal

namespace JanetCartan.HamiltonPhase

variable {P E : Type*} [NormedAddCommGroup P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `app:ch_regular_base:lem:buffered-interpolation`: comparison of two genuine
autonomous trajectories, in either time direction. Only the low Lipschitz
constant of the field enters the exponential. -/
theorem autonomousFlow_dist_le {V : E → E} {U : Set E} {u v : ℝ → E}
    {t₀ t : ℝ} {K : ℝ≥0} (hV : LipschitzOnWith K V U)
    (hu : ∀ τ ∈ uIcc t₀ t, HasDerivAt u (V (u τ)) τ)
    (hv : ∀ τ ∈ uIcc t₀ t, HasDerivAt v (V (v τ)) τ)
    (huU : ∀ τ ∈ uIcc t₀ t, u τ ∈ U)
    (hvU : ∀ τ ∈ uIcc t₀ t, v τ ∈ U) :
    dist (u t) (v t) ≤ dist (u t₀) (v t₀) * Real.exp (K * |t - t₀|) := by
  have h := ODE.norm_le_gronwallBound_of_hasDerivAt_uIcc
    (R := fun τ ↦ u τ - v τ) (R' := fun τ ↦ V (u τ) - V (v τ))
    (δ := ‖u t₀ - v t₀‖) (L := K) (ε := 0)
    (fun τ hτ ↦ (hu τ hτ).sub (hv τ hτ)) le_rfl
    (fun τ hτ ↦ by simpa using hV.norm_sub_le (huU τ hτ) (hvU τ hτ))
  simpa only [dist_eq_norm, gronwallBound_ε0] using h

/-- `app:lem:common-hamilton-phase`: a bounded autonomous field gives the
time displacement estimate on the entire segment, also for negative time. -/
theorem autonomousFlow_time_dist_le {V : E → E} {u : ℝ → E} {t₀ t B : ℝ}
    (hu : ∀ τ ∈ uIcc t₀ t, HasDerivAt u (V (u τ)) τ)
    (hV : ∀ τ ∈ uIcc t₀ t, ‖V (u τ)‖ ≤ B) :
    dist (u t) (u t₀) ≤ B * |t - t₀| := by
  have h := ODE.norm_le_gronwallBound_of_hasDerivAt_uIcc
    (R := fun τ ↦ u τ - u t₀) (R' := fun τ ↦ V (u τ))
    (δ := 0) (L := 0) (ε := B)
    (fun τ hτ ↦ (hu τ hτ).sub_const _) (by simp)
    (fun τ hτ ↦ by simpa using hV τ hτ)
  simpa [dist_eq_norm, gronwallBound] using h

/-- `app:lem:common-hamilton-phase`: joint time/parameter Lipschitz control of
a genuine flow with variable initial section. The state range and the ODE are
required on the outer open time interval; `T` bounds its distance from `t₀`.
No variational identity or derivative budget for the flow is assumed. -/
theorem autonomousFlow_joint_lipschitzOn
    {V : E → E} {σ : P → E} {Φ : P × ℝ → E} {U : Set E} {s : Set P}
    {a b t₀ T : ℝ} {K L B : ℝ≥0}
    (ht₀ : t₀ ∈ Ioo a b) (hT : ∀ t ∈ Ioo a b, |t - t₀| ≤ T)
    (hV : LipschitzOnWith K V U) (hVB : ∀ y ∈ U, ‖V y‖ ≤ B)
    (hσ : LipschitzOnWith L σ s) (hinit : ∀ x ∈ s, Φ (x, t₀) = σ x)
    (hode : ∀ x ∈ s, ∀ t ∈ Ioo a b,
      HasDerivAt (fun τ ↦ Φ (x, τ)) (V (Φ (x, t))) t)
    (hrange : ∀ x ∈ s, ∀ t ∈ Ioo a b, Φ (x, t) ∈ U) :
    LipschitzOnWith ⟨L * Real.exp (K * T) + B, by positivity⟩ Φ (s ×ˢ Ioo a b) := by
  apply LipschitzOnWith.of_dist_le_mul
  rintro ⟨x, t⟩ ⟨hx, ht⟩ ⟨y, u⟩ ⟨hy, hu⟩
  have hseg := ordConnected_Ioo.uIcc_subset ht₀ ht
  have hspace := autonomousFlow_dist_le hV
    (fun τ hτ ↦ hode x hx τ (hseg hτ))
    (fun τ hτ ↦ hode y hy τ (hseg hτ))
    (fun τ hτ ↦ hrange x hx τ (hseg hτ))
    (fun τ hτ ↦ hrange y hy τ (hseg hτ))
  rw [hinit x hx, hinit y hy] at hspace
  have hspace' : dist (Φ (x, t)) (Φ (y, t)) ≤
      (L * Real.exp (K * T)) * dist x y := by
    calc
      _ ≤ dist (σ x) (σ y) * Real.exp (K * |t - t₀|) := hspace
      _ ≤ (L * dist x y) * Real.exp (K * T) := by
        apply mul_le_mul (hσ.dist_le_mul x hx y hy) _ (Real.exp_nonneg _) (by positivity)
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hT t ht) K.coe_nonneg)
      _ = _ := by ring
  have hseg' := ordConnected_Ioo.uIcc_subset hu ht
  have htime := autonomousFlow_time_dist_le
    (fun τ hτ ↦ hode y hy τ (hseg' hτ))
    (fun τ hτ ↦ hVB _ (hrange y hy τ (hseg' hτ)))
  calc
    _ ≤ dist (Φ (x, t)) (Φ (y, t)) + dist (Φ (y, t)) (Φ (y, u)) := dist_triangle _ _ _
    _ ≤ (L * Real.exp (K * T)) * dist x y + B * dist t u :=
      add_le_add hspace' (by simpa only [Real.dist_eq] using htime)
    _ ≤ (L * Real.exp (K * T)) * dist (x, t) (y, u) +
        B * dist (x, t) (y, u) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
      · exact mul_le_mul_of_nonneg_left (le_max_right _ _) B.coe_nonneg
    _ = _ := by
      change _ = ((L : ℝ) * Real.exp (K * T) + B) * dist (x, t) (y, u)
      ring

variable [NormedSpace ℝ P]

/-- `app:ch_regular_base:lem:buffered-interpolation`: the joint `C¹` budget on
an inner parameter ball and closed time interval. The strict radius and time
inequalities keep this box inside the open domain where the genuine ODE holds.
The bound has derivative loss zero and depends only on low-order data. -/
theorem autonomousFlow_cNorm_one_le
    {V : E → E} {σ : P → E} {Φ : P × ℝ → E} {U : Set E}
    {z : P} {ρ R a b α β t₀ T M : ℝ} {K L B : ℝ≥0}
    (hρ : ρ < R) (ha : a < α) (hb : β < b)
    (ht₀ : t₀ ∈ Ioo a b) (hT : ∀ t ∈ Ioo a b, |t - t₀| ≤ T)
    (hM : 0 ≤ M) (hUM : ∀ y ∈ U, ‖y‖ ≤ M)
    (hV : LipschitzOnWith K V U) (hVB : ∀ y ∈ U, ‖V y‖ ≤ B)
    (hσ : LipschitzOnWith L σ (ball z R))
    (hinit : ∀ x ∈ ball z R, Φ (x, t₀) = σ x)
    (hode : ∀ x ∈ ball z R, ∀ t ∈ Ioo a b,
      HasDerivAt (fun τ ↦ Φ (x, τ)) (V (Φ (x, t))) t)
    (hrange : ∀ x ∈ ball z R, ∀ t ∈ Ioo a b, Φ (x, t) ∈ U) :
    cNorm (closedBall z ρ ×ˢ Icc α β) 1 Φ ≤ M + (L * Real.exp (K * T) + B) := by
  have hLip := autonomousFlow_joint_lipschitzOn ht₀ hT hV hVB hσ hinit hode hrange
  have hsub : closedBall z ρ ×ˢ Icc α β ⊆ ball z R ×ˢ Ioo a b := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    exact ⟨closedBall_subset_ball hρ hx, ha.trans_le ht.1, ht.2.trans_lt hb⟩
  have hbound := CompositionBounds.cNorm_le_sum
    (s := closedBall z ρ ×ˢ Icc α β) (r := 1) (f := Φ)
    (B := fun j ↦ if j = 0 then M else L * Real.exp (K * T) + B)
    (by intro j _; split_ifs <;> positivity) (by
      intro j hj p hp
      have hp' := hsub hp
      interval_cases j
      · simpa only [norm_iteratedFDeriv_zero, ↓reduceIte] using hUM _ (hrange _ hp'.1 _ hp'.2)
      · simp only [norm_iteratedFDeriv_one, Nat.one_ne_zero, ↓reduceIte]
        exact norm_fderiv_le_of_lipschitzOn ℝ
          ((isOpen_ball.prod isOpen_Ioo).mem_nhds hp') hLip)
  simpa [Finset.sum_range_succ] using hbound

/-- `app:lem:common-hamilton-phase`: the joint low-order flow budget directly
from `C¹` vector-field and initial-section data on buffered convex domains.
The Lipschitz hypotheses of `autonomousFlow_cNorm_one_le` are discharged by
the first derivative bounds, so every quantitative input concerns the field,
the initial section, or the containing state domain. -/
theorem autonomousFlow_cNorm_one_le_of_fderiv_le
    {V : E → E} {σ : P → E} {Φ : P × ℝ → E} {U : Set E}
    {z : P} {ρ R a b α β t₀ T M : ℝ} {K L B : ℝ≥0}
    (hρ : ρ < R) (ha : a < α) (hb : β < b)
    (ht₀ : t₀ ∈ Ioo a b) (hT : ∀ t ∈ Ioo a b, |t - t₀| ≤ T)
    (hM : 0 ≤ M) (hUM : ∀ y ∈ U, ‖y‖ ≤ M)
    (hU : IsOpen U) (hUc : Convex ℝ U)
    (hV : ContDiffOn ℝ 1 V U) (hVK : ∀ y ∈ U, ‖fderiv ℝ V y‖ ≤ K)
    (hVB : ∀ y ∈ U, ‖V y‖ ≤ B)
    (hσ : ContDiffOn ℝ 1 σ (ball z R))
    (hσL : ∀ x ∈ ball z R, ‖fderiv ℝ σ x‖ ≤ L)
    (hinit : ∀ x ∈ ball z R, Φ (x, t₀) = σ x)
    (hode : ∀ x ∈ ball z R, ∀ t ∈ Ioo a b,
      HasDerivAt (fun τ ↦ Φ (x, τ)) (V (Φ (x, t))) t)
    (hrange : ∀ x ∈ ball z R, ∀ t ∈ Ioo a b, Φ (x, t) ∈ U) :
    cNorm (closedBall z ρ ×ˢ Icc α β) 1 Φ ≤ M + (L * Real.exp (K * T) + B) := by
  apply autonomousFlow_cNorm_one_le hρ ha hb ht₀ hT hM hUM _ hVB _ hinit hode hrange
  · exact hUc.lipschitzOnWith_of_nnnorm_fderiv_le
      (fun y hy ↦ (hV.contDiffAt (hU.mem_nhds hy)).differentiableAt one_ne_zero)
      (fun y hy ↦ by exact_mod_cast hVK y hy)
  · exact (convex_ball z R).lipschitzOnWith_of_nnnorm_fderiv_le
      (fun x hx ↦ (hσ.contDiffAt (isOpen_ball.mem_nhds hx)).differentiableAt one_ne_zero)
      (fun x hx ↦ by exact_mod_cast hσL x hx)

/-- `app:ch_regular_base:lem:buffered-interpolation`: the Gronwall induction
step used by `exists_autonomousFlow_spatial_jet_bound`, in both time directions.
The public theorem below discharges the forcing premise. -/
private theorem autonomousFlow_jet_le_of_forcing
    {U : Set P} (hU : IsOpen U) {a b t₀ T K H ε : ℝ}
    (hK : 0 ≤ K) (hH : 0 ≤ H) (hε : 0 ≤ ε)
    (ht₀ : t₀ ∈ Ioo a b) {t : ℝ} (ht : t ∈ Ioo a b) (hT : |t - t₀| ≤ T)
    {Φ : P × ℝ → E} (hΦ : ContDiffOn ℝ ∞ Φ (U ×ˢ Ioo a b))
    {V : E → E} {n : ℕ} (hn : 0 < n) {x : P} (hx : x ∈ U)
    (hode : ∀ y ∈ U, ∀ τ ∈ Ioo a b,
      HasDerivAt (fun s ↦ Φ (y, s)) (V (Φ (y, τ))) τ)
    (hV : ∀ τ ∈ uIcc t₀ t, ContDiffAt ℝ n V (Φ (x, τ)))
    (hVK : ∀ τ ∈ uIcc t₀ t, ‖fderiv ℝ V (Φ (x, τ))‖ ≤ K)
    (hinit : ‖iteratedFDeriv ℝ n (fun y ↦ Φ (y, t₀)) x‖ ≤ H)
    (hR : ∀ τ ∈ uIcc t₀ t,
      ‖ODE.jetPartitionRemainder n V (fun y ↦ Φ (y, τ)) x‖ ≤ ε * H) :
    ‖iteratedFDeriv ℝ n (fun y ↦ Φ (y, t)) x‖ ≤
      gronwallBound 1 K ε T * H := by
  have hseg := ordConnected_Ioo.uIcc_subset ht₀ ht
  have h := ODE.norm_le_gronwallBound_of_hasDerivAt_uIcc
    (fun τ hτ ↦ ODE.hasDerivAt_iteratedFDeriv_top_add_jetPartitionRemainder
      hU hΦ hode hn hx (hseg hτ) (hV τ hτ)) hinit (fun τ hτ ↦ by
      exact (norm_add_le _ _).trans (add_le_add
        (((fderiv ℝ V (Φ (x, τ))).norm_compContinuousMultilinearMap_le _).trans
          (mul_le_mul_of_nonneg_right (hVK τ hτ) (norm_nonneg _))) (hR τ hτ)))
  calc
    _ ≤ gronwallBound H K (ε * H) |t - t₀| := h
    _ ≤ gronwallBound H K (ε * H) T :=
      gronwallBound_mono hH (mul_nonneg hε hH) hK hT
    _ = gronwallBound 1 K ε T * H := by simpa using gronwallBound_mul 1 K ε H T

variable [FiniteDimensional ℝ P] [FiniteDimensional ℝ E]

/-- `app:ch_regular_base:lem:buffered-interpolation`: genuine flows have spatial
jet bounds linear in the field and initial-section norms of the same order.
The constant is chosen before the maps. Strong induction discharges every
lower-jet input to the baseline-one forcing estimate. The time interval may
extend on both sides of the initial time. The derivative-order shift is zero. -/
theorem exists_autonomousFlow_spatial_jet_bound
    (z : P) (w : E) {ρ τ : ℝ} (hρ : 0 < ρ) (hτ : 0 < τ)
    {U : Set P} {W : Set E} (hU : IsOpen U) (hW : IsOpen W)
    (hz : closedBall z ρ ⊆ U) (hw : closedBall w τ ⊆ W)
    {a b t₀ T M N : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    (hT : ∀ t ∈ Ioo a b, |t - t₀| ≤ T) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : E → E) (σ : P → E) (Φ : P × ℝ → E),
      ContDiffOn ℝ ∞ V W → ContDiffOn ℝ ∞ σ U →
      ContDiffOn ℝ ∞ Φ (U ×ˢ Ioo a b) →
      cNorm (closedBall w τ) 1 V ≤ M → cNorm (closedBall z ρ) 1 σ ≤ N →
      (∀ x ∈ U, Φ (x, t₀) = σ x) →
      (∀ x ∈ U, ∀ t ∈ Ioo a b,
        HasDerivAt (fun s ↦ Φ (x, s)) (V (Φ (x, t))) t) →
      (∀ x ∈ closedBall z ρ, ∀ t ∈ Ioo a b, Φ (x, t) ∈ closedBall w τ) →
      ∀ x ∈ closedBall z ρ, ∀ t ∈ Ioo a b,
        ‖iteratedFDeriv ℝ n (fun y ↦ Φ (y, t)) x‖ ≤
          C * (1 + cNorm (closedBall w τ) n V + cNorm (closedBall z ρ) n σ) := by
  classical
  induction n using Nat.strong_induction_on with | h n ih =>
  have hT0 : 0 ≤ T := (abs_nonneg _).trans (hT t₀ ht₀)
  by_cases hn0 : n = 0
  · subst n
    refine ⟨1 + ‖w‖ + τ, by positivity, ?_⟩
    intro V σ Φ _ _ _ _ _ _ _ hrange x hx t ht
    rw [norm_iteratedFDeriv_zero]
    have hr := mem_closedBall.mp (hrange x hx t ht)
    have hnorm : ‖Φ (x, t)‖ ≤ ‖w‖ + τ := by
      have := norm_le_insert w (Φ (x, t))
      rw [← dist_eq_norm, dist_comm w] at this
      linarith
    have hv := cNorm_nonneg (closedBall w τ) 0 V
    have hs := cNorm_nonneg (closedBall z ρ) 0 σ
    nlinarith [norm_nonneg w]
  have hn : 0 < n := Nat.pos_of_ne_zero hn0
  choose A hA hAb using fun j : Fin n ↦ ih j j.isLt
  let A' : ℕ → ℝ := fun j ↦ if hj : j < n then A ⟨j, hj⟩ else 0
  have hA' (j : ℕ) : 0 ≤ A' j := by
    dsimp [A']; split_ifs with hj
    · exact (hA ⟨j, hj⟩).le
    · exact le_rfl
  have hforce : ∃ ε : ℝ, 0 ≤ ε ∧ ∀ (V : E → E) (σ : P → E),
      ContDiffOn ℝ ∞ V W → ContDiffOn ℝ ∞ σ U →
      cNorm (closedBall w τ) 1 V ≤ M → cNorm (closedBall z ρ) 1 σ ≤ N →
      ∀ (f : P → E) (x : P), f x ∈ closedBall w τ →
      (∀ j, 1 ≤ j → j < n → ‖iteratedFDeriv ℝ j f x‖ ≤
        A' j * (1 + cNorm (closedBall w τ) j V + cNorm (closedBall z ρ) j σ)) →
      ‖ODE.jetPartitionRemainder n V f x‖ ≤
        ε * (1 + cNorm (closedBall w τ) n V + cNorm (closedBall z ρ) n σ) := by
    by_cases hn1 : n = 1
    · subst n
      exact ⟨0, le_rfl, fun _ _ _ _ _ _ _ _ _ _ ↦ by
        simp only [ODE.jetPartitionRemainder_one, norm_zero, zero_mul, le_refl]⟩
    · obtain ⟨ε, hε, hb⟩ := FlowForcing.exists_forcingSum_le_closedBall_on
        z w hρ hτ hU hW hz hw (by omega : 2 ≤ n) hM hN A' hA'
      exact ⟨ε, hε.le, fun V σ hV hσ hVM hσN f x hx hj ↦
        (ODE.norm_jetPartitionRemainder_le n V f x).trans (hb V σ hV hσ hVM hσN f x hx hj)⟩
  obtain ⟨ε, hε, hforce⟩ := hforce
  have hG : 0 ≤ gronwallBound 1 M ε T := gronwallBound_nonneg (by positivity) hM hε hT0
  refine ⟨1 + gronwallBound 1 M ε T, by positivity, ?_⟩
  intro V σ Φ hV hσ hΦ hVM hσN hinit hode hrange x hx t ht
  have hσjet : ‖iteratedFDeriv ℝ n (fun y ↦ Φ (y, t₀)) x‖ ≤
      cNorm (closedBall z ρ) n σ := by
    have heq : (fun y ↦ Φ (y, t₀)) =ᶠ[𝓝 x] σ :=
      Filter.eventuallyEq_iff_exists_mem.mpr ⟨U, hU.mem_nhds (hz hx), hinit⟩
    rw [(heq.iteratedFDeriv ℝ n).eq_of_nhds]
    exact norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall z ρ)
      (fun y hy ↦ (hσ.contDiffAt (hU.mem_nhds (hz hy))).of_le (by simp)) hx le_rfl
  have hVK (s : ℝ) (hs : s ∈ Ioo a b) : ‖fderiv ℝ V (Φ (x, s))‖ ≤ M := by
    rw [← norm_iteratedFDeriv_one]
    exact (norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall w τ)
      (fun y hy ↦ (hV.contDiffAt (hW.mem_nhds (hw hy))).of_le (by simp))
      (hrange x hx s hs) (le_refl 1)).trans hVM
  have hH : 0 ≤ 1 + cNorm (closedBall w τ) n V + cNorm (closedBall z ρ) n σ := by
    linarith [cNorm_nonneg (closedBall w τ) n V, cNorm_nonneg (closedBall z ρ) n σ]
  have hb := autonomousFlow_jet_le_of_forcing hU hM hH hε ht₀ ht (hT t ht) hΦ hn
    (hz hx) hode
    (fun s hs ↦ (hV.contDiffAt (hW.mem_nhds (hw
      (hrange x hx s (ordConnected_Ioo.uIcc_subset ht₀ ht hs))))).of_le (by simp))
    (fun s hs ↦ hVK s (ordConnected_Ioo.uIcc_subset ht₀ ht hs))
    (hσjet.trans (by linarith [cNorm_nonneg (closedBall w τ) n V]))
    (fun s hs ↦ hforce V σ hV hσ hVM hσN (fun y ↦ Φ (y, s)) x
      (hrange x hx s (ordConnected_Ioo.uIcc_subset ht₀ ht hs)) (by
        intro j _ hj
        simpa only [A', dite_eq_left hj] using
          hAb ⟨j, hj⟩ V σ Φ hV hσ hΦ hVM hσN hinit hode hrange x hx s
            (ordConnected_Ioo.uIcc_subset ht₀ ht hs)))
  exact hb.trans (mul_le_mul_of_nonneg_right (by linarith) hH)

/-- `app:ch_regular_base:lem:buffered-interpolation`: summing the genuine spatial
jet bounds gives a uniform fixed-time `Cⁿ` estimate. The coefficient is independent
of the high norms, all lower-jet hypotheses have been discharged, and the order
shift is zero. The containing open domains supply explicit spatial buffers. -/
theorem exists_autonomousFlow_spatial_cNorm_bound
    (z : P) (w : E) {ρ τ : ℝ} (hρ : 0 < ρ) (hτ : 0 < τ)
    {U : Set P} {W : Set E} (hU : IsOpen U) (hW : IsOpen W)
    (hz : closedBall z ρ ⊆ U) (hw : closedBall w τ ⊆ W)
    {a b t₀ T M N : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    (hT : ∀ t ∈ Ioo a b, |t - t₀| ≤ T) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : E → E) (σ : P → E) (Φ : P × ℝ → E),
      ContDiffOn ℝ ∞ V W → ContDiffOn ℝ ∞ σ U →
      ContDiffOn ℝ ∞ Φ (U ×ˢ Ioo a b) →
      cNorm (closedBall w τ) 1 V ≤ M → cNorm (closedBall z ρ) 1 σ ≤ N →
      (∀ x ∈ U, Φ (x, t₀) = σ x) →
      (∀ x ∈ U, ∀ t ∈ Ioo a b,
        HasDerivAt (fun s ↦ Φ (x, s)) (V (Φ (x, t))) t) →
      (∀ x ∈ closedBall z ρ, ∀ t ∈ Ioo a b, Φ (x, t) ∈ closedBall w τ) →
      ∀ t ∈ Ioo a b, cNorm (closedBall z ρ) n (fun y ↦ Φ (y, t)) ≤
        C * (1 + cNorm (closedBall w τ) n V + cNorm (closedBall z ρ) n σ) := by
  choose C hC hbound using
    exists_autonomousFlow_spatial_jet_bound z w hρ hτ hU hW hz hw ht₀ hT hM hN
  have hsum : 0 ≤ ∑ j ∈ Finset.range (n + 1), C j :=
    Finset.sum_nonneg fun j _ ↦ (hC j).le
  refine ⟨1 + ∑ j ∈ Finset.range (n + 1), C j, by positivity, ?_⟩
  intro V σ Φ hV hσ hΦ hVM hσN hinit hode hrange t ht
  have hH : 0 ≤ 1 + cNorm (closedBall w τ) n V + cNorm (closedBall z ρ) n σ := by
    linarith [cNorm_nonneg (closedBall w τ) n V, cNorm_nonneg (closedBall z ρ) n σ]
  calc
    _ ≤ ∑ j ∈ Finset.range (n + 1), C j *
        (1 + cNorm (closedBall w τ) n V + cNorm (closedBall z ρ) n σ) := by
      apply CompositionBounds.cNorm_le_sum (fun j _ ↦ mul_nonneg (hC j).le hH)
      intro j hj x hx
      apply (hbound j V σ Φ hV hσ hΦ hVM hσN hinit hode hrange x hx t ht).trans
      apply mul_le_mul_of_nonneg_left _ (hC j).le
      exact add_le_add (add_le_add_right (cNorm_mono_order hj) 1) (cNorm_mono_order hj)
    _ = (∑ j ∈ Finset.range (n + 1), C j) *
        (1 + cNorm (closedBall w τ) n V + cNorm (closedBall z ρ) n σ) :=
      (Finset.sum_mul ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hH

/-- `app:ch_regular_base:lem:buffered-interpolation` and
`app:lem:common-hamilton-phase`: a genuine autonomous flow with variable initial
section has one-high joint time/parameter bounds at every order. The inner box
is `closedBall z ρ × Icc (t₀ - l * ρ) (t₀ + l * ρ)`; its explicit outer buffer
is `ball z R × Ioo (t₀ - l * q * R) (t₀ + l * q * R)`, with `ρ < R` and `1 < q`.
The state ball lies in the open smoothness domain `W`.

The constant is quantified before the field, section and flow, and depends only
on the order, geometry, time scale and fixed `C¹` bounds `M,N`. The high norms
occur linearly at order `n`, so the derivative-order shift is zero, independently
of `n`. All variational, forcing and lower-jet premises are discharged by the
spatial theorem applied to the actual time-rescaled autonomous flow. This is
an estimate for a given smooth flow; it does not assert flow existence. -/
theorem exists_autonomousFlow_joint_cNorm_bound
    (z : P) (w : E) {ρ R τ l q : ℝ}
    (hρ : 0 < ρ) (hρR : ρ < R) (hτ : 0 < τ) (hl : 0 < l) (hq : 1 < q)
    {W : Set E} (hW : IsOpen W) (hw : closedBall w τ ⊆ W)
    (t₀ : ℝ) {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : E → E) (σ : P → E) (Φ : P × ℝ → E),
      ContDiffOn ℝ ∞ V W → ContDiffOn ℝ ∞ σ (ball z R) →
      ContDiffOn ℝ ∞ Φ
        (ball z R ×ˢ Ioo (t₀ - l * q * R) (t₀ + l * q * R)) →
      cNorm (closedBall w τ) 1 V ≤ M → cNorm (closedBall z ρ) 1 σ ≤ N →
      (∀ x ∈ ball z R, Φ (x, t₀) = σ x) →
      (∀ x ∈ ball z R, ∀ t ∈ Ioo (t₀ - l * q * R) (t₀ + l * q * R),
        HasDerivAt (fun s ↦ Φ (x, s)) (V (Φ (x, t))) t) →
      (∀ x ∈ closedBall z ρ, ∀ t ∈ Ioo (t₀ - l * q * R) (t₀ + l * q * R),
        Φ (x, t) ∈ closedBall w τ) →
      cNorm (closedBall z ρ ×ˢ Icc (t₀ - l * ρ) (t₀ + l * ρ)) n Φ ≤
        C * (1 + cNorm (closedBall w τ) n V + cNorm (closedBall z ρ) n σ) := by
  let c := τ / ρ
  have hc : 0 < c := div_pos hτ hρ
  have hcρ : c * ρ ≤ τ := le_of_eq (div_mul_cancel₀ τ hρ.ne')
  obtain ⟨A₁, hA₁, hfield₁⟩ := TimeRescaling.exists_cNorm_field_bound w hτ l c 1
  obtain ⟨B₁, hB₁, hsection₁⟩ :=
    TimeRescaling.exists_cNorm_sectionMap_bound (E := E) z hρ c 1
  obtain ⟨A, hA, hfield⟩ := TimeRescaling.exists_cNorm_field_bound w hτ l c n
  obtain ⟨B, hB, hsection⟩ :=
    TimeRescaling.exists_cNorm_sectionMap_bound (E := E) z hρ c n
  have hq₀ : 0 < q := zero_lt_one.trans hq
  have hw' : closedBall (w, (0 : ℝ)) τ ⊆ W ×ˢ univ := by
    intro y hy
    refine ⟨hw ?_, mem_univ _⟩
    exact (show dist y.1 w ≤ dist y (w, 0) by
      rw [Prod.dist_eq]; exact le_max_left _ _).trans hy
  obtain ⟨D, hD, hspatial⟩ := exists_autonomousFlow_spatial_cNorm_bound
    (z, (0 : ℝ)) (w, (0 : ℝ)) hρ hτ isOpen_ball (hW.prod isOpen_univ)
    (closedBall_subset_ball hρR) hw'
    (show (0 : ℝ) ∈ Ioo (-q) q by constructor <;> linarith)
    (show ∀ u ∈ Ioo (-q) q, |u - 0| ≤ q by
      intro u hu; simpa only [sub_zero] using (abs_lt.mpr hu).le)
    (show 0 ≤ A₁ * (1 + M) by positivity)
    (show 0 ≤ B₁ * (1 + N) by positivity) n
  let K := (max 1 |l⁻¹|) ^ n
  have hK : 0 < K := pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) n
  refine ⟨K * D * (1 + A + B), by positivity, ?_⟩
  intro V σ Φ hV hσ hΦ hVM hσN hinit hode hrange
  have haug := hspatial (TimeRescaling.field l c V) (TimeRescaling.sectionMap c σ)
    (TimeRescaling.flow t₀ l c Φ)
    (TimeRescaling.contDiffOn_field hV l c)
    (TimeRescaling.contDiffOn_sectionMap hσ c)
    (TimeRescaling.contDiffOn_flow hl hq₀ hΦ)
    ((hfield₁ V W hW hw hV).trans
      (mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) hVM) hA₁.le))
    ((hsection₁ σ (ball z R) isOpen_ball (closedBall_subset_ball hρR) hσ).trans
      (mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) hσN) hB₁.le))
    (fun _ hx ↦ TimeRescaling.flow_initial hinit hx)
    (fun _ hx _ ht ↦ TimeRescaling.hasDerivAt_flow hl hq₀ hc.ne' hode hx ht)
    (fun _ hx _ ht ↦ TimeRescaling.flow_mem_closedBall hρR hl hq₀ hc.le hcρ hrange hx ht)
    1 (by constructor <;> linarith)
  have hhigh : 1 + cNorm (closedBall (w, (0 : ℝ)) τ) n (TimeRescaling.field l c V) +
      cNorm (closedBall (z, (0 : ℝ)) ρ) n (TimeRescaling.sectionMap c σ) ≤
      (1 + A + B) *
        (1 + cNorm (closedBall w τ) n V + cNorm (closedBall z ρ) n σ) := by
    have ha := hfield V W hW hw hV
    have hb := hsection σ (ball z R) isOpen_ball (closedBall_subset_ball hρR) hσ
    have hv := cNorm_nonneg (closedBall w τ) n V
    have hs := cNorm_nonneg (closedBall z ρ) n σ
    nlinarith
  calc
    _ ≤ K * cNorm (closedBall (z, 0) ρ) n
        (fun p ↦ TimeRescaling.flow t₀ l c Φ (p, 1)) :=
      TimeRescaling.cNorm_flow_recover_le z hρ hρR hq hl t₀ c n hΦ
    _ ≤ K * (D * (1 +
        cNorm (closedBall (w, (0 : ℝ)) τ) n (TimeRescaling.field l c V) +
        cNorm (closedBall (z, (0 : ℝ)) ρ) n (TimeRescaling.sectionMap c σ))) :=
      mul_le_mul_of_nonneg_left haug hK.le
    _ ≤ K * (D * ((1 + A + B) *
        (1 + cNorm (closedBall w τ) n V + cNorm (closedBall z ρ) n σ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hhigh hD.le) hK.le
    _ = _ := by ring


end JanetCartan.HamiltonPhase
