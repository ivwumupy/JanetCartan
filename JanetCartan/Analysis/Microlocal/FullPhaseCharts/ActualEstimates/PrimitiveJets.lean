module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.ActualPhaseBounds
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseEstimates.Identifications

/-!
# Primitive budgets for the actual quotient-chart inverse estimates

The primitive inputs of `InverseEstimates.exists_carrierQuotient_inverse_epsilon_oneHigh`
are proved here for the SAME `T.currentChart`. The low phase bound follows from
finite-order continuity, independently of high immersion norms. The high phase
bound retains immersion order `m+3`. The carrier and direction are frozen, so
all their norms belong to the fixed constants in
`app:ch_seed:prop:seed-phase-charts`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.FullPhaseCharts.ActualEstimates
open ActualCarriers ActualCarriers.CurrentFullPhase FrozenMenu ActualPhase ProjectedStressFrame

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- A fixed primitive `C³` phase bound from the paper's frame `C⁶`
neighborhood. The threshold and bound precede the current frame; no high
immersion norm enters (`app:ch_seed:prop:seed-phase-charts`). -/
theorem exists_current_low_bound :
    ∃ δ > (0 : ℝ), ∃ N > (0 : ℝ), ∀ Q,
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress n) < δ →
      cNorm (closedBall (0, covectorCenter T) T.family.radius) 3 (current T Q) ≤ N := by
  let K := closedBall ((0 : WithLp 2 (ℝ × Euclidean (n - 1))), covectorCenter T) T.family.radius
  let S₀ := Comparison.referencePhase (dispersion T)
  obtain ⟨δ, hδ, hclose⟩ := exists_current_comparison_threshold T 3 (by norm_num : (0 : ℝ) < 1)
  refine ⟨δ, hδ, 1 + cNorm K 3 S₀, by linarith [cNorm_nonneg K 3 S₀], ?_⟩
  intro Q hQ
  have hc := hclose Q ((cNorm_mono_order (by omega : 3 + 1 ≤ 6)).trans_lt hQ) K Subset.rfl
  have hK : K ⊆ ball (0, covectorCenter T) (2 * T.family.radius) :=
    closedBall_subset_ball (by linarith [T.family.radius_pos])
  have hS₀ : ContDiffOn ℝ ∞ S₀ (ball (0, covectorCenter T) (2 * T.family.radius)) :=
    (reference_smooth T).congr (fun _ h ↦ (reference_eq_affine T h).symm)
  have hs (x) (hx : x ∈ K) : ContDiffAt ℝ (3 : ℕ) (current T Q) x :=
    ((current_smooth T Q).contDiffAt (isOpen_ball.mem_nhds (hK hx))).of_le (by simp)
  have hr (x) (hx : x ∈ K) : ContDiffAt ℝ (3 : ℕ) S₀ x :=
    (hS₀.contDiffAt (isOpen_ball.mem_nhds (hK hx))).of_le (by simp)
  have hb := cNorm_add_le_of_contDiffAt (isCompact_closedBall _ _)
    (fun x hx ↦ (hs x hx).sub (hr x hx)) hr
  change cNorm K 3 ((current T Q - S₀) + S₀) ≤ cNorm K 3 (current T Q - S₀) + cNorm K 3 S₀ at hb
  rw [sub_add_cancel] at hb
  exact hb.trans (by linarith)

/-- Forget the adjoined full-chart spectators and data in the primitive phase.
This is the literal phase in `carrierQuotientChart_eq_fullChartFamily`
(`app:ch_seed:prop:seed-phase-charts`). -/
def fullPhaseProjection :
    (((Euclidean 2 × (ℝ × Euclidean (n - 1))) ×
      WithLp 2 (ℝ × Euclidean (n - 1))) × Euclidean (n - 1)) →L[ℝ]
      (WithLp 2 (ℝ × Euclidean (n - 1)) × Euclidean (n - 1)) :=
  ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.fst ℝ _ _)).prod
    (ContinuousLinearMap.snd ℝ _ _)

/-- The transverse primitive phase retains time among the spectators
(`app:ch_seed:prop:seed-phase-charts`). -/
def transversePhaseProjection :
    ((((Euclidean 2 × ℝ × ℝ) × Euclidean (n - 1)) × Euclidean (n - 1)) ×
      Euclidean (n - 1)) →L[ℝ]
      (WithLp 2 (ℝ × Euclidean (n - 1)) × Euclidean (n - 1)) :=
  LinearMap.toContinuousLinearMap {
    toFun := fun q ↦ (WithLp.toLp 2 (q.1.1.1.2.1, q.1.2), q.2)
    map_add' := by intro a b; rfl
    map_smul' := by intro a b; rfl }

/-- The literal full phase projection is a contraction. -/
theorem norm_fullPhaseProjection_le : ‖fullPhaseProjection (n := n)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro q
  change max ‖q.1.2‖ ‖q.2‖ ≤ 1 * ‖q‖
  rw [one_mul]
  exact max_le ((norm_snd_le q.1).trans (norm_fst_le q)) (norm_snd_le q)

/-- Combining time and transverse space costs at most two in operator norm,
with no derivative loss. -/
theorem norm_transversePhaseProjection_le : ‖transversePhaseProjection (n := n)‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro q
  change max ‖WithLp.toLp 2 (q.1.1.1.2.1, q.1.2)‖ ‖q.2‖ ≤ 2 * ‖q‖
  have ht := (norm_fst_le q.1.1.1.2).trans ((norm_snd_le q.1.1.1).trans
    ((norm_fst_le q.1.1).trans ((norm_fst_le q.1).trans (norm_fst_le q))))
  have hy := (norm_snd_le q.1).trans (norm_fst_le q)
  have hh := norm_add_le (WithLp.toLp 2 (q.1.1.1.2.1, (0 : Euclidean (n - 1))))
    (WithLp.toLp 2 ((0 : ℝ), q.1.2))
  have he : WithLp.toLp 2 (q.1.1.1.2.1, (0 : Euclidean (n - 1))) +
      WithLp.toLp 2 ((0 : ℝ), q.1.2) = WithLp.toLp 2 (q.1.1.1.2.1, q.1.2) := by
    apply WithLp.ofLp_injective
    simp
  rw [he] at hh
  simp only [WithLp.norm_toLp_fst, WithLp.norm_toLp_snd] at hh
  exact max_le (by linarith) (by linarith [norm_snd_le q, norm_nonneg q])

private theorem cNorm_phase_projection_le
    {A : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (L : A →L[ℝ] (WithLp 2 (ℝ × Euclidean (n - 1)) × Euclidean (n - 1)))
    {d : ℝ} (hd : 1 ≤ d) (hL : ‖L‖ ≤ d) (Q : _) {K : Set A}
    (hK : MapsTo L K (closedBall (0, covectorCenter T) T.family.radius)) (m : ℕ) :
    cNorm K m (current T Q ∘ L) ≤
      ((m + 1 : ℝ) * d ^ m) *
        cNorm (closedBall (0, covectorCenter T) T.family.radius) m (current T Q) := by
  let J := closedBall ((0 : WithLp 2 (ℝ × Euclidean (n - 1))), covectorCenter T) T.family.radius
  have hJ : J ⊆ ball (0, covectorCenter T) (2 * T.family.radius) :=
    closedBall_subset_ball (by linarith [T.family.radius_pos])
  have hb : ∀ j ≤ m, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ j (current T Q ∘ L) x‖ ≤
        d ^ m * cNorm J m (current T Q) := by
    intro j hj x hx
    apply (NormalComparison.norm_iteratedFDeriv_comp_linear_on_open_le L isOpen_ball
      (current_smooth T Q) (hJ (hK hx)) j).trans
    rw [mul_comm]
    apply mul_le_mul
    · exact (pow_le_pow_left₀ (norm_nonneg _) hL _).trans (pow_le_pow_right₀ hd hj)
    · exact norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall _ _)
        (fun y hy ↦ ((current_smooth T Q).contDiffAt
          (isOpen_ball.mem_nhds (hJ hy))).of_le (by simp)) (hK hx) hj
    · exact norm_nonneg _
    · positivity
  have hh := cNorm_le_sum_of_bounds
    (fun _ _ ↦ mul_nonneg (pow_nonneg (by linarith : 0 ≤ d) _) (cNorm_nonneg _ _ _)) hb
  simpa [mul_assoc] using hh

/-- Primitive full-phase jets, including all adjoined parameters, are bounded
by the actual phase jets at the SAME order. -/
theorem cNorm_fullPhase_le (Q : _) {K : Set
    (((Euclidean 2 × (ℝ × Euclidean (n - 1))) ×
      WithLp 2 (ℝ × Euclidean (n - 1))) × Euclidean (n - 1))}
    (hK : MapsTo fullPhaseProjection K
      (closedBall (0, covectorCenter T) T.family.radius)) (m : ℕ) :
    cNorm K m (fun q ↦ current T Q (q.1.2, q.2)) ≤ (m + 1 : ℝ) *
      cNorm (closedBall (0, covectorCenter T) T.family.radius) m (current T Q) := by
  simpa [fullPhaseProjection, Function.comp_def] using cNorm_phase_projection_le T fullPhaseProjection (le_refl 1)
    norm_fullPhaseProjection_le Q hK m

/-- The transverse primitive phase has the same derivative order as the
actual phase, retaining time, scalar carrier and spectator derivatives. -/
theorem cNorm_transversePhase_le (Q : _) {K : Set
    ((((Euclidean 2 × ℝ × ℝ) × Euclidean (n - 1)) × Euclidean (n - 1)) ×
      Euclidean (n - 1))}
    (hK : MapsTo transversePhaseProjection K
      (closedBall (0, covectorCenter T) T.family.radius)) (m : ℕ) :
    cNorm K m (fun q ↦ current T Q (WithLp.toLp 2 (q.1.1.1.2.1, q.1.2), q.2)) ≤
      ((m + 1 : ℝ) * 2 ^ m) *
        cNorm (closedBall (0, covectorCenter T) T.family.radius) m (current T Q) :=
  cNorm_phase_projection_le T transversePhaseProjection (by norm_num)
    norm_transversePhaseProjection_le Q hK m

end JanetCartan.FullPhaseCharts.ActualEstimates
