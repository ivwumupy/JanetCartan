module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.FlowFamily.Geometry
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseEstimates.FiberBounds
public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.InputJets.Base

/-!
# Joint projection budgets on fixed two-time balls

For `app:ch_regular_base:lem:characteristic-kernel`, a fixed linear substitution
passes the actual autonomous-flow estimates to both original times. The spatial
projection retains the other coordinates linearly. Consequently its budgets
remain single-high, with reserve one in the scalar root. The second-order bound
is the input for choosing a common inverse radius from the diagonal shear.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff Topology

namespace JanetCartan.RegularSector.Characteristic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local instance twoTimeProjectionJetsNormedSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace

/-- The fixed linear substitution `(t,s,y,η) ↦ ((s,y,η),t-s)` used by the
two-time flow (`app:ch_regular_base:lem:characteristic-kernel`). -/
def twoTimeFlowArguments : TwoTimePoint E →L[ℝ] RootState E × ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ (RootState E)).prod
    (ContinuousLinearMap.fst ℝ ℝ (RootState E) -
      (ContinuousLinearMap.fst ℝ ℝ (E × E)).comp
        (ContinuousLinearMap.snd ℝ ℝ (RootState E)))

/-- The two original times cost at most a factor two in the fixed linear
change of variables (`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem norm_twoTimeFlowArguments_le : ‖twoTimeFlowArguments (E := E)‖ ≤ 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) ?_
  intro q
  change max ‖q.2‖ ‖q.1 - q.2.1‖ ≤ 2 * ‖q‖
  have ht := norm_fst_le q
  have hs := (norm_fst_le q.2).trans (norm_snd_le q)
  have hw := norm_snd_le q
  exact max_le (by linarith [norm_nonneg q]) ((norm_sub_le _ _).trans (by linarith))

/-- A prescribed two-time ball maps into the fixed inner autonomous cylinder.
This supplies a common compact buffer before the root is chosen
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem twoTimeFlowArguments_mapsTo_cylinder (z : RootState E) {R T ρ : ℝ}
    (hρR : 2 * ρ ≤ R / 4) (hρT : 2 * ρ ≤ T / 4) :
    MapsTo (twoTimeFlowArguments (E := E)) (closedBall (z.1, z) ρ)
      (closedBall z (R / 4) ×ˢ Icc (-T / 4) (T / 4)) := by
  intro q hq
  have hd : dist (twoTimeFlowArguments q) (twoTimeFlowArguments (z.1, z)) ≤ 2 * ρ := by
    calc
      _ ≤ ‖twoTimeFlowArguments (E := E)‖ * dist q (z.1, z) :=
        (twoTimeFlowArguments (E := E)).lipschitzWith.dist_le_mul _ _
      _ ≤ 2 * ρ := mul_le_mul norm_twoTimeFlowArguments_le hq (dist_nonneg) (by norm_num)
  change max (dist q.2 z) (dist (q.1 - q.2.1) (z.1 - z.1)) ≤ 2 * ρ at hd
  have hx := (le_max_left _ _).trans hd
  have ht := (le_max_right _ _).trans hd
  simp only [sub_self, dist_zero_right, Real.norm_eq_abs] at ht
  refine ⟨hx.trans hρR, ?_⟩
  change -T / 4 ≤ q.1 - q.2.1 ∧ q.1 - q.2.1 ≤ T / 4
  simpa only [neg_div] using abs_le.mp (ht.trans hρT)

omit [InnerProductSpace ℝ E] in
/-- The common compact cylinder has an open smoothness margin
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem rootFlow_innerCylinder_subset {R T : ℝ} (z : RootState E)
    (hR : 0 < R) (hT : 0 < T) :
    closedBall z (R / 4) ×ˢ Icc (-T / 4) (T / 4) ⊆
      ball z (R / 2) ×ˢ Ioo (-T) T := by
  rintro ⟨w, u⟩ ⟨hw, hu⟩
  exact ⟨closedBall_subset_ball (by linarith) hw, by constructor <;> linarith [hu.1, hu.2]⟩

/-- Common compact source balls lie in the genuine two-time flow domain
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem closedBall_subset_twoTimeDomain (z : RootState E) {R T ρ : ℝ}
    (hR : 0 < R) (hT : 0 < T) (hρR : 2 * ρ ≤ R / 4) (hρT : 2 * ρ ≤ T / 4) :
    closedBall (z.1, z) ρ ⊆ twoTimeDomain z (R / 2) T :=
  fun _ hq ↦ rootFlow_innerCylinder_subset z hR hT
    (twoTimeFlowArguments_mapsTo_cylinder z hρR hρT hq)

/-- The unchanged time and initial-covector coordinates of the projection
(`app:ch_regular_base:lem:characteristic-kernel`). -/
def twoTimeProjectionFixedPart : TwoTimePoint E →L[ℝ] TwoTimePoint E :=
  let t := ContinuousLinearMap.fst ℝ ℝ (RootState E)
  let w := ContinuousLinearMap.snd ℝ ℝ (RootState E)
  t.prod (((ContinuousLinearMap.fst ℝ ℝ (E × E)).comp w).prod
    ((0 : TwoTimePoint E →L[ℝ] E).prod
      ((ContinuousLinearMap.snd ℝ E E).comp ((ContinuousLinearMap.snd ℝ ℝ (E × E)).comp w))))

/-- Insert only the evolved position into the projection
(`app:ch_regular_base:lem:characteristic-kernel`). -/
def twoTimeProjectionPositionPart : RootState E →L[ℝ] TwoTimePoint E :=
  (0 : RootState E →L[ℝ] ℝ).prod ((0 : RootState E →L[ℝ] ℝ).prod
    (((ContinuousLinearMap.fst ℝ E E).comp (ContinuousLinearMap.snd ℝ ℝ (E × E))).prod 0))

/-- The actual projection is affine-linear in the evolved state
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem twoTimeProjection_eq_fixed_add (Φ : RootState E × ℝ → RootState E) :
    twoTimeProjection Φ = (twoTimeProjectionFixedPart : TwoTimePoint E → TwoTimePoint E) +
      twoTimeProjectionPositionPart ∘ twoTimeState Φ := by
  funext q
  simp [twoTimeProjection, twoTimeProjectionFixedPart, twoTimeProjectionPositionPart]

variable [FiniteDimensional ℝ E]

/-- Transfer the actual flow's joint norm to the two original times on a
fixed compact ball, with no derivative loss
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem cNorm_twoTimeState_le
    {Φ : RootState E × ℝ → RootState E} (z : RootState E) {R T ρ : ℝ}
    (hR : 0 < R) (hT : 0 < T) (hρR : 2 * ρ ≤ R / 4) (hρT : 2 * ρ ≤ T / 4)
    (hΦ : ContDiffOn ℝ ∞ Φ (ball z (R / 2) ×ˢ Ioo (-T) T)) (n : ℕ) :
    cNorm (closedBall (z.1, z) ρ) n (twoTimeState Φ) ≤
      ((n + 1 : ℝ) * 2 ^ n) *
        cNorm (closedBall z (R / 4) ×ˢ Icc (-T / 4) (T / 4)) n Φ := by
  let K := closedBall z (R / 4) ×ˢ Icc (-T / 4) (T / 4)
  have hK : IsCompact K := (isCompact_closedBall _ _).prod isCompact_Icc
  have hKU := rootFlow_innerCylinder_subset z hR hT
  have hmap := twoTimeFlowArguments_mapsTo_cylinder z hρR hρT
  have hb : ∀ j ≤ n, ∀ q ∈ closedBall (z.1, z) ρ,
      ‖iteratedFDeriv ℝ j (twoTimeState Φ) q‖ ≤ 2 ^ n * cNorm K n Φ := by
    intro j hj q hq
    have he := NormalComparison.norm_iteratedFDeriv_comp_linear_on_open_le
      (twoTimeFlowArguments (E := E)) (isOpen_ball.prod isOpen_Ioo) hΦ (hKU (hmap hq)) j
    have hp : ‖twoTimeFlowArguments (E := E)‖ ^ j ≤ (2 : ℝ) ^ n :=
      (pow_le_pow_left₀ (norm_nonneg _) norm_twoTimeFlowArguments_le j).trans
        (pow_le_pow_right₀ (by norm_num) hj)
    exact he.trans ((mul_le_mul
      (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
        (fun w hw ↦ (hΦ.contDiffAt ((isOpen_ball.prod isOpen_Ioo).mem_nhds
          (hKU hw))).of_le (by simp)) (hmap hq) hj)
      hp (by positivity) (cNorm_nonneg _ _ _)).trans_eq (mul_comm _ _))
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one, ← mul_assoc] using
    cNorm_le_sum_of_bounds (fun _ _ ↦ mul_nonneg (by positivity) (cNorm_nonneg K n Φ)) hb

/-- Uniform single-high norms for the same two-time state and spatial
projection, on any prescribed common small ball. At order two these are
controlled by the single fixed scalar `C³` budget; this is the common-radius
inverse constructor's low input
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem exists_rootFlow_twoTime_cNorm_bound
    (z : RootState E) {R T ρ M : ℝ} (hR : 0 < R) (hT : 0 < T) (hM : 0 ≤ M)
    (hρR : 2 * ρ ≤ R / 4) (hρT : 2 * ρ ≤ T / 4)
    {D : Set (RootState E)} (hD : IsOpen D) (hRD : closedBall z R ⊆ D) (n : ℕ) :
    ∃ C > (0 : ℝ), ∀ (h : RootState E → ℝ) (Φ : RootState E × ℝ → RootState E),
      ContDiffOn ℝ ∞ h D → cNorm (closedBall z R) 3 h ≤ M →
      ODE.IsSmoothFlowOn (rootHamiltonField h) z R (R / 2) T Φ →
      cNorm (closedBall (z.1, z) ρ) n (twoTimeState Φ) +
        cNorm (closedBall (z.1, z) ρ) n (twoTimeProjection Φ) ≤
          C * (1 + cNorm (closedBall z R) (n + 1) h) := by
  let K := closedBall (z.1, z) ρ
  let B := cNorm K n (twoTimeProjectionFixedPart (E := E))
  let J := twoTimeProjectionPositionPart (E := E)
  let a : ℝ := (n + 1 : ℝ) * 2 ^ n
  have hB : 0 ≤ B := cNorm_nonneg _ _ _
  have ha : 0 < a := by dsimp [a]; positivity
  obtain ⟨A, hA, hbound⟩ := exists_rootHamiltonFlow_cNorm_bound z hR hT hM hD hRD n
  refine ⟨1 + B + (1 + ‖J‖) * a * A, by positivity, ?_⟩
  intro h Φ hh hlow hΦ
  have hsub := closedBall_subset_twoTimeDomain z hR hT hρR hρT
  have hs (q) (hq : q ∈ K) : ContDiffAt ℝ n (twoTimeState Φ) q :=
    ((rootFlow_twoTimeState_smooth hΦ).contDiffAt
      ((isOpen_twoTimeDomain z (R / 2) T).mem_nhds (hsub hq))).of_le (by simp)
  have hj := FullPhaseCharts.InverseEstimates.cNorm_postLinear_le_on
    (isCompact_closedBall (z.1, z) ρ) n J hs
  have hp : cNorm K n (twoTimeProjection Φ) ≤ B + ‖J‖ * cNorm K n (twoTimeState Φ) := by
    rw [twoTimeProjection_eq_fixed_add]
    exact (cNorm_add_le_of_contDiffAt (isCompact_closedBall (z.1, z) ρ)
      (fun _ _ ↦ (twoTimeProjectionFixedPart (E := E)).contDiff.contDiffAt)
      (fun q hq ↦ J.contDiff.contDiffAt.comp q (hs q hq))).trans (add_le_add le_rfl hj)
  have hstate : cNorm K n (twoTimeState Φ) ≤ a * A * (1 + cNorm (closedBall z R) (n + 1) h) := by
    calc
      _ ≤ a * cNorm (closedBall z (R / 4) ×ˢ Icc (-T / 4) (T / 4)) n Φ :=
        cNorm_twoTimeState_le z hR hT hρR hρT hΦ.smooth n
      _ ≤ a * (A * (1 + cNorm (closedBall z R) (n + 1) h)) :=
        mul_le_mul_of_nonneg_left (hbound h Φ hh hlow hΦ) ha.le
      _ = _ := by ring
  have hhigh := cNorm_nonneg (closedBall z R) (n + 1) h
  nlinarith [mul_le_mul_of_nonneg_left hstate (norm_nonneg J), norm_nonneg J]

end JanetCartan.RegularSector.Characteristic
