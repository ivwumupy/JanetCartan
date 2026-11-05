module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.FullNormalGeometry.PhaseJets.Geometry
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.ActualPhaseBounds
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseEstimates.QuotientJets.Averaging
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.DifferentiatedAmplitudes.PullbackGrades

/-!
# Uniform full-input integral phase jets

For `app:ch_seed:eq:seed-quotient-integral`, differentiate the actual scalar
covector integral, including the incidence variable. A joint quotient jet of
order `k` uses phase order `k+1`, hence immersion order `k+4`. The additional
joint order for the epsilon derivative gives the fixed immersion reserve
`20*(n+1)+5` required by `app:ch_waves:setup:oscillatory`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.Sampling.FullNormalGeometry.PhaseJets
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualPhase
open ContinuumRow.CanonicalConic ContinuumRow.CanonicalCarrier RawKernel
open MeanNormalBound.CanonicalGap ProjectedStressFrame
open FullPhaseCharts.InverseEstimates RawPrimary.SliceBounds FourierIntegral.NormalOneHigh

variable {m : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- The full-input epsilon cap is fixed before the immersion budget and
metric/normal gaps. This permits the original sampling geometry and frame
margin to precede the reference scale; only the phase-jet constants depend on
the later map bounds. The literal phase, extension and derivative reserve are
unchanged (`app:ch_seed:eq:seed-quotient-integral`,
`app:ch_waves:setup:oscillatory`). -/
theorem exists_literalJoint_budgets_before_immersion_bounds {c C : ℝ} (hP : P.IsValid c C)
    {M : ℝ} (hM : 0 < M)
    {H : Set (Euclidean 2 × (Euclidean (m + 1) × Euclidean (m + 1)))}
    (hH : IsCompact H) (hHM : H ⊆ tripleDomain T M)
    : ∃ e > (0 : ℝ),
    ∀ {KF : Set (Euclidean (m + 1))}, IsCompact KF → KF ⊆ U →
      (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius ⊆ KF) →
    ∀ (B : ℝ) {γ κ : ℝ}, 0 < γ → 0 < κ →
    ∃ A : ℕ → ℝ, (∀ k, 0 < A k) ∧
      ∀ (F : Euclidean (m + 1) → Euclidean (embeddingDimension (m + 1)))
        (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
        (hrank : HasFullNormalRankOn F U),
        cNorm KF (20 * ((m + 1) + 1) + 5) F ≤ B →
        (∀ x ∈ KF, ∀ v, γ * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ KF, ∀ w ∈ normalSpace F x,
          κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        ∀ hlow : cNorm (closedBall (0 : Euclidean (m + 1))
            T.data.localReference.stateRadius) 6
            (projectedStress F - fun _ ↦ cubeStress (m + 1)) < T.family.threshold,
        let Q := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        ContDiffOn ℝ ∞ (literalJoint T Q) (Ioo (-2 * e) (2 * e) ×ˢ tripleDomain T M) ∧
          ∀ q ∈ Icc (-e) e ×ˢ H, ∀ k ≤ 20 * ((m + 1) + 1) + 1,
            ‖iteratedFDeriv ℝ k (literalJoint T Q) q‖ ≤ A k := by
  obtain ⟨es, hes, hshift⟩ := exists_shift_cap T hP hM
  obtain ⟨ep, hep, hsmooth⟩ := exists_literalJoint_smooth T hP hM
  let e := min es ep / 2
  have he : 0 < e := by dsimp [e]; positivity
  have hees : 2 * e ≤ es := by dsimp [e]; linarith [min_le_left es ep]
  have heep : 2 * e ≤ ep := by dsimp [e]; linarith [min_le_right es ep]
  let V := Ioo (-2 * e) (2 * e) ×ˢ tripleDomain T M
  have hV : IsOpen V := isOpen_Ioo.prod (isOpen_tripleDomain T M)
  have hHV : Icc (-e) e ×ˢ H ⊆ V := by
    intro q hq
    exact ⟨⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩, hHM hq.2⟩
  have hW : Icc (0 : ℝ) 1 ⊆ Ioo (-1 : ℝ) 2 :=
    fun s hs ↦ ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hmap (s : ℝ) (hs : s ∈ Ioo (-1 : ℝ) 2) :
      MapsTo (shift T s) V (ball (0, covectorCenter T) T.family.radius) := by
    intro q hq
    exact hshift s hs ⟨⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩, hq.2⟩
  refine ⟨e, he, ?_⟩
  intro KF hKF hKU hball B γ κ hγ hκ
  obtain ⟨a, ha, hphase⟩ := exists_current_projected_sharp_bound T
    (N := embeddingDimension (m + 1)) hKF hKU hball B hγ hκ
  obtain ⟨b, hb, hsub⟩ := exists_shift_jet_bounds T hP M e hH hHM
  let p : ℕ → ℝ := fun j ↦ a (j + 1) * (1 + max B 0)
  let d : ℕ → ℝ := fun j ↦ cNorm (Icc (-e) e ×ˢ H) j (direction T)
  have hp (j : ℕ) : 0 ≤ p j := mul_nonneg (ha _).le (by linarith [le_max_right B 0])
  have hd (j : ℕ) : 0 ≤ d j := cNorm_nonneg _ _ _
  let A := sliceMaskJetConstant (compositionBudget p b) d
  have hA (j : ℕ) : 0 ≤ A j :=
    sliceMaskJetConstant_nonneg (compositionBudget_nonneg hp hb) hd j
  refine ⟨fun j ↦ 1 + A j, fun j ↦ by linarith [hA j], ?_⟩
  intro F hF hi hrank hFB hmet hnormal hlow Q
  have hQ : ContDiffOn ℝ ∞ (literalJoint T Q) V := (hsmooth Q).mono (by
    intro q hq
    exact ⟨⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩, hq.2⟩)
  refine ⟨hQ, ?_⟩
  let Z := ball ((0 : WithLp 2 (ℝ × Euclidean (m + 1 - 1))), covectorCenter T)
    (2 * T.family.radius)
  let R := physicalDifferentialRestriction
    (P := WithLp 2 (ℝ × Euclidean (m + 1 - 1))) (X := Euclidean (m + 1 - 1))
  let D := R ∘ fderiv ℝ (current T Q)
  have hD : ContDiffOn ℝ ∞ D Z := R.contDiff.comp_contDiffOn
    ((current_smooth T Q).fderiv_of_isOpen isOpen_ball (m := ∞) (by simp))
  have hballZ : closedBall (0, covectorCenter T) T.family.radius ⊆ Z :=
    closedBall_subset_ball (by linarith [T.family.radius_pos])
  have hshiftSmooth (s : ℝ) : ContDiffOn ℝ ∞ (shift T s) V :=
    (shift_smooth T hP M).comp (contDiffOn_const.prodMk contDiffOn_id)
      (fun q hq ↦ ⟨mem_univ _, mem_univ _, hq.2⟩)
  have hcomp (s : ℝ) (hs : s ∈ Ioo (-1 : ℝ) 2) : ContDiffOn ℝ ∞ (D ∘ shift T s) V :=
    hD.comp (hshiftSmooth s) (fun q hq ↦ hballZ (ball_subset_closedBall (hmap s hs hq)))
  have hint : ContDiffOn ℝ ∞
      (fun w : (ℝ × (Euclidean 2 × (Euclidean (m + 1) × Euclidean (m + 1)))) × ℝ ↦
        D (shift T w.2 w.1) (direction T w.1)) (V ×ˢ Ioo (-1 : ℝ) 2) := by
    apply (hD.comp
      ((shift_smooth T hP M).comp (contDiffOn_snd.prodMk contDiffOn_fst)
        (fun w hw ↦ ⟨mem_univ _, mem_univ _, hw.1.2⟩))
      (fun w hw ↦ hballZ (ball_subset_closedBall (hmap w.2 hw.2 hw.1)))).clm_apply
    unfold direction
    fun_prop
  have heq : EqOn (literalJoint T Q)
      (fun q ↦ ∫ s in (0 : ℝ)..1, D (shift T s q) (direction T q)) V := by
    intro q hq
    unfold literalJoint normalizedFullPhase modulation phaseShiftQuotient
    simp only [inner_gradient_left]
    apply intervalIntegral.integral_congr
    intro s hs
    have hmem := hballZ (ball_subset_closedBall
      (hmap s (hW (by simpa using hs)) hq))
    exact congrArg (fun L ↦ L (direction T q))
      (physicalDifferentialRestriction_fderiv
        (S := fun x η ↦ current T Q (x, η)) (q := shift T s q)
        (((current_smooth T Q).contDiffAt (isOpen_ball.mem_nhds hmem)).differentiableAt
          (by simp))).symm
  intro q hq k hk
  have hqV := hHV hq
  have hj : ‖iteratedFDeriv ℝ k (literalJoint T Q) q‖ ≤ A k := by
    have hevent : literalJoint T Q =ᶠ[𝓝 q]
        (fun z ↦ ∫ s in (0 : ℝ)..1, D (shift T s z) (direction T z)) :=
      Filter.mem_of_superset (hV.mem_nhds hqV) heq
    rw [(hevent.iteratedFDeriv ℝ k).eq_of_nhds]
    apply norm_iteratedFDeriv_unitIntervalParameterIntegral_le hV isOpen_Ioo hW hint hqV k
    intro s hs
    have hprimitive (j : ℕ) (hj : j ≤ k) :
        ‖iteratedFDeriv ℝ j D (shift T s q)‖ ≤ p j := by
      have hmem := ball_subset_closedBall (hmap s (hW hs) hqV)
      have hcont := (current_smooth T Q).contDiffAt (isOpen_ball.mem_nhds (hballZ hmem))
      have hjet : ‖iteratedFDeriv ℝ j D (shift T s q)‖ ≤
          ‖iteratedFDeriv ℝ (j + 1) (current T Q) (shift T s q)‖ := by
        apply (R.norm_iteratedFDeriv_comp_left (hcont.fderiv_right (m := ∞) (by simp))
          (by simp : (j : ℕ∞ω) ≤ ∞)).trans
        calc
          _ ≤ 1 * ‖iteratedFDeriv ℝ j (fderiv ℝ (current T Q)) (shift T s q)‖ :=
            mul_le_mul_of_nonneg_right norm_physicalDifferentialRestriction_le (norm_nonneg _)
          _ = _ := by rw [one_mul, norm_iteratedFDeriv_fderiv]
      apply hjet.trans
      apply (norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall _ _)
        (fun y hy ↦ ((current_smooth T Q).contDiffAt
          (isOpen_ball.mem_nhds (hballZ hy))).of_le (by simp)) hmem (le_refl (j + 1))).trans
      have hlowF : cNorm KF 4 F ≤ B :=
        (cNorm_mono_order (by omega : 4 ≤ 20 * ((m + 1) + 1) + 5)).trans hFB
      apply (hphase F hF hi hrank hlowF hmet hnormal hlow (j + 1)
        (closedBall (0, covectorCenter T) T.family.radius) Subset.rfl).trans
      exact mul_le_mul_of_nonneg_left (add_le_add_right
        (((cNorm_mono_order (by omega : j + 1 + 3 ≤ 20 * ((m + 1) + 1) + 5)).trans
          hFB).trans (le_max_left B 0)) 1) (ha _).le
    have hinner (j : ℕ) : ‖iteratedFDeriv ℝ j (shift T s) q‖ ≤ b j := hsub s hs q hq j
    have hdir (j : ℕ) : ‖iteratedFDeriv ℝ j (direction T) q‖ ≤ d j :=
      norm_iteratedFDeriv_le_cNorm (isCompact_Icc.prod hH)
        (by unfold direction; fun_prop) hq le_rfl
    have hc (i : ℕ) (hi : i ≤ k) :
        ‖iteratedFDeriv ℝ i (D ∘ shift T s) q‖ ≤ compositionBudget p b i := by
      simpa only [one_pow, mul_one] using norm_iteratedFDeriv_comp_le_sliceGrade
        (R := 0) (L := 1) ((hshiftSmooth s).contDiffAt (hV.mem_nhds hqV))
        (hD.contDiffAt (isOpen_ball.mem_nhds
          (hballZ (ball_subset_closedBall (hmap s (hW hs) hqV)))))
        (fun j _ ↦ hp j) le_rfl (fun j hj ↦ by simpa using hprimitive j (hj.trans hi))
        (fun j _ _ ↦ hinner j)
    have hh := norm_iteratedFDerivWithin_clm_apply (hcomp s (hW hs))
      (by unfold direction; fun_prop : ContDiffOn ℝ ∞ (direction T) V)
      hV.uniqueDiffOn hqV (by simp : (k : ℕ∞ω) ≤ ∞)
    simp only [iteratedFDerivWithin_of_isOpen _ hV hqV] at hh
    apply hh.trans
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (hc i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
        (Nat.cast_nonneg _)) (hdir (k - i)) (norm_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _) (compositionBudget_nonneg hp hb _))
  linarith

/-- All joint phase jets, with the epsilon cap and constants before the
immersion and every spectator. Only the actual projected frame and a fixed
finite immersion budget are used. The compact `H` is explicitly contained in
the full extension; it is independent of `F`. Consumer: the phase part of
`UniformNormalData.input_jets` (`app:ch_waves:setup:oscillatory`). -/
theorem exists_literalJoint_budgets {c C : ℝ} (hP : P.IsValid c C)
    {M : ℝ} (hM : 0 < M)
    {H : Set (Euclidean 2 × (Euclidean (m + 1) × Euclidean (m + 1)))}
    (hH : IsCompact H) (hHM : H ⊆ tripleDomain T M)
    {KF : Set (Euclidean (m + 1))} (hKF : IsCompact KF) (hKU : KF ⊆ U)
    (hball : closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius ⊆ KF)
    (B : ℝ) {γ κ : ℝ} (hγ : 0 < γ) (hκ : 0 < κ) :
    ∃ e > (0 : ℝ), ∃ A : ℕ → ℝ, (∀ k, 0 < A k) ∧
      ∀ (F : Euclidean (m + 1) → Euclidean (embeddingDimension (m + 1)))
        (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
        (hrank : HasFullNormalRankOn F U),
        cNorm KF (20 * ((m + 1) + 1) + 5) F ≤ B →
        (∀ x ∈ KF, ∀ v, γ * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ KF, ∀ w ∈ normalSpace F x,
          κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        ∀ hlow : cNorm (closedBall (0 : Euclidean (m + 1))
            T.data.localReference.stateRadius) 6
            (projectedStress F - fun _ ↦ cubeStress (m + 1)) < T.family.threshold,
        let Q := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        ContDiffOn ℝ ∞ (literalJoint T Q) (Ioo (-2 * e) (2 * e) ×ˢ tripleDomain T M) ∧
          ∀ q ∈ Icc (-e) e ×ˢ H, ∀ k ≤ 20 * ((m + 1) + 1) + 1,
            ‖iteratedFDeriv ℝ k (literalJoint T Q) q‖ ≤ A k := by
  obtain ⟨e, he, hbudgets⟩ :=
    exists_literalJoint_budgets_before_immersion_bounds T hP hM hH hHM
  obtain ⟨A, hA, hbound⟩ := hbudgets hKF hKU hball B hγ hκ
  exact ⟨e, he, A, hA, hbound⟩

end JanetCartan.Sampling.FullNormalGeometry.PhaseJets
