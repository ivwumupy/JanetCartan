module

public import JanetCartan.Iteration.RevisedGlobal.History
public import JanetCartan.Analysis.Iteration.ErrorInduction

/-!
# Compatible recursion for the global physical increments

`new:lem:one-step` absorbs the unabsorbed bounds of the revised analytic step
on the *same* Schwartz increment. Section 18's `main:eq:staircase` then gives
one sequence by appending to finite prefixes. No infinite family of corrections,
metric induction hypothesis at future times, or derivative estimates are assumed.
The threshold family is chosen before `R₀` and before the single target `g s`.
-/

@[expose] public noncomputable section

open Filter
open scoped Matrix.Norms.Frobenius

namespace JanetCartan.RevisedGlobal

-- The analytic producer only extends a finite prefix. Independent choices of a
-- prefix for each length would not give a sequence, so store it in the recursive state.
private theorem chooseCompatibleSequence {α : Type*} (P : (j : ℕ) → (Fin j → α) → Prop)
    (h₀ : P 0 Fin.elim0)
    (hs : ∀ j u, P j u → ∃ a, P (j + 1) (Fin.snoc u a)) :
    ∃ u : ℕ → α, ∀ j, P j (fun i ↦ u i.val) := by
  classical
  let extend (j : ℕ) (v : {u // P j u}) : {u // P (j + 1) u} :=
    ⟨Fin.snoc v.1 (hs j v.1 v.2).choose, (hs j v.1 v.2).choose_spec⟩
  let hist : (j : ℕ) → {u // P j u} := Nat.rec ⟨Fin.elim0, h₀⟩ extend
  let u (j : ℕ) := (hist (j + 1)).1 (Fin.last j)
  have agree (j : ℕ) : ∀ i : Fin j, (hist j).1 i = u i.val := by
    induction j with
    | zero => exact fun i ↦ Fin.elim0 i
    | succ j ih =>
      intro i
      refine Fin.lastCases rfl (fun a ↦ ?_) i
      simpa only [hist, extend, Fin.snoc_castSucc, Fin.val_castSucc] using ih a
  exact ⟨u, fun j ↦ (funext (agree j)) ▸ (hist j).2⟩

namespace UniformHistoryCorrection

variable {n N : ℕ} {G : Euclidean n → Euclidean N} {D : Set (Euclidean n)}
  {g : ℝ → MetricField n} {s₀ B Tref : ℝ} {kMin : ℕ} {C T : ℕ → ℝ}

/-- `new:lem:one-step` and `main:eq:metric-two-errors`: append one and the same
physical correction to an arbitrary admissible prefix. The literal revised `B₀`
and `B₃` are paid by the current scale and by the strict cubic order gap. The
last two inequalities display the intermediate `2 C_{2k} R^{-3k+B₃}`. -/
theorem oneStep (h : UniformHistoryCorrection G D g s₀ kMin B Tref C T)
    (hgap : RevisedScales.cubicLoss n + 2 * growthExponent + 4 <
      (3 - 2 * growthExponent) * (kMin : ℝ))
    {R₀ s : ℝ} {j k : ℕ} {u : Fin j → SchwartzMap (Euclidean n) (Euclidean N)}
    {ell : Fin j → ℕ} (hR₀ : Tref ≤ R₀) (hs : 0 < s) (hs₀ : s ≤ s₀)
    (hk : kMin ≤ k) (hT : T k ≤ iterationScale R₀ growthExponent j)
    (hC : C k ≤ iterationScale R₀ growthExponent j) (hu : IsAdmissibleHistory B R₀ kMin u ell)
    (hdefect : cNorm D 0 (inducedMetric (finiteMap G u) - g s) ≤
      (iterationScale R₀ growthExponent j ^ (-(k : ℝ))) ^ 2) :
    let R := iterationScale R₀ growthExponent j
    ∃ U : SchwartzMap (Euclidean n) (Euclidean N),
      IsAdmissibleHistory B R₀ kMin (Fin.snoc u U) (Fin.snoc ell k) ∧
      cNorm D 0 (inducedMetric (finiteMap G (Fin.snoc u U)) - g s) ≤
        2 * C k * R ^ (-3 * (k : ℝ) + RevisedScales.cubicLoss n) ∧
      2 * C k * R ^ (-3 * (k : ℝ) + RevisedScales.cubicLoss n) ≤
        R ^ (-2 * growthExponent * ((k : ℝ) + 1)) := by
  let R := iterationScale R₀ growthExponent j
  have hbase := h.two_le_referenceThreshold.trans hR₀
  have hRtwo : 2 ≤ R := by
    calc
      2 ≤ R₀ := hbase
      _ = iterationScale R₀ growthExponent 0 := (iterationScale_zero ..).symm
      _ ≤ R := iterationScale_monotone (by linarith) (by norm_num [growthExponent]) (Nat.zero_le j)
  have hR : 1 ≤ R := by linarith
  obtain ⟨U, hband, hnorm, hmetric⟩ := h.correction hR₀ hs hs₀ hk hT hu hdefect
  refine ⟨U, isAdmissibleHistory_snoc_iff.mpr ⟨hu, hk, hband, ?_⟩, ?_, ?_⟩
  · exact RevisedScales.displacement_budget_of_constant_le hR hC hnorm
  · rw [finiteMap_snoc]
    apply hmetric.trans
    simpa only [neg_mul, mul_one] using twoMetricErrors_le (ε := 1)
      (R := R) (C := C k) (k := (k : ℝ)) (Q := 2 * (k : ℝ)) hR (h.constant_nonneg k)
      zero_le_one (le_refl _) (Real.rpow_nonneg (zero_le_one.trans hR) _)
      (by simp) (RevisedScales.cubicLoss_nonneg n) (le_refl _)
  · exact metricTwoErrors_absorb hRtwo hC (by norm_num [growthExponent]) hk hgap

/-- `main:eq:staircase`, `main:eq:history-data`, and `main:eq:metric-induction`:
one threshold family dominates every analytic threshold and step constant,
as well as an arbitrary prescribed auxiliary requirement `H₀`. For every
sufficiently large initial scale and every **single** target satisfying the
initial bound, there is one sequence of real global corrections, simultaneously
realizing all admissible prefixes and all metric budgets. The predicates refer
to physical L² and the exact Fourier band of that same sequence. -/
theorem exists_adaptive_correction_sequence
    (h : UniformHistoryCorrection G D g s₀ kMin B Tref C T)
    (hgap : RevisedScales.cubicLoss n + 2 * growthExponent + 4 <
      (3 - 2 * growthExponent) * (kMin : ℝ)) (H₀ : ℕ → ℝ) :
    ∃ H : ℕ → ℝ, Monotone H ∧
      (∀ k, 2 ≤ H k ∧ H₀ k ≤ H k ∧ Tref ≤ H k ∧ T k ≤ H k ∧ C k ≤ H k) ∧
      ∀ R₀ s : ℝ, H kMin ≤ R₀ → 0 < s → s ≤ s₀ →
        cNorm D 0 (inducedMetric G - g s) ≤ (R₀ ^ (-(kMin : ℝ))) ^ 2 →
        let R := iterationScale R₀ growthExponent
        let k := powerAdaptiveSchedule H R₀ growthExponent kMin
        Tendsto k atTop atTop ∧ (∀ j, H (k j) ≤ R j) ∧
        ∃ u : ℕ → SchwartzMap (Euclidean n) (Euclidean N),
          (∀ j, PhysicalBernstein.HasFourierSupport (B * R j ^ bandExponent) (u j) ∧
            PhysicalBernstein.physicalL2Norm (u j) ≤
              R j ^ (-(k j : ℝ) + RevisedScales.displacementLoss n + 1)) ∧
          (∀ j, IsAdmissibleHistory B R₀ kMin (fun i : Fin j ↦ u i.val)
            (fun i : Fin j ↦ k i.val)) ∧
          ∀ j, cNorm D 0 (inducedMetric (currentHistoryMap G (fun i ↦ ⇑(u i)) j) - g s) ≤
            (R j ^ (-(k j : ℝ))) ^ 2 := by
  -- The actual finite maximum, independent of the target and of every chosen correction.
  let f (q : ℕ) := max (max Tref (H₀ q)) (max (T q) (C q))
  let H (q : ℕ) := (Finset.range (q + 1)).sup' Finset.nonempty_range_add_one f
  have hH : Monotone H := fun _ _ hij ↦
    Finset.sup'_mono f (Finset.range_mono (Nat.succ_le_succ hij)) Finset.nonempty_range_add_one
  have hdom (q : ℕ) : 2 ≤ H q ∧ H₀ q ≤ H q ∧ Tref ≤ H q ∧ T q ≤ H q ∧ C q ≤ H q := by
    have hq : f q ≤ H q := Finset.le_sup' f (Finset.mem_range.mpr (Nat.lt_succ_self q))
    have hleft := (le_max_left (max Tref (H₀ q)) (max (T q) (C q))).trans hq
    have hright := (le_max_right (max Tref (H₀ q)) (max (T q) (C q))).trans hq
    have href := (le_max_left Tref (H₀ q)).trans hleft
    exact ⟨h.two_le_referenceThreshold.trans href, (le_max_right _ _).trans hleft, href,
      (le_max_left _ _).trans hright, (le_max_right _ _).trans hright⟩
  refine ⟨H, hH, hdom, ?_⟩
  intro R₀ s hR₀ hs hs₀ hinit
  let R := iterationScale R₀ growthExponent
  let k := powerAdaptiveSchedule H R₀ growthExponent kMin
  have hbase : 2 ≤ R₀ := (hdom kMin).1.trans hR₀
  have hRone (j : ℕ) : 1 ≤ R j :=
    Real.one_le_rpow (by linarith) (pow_nonneg (by norm_num [growthExponent]) _)
  have horder (j : ℕ) : kMin ≤ k j := initialOrder_le_adaptiveSchedule H R kMin j
  have hthreshold (j : ℕ) : H (k j) ≤ R j :=
    powerAdaptiveSchedule_threshold (by linarith) (by norm_num [growthExponent]) hR₀ j
  refine ⟨powerAdaptiveSchedule_tendsto_atTop H kMin (by linarith) (by norm_num [growthExponent]),
    hthreshold, ?_⟩
  let P (j : ℕ) (u : Fin j → SchwartzMap (Euclidean n) (Euclidean N)) :=
    IsAdmissibleHistory B R₀ kMin u (fun i ↦ k i.val) ∧
    cNorm D 0 (inducedMetric (finiteMap G u) - g s) ≤ (R j ^ (-(k j : ℝ))) ^ 2
  have hzero : P 0 Fin.elim0 := by
    refine ⟨isAdmissibleHistory_empty _ _ _ _ _, ?_⟩
    simpa [R, k] using hinit
  have hstep (j : ℕ) (u : Fin j → SchwartzMap (Euclidean n) (Euclidean N)) (hu : P j u) :
      ∃ U, P (j + 1) (Fin.snoc u U) := by
    obtain ⟨U, hU, herr, hgain⟩ := h.oneStep hgap ((hdom kMin).2.2.1.trans hR₀)
      hs hs₀ (horder j) ((hdom (k j)).2.2.2.1.trans (hthreshold j))
      ((hdom (k j)).2.2.2.2.trans (hthreshold j)) hu.1 hu.2
    have horders : (fun i : Fin (j + 1) ↦ k i.val) = Fin.snoc (fun i : Fin j ↦ k i.val) (k j) := by
      funext i
      exact Fin.lastCases (by simp) (fun i ↦ by simp) i
    refine ⟨U, horders.symm ▸ hU, (herr.trans hgain).trans ?_⟩
    simpa only [R, iterationScale_succ_rpow (show 0 ≤ R₀ by linarith), one_mul, one_pow] using
      nextMetricBudget (ε := 1) (hRone j) (by norm_num [growthExponent] : 0 ≤ growthExponent)
        (adaptiveSchedule_succ_le H R kMin j)
  obtain ⟨u, hu⟩ := chooseCompatibleSequence P hzero hstep
  refine ⟨u, fun j ↦ ((hu (j + 1)).1 (Fin.last j)).2, fun j ↦ (hu j).1, ?_⟩
  intro j
  simpa only [finiteMap_eq_currentHistoryMap] using (hu j).2

end UniformHistoryCorrection

end JanetCartan.RevisedGlobal
