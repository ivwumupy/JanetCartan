module

public import JanetCartan.Iteration.PhysicalMean.NormalProfile

/-!
# The profile of the actual single normal completion

The v2 mean is completed once, on the same current map, with the full defect.
The normal-multiplier bounds below are actual consequences of physical history
admissibility.  The uncompleted canonical field, its FULL strain, normalized
target and sampled self tensor still have their original producer obligations.
No completed-mean profile is a hypothesis.  The consumer is the fixed physical
cutoff and the physical Sobolev profile in `RevisedStage`.
-/

@[expose] public noncomputable section

open Set Metric Finset
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
open scoped JanetCartan.NormalRankStability

namespace JanetCartan.PhysicalMean

open CurrentMean AmbientResponse GeometricProfile

/-- The actual canonical normal correction preserves separated derivative
orders in the datum (`main:eq:mean-normal-field`).  All multiplier constants
precede the physical prefix, tensor datum and requested order. -/
theorem exists_history_meanNormalCorrection_bounds {n : ℕ}
    (G : FlatReference n) {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hR : R < G.domain.chartRadius) {B : ℝ} (hB : 1 ≤ B)
    {rStar kMin : ℕ} (hStar : 8 ≤ rStar)
    (horder : RevisedScales.displacementLoss n +
      bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < (kMin : ℝ)) :
    ∃ S : ℝ, 2 ≤ S ∧ ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ R₀, S ≤ R₀ →
      ∀ (j : ℕ) (u : Fin j → SchwartzMap (Euclidean n) (Euclidean (embeddingDimension n)))
        (ell : Fin j → ℕ), RevisedGlobal.IsAdmissibleHistory B R₀ kMin u ell →
      ∀ T : MetricField n, ContDiffOn ℝ ∞ T (ball 0 R) → ∀ s : ℕ,
      cNorm (closedBall 0 r) s (meanNormalCorrection (RevisedGlobal.finiteMap G.map u) T) ≤
        ∑ q ∈ range (s + 1), ∑ i ∈ range (q + 1),
          (q.choose i : ℝ) * C i * currentCoefficientScale R₀ j ^ i *
            cNorm (closedBall 0 r) (q - i) T := by
  obtain ⟨S, hS, C, hC, hnormal⟩ := exists_history_normal_multiplier_profile
    G hr hrR hR hB hStar (show 2 + 0 ≤ rStar by omega) horder
  refine ⟨S, hS, C, hC, ?_⟩
  intro R₀ hR₀ j u ell hu T hT s
  let F := RevisedGlobal.finiteMap G.map u
  let K := closedBall (0 : Euclidean n) r
  let U := ball (0 : Euclidean n) R
  let L := fun x ↦ (canonicalNormalCompletion F x).toContinuousLinearMap
  obtain ⟨_, _, hL, hLbound⟩ := hnormal R₀ hR₀ j u ell hu
  have hKU : K ⊆ U := closedBall_subset_ball hrR
  have hK : IsCompact K := isCompact_closedBall _ _
  have hLjet (i : ℕ) (x : Euclidean n) (hx : x ∈ K) :
      ‖iteratedFDeriv ℝ i L x‖ ≤ C i * currentCoefficientScale R₀ j ^ i := by
    apply (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
      (fun y hy ↦ (hL.contDiffAt (isOpen_ball.mem_nhds (hKU hy))).of_le (by simp)) hx le_rfl).trans
    simpa only [Nat.sub_zero] using hLbound i
  have hTjet (i : ℕ) (x : Euclidean n) (hx : x ∈ K) :
      ‖iteratedFDeriv ℝ i T x‖ ≤ cNorm K i T :=
    norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
      (fun y hy ↦ (hT.contDiffAt (isOpen_ball.mem_nhds (hKU hy))).of_le (by simp)) hx le_rfl
  have hscale : 0 ≤ currentCoefficientScale R₀ j :=
    (show (0 : ℝ) ≤ 1 by norm_num).trans
      (one_le_currentCoefficientScale (by linarith [hS.trans hR₀]) j)
  let ev := ContinuousLinearMap.id ℝ (MetricTensor n →L[ℝ] Euclidean (embeddingDimension n))
  have hprod : ContDiffOn ℝ ∞ (fun x ↦ L x (T x)) U := hL.clm_apply hT
  apply cNorm_le_sum_of_bounds
    (fun q _ ↦ sum_nonneg fun i _ ↦ mul_nonneg
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC i)) (pow_nonneg hscale i))
      (cNorm_nonneg _ _ _))
  intro q _ x hx
  have hderiv := ev.norm_iteratedFDerivWithin_le_of_bilinear hL hT
    isOpen_ball.uniqueDiffOn (hKU hx) (n := q) (by simp)
  simp only [iteratedFDerivWithin_of_isOpen _ isOpen_ball (hKU hx)] at hderiv
  have hcorr : ‖iteratedFDeriv ℝ q (meanNormalCorrection F T) x‖ =
      (1 / 2 : ℝ) * ‖iteratedFDeriv ℝ q (fun y ↦ L y (T y)) x‖ := by
    change ‖iteratedFDeriv ℝ q ((-(1 / 2 : ℝ)) • (fun y ↦ L y (T y))) x‖ = _
    rw [iteratedFDeriv_const_smul_apply
      ((hprod.contDiffAt (isOpen_ball.mem_nhds (hKU hx))).of_le (by simp)), norm_smul]
    norm_num
  rw [hcorr]
  calc
    _ ≤ ‖iteratedFDeriv ℝ q (fun y ↦ L y (T y)) x‖ := by
      nlinarith [norm_nonneg (iteratedFDeriv ℝ q (fun y ↦ L y (T y)) x)]
    _ ≤ ‖ev‖ * ∑ i ∈ range (q + 1), (q.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i L x‖ * ‖iteratedFDeriv ℝ (q - i) T x‖ := hderiv
    _ ≤ 1 * ∑ i ∈ range (q + 1), (q.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i L x‖ * ‖iteratedFDeriv ℝ (q - i) T x‖ := by
      apply mul_le_mul_of_nonneg_right ContinuousLinearMap.norm_id_le
      positivity
    _ ≤ _ := by
      rw [one_mul]
      apply sum_le_sum
      intro i _
      calc
        _ ≤ (q.choose i : ℝ) * (C i * currentCoefficientScale R₀ j ^ i) *
            cNorm K (q - i) T := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left (hLjet i x hx) (Nat.cast_nonneg _))
            (hTjet (q - i) x hx) (norm_nonneg _)
            (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hC i) (pow_nonneg hscale i)))
        _ = _ := by ring

private theorem cNorm_add_local {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : Euclidean n → E} {r R : ℝ} (hrR : r < R)
    (hf : ContDiffOn ℝ ∞ f (ball 0 R)) (hg : ContDiffOn ℝ ∞ g (ball 0 R)) (s : ℕ) :
    cNorm (closedBall 0 r) s (f + g) ≤ cNorm (closedBall 0 r) s f + cNorm (closedBall 0 r) s g := by
  apply cNorm_add_le_of_contDiffAt (isCompact_closedBall _ _)
  · intro x hx
    exact (hf.contDiffAt (isOpen_ball.mem_nhds (closedBall_subset_ball hrR hx))).of_le (by simp)
  · intro x hx
    exact (hg.contDiffAt (isOpen_ball.mem_nhds (closedBall_subset_ball hrR hx))).of_le (by simp)

private theorem cNorm_sub_local {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : Euclidean n → E} {r R : ℝ} (hrR : r < R)
    (hf : ContDiffOn ℝ ∞ f (ball 0 R)) (hg : ContDiffOn ℝ ∞ g (ball 0 R)) (s : ℕ) :
    cNorm (closedBall 0 r) s (f - g) ≤ cNorm (closedBall 0 r) s f + cNorm (closedBall 0 r) s g := by
  simpa only [sub_eq_add_neg, cNorm_neg] using
    cNorm_add_local (f := f) (g := -g) hrR hf hg.neg s

/-- `main:prop:mean`: the actual single completion has the physical `R^s`
profile once the canonical field/FULL strain, normalized source and complete
self tensor have their original profiles.  All completion geometry and normal
multipliers are discharged from actual revised history admissibility. -/
theorem exists_history_completedMean_profile {n : ℕ}
    (G : FlatReference n) {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hR : R < G.domain.chartRadius) {B : ℝ} (hB : 1 ≤ B)
    {rStar kMin : ℕ} (hStar : 8 ≤ rStar)
    (horder : RevisedScales.displacementLoss n +
      bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < (kMin : ℝ))
    (a b d : ℕ → ℝ) (ha : ∀ s, 0 ≤ a s) (hb : ∀ s, 0 ≤ b s) (hd : ∀ s, 0 ≤ d s) :
    ∃ S : ℝ, 2 ≤ S ∧ ∃ C : ℕ → ℝ, (∀ s, 0 ≤ C s) ∧
      ∀ R₀, S ≤ R₀ →
      ∀ (j : ℕ) (u : Fin j → SchwartzMap (Euclidean n) (Euclidean (embeddingDimension n)))
        (ell : Fin j → ℕ), RevisedGlobal.IsAdmissibleHistory B R₀ kMin u ell →
      ∀ (W : Euclidean n → Euclidean (embeddingDimension n)) (target H : MetricField n),
      ContDiffOn ℝ ∞ W (ball 0 R) → ContDiffOn ℝ ∞ target (ball 0 R) →
      ContDiffOn ℝ ∞ H (ball 0 R) →
      let F := RevisedGlobal.finiteMap G.map u
      ContDiffOn ℝ ∞ (completedMeanField F W target H) (ball 0 R) ∧
      ∀ M : ℝ, currentCoefficientScale R₀ j ≤ M →
      (∀ s, cNorm (closedBall 0 r) s W + cNorm (closedBall 0 r) s (linearizedMetric F W) ≤ a s * M ^ s) →
      (∀ s, cNorm (closedBall 0 r) s target ≤ b s * M ^ s) →
      (∀ s, cNorm (closedBall 0 r) s H ≤ d s * M ^ s) →
      ∀ s, cNorm (closedBall 0 r) s (completedMeanField F W target H) ≤ C s * M ^ s := by
  obtain ⟨Sn, hSn, Cn, hCn, hnormal⟩ :=
    exists_history_meanNormalCorrection_bounds G hr hrR hR hB hStar horder
  obtain ⟨Sg, hSg, _, _, _, _, hgeometry⟩ := PhysicalGeometry.exists_geometric_neighborhood
    G hr hrR hR hB hStar horder (by norm_num : (0 : ℝ) < 1)
  let D := fun s ↦ b s + a s + d s
  have hD : ∀ s, 0 ≤ D s := fun s ↦ add_nonneg (add_nonneg (hb s) (ha s)) (hd s)
  let C := fun s ↦ a s + ∑ q ∈ range (s + 1), ∑ i ∈ range (q + 1),
    (q.choose i : ℝ) * Cn i * D (q-i)
  refine ⟨max Sn Sg, hSn.trans (le_max_left _ _), C, ?_, ?_⟩
  · intro s
    exact add_nonneg (ha s) (sum_nonneg fun q _ ↦ sum_nonneg fun i _ ↦ by positivity [hCn i, hD (q-i)])
  intro R₀ hR₀ j u ell hu W target H hW ht hH F
  have hn := (le_max_left Sn Sg).trans hR₀
  have hg := (le_max_right Sn Sg).trans hR₀
  have htwo := hSn.trans hn
  have hF : ContDiff ℝ ∞ F := G.contDiff.add (ContDiff.sum (fun i _ ↦ (u i).smooth'))
  obtain ⟨hi, hrank, _⟩ := hgeometry R₀ hg j u ell hu
  refine ⟨contDiffOn_completedMeanField isOpen_ball hF.contDiffOn hW ht hH hi hrank, ?_⟩
  intro M hTM hWb htb hHb s
  have hT : 1 ≤ currentCoefficientScale R₀ j := one_le_currentCoefficientScale (by linarith) j
  have hM : 1 ≤ M := hT.trans hTM
  have hstrain : ContDiffOn ℝ ∞ (linearizedMetric F W) (ball 0 R) :=
    AmbientResponse.contDiffOn_linearizedMetric isOpen_ball hF.contDiffOn hW
  have hdef : ContDiffOn ℝ ∞ (target - linearizedMetric F W - H) (ball 0 R) :=
    (ht.sub hstrain).sub hH
  have hdatum (q : ℕ) : cNorm (closedBall 0 r) q (target - linearizedMetric F W - H) ≤ D q * M ^ q := by
    have hsub := cNorm_sub_local hrR (ht.sub hstrain) hH q
    have hsub' := cNorm_sub_local hrR ht hstrain q
    have hstrainb : cNorm (closedBall 0 r) q (linearizedMetric F W) ≤ a q * M ^ q :=
      (le_add_of_nonneg_left (cNorm_nonneg _ _ W)).trans (hWb q)
    exact (hsub.trans (add_le_add (hsub'.trans (add_le_add (htb q) hstrainb)) (hHb q))).trans_eq
      (by dsimp only [D]; ring)
  have hnormalb := (hnormal R₀ hn j u ell hu _ hdef s).trans <|
    sum_le_sum fun q _ ↦ sum_le_sum fun i _ ↦
      mul_le_mul_of_nonneg_left (hdatum (q-i)) (by positivity [hCn i, zero_le_one.trans hT])
  have hnormalp : cNorm (closedBall 0 r) s (meanNormalCorrection F (target - linearizedMetric F W - H)) ≤
      (∑ q ∈ range (s + 1), ∑ i ∈ range (q + 1), (q.choose i : ℝ) * Cn i * D (q-i)) * M ^ s := by
    apply hnormalb.trans
    rw [sum_mul]
    apply sum_le_sum
    intro q hq
    rw [sum_mul]
    apply sum_le_sum
    intro i hiq
    have hqs : q ≤ s := by have := mem_range.mp hq; omega
    have hiq' : i ≤ q := by have := mem_range.mp hiq; omega
    calc
      _ ≤ (q.choose i : ℝ) * Cn i * M ^ i * (D (q-i) * M ^ (q-i)) := by
        apply mul_le_mul_of_nonneg_right _
          (mul_nonneg (hD (q-i)) (pow_nonneg (zero_le_one.trans hM) _))
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (zero_le_one.trans hT) hTM i)
          (mul_nonneg (Nat.cast_nonneg _) (hCn i))
      _ = ((q.choose i : ℝ) * Cn i * D (q-i)) * M ^ q := by
        rw [show (q.choose i : ℝ) * Cn i * M ^ i * (D (q-i) * M ^ (q-i)) =
          ((q.choose i : ℝ) * Cn i * D (q-i)) * (M ^ i * M ^ (q-i)) by ring,
          ← pow_add, Nat.add_sub_of_le hiq']
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hM hqs) (by positivity [hCn i, hD (q-i)])
  change cNorm (closedBall 0 r) s (W + meanNormalCorrection F _) ≤ _
  apply (cNorm_add_local hrR hW (contDiffOn_meanNormalCorrection isOpen_ball hF.contDiffOn hdef hi hrank) s).trans
  have hWbound := (le_add_of_nonneg_right (cNorm_nonneg _ _ (linearizedMetric F W))).trans (hWb s)
  exact (add_le_add hWbound hnormalp).trans_eq (by dsimp only [C]; ring)

end JanetCartan.PhysicalMean
