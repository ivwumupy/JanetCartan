module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.PhysicalCompletion.HistoryBounds

/-!
# Uniform profiles for the single physical normal completion

For `main:eq:mean-coarse-size` and `main:eq:mean-fine-size`, apply the
actual finite-history normal multiplier to the original uncompleted field,
its full strain, the target and the self tensor. Its coefficient profiles
are derived from the existing geometric-history producer. Constants precede
all histories and all input fields, and no completed-mean estimate is assumed.
The offset in the power is retained, so the SAME theorem applies to the
coarse scale and to the fine `n/2` loss.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Finset
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.CurrentMean
open AmbientResponse CurrentCoefficientProfiles

/-- The normal multiplier's Leibniz convolution preserves the original
input scale and offset (`main:eq:mean-coarse-size`, `main:eq:mean-fine-size`). -/
private theorem profile_convolution_le (C D : ℕ → ℝ)
    (hC : ∀ i, 0 ≤ C i) (hD : ∀ i, 0 ≤ D i)
    {T K ε σ : ℝ} (hT : 0 ≤ T) (hTK : T ≤ K) (hK : 1 ≤ K) (hε : 0 ≤ ε)
    (s : ℕ) :
    (∑ q ∈ range (s + 1), ∑ i ∈ range (q + 1),
      (q.choose i : ℝ) * C i * T ^ i * (D (q-i) * ε * K ^ ((q-i : ℕ) + σ))) ≤
    (∑ q ∈ range (s + 1), ∑ i ∈ range (q + 1),
      (q.choose i : ℝ) * C i * D (q-i)) * ε * K ^ ((s : ℝ) + σ) := by
  have hp : 0 < K := zero_lt_one.trans_le hK
  rw [sum_mul, sum_mul]
  apply sum_le_sum
  intro q hq
  rw [sum_mul, sum_mul]
  apply sum_le_sum
  intro i hi
  have hqs : q ≤ s := by have := mem_range.mp hq; omega
  have hiq : i ≤ q := by have := mem_range.mp hi; omega
  have hcoef : 0 ≤ (q.choose i : ℝ) * C i * D (q-i) * ε := by positivity [hC i, hD (q-i)]
  calc
    _ ≤ (q.choose i : ℝ) * C i * K ^ i * (D (q-i) * ε * K ^ ((q-i : ℕ) + σ)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity [hD (q-i)])
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hT hTK i) (by positivity [hC i])
    _ = ((q.choose i : ℝ) * C i * D (q-i) * ε) * K ^ ((q : ℝ) + σ) := by
      rw [← Real.rpow_natCast K i]
      have he : (i : ℝ) + ((q-i : ℕ) + σ) = (q : ℝ) + σ := by rw [Nat.cast_sub hiq]; ring
      rw [show (q.choose i : ℝ) * C i * K ^ (i : ℝ) * (D (q-i) * ε * K ^ ((q-i : ℕ) + σ)) =
        ((q.choose i : ℝ) * C i * D (q-i) * ε) * (K ^ (i : ℝ) * K ^ ((q-i : ℕ) + σ)) by ring,
        ← Real.rpow_add hp, he]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hK (add_le_add (Nat.cast_le.mpr hqs) le_rfl)) hcoef

/-- Local smoothness suffices for the physical field sum in
`main:eq:mean-normal-field` on the buffered compact domain. -/
private theorem cNorm_add_on {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : Euclidean n → E} {r R : ℝ} (hrR : r < R)
    (hf : ContDiffOn ℝ ∞ f (Metric.ball 0 R))
    (hg : ContDiffOn ℝ ∞ g (Metric.ball 0 R)) (s : ℕ) :
    cNorm (Metric.closedBall 0 r) s (f + g) ≤
      cNorm (Metric.closedBall 0 r) s f + cNorm (Metric.closedBall 0 r) s g := by
  apply cNorm_add_le_of_contDiffAt (isCompact_closedBall _ _)
  · intro x hx
    exact (hf.contDiffAt (Metric.isOpen_ball.mem_nhds (Metric.closedBall_subset_ball hrR hx))).of_le (by simp)
  · intro x hx
    exact (hg.contDiffAt (Metric.isOpen_ball.mem_nhds (Metric.closedBall_subset_ball hrR hx))).of_le (by simp)

/-- The literal tensor defect in `main:eq:mean-normal-field` uses
subtraction on the same compact domain and its original smooth neighborhood. -/
private theorem cNorm_sub_on {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : Euclidean n → E} {r R : ℝ} (hrR : r < R)
    (hf : ContDiffOn ℝ ∞ f (Metric.ball 0 R))
    (hg : ContDiffOn ℝ ∞ g (Metric.ball 0 R)) (s : ℕ) :
    cNorm (Metric.closedBall 0 r) s (f - g) ≤
      cNorm (Metric.closedBall 0 r) s f + cNorm (Metric.closedBall 0 r) s g := by
  simpa only [sub_eq_add_neg, cNorm_neg] using
    cNorm_add_on (f := f) (g := -g) hrR hf hg.neg s

/-- The actual history's single completed mean has the scale of its
uncompleted field, FULL strain, target and self tensor
(`main:eq:mean-coarse-size`, `main:eq:mean-fine-size`). The geometric
multiplier and its uniformity are discharged. The preparation and canonical
producers must supply the displayed input profiles; no completed field or
canonical-adjoint bound is a premise. -/
theorem exists_admissible_history_completedMeanField_profile {n : ℕ}
    (G : FlatReference n) {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hR : R < G.domain.chartRadius) {rStar kMin : ℕ} (hStar : 8 ≤ rStar)
    (horder : displacementLoss n + bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < kMin)
    (a b d : ℕ → ℝ) (ha : ∀ s, 0 ≤ a s) (hb : ∀ s, 0 ≤ b s) (hd : ∀ s, 0 ≤ d s) :
    ∃ S : ℝ, 2 ≤ S ∧ ∃ B : ℕ → ℝ, (∀ s, 0 ≤ B s) ∧
      ∀ R₀, S ≤ R₀ →
      ∀ (j : ℕ) (u : Fin j → Torus n → Euclidean (embeddingDimension n))
        (ell : Fin j → ℕ), IsAdmissibleHistory R₀ kMin u ell →
      ∀ (W : Euclidean n → Euclidean (embeddingDimension n)) (target H : MetricField n),
      ContDiffOn ℝ ∞ W (Metric.ball 0 R) →
      ContDiffOn ℝ ∞ target (Metric.ball 0 R) → ContDiffOn ℝ ∞ H (Metric.ball 0 R) →
      ContDiffOn ℝ ∞ (completedMeanField (finiteHistoryMap G.map u) W target H)
        (Metric.ball 0 R) ∧ ∀ K ε σ : ℝ, currentCoefficientScale R₀ j ≤ K → 0 ≤ ε →
      (∀ s, cNorm (Metric.closedBall 0 r) s W +
        cNorm (Metric.closedBall 0 r) s (linearizedMetric (finiteHistoryMap G.map u) W) ≤
          a s * ε * K ^ ((s : ℝ) + σ)) →
      (∀ s, cNorm (Metric.closedBall 0 r) s target ≤ b s * ε * K ^ ((s : ℝ) + σ)) →
      (∀ s, cNorm (Metric.closedBall 0 r) s H ≤ d s * ε * K ^ ((s : ℝ) + σ)) →
      ∀ s, cNorm (Metric.closedBall 0 r) s
        (completedMeanField (finiteHistoryMap G.map u) W target H) ≤
          B s * ε * K ^ ((s : ℝ) + σ) := by
  obtain ⟨Sn, hSn, C, hC, hnormal⟩ :=
    exists_admissible_history_meanNormalCorrection_bounds G hr hrR hR hStar horder
  obtain ⟨Sg, hSg, C₀, _, κ, _, A, Cg, _, _, hgeometry⟩ :=
    exists_admissible_history_geometric_profiles G hr hrR hR hStar (show 2 + 0 ≤ rStar by omega) horder
  let D := fun s ↦ b s + a s + d s
  have hD : ∀ s, 0 ≤ D s := fun s ↦ add_nonneg (add_nonneg (hb s) (ha s)) (hd s)
  let B := fun s ↦ a s + ∑ q ∈ range (s + 1), ∑ i ∈ range (q + 1),
    (q.choose i : ℝ) * C i * D (q-i)
  refine ⟨max Sn Sg, hSn.trans (le_max_left _ _), B, ?_, ?_⟩
  · intro s
    exact add_nonneg (ha s) (sum_nonneg fun q _ ↦ sum_nonneg fun i _ ↦ by positivity [hC i, hD (q-i)])
  intro R₀ hR₀ j u ell hu W target H hW ht hH
  have hn := (le_max_left Sn Sg).trans hR₀
  have hg := (le_max_right Sn Sg).trans hR₀
  have hR₀two := hSn.trans hn
  let F := finiteHistoryMap G.map u
  have hF : ContDiff ℝ ∞ F := hu.contDiff_finiteHistoryMap G.contDiff
  obtain ⟨hi, hrank, _⟩ := hgeometry R₀ hg j u ell hu
  refine ⟨contDiffOn_completedMeanField Metric.isOpen_ball hF.contDiffOn hW ht hH hi hrank, ?_⟩
  intro K ε σ hTK hε hWb htb hHb s
  have hT : 1 ≤ currentCoefficientScale R₀ j := one_le_currentCoefficientScale (by linarith) j
  have hK : 1 ≤ K := hT.trans hTK
  have hstrain := AmbientResponse.contDiffOn_linearizedMetric Metric.isOpen_ball hF.contDiffOn hW
  have hdef : ContDiffOn ℝ ∞ (target - linearizedMetric F W - H) (Metric.ball 0 R) :=
    (ht.sub hstrain).sub hH
  have hdatum (q : ℕ) : cNorm (Metric.closedBall 0 r) q (target - linearizedMetric F W - H) ≤
      D q * ε * K ^ ((q : ℝ) + σ) := by
    have hsub := cNorm_sub_on hrR (ht.sub hstrain) hH q
    have hsub' := cNorm_sub_on hrR ht hstrain q
    have hstrainb : cNorm (Metric.closedBall 0 r) q (linearizedMetric F W) ≤
        a q * ε * K ^ ((q : ℝ) + σ) :=
      (le_add_of_nonneg_left (cNorm_nonneg _ _ W)).trans (hWb q)
    exact (hsub.trans (add_le_add (hsub'.trans (add_le_add (htb q) hstrainb)) (hHb q))).trans_eq
      (by dsimp only [D]; ring)
  have hnormalb := (hnormal R₀ hn j u ell hu _ hdef s).trans <|
    sum_le_sum fun q _ ↦ sum_le_sum fun i _ ↦
      mul_le_mul_of_nonneg_left (hdatum (q-i)) (by positivity [hC i])
  have hnormalp := hnormalb.trans (profile_convolution_le C D hC hD (zero_le_one.trans hT) hTK hK hε s)
  have hreg := contDiffOn_meanNormalCorrection Metric.isOpen_ball hF.contDiffOn hdef hi hrank
  change cNorm (Metric.closedBall 0 r) s (W + meanNormalCorrection F _) ≤ _
  apply (cNorm_add_on hrR hW hreg s).trans
  have hWbound := (le_add_of_nonneg_right (cNorm_nonneg _ _ (linearizedMetric F W))).trans (hWb s)
  exact (add_le_add hWbound hnormalp).trans_eq (by dsimp only [B]; ring)

/-- The coarse and fine fields in `main:eq:mean-coarse-size` and
`main:eq:mean-fine-size` are two explicit instances of the SAME normal
completion. Their sum is the singly completed final field, on the original
physical domain; no completed-field estimate is assumed. -/
theorem completedMeanField_split {n N : ℕ} (F Vc Va : Euclidean n → Euclidean N) (target H Hc : MetricField n)
    {x : Euclidean n} (hVc : DifferentiableAt ℝ Vc x) (hVa : DifferentiableAt ℝ Va x) :
    completedMeanField F (Vc + Va) target H x =
      completedMeanField F Vc 0 Hc x + completedMeanField F Va target (H - Hc) x := by
  rw [completedMeanField_eq_coarse_add_fine F Vc Va target H Hc hVc hVa]
  simp only [completedMeanField, meanNormalCorrection, Pi.add_apply, Pi.sub_apply,
    Pi.neg_apply, zero_sub, map_neg, map_sub, map_add, neg_smul, smul_sub, smul_add, smul_neg, neg_neg]
  abel

end JanetCartan.CurrentMean
