module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.PhysicalCompletion.Profiles
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.UniformStep.FixedCutoff
public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.ProductBounds.Derivatives.SobolevComparison.Hilbert

/-!
# The same fixed cutoff preserves completed-mean profiles

The physical estimates in `main:eq:mean-coarse-size` and
`main:eq:mean-fine-size` concern the actual cut and periodized field.
Local smoothness on the original chart suffices. The cutoff is fixed before
fields, histories and scales; multiplication and periodization introduce
only constants at the same derivative order, without another power of the
varying frequency. Sobolev norms use the original normalized Haar measure.
-/

@[expose] public noncomputable section
open Set Finset
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.CurrentMean
open UniformStep.Periodization

/-- The jet/Sobolev comparison used in `main:eq:mean-fine-size` loses no
derivative order for the same smooth torus field and normalized Haar measure. -/
private theorem periodicSobolevNorm_le_cNorm {n N : ℕ}
    {f : Torus n → Euclidean N} (hf : IsSmoothPeriodic f) (s : ℕ) :
    periodicSobolevNorm s f ≤ sobolevPeriodicJetConstant n s * (s + 1) *
      cNorm (fundamentalCell n) s (periodicLift f) := by
  apply (periodicSobolevNorm_le_sum_periodicJet_uniform s hf).trans
  calc
    _ ≤ sobolevPeriodicJetConstant n s *
        ∑ _q ∈ range (s + 1), cNorm (fundamentalCell n) s (periodicLift f) := by
      apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans (one_le_sobolevPeriodicJetConstant n s))
      apply sum_le_sum
      intro q hq
      exact periodicL2Norm_le_of_bound _ (cNorm_nonneg _ _ _) (fun x ↦
        (norm_periodicJet_le_cNorm hf q x).trans (cNorm_mono_order (by have := mem_range.mp hq; omega)))
    _ = _ := by simp [mul_assoc]

/-- The original cutoff bounds the actual physical jets on its support,
and all jets vanish outside that support (`main:eq:mean-coarse-size`). -/
private theorem norm_iteratedFDeriv_cutField_le_local_cNorm {n N : ℕ}
    {r R : ℝ} (hrR : r < R) {χ : Euclidean n → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ Metric.closedBall 0 r)
    {f : Euclidean n → Euclidean N} (hf : ContDiffOn ℝ ∞ f (Metric.ball 0 R))
    (s q : ℕ) (hqs : q ≤ s) (x : Euclidean n) :
    ‖iteratedFDeriv ℝ q (cutField χ f) x‖ ≤ (2 : ℝ) ^ s *
      cNorm (Metric.closedBall 0 r) s χ * cNorm (Metric.closedBall 0 r) s f := by
  by_cases hx : x ∈ tsupport χ
  · have hxr := hs hx
    have hxR := Metric.closedBall_subset_ball hrR hxr
    let B : ℝ →L[ℝ] Euclidean N →L[ℝ] Euclidean N := ContinuousLinearMap.lsmul ℝ ℝ
    have hjet := B.norm_iteratedFDerivWithin_le_of_bilinear hχ.contDiffOn hf
      Metric.isOpen_ball.uniqueDiffOn hxR (n := q) (by simp)
    simp only [iteratedFDerivWithin_of_isOpen _ Metric.isOpen_ball hxR] at hjet
    have hχb (i : ℕ) (hi : i ≤ s) : ‖iteratedFDeriv ℝ i χ x‖ ≤
        cNorm (Metric.closedBall 0 r) s χ :=
      norm_iteratedFDeriv_le_cNorm (isCompact_closedBall _ _) (hχ.of_le (by simp)) hxr hi
    have hfb (i : ℕ) (hi : i ≤ s) : ‖iteratedFDeriv ℝ i f x‖ ≤
        cNorm (Metric.closedBall 0 r) s f :=
      norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall _ _)
        (fun y hy ↦ (hf.contDiffAt
          (Metric.isOpen_ball.mem_nhds (Metric.closedBall_subset_ball hrR hy))).of_le (by simp)) hxr hi
    change ‖iteratedFDeriv ℝ q (fun y ↦ B (χ y) (f y)) x‖ ≤ _
    apply hjet.trans
    calc
      _ ≤ 1 * ∑ i ∈ range (q + 1), (q.choose i : ℝ) *
          cNorm (Metric.closedBall 0 r) s χ * cNorm (Metric.closedBall 0 r) s f := by
        apply mul_le_mul ContinuousLinearMap.opNorm_lsmul_le _ (by positivity) zero_le_one
        apply sum_le_sum
        intro i hi
        have his : i ≤ s := by have := mem_range.mp hi; omega
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hχb i his) (Nat.cast_nonneg _))
          (hfb (q-i) ((Nat.sub_le _ _).trans hqs)) (norm_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _) (cNorm_nonneg _ _ _))
      _ = (2 : ℝ) ^ q * cNorm (Metric.closedBall 0 r) s χ *
          cNorm (Metric.closedBall 0 r) s f := by
        rw [one_mul, ← sum_mul, ← sum_mul]
        congr 2
        exact_mod_cast Nat.sum_range_choose q
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) hqs)
          (cNorm_nonneg _ _ _)) (cNorm_nonneg _ _ _)
  · have hz : iteratedFDeriv ℝ q (cutField χ f) x = 0 := by
      by_contra hz
      exact hx (tsupport_cutField_subset χ f (support_iteratedFDeriv_subset q hz))
    rw [hz, norm_zero]
    positivity [cNorm_nonneg (Metric.closedBall 0 r) s χ, cNorm_nonneg (Metric.closedBall 0 r) s f]

/-- The SAME fixed cutoff and periodization preserve both physical and
Sobolev profiles in `main:prop:mean`, using only local smoothness and the
input field's derivatives on the buffered compact. Constants are chosen
before the field and no global smooth extension is assumed. -/
theorem exists_cutToTorus_local_profile_bound {n N : ℕ} {r R : ℝ} (hrR : r < R) (hr : r < 1 / 2)
    (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hs : tsupport χ ⊆ Metric.closedBall 0 r) :
    ∃ C : ℕ → ℝ, (∀ s, 0 ≤ C s) ∧
      ∀ f : Euclidean n → Euclidean N, ContDiffOn ℝ ∞ f (Metric.ball 0 R) →
      IsSmoothPeriodic (cutToTorus χ f) ∧ ∀ s,
      cNorm (fundamentalCell n) s (periodicLift (cutToTorus χ f)) +
        periodicSobolevNorm s (cutToTorus χ f) ≤ C s * cNorm (Metric.closedBall 0 r) s f := by
  let L := fun s ↦ (s + 1 : ℕ) * (2 : ℝ) ^ s * cNorm (Metric.closedBall 0 r) s χ
  let C := fun s ↦ (1 + sobolevPeriodicJetConstant n s * (s + 1)) * L s
  have hL (s) : 0 ≤ L s := by dsimp [L]; positivity [cNorm_nonneg (Metric.closedBall 0 r) s χ]
  have hS (s) : 0 ≤ sobolevPeriodicJetConstant n s :=
    zero_le_one.trans (one_le_sobolevPeriodicJetConstant n s)
  refine ⟨C, fun s ↦ mul_nonneg (by positivity [hS s]) (hL s), ?_⟩
  intro f hf
  have hbox : tsupport (cutField χ f) ⊆ {x | ∀ i, |x i| ≤ r} := by
    intro x hx i
    have hxnorm : ‖x‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_zero_right] using hs (tsupport_cutField_subset χ f hx)
    exact (PiLp.norm_apply_le x i).trans hxnorm
  have hglob : ContDiff ℝ ∞ (cutField χ f) :=
    PrimarySourceAdmission.contDiff_cutoff_of_support_subset hχ Metric.isOpen_ball hf
      (hs.trans (Metric.closedBall_subset_ball hrR))
  have hperiodic : IsSmoothPeriodic (cutToTorus χ f) :=
    isSmoothPeriodic_vectorPeriodization hr hbox hglob
  refine ⟨hperiodic, ?_⟩
  intro s
  have hc : cNorm (fundamentalCell n) s (periodicLift (cutToTorus χ f)) ≤
      L s * cNorm (Metric.closedBall 0 r) s f := by
    have hh := cNorm_le_sum_of_bounds
      (s := fundamentalCell n) (r := s) (f := periodicLift (cutToTorus χ f))
      (C := fun _ ↦ (2 : ℝ) ^ s * cNorm (Metric.closedBall 0 r) s χ *
        cNorm (Metric.closedBall 0 r) s f)
      (fun _ _ ↦ by positivity [cNorm_nonneg (Metric.closedBall 0 r) s χ,
        cNorm_nonneg (Metric.closedBall 0 r) s f]) (fun q hq x hx ↦ by
          rw [show periodicLift (cutToTorus χ f) = periodicLift (vectorPeriodization (cutField χ f)) from rfl,
            iteratedFDeriv_vectorPeriodization_eq hr hbox q hx]
          exact norm_iteratedFDeriv_cutField_le_local_cNorm hrR hχ hs hf s q hq x)
    simpa only [sum_const, card_range, nsmul_eq_mul, L, mul_assoc] using hh
  have hsob := (periodicSobolevNorm_le_cNorm hperiodic s).trans
    (mul_le_mul_of_nonneg_left hc (by positivity [hS s]))
  exact (add_le_add hc hsob).trans_eq (by dsimp only [C]; ring)

/-- The actual history's completed field, after the ORIGINAL physical
cutoff, satisfies both bounds in `main:prop:mean` at its input scale and
offset. Geometry, cutoff multiplication and Sobolev transfer are discharged;
constants precede every history, target and field. The coarse specialization
is `ε=1, σ=0`; the fine specialization is `σ=n/2` with its actual residual
amplitude. No change to `forcingExponent` is made. -/
theorem exists_admissible_history_cutCompletedMeanField_profiles {n : ℕ}
    (G : FlatReference n) {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hR : R < G.domain.chartRadius) (hcell : r < 1 / 2)
    (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hs : tsupport χ ⊆ Metric.closedBall 0 r)
    {rStar kMin : ℕ} (hStar : 8 ≤ rStar)
    (horder : displacementLoss n + bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < kMin)
    (a b d : ℕ → ℝ) (ha : ∀ s, 0 ≤ a s) (hb : ∀ s, 0 ≤ b s) (hd : ∀ s, 0 ≤ d s) :
    ∃ S : ℝ, 2 ≤ S ∧ ∃ B : ℕ → ℝ, (∀ s, 0 ≤ B s) ∧
      ∀ R₀, S ≤ R₀ →
      ∀ (j : ℕ) (u : Fin j → Torus n → Euclidean (embeddingDimension n))
        (ell : Fin j → ℕ), IsAdmissibleHistory R₀ kMin u ell →
      ∀ (W : Euclidean n → Euclidean (embeddingDimension n)) (target H : MetricField n),
      ContDiffOn ℝ ∞ W (Metric.ball 0 R) →
      ContDiffOn ℝ ∞ target (Metric.ball 0 R) → ContDiffOn ℝ ∞ H (Metric.ball 0 R) →
      IsSmoothPeriodic (cutToTorus χ (completedMeanField (finiteHistoryMap G.map u) W target H)) ∧
      ∀ K ε σ : ℝ, currentCoefficientScale R₀ j ≤ K → 0 ≤ ε →
      (∀ s, cNorm (Metric.closedBall 0 r) s W +
        cNorm (Metric.closedBall 0 r) s (linearizedMetric (finiteHistoryMap G.map u) W) ≤
          a s * ε * K ^ ((s : ℝ) + σ)) →
      (∀ s, cNorm (Metric.closedBall 0 r) s target ≤ b s * ε * K ^ ((s : ℝ) + σ)) →
      (∀ s, cNorm (Metric.closedBall 0 r) s H ≤ d s * ε * K ^ ((s : ℝ) + σ)) →
      ∀ s, let V := cutToTorus χ (completedMeanField (finiteHistoryMap G.map u) W target H)
        cNorm (fundamentalCell n) s (periodicLift V) + periodicSobolevNorm s V ≤
          B s * ε * K ^ ((s : ℝ) + σ) := by
  obtain ⟨S, hS, B, hB, hprofile⟩ :=
    exists_admissible_history_completedMeanField_profile G hr hrR hR hStar horder a b d ha hb hd
  obtain ⟨D, hD, hcut⟩ := exists_cutToTorus_local_profile_bound (N := embeddingDimension n) hrR hcell χ hχ hs
  refine ⟨S, hS, fun s ↦ D s * B s, fun s ↦ mul_nonneg (hD s) (hB s), ?_⟩
  intro R₀ hR₀ j u ell hu W target H hW ht hH
  obtain ⟨hreg, hbnd⟩ := hprofile R₀ hR₀ j u ell hu W target H hW ht hH
  obtain ⟨hperiodic, hcutb⟩ := hcut _ hreg
  refine ⟨hperiodic, ?_⟩
  intro K ε σ hTK hε hWb htb hHb s
  exact (hcutb s).trans <| (mul_le_mul_of_nonneg_left
    (hbnd K ε σ hTK hε hWb htb hHb s) (hD s)).trans_eq (by ring)

/-- The original cutoff preserves the exact coarse/fine split of
`main:eq:mean-normal-field` globally on the torus. Differentiability is
needed only on the original physical chart containing its support. -/
theorem cutToTorus_completedMeanField_split {n N : ℕ}
    (F Vc Va : Euclidean n → Euclidean N) (target H Hc : MetricField n)
    (χ : Euclidean n → ℝ) {U : Set (Euclidean n)} (hU : IsOpen U)
    (hs : tsupport χ ⊆ U) (hVc : ContDiffOn ℝ ∞ Vc U) (hVa : ContDiffOn ℝ ∞ Va U) :
    cutToTorus χ (completedMeanField F (Vc + Va) target H) =
      cutToTorus χ (completedMeanField F Vc 0 Hc) +
        cutToTorus χ (completedMeanField F Va target (H - Hc)) := by
  funext z
  let x := AmplitudeBound.centeredTorusRepresentative z
  change χ x • completedMeanField F (Vc + Va) target H x =
    χ x • completedMeanField F Vc 0 Hc x + χ x • completedMeanField F Va target (H - Hc) x
  by_cases hx : χ x = 0
  · simp only [hx, zero_smul, add_zero]
  · have hxU : x ∈ U := hs (subset_tsupport χ hx)
    rw [completedMeanField_split F Vc Va target H Hc
      ((hVc.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp))
      ((hVa.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)), smul_add]

end JanetCartan.CurrentMean
