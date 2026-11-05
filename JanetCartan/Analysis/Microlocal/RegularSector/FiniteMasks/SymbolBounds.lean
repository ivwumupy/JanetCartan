module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteMasks.Conic
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets.AffinePullback
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.PrimitiveProfiles.NormalizedSeminorms

/-!
# Normalized symbol budgets for the fixed sector masks

The smooth radially collared angular mask has finite normalized seminorms on
every compact frequency buffer away from zero, uniformly over all shell
radii. On the bounded range of radii this follows from the literal affine
chain rule. At large radii the cutoff is identically one near the buffer, so
all normalized jets are those of one fixed radial lift. No symbol budget is
assumed. This supplies the multiplier input of
`EvolutionIntegral.SymbolBudgets.hasFullSourceSymbolBound_elapsedAmplitude`
in `app:ch_regular_base:lem:retarded-kernel`.
-/

@[expose] public noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace JanetCartan.RegularSector.FiniteMasks
open CompatibleResponse FourierIntegral.PrimitiveProfiles
open Characteristic.EvolutionIntegral.SymbolBudgets
variable {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
local notation "E" => Euclidean n
local notation "P" => X × Euclidean n

private theorem cNorm_scaled_mask_le (f : E → ℂ) (hf : ContDiff ℝ ∞ f)
    {K : Set P} {B L R : ℝ} (hL : 1 ≤ L)
    (hR : 1 ≤ R) (hRL : R ≤ L) (hK : ∀ p ∈ K, ‖p.2‖ ≤ B) (m : ℕ) :
    cNorm K m (fun p ↦ f (R • p.2)) ≤
      (m + 1 : ℝ) * (cNorm (closedBall (0 : E) (L * B)) m f * L ^ m) := by
  let T : P →L[ℝ] E := R • ContinuousLinearMap.snd ℝ X E
  have hT : ‖T‖ ≤ L := by
    apply le_trans (norm_smul_le R (ContinuousLinearMap.snd ℝ X E))
    rw [Real.norm_of_nonneg (zero_le_one.trans hR)]
    exact (mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_snd_le _ _ _) (by linarith)).trans
      (by simpa using hRL)
  have hp (p : P) (hp : p ∈ K) : T p ∈ closedBall (0 : E) (L * B) := by
    change ‖R • p.2 - (0 : E)‖ ≤ L * B
    rw [sub_zero, norm_smul, Real.norm_of_nonneg (zero_le_one.trans hR)]
    exact mul_le_mul hRL (hK p hp) (norm_nonneg _) (by linarith)
  have hb (k : ℕ) (hk : k ≤ m) (p : P) (hpk : p ∈ K) :
      ‖iteratedFDeriv ℝ k (fun p : P ↦ f (R • p.2)) p‖ ≤
        cNorm (closedBall (0 : E) (L * B)) m f * L ^ m := by
    have hder := norm_iteratedFDeriv_preAffine_le (x := p) T (0 : E) isOpen_univ
      hf.contDiffOn (mem_univ (T p)) k
    simp only [add_zero] at hder
    apply hder.trans
    exact mul_le_mul
      (norm_iteratedFDeriv_le_cNorm (isCompact_closedBall _ _) (hf.of_le (by simp)) (hp p hpk) hk)
      ((pow_le_pow_left₀ (norm_nonneg _) hT k).trans (pow_le_pow_right₀ hL hk))
      (by positivity) (cNorm_nonneg _ _ _)
  have := cNorm_le_sum_of_bounds
    (fun k (_ : k ≤ m) ↦ mul_nonneg (cNorm_nonneg _ _ _) (pow_nonneg (by linarith) m)) hb
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    using this

/-- The actual fixed mask supplies every order-zero normalized shell budget.
Both position variables are retained in the joint domain. The only geometric
inputs are compactness and exclusion of zero on that normalized buffer
(`app:ch_regular_base:lem:retarded-kernel`). -/
theorem boundedNormalizedSeminorm_conicMask
    {a : E → ℝ} (ha : ContDiff ℝ ∞ a) {K : Set P} (hK : IsCompact K)
    (hzero : ∀ p ∈ K, p.2 ≠ 0) (m : ℕ) :
    BoundedNormalizedSeminorm K m (fun p : P ↦ (conicMask a p.2 : ℂ)) := by
  obtain ⟨c, hc, hlow⟩ := hK.exists_forall_le'
    (continuous_snd.norm.continuousOn) (fun p hp ↦ norm_pos_iff.mpr (hzero p hp))
  obtain ⟨B, hB, hupper⟩ := hK.isBounded.exists_pos_norm_le
  let L := max 1 (3 / c)
  have hL : 1 ≤ L := le_max_left _ _
  have hLc : 2 < L * c := by
    have ht := mul_le_mul_of_nonneg_right (le_max_right 1 (3 / c)) hc.le
    rw [div_mul_cancel₀ _ hc.ne'] at ht
    linarith
  let f : E → ℂ := fun ξ ↦ conicMask a ξ
  have hf : ContDiff ℝ ∞ f := Complex.ofRealCLM.contDiff.comp (contDiff_conicMask ha)
  let C := (m + 1 : ℝ) * (cNorm (closedBall (0 : E) (L * B)) m f * L ^ m)
  have hsmall (R : ℝ) (hR : 1 ≤ R) (hRL : R ≤ L) :
      cNorm K m (fun p : P ↦ f (R • p.2)) ≤ C :=
    cNorm_scaled_mask_le f hf hL hR hRL
      (fun p hp ↦ (norm_snd_le p).trans (hupper p hp)) m
  refine ⟨C, ?_⟩
  rintro _ ⟨R, rfl⟩
  change cNorm K m (fun p : P ↦ f ((R : ℝ) • p.2)) ≤ C
  by_cases hRL : (R : ℝ) ≤ L
  · exact hsmall R R.2 hRL
  · have hLR : L ≤ (R : ℝ) := (lt_of_not_ge hRL).le
    have he (p : P) (hp : p ∈ K) :
        (fun p : P ↦ f ((R : ℝ) • p.2)) =ᶠ[𝓝 p] (fun p ↦ f (L • p.2)) := by
      have hLp : 2 < L * ‖p.2‖ := hLc.trans_le
        (mul_le_mul_of_nonneg_left (hlow p hp) (by linarith))
      filter_upwards [((continuous_const.mul continuous_snd.norm).continuousAt.eventually
        (lt_mem_nhds hLp))] with q hq
      have hRq : 2 ≤ ‖(R : ℝ) • q.2‖ := by
        rw [norm_smul, Real.norm_of_nonneg (zero_le_one.trans R.2)]
        exact hq.le.trans (mul_le_mul_of_nonneg_right hLR (norm_nonneg _))
      have hLq : 2 ≤ ‖L • q.2‖ := by
        rw [norm_smul, Real.norm_of_nonneg (zero_le_one.trans hL)]
        exact hq.le
      dsimp [f]
      rw [conicMask_eq_radial hRq, conicMask_eq_radial hLq,
        radialSourceCutoff_smul a _ (zero_lt_one.trans_le R.2),
        radialSourceCutoff_smul a _ (zero_lt_one.trans_le hL)]
    have hn : cNorm K m (fun p : P ↦ f ((R : ℝ) • p.2)) =
        cNorm K m (fun p : P ↦ f (L • p.2)) := by
      unfold cNorm
      apply Finset.sum_congr rfl
      intro k _
      congr 1
      apply Set.image_congr
      intro p hp
      rw [((he p hp).iteratedFDeriv ℝ k).eq_of_nhds]
    rw [hn]
    exact hsmall L hL le_rfl

end JanetCartan.RegularSector.FiniteMasks
