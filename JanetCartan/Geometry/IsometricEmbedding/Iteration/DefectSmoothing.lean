module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.DefectSmoothing.Combined
public import JanetCartan.Geometry.IsometricEmbedding.Reference.Initialization.LocalTarget

/-!
# Smoothing the actual finite-history defect

The fixed Seeley extension and Fourier cutoff act on the literal signed metric
defect. The high profile is derived from finite-history budgets and local target
dilation bounds; the independent small and high tails yield the geometric-mean
estimate at `Q = 2k`. Both low profiles and the normalized source refer to this
same output. Constants precede target dilation, scales, accuracy and history.

Only primitive reference/target data, admissible-history budgets and the genuine
zeroth-defect bound remain inputs. This proves the smoothing component of the
step, not the other components of the uniform correction theorem.
-/

@[expose] public noncomputable section
open scoped ContDiff Matrix.Norms.Frobenius
open Set

namespace JanetCartan.DefectSmoothing

variable {n : ℕ}

/-- `main:eq:smoothing-low`: actual finite histories, with the constant fixed
before every later target, scale, accuracy and history. The sole quantitative
input here is the genuine zeroth defect bound. -/
theorem exists_history_low_bound (D : LocalDomain) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R → ∀ (g : MetricField n),
      ContDiffOn ℝ ∞ g (D.chart n) → ∀ (G : FlatReference n) (R₀ : ℝ)
      (kMin j : ℕ) (u : Fin j → Torus n → Euclidean (embeddingDimension n))
      (ell : Fin j → ℕ), IsAdmissibleHistory R₀ kMin u ell → ∀ δ : ℝ,
      cNorm (D.core n) 0 (historyDefect g G.map u) ≤ δ ^ 2 →
      ∀ s : Set (Euclidean n),
      cNorm s r (periodicLift (smoothedHistoryDefect D R g G.map u)) +
        periodicSobolevNorm (r : ℝ) (smoothedHistoryDefect D R g G.map u) ≤
          C * δ ^ 2 * R ^ r := by
  obtain ⟨C, hC, hb⟩ := exists_smoothTensor_low_bound (n := n) D r
  refine ⟨C, hC, ?_⟩
  intro R hR g hg G R₀ kMin j u ell hu δ hδ s
  exact hb R hR _ (contDiffOn_historyDefect hg G.contDiff hu) δ hδ s

/-- `main:eq:smoothing-small`: the independently derived small tail for the
same actual history defect, without a high-tail hypothesis. -/
theorem exists_history_small_tail_bound (D : LocalDomain) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R → ∀ (g : MetricField n),
      ContDiffOn ℝ ∞ g (D.chart n) → ∀ (G : FlatReference n) (R₀ : ℝ)
      (kMin j : ℕ) (u : Fin j → Torus n → Euclidean (embeddingDimension n))
      (ell : Fin j → ℕ), IsAdmissibleHistory R₀ kMin u ell → ∀ δ : ℝ,
      cNorm (D.core n) 0 (historyDefect g G.map u) ≤ δ ^ 2 →
      cNorm (D.core n) 0 (historyDefect g G.map u -
        periodicLift (smoothedHistoryDefect D R g G.map u)) ≤ C * δ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := exists_smoothTensor_small_tail_bound (n := n) D
  refine ⟨C, hC, ?_⟩
  intro R hR g hg G R₀ kMin j u ell hu δ hδ
  exact hb R hR _ (contDiffOn_historyDefect hg G.contDiff hu) δ hδ

/-- `main:eq:smoothing-low` for the actual locally smooth normalized target
family. The common dilation interval is supplied by the already proved local
target theorem. In particular smoothness of the dilated target is discharged,
not left as a target-family oracle. -/
theorem exists_local_target_history_low_bound (D : LocalDomain) {ρ : ℝ} (hρ : 0 < ρ)
    {g : MetricField n} {U : Set (Euclidean n)} (hU : IsOpen U)
    (h0 : (0 : Euclidean n) ∈ U) (hg : ContDiffOn ℝ ∞ g U) (hg0 : g 0 = 1) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1 ∧ ∀ r : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ s ∈ Icc (0 : ℝ) s₀, ∀ R : ℝ, 1 ≤ R →
      ∀ (G : FlatReference n) (R₀ : ℝ) (kMin j : ℕ)
        (u : Fin j → Torus n → Euclidean (embeddingDimension n)) (ell : Fin j → ℕ),
      IsAdmissibleHistory R₀ kMin u ell → ∀ δ : ℝ,
      cNorm (D.core n) 0 (historyDefect (fun x ↦ g ((s * ρ) • x)) G.map u) ≤ δ ^ 2 →
      ∀ K : Set (Euclidean n),
      cNorm K r (periodicLift (smoothedHistoryDefect D R (fun x ↦ g ((s * ρ) • x)) G.map u)) +
        periodicSobolevNorm (r : ℝ)
          (smoothedHistoryDefect D R (fun x ↦ g ((s * ρ) • x)) G.map u) ≤
            C * δ ^ 2 * R ^ r := by
  obtain ⟨s₀, hs₀, hs₁, hmaps, _⟩ := exists_local_target_dilation_bounds D hρ hU h0 hg hg0
  refine ⟨s₀, hs₀, hs₁, ?_⟩
  intro r
  obtain ⟨C, hC, hb⟩ := exists_history_low_bound (n := n) D r
  refine ⟨C, hC, ?_⟩
  intro s hs R hR G R₀ kMin j u ell hu δ hδ K
  apply hb R hR _ _ G R₀ kMin j u ell hu δ hδ K
  apply hg.comp (contDiff_id.const_smul (s * ρ)).contDiffOn
  intro x hx
  exact hmaps s hs x (Metric.ball_subset_closedBall hx)


/-- The concrete construction in `main:lem:smoothing`, specialized to the actual
local normalized target and `δ = R^(-k)`. The output is the same fixed extension
and cutoff at every order. This supplies `StageConstants.ComponentEstimates.smoothing`
and both profiles for the current mean's literal `eR/b²`.

All constants and the common dilation interval precede accuracy, dilation,
initial scale, stage and history. The only quantitative hypotheses are the
prospective history budgets and the actual zeroth-defect bound; high profiles,
small/high tails and smoothing error are proved, not assumed. Symmetry is
preserved whenever the primitive target is symmetric. -/
theorem exists_local_target_history_smoothing
    (D : LocalDomain) (G : FlatReference n) {ρ : ℝ} (hρ : 0 < ρ)
    {g : MetricField n} {U : Set (Euclidean n)} (hU : IsOpen U)
    (h0 : (0 : Euclidean n) ∈ U) (hg : ContDiffOn ℝ ∞ g U) (hg0 : g 0 = 1)
    {kMin : ℕ}
    (horder : displacementLoss n + bandExponent * (1 + (n : ℝ) / 2) + 2 < kMin) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1 ∧ ∃ L A C : ℕ → ℝ,
      (∀ r, 0 ≤ L r) ∧ (∀ r, 0 ≤ A r) ∧ (∀ k, 0 ≤ C k) ∧
      ∀ k : ℕ, ∀ s ∈ Icc (0 : ℝ) s₀, ∀ R₀ : ℝ, 2 ≤ R₀ →
        ∀ (j : ℕ) (u : Fin j → Torus n → Euclidean (embeddingDimension n))
          (ell : Fin j → ℕ), IsAdmissibleHistory R₀ kMin u ell →
        let R := iterationScale R₀ growthExponent j
        let δ := R ^ (-(k : ℝ))
        let gs := fun x ↦ g ((s * ρ) • x)
        let e := historyDefect gs G.map u
        cNorm (D.core n) 0 e ≤ δ ^ 2 →
        let eR := smoothedHistoryDefect D R gs G.map u
        IsSmoothPeriodic eR ∧ HasFourierSupport (2 * R) eR ∧
        ((∀ x ∈ D.core n, (gs x).IsSymm) → ∀ z, (eR z).IsSymm) ∧
        (∀ r (K : Set (Euclidean n)),
          cNorm K r (periodicLift eR) + periodicSobolevNorm (r : ℝ) eR ≤
            L r * δ ^ 2 * R ^ r) ∧
        (∀ r (K : Set (Euclidean n)),
          cNorm K r (periodicLift (normalizedHistorySource D R δ gs G.map u)) +
            periodicSobolevNorm (r : ℝ) (normalizedHistorySource D R δ gs G.map u) ≤
              A r * R ^ ((r : ℝ) - 2 * forcingExponent n)) ∧
        cNorm (D.core n) 0 (e - periodicLift eR) ≤ C k * δ * R ^ (-2 * (k : ℝ)) ∧
        (∀ x ∈ D.core n, ‖periodicLift eR x - e x‖ ≤
          C k * δ * R ^ (-2 * (k : ℝ))) := by
  obtain ⟨s₀, hs₀, hs₁, hmaps, C, hC, hc⟩ :=
    exists_history_combined_tail_bound D G hρ hU h0 hg hg0 horder
  choose L hL hl using fun r ↦ exists_history_low_bound (n := n) D r
  choose A hA ha using fun r ↦ exists_normalizedHistorySource_bound (n := n) D r
  refine ⟨s₀, hs₀, hs₁, L, A, C, hL, hA, hC, ?_⟩
  intro k s hs R₀ hR₀ j u ell hu
  dsimp only
  intro hsmall
  let R := iterationScale R₀ growthExponent j
  let δ := R ^ (-(k : ℝ))
  let gs := fun x ↦ g ((s * ρ) • x)
  let e := historyDefect gs G.map u
  let eR := smoothedHistoryDefect D R gs G.map u
  have hR1 : 1 ≤ R := Real.one_le_rpow (by linarith)
    (pow_nonneg (by norm_num [growthExponent]) _)
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  have hδ : 0 < δ := Real.rpow_pos_of_pos hR _
  have ht : ContDiffOn ℝ ∞ gs (D.chart n) :=
    hg.comp (contDiff_id.const_smul (s * ρ)).contDiffOn
      (fun x hx ↦ hmaps s hs x (Metric.ball_subset_closedBall hx))
  have he : ContDiffOn ℝ ∞ e (D.chart n) := contDiffOn_historyDefect ht G.contDiff hu
  have heR : IsSmoothPeriodic eR := isSmoothPeriodic_smoothedHistoryDefect D R gs G.map u
  have herror : cNorm (D.core n) 0 (e - periodicLift eR) ≤
      C k * δ * R ^ (-2 * (k : ℝ)) :=
    hc k s hs R₀ hR₀ j u ell hu δ hδ.le hsmall
  refine ⟨heR, hasFourierSupport_smoothedHistoryDefect hR ht G.contDiff hu,
    ?_, ?_, ?_, herror, ?_⟩
  · intro hsym z
    exact smoothedHistoryDefect_isSymm ht hsym G.contDiff hu z
  · intro r K
    exact hl r R hR1 gs ht G R₀ kMin j u ell hu δ hsmall K
  · intro r K
    exact ha r R hR1 δ hδ gs ht G R₀ kMin j u ell hu hsmall K
  · intro x hx
    have hpoint : ‖(e - periodicLift eR) x‖ ≤ cNorm (D.core n) 0 (e - periodicLift eR) := by
      simpa only [norm_iteratedFDeriv_zero] using
        norm_iteratedFDeriv_le_cNorm_of_contDiffAt (s := D.core n)
          (f := e - periodicLift eR) (r := 0) (j := 0) (isCompact_closedBall _ _)
          (fun y hy ↦ ((he.contDiffAt (Metric.isOpen_ball.mem_nhds
            (Metric.closedBall_subset_ball D.coreRadius_lt_chartRadius hy))).sub
              heR.2.contDiffAt).of_le (by simp)) hx le_rfl
    calc
      ‖periodicLift eR x - e x‖ = ‖(e - periodicLift eR) x‖ := norm_sub_rev _ _
      _ ≤ _ := hpoint.trans herror

end JanetCartan.DefectSmoothing
