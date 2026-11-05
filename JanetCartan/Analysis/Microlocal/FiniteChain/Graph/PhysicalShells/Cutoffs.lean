module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelLimits.Integrability
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Fixed physical frequency cutoffs

The graph regularizers for `app:ch_regular:eq:joint-kernel-phase` must each avoid
zero, while their sum covers every nonzero covector. Pairing expanding and
contracting dyadic annuli gives a natural-number index without deleting the
bounded-frequency part. The independent output family includes a low ball.
These cutoffs depend on neither the requested accuracy nor the symbol order.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace JanetCartan.FiniteChain.Graph.PhysicalShells
open FourierIntegral
variable {n r : ℕ}

/-- The fixed unit plateau used in the shell partition for
`app:ch_regular:eq:joint-kernel-phase`. -/
def frequencyBump (n : ℕ) : ContDiffBump (0 : Euclidean n) :=
  ⟨1, 2, by norm_num, by norm_num⟩

/-- The expanding dyadic balls for `app:ch_regular:eq:chain-tail`. -/
def expandingCutoff (j : ℕ) (ξ : Euclidean n) : ℝ :=
  frequencyBump n (((2 : ℝ) ^ j)⁻¹ • ξ)

/-- The contracting dyadic balls retain arbitrarily small graph frequencies
in `app:ch_regular:eq:chain-tail`. -/
def contractingCutoff (j : ℕ) (ξ : Euclidean n) : ℝ :=
  frequencyBump n ((2 : ℝ) ^ j • ξ)

/-- One expanding graph annulus (`app:ch_regular:eq:chain-tail`). -/
def highGraphCutoff (j : ℕ) (ξ : Euclidean n) : ℝ :=
  expandingCutoff (j + 1) ξ - expandingCutoff j ξ

/-- One contracting graph annulus (`app:ch_regular:eq:chain-tail`). -/
def lowGraphCutoff (j : ℕ) (ξ : Euclidean n) : ℝ :=
  contractingCutoff j ξ - contractingCutoff (j + 1) ξ

/-- The graph cutoff supplied to `KernelLimits.exists_jointKernel_physical_extension`.
Each term avoids zero; the low and high annuli are both retained
(`app:ch_regular:eq:joint-kernel-phase`). -/
def graphCutoff (j : ℕ) (ξ : Euclidean n) : ℝ :=
  highGraphCutoff j ξ + lowGraphCutoff j ξ

/-- The independently indexed output cutoff, including its bounded-frequency
ball (`app:ch_regular:eq:joint-kernel-phase`). -/
def outputCutoff : ℕ → Euclidean n → ℝ
  | 0 => expandingCutoff 0
  | j + 1 => highGraphCutoff j

/-- Smoothness of expanding physical cutoffs (`app:ch_regular:eq:chain-tail`). -/
theorem contDiff_expandingCutoff (j : ℕ) : ContDiff ℝ ∞ (expandingCutoff (n := n) j) :=
  (frequencyBump n).contDiff.comp (contDiff_id.const_smul _)

/-- Smoothness of contracting physical cutoffs (`app:ch_regular:eq:chain-tail`). -/
theorem contDiff_contractingCutoff (j : ℕ) : ContDiff ℝ ∞ (contractingCutoff (n := n) j) :=
  (frequencyBump n).contDiff.comp (contDiff_id.const_smul _)

/-- Smoothness of expanding annuli (`app:ch_regular:eq:chain-tail`). -/
theorem contDiff_highGraphCutoff (j : ℕ) : ContDiff ℝ ∞ (highGraphCutoff (n := n) j) :=
  (contDiff_expandingCutoff (j + 1)).sub (contDiff_expandingCutoff j)

/-- Smoothness of contracting annuli (`app:ch_regular:eq:chain-tail`). -/
theorem contDiff_lowGraphCutoff (j : ℕ) : ContDiff ℝ ∞ (lowGraphCutoff (n := n) j) :=
  (contDiff_contractingCutoff j).sub (contDiff_contractingCutoff (j + 1))

/-- Smoothness of every physical graph regularizer
(`app:ch_regular:eq:joint-kernel-phase`). -/
theorem contDiff_graphCutoff (j : ℕ) : ContDiff ℝ ∞ (graphCutoff (n := n) j) :=
  (contDiff_highGraphCutoff j).add (contDiff_lowGraphCutoff j)

/-- Smoothness of every independent output regularizer
(`app:ch_regular:eq:joint-kernel-phase`). -/
theorem contDiff_outputCutoff (j : ℕ) : ContDiff ℝ ∞ (outputCutoff (n := n) j) := by
  cases j with
  | zero => exact contDiff_expandingCutoff 0
  | succ j => exact contDiff_highGraphCutoff j

/-- Compactness of expanding balls (`app:ch_regular:eq:chain-tail`). -/
theorem hasCompactSupport_expandingCutoff (j : ℕ) :
    HasCompactSupport (expandingCutoff (n := n) j) :=
  (frequencyBump n).hasCompactSupport.comp_smul (by positivity : ((2 : ℝ) ^ j)⁻¹ ≠ 0)

/-- Compactness of contracting balls (`app:ch_regular:eq:chain-tail`). -/
theorem hasCompactSupport_contractingCutoff (j : ℕ) :
    HasCompactSupport (contractingCutoff (n := n) j) :=
  (frequencyBump n).hasCompactSupport.comp_smul (by positivity : (2 : ℝ) ^ j ≠ 0)

/-- Compactness of high graph annuli (`app:ch_regular:eq:chain-tail`). -/
theorem hasCompactSupport_highGraphCutoff (j : ℕ) :
    HasCompactSupport (highGraphCutoff (n := n) j) :=
  (hasCompactSupport_expandingCutoff (j + 1)).sub (hasCompactSupport_expandingCutoff j)

/-- Compactness of low graph annuli (`app:ch_regular:eq:chain-tail`). -/
theorem hasCompactSupport_lowGraphCutoff (j : ℕ) :
    HasCompactSupport (lowGraphCutoff (n := n) j) :=
  (hasCompactSupport_contractingCutoff j).sub (hasCompactSupport_contractingCutoff (j + 1))

/-- Compact primitive graph-frequency carriers for the physical kernel limit
(`app:ch_regular:eq:joint-kernel-phase`). -/
theorem hasCompactSupport_graphCutoff (j : ℕ) :
    HasCompactSupport (graphCutoff (n := n) j) :=
  (hasCompactSupport_highGraphCutoff j).add (hasCompactSupport_lowGraphCutoff j)

/-- Compact primitive output-frequency carriers for the physical kernel limit
(`app:ch_regular:eq:joint-kernel-phase`). -/
theorem hasCompactSupport_outputCutoff (j : ℕ) :
    HasCompactSupport (outputCutoff (n := n) j) := by
  cases j with
  | zero => exact hasCompactSupport_expandingCutoff 0
  | succ j => exact hasCompactSupport_highGraphCutoff j

private theorem expandingCutoff_eventuallyEq_one (j : ℕ) :
    expandingCutoff (n := n) j =ᶠ[𝓝 0] fun _ => 1 :=
  (frequencyBump n).eventuallyEq_one.comp_tendsto
    (by simpa [Pi.smul_def] using (continuous_id.const_smul (((2 : ℝ) ^ j)⁻¹)).tendsto (0 : Euclidean n))

private theorem contractingCutoff_eventuallyEq_one (j : ℕ) :
    contractingCutoff (n := n) j =ᶠ[𝓝 0] fun _ => 1 :=
  (frequencyBump n).eventuallyEq_one.comp_tendsto
    (by simpa [Pi.smul_def] using (continuous_id.const_smul ((2 : ℝ) ^ j)).tendsto (0 : Euclidean n))

/-- Every graph regularizer vanishes on a neighborhood of zero. Thus conic
phase smoothness suffices for each physical cutoff pair
(`app:ch_regular:eq:joint-kernel-phase`). -/
theorem zero_notMem_tsupport_graphCutoff (j : ℕ) :
    (0 : Euclidean n) ∉ tsupport (graphCutoff j) := by
  rw [notMem_tsupport_iff_eventuallyEq]
  filter_upwards [expandingCutoff_eventuallyEq_one (n := n) j,
    expandingCutoff_eventuallyEq_one (n := n) (j + 1),
    contractingCutoff_eventuallyEq_one (n := n) j,
    contractingCutoff_eventuallyEq_one (n := n) (j + 1)] with ξ h₁ h₂ h₃ h₄
  simp [graphCutoff, highGraphCutoff, lowGraphCutoff, h₁, h₂, h₃, h₄]

/-- The exact finite graph partition retains both ends of the frequency axis
(`app:ch_regular:eq:joint-kernel-phase`). -/
theorem sum_graphCutoff (N : ℕ) (ξ : Euclidean n) :
    ∑ j ∈ Finset.range N, graphCutoff j ξ = expandingCutoff N ξ - contractingCutoff N ξ := by
  induction N with
  | zero => simp [expandingCutoff, contractingCutoff]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [graphCutoff, highGraphCutoff, lowGraphCutoff]
    ring

/-- The exact finite output partition includes its low ball
(`app:ch_regular:eq:joint-kernel-phase`). -/
theorem sum_outputCutoff_succ (N : ℕ) (ξ : Euclidean n) :
    ∑ k ∈ Finset.range (N + 1), outputCutoff k ξ = expandingCutoff N ξ := by
  induction N with
  | zero => simp [outputCutoff]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    simp [outputCutoff, highGraphCutoff]

/-- Bounded output partial sums required by
`KernelLimits.exists_jointKernel_physical_extension`
(`app:ch_regular:eq:chain-tail`). -/
theorem abs_sum_outputCutoff_le_one (N : ℕ) (ξ : Euclidean n) :
    |∑ k ∈ Finset.range N, outputCutoff k ξ| ≤ 1 := by
  cases N with
  | zero => simp
  | succ N =>
    rw [sum_outputCutoff_succ, expandingCutoff, abs_of_nonneg (frequencyBump n).nonneg]
    exact (frequencyBump n).le_one

/-- Bounded graph partial sums, including the shrinking hole at zero
(`app:ch_regular:eq:chain-tail`). -/
theorem abs_sum_graphCutoff_le_one (N : ℕ) (ξ : Euclidean n) :
    |∑ j ∈ Finset.range N, graphCutoff j ξ| ≤ 1 := by
  rw [sum_graphCutoff, expandingCutoff, contractingCutoff, abs_le]
  constructor <;>
    linarith [(frequencyBump n).nonneg (x := (((2 : ℝ) ^ N)⁻¹ • ξ)),
      (frequencyBump n).le_one (x := (((2 : ℝ) ^ N)⁻¹ • ξ)),
      (frequencyBump n).nonneg (x := ((2 : ℝ) ^ N • ξ)),
      (frequencyBump n).le_one (x := ((2 : ℝ) ^ N • ξ))]

private theorem expandingCutoff_eventually_one (ξ : Euclidean n) :
    ∀ᶠ N : ℕ in atTop, expandingCutoff N ξ = 1 := by
  have h : Tendsto (fun N : ℕ => ((2 : ℝ) ^ N)⁻¹ • ξ) atTop (𝓝 0) := by
    simpa only [inv_pow, zero_smul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ (2 : ℝ)⁻¹)
        (by norm_num : (2 : ℝ)⁻¹ < 1)).smul_const ξ
  exact (frequencyBump n).eventuallyEq_one.comp_tendsto h

private theorem contractingCutoff_eventually_zero {ξ : Euclidean n} (hξ : ξ ≠ 0) :
    ∀ᶠ N : ℕ in atTop, contractingCutoff N ξ = 0 := by
  have h : Tendsto (fun N : ℕ => (2 : ℝ) ^ N * ‖ξ‖) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).atTop_mul_const
      (norm_pos_iff.mpr hξ)
  filter_upwards [h.eventually (eventually_ge_atTop 2)] with N hN
  apply (frequencyBump n).zero_of_le_dist
  simpa [frequencyBump, dist_zero_right, norm_smul, abs_of_pos (by positivity : 0 < (2 : ℝ) ^ N)]
    using hN

/-- The graph partial sums converge to one at every nonzero physical frequency,
including arbitrarily small ones (`app:ch_regular:eq:joint-kernel-phase`). -/
theorem tendsto_sum_graphCutoff {ξ : Euclidean n} (hξ : ξ ≠ 0) :
    Tendsto (fun N => ∑ j ∈ Finset.range N, graphCutoff j ξ) atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [expandingCutoff_eventually_one ξ,
    contractingCutoff_eventually_zero hξ] with N he hc
  simp [sum_graphCutoff, he, hc]

/-- Output cutoff removal uses bounded partial sums converging to one at every
frequency, including zero. This supplies `hclim` in
`KernelLimits.exists_jointKernel_physical_extension`
(`app:ch_regular:eq:chain-tail`). -/
theorem tendsto_sum_outputCutoff (ξ : Euclidean n) :
    Tendsto (fun N => ∑ k ∈ Finset.range N, outputCutoff k ξ) atTop (𝓝 1) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  apply tendsto_const_nhds.congr'
  filter_upwards [expandingCutoff_eventually_one ξ] with N he
  simp [sum_outputCutoff_succ, he]

/-- For each fixed nonzero frequency only finitely many graph cutoffs contribute
(`app:ch_regular:eq:joint-kernel-phase`). -/
theorem summable_graphCutoff (ξ : Euclidean n) : Summable (fun j => graphCutoff j ξ) := by
  by_cases hξ : ξ = 0
  · subst ξ
    simp only [graphCutoff, highGraphCutoff, lowGraphCutoff, expandingCutoff,
      contractingCutoff, smul_zero, sub_self, add_zero]
    exact summable_zero
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((expandingCutoff_eventually_one ξ).and (contractingCutoff_eventually_zero hξ))
  apply summable_of_ne_finset_zero (s := Finset.range N)
  intro j hj
  have hjN : N ≤ j := Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hj)
  simp [graphCutoff, highGraphCutoff, lowGraphCutoff, (hN j hjN).1, (hN j hjN).2,
    (hN (j + 1) (by omega)).1, (hN (j + 1) (by omega)).2]

/-- The graph cutoffs are an actual partition on the punctured frequency space,
not merely a formal shell decomposition (`app:ch_regular:eq:joint-kernel-phase`). -/
theorem hasSum_graphCutoff {ξ : Euclidean n} (hξ : ξ ≠ 0) :
    HasSum (fun j => graphCutoff j ξ) 1 := by
  have hs := (summable_graphCutoff ξ).hasSum
  exact (tendsto_nhds_unique hs.tendsto_sum_nat (tendsto_sum_graphCutoff hξ)) ▸ hs

/-- The output partition is locally finite at each frequency
(`app:ch_regular:eq:joint-kernel-phase`). -/
theorem summable_outputCutoff (ξ : Euclidean n) : Summable (fun k => outputCutoff k ξ) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (expandingCutoff_eventually_one ξ)
  apply summable_of_ne_finset_zero (s := Finset.range (N + 1))
  intro k hk
  have hkN : N + 1 ≤ k := Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hk)
  cases k with
  | zero => omega
  | succ k => simp [outputCutoff, highGraphCutoff, hN k (by omega), hN (k + 1) (by omega)]

/-- The independent output cutoffs partition all physical output frequencies
(`app:ch_regular:eq:joint-kernel-phase`). -/
theorem hasSum_outputCutoff (ξ : Euclidean n) : HasSum (fun k => outputCutoff k ξ) 1 := by
  have hs := (summable_outputCutoff ξ).hasSum
  exact (tendsto_nhds_unique hs.tendsto_sum_nat (tendsto_sum_outputCutoff ξ)) ▸ hs

/-- Primitive compact carriers for every independent physical cutoff pair.
Only the amplitude's two-position carrier and the input symbol's actual carrier
are inputs; all frequency regularizers are constructed above. The source
shoulder remains in the input symbol (`app:ch_regular:eq:joint-kernel-phase`). -/
def cutoffPairCarriers (A : FullAmplitude n r) (mi : LocalizerSymbol n)
    (Kb : Set (Euclidean n × Euclidean n)) (Ki Kη : Set (Euclidean n))
    (hKb : IsCompact Kb) (hKi : IsCompact Ki) (hKη : IsCompact Kη)
    (hA : ∀ u z ξ, (u, z) ∉ Kb → A u z ξ = 0)
    (hi : ∀ y η, (y, η) ∉ Ki ×ˢ Kη → mi (y, η) = 0) (j k : ℕ) :
    KernelLimits.RegularizedCarriers A mi (graphCutoff j) (outputCutoff k) where
  amplitudeBase := Kb
  inputBase := Ki
  inputFrequency := Kη
  compact_amplitudeBase := hKb
  compact_inputBase := hKi
  compact_inputFrequency := hKη
  compact_graphCutoff := hasCompactSupport_graphCutoff j
  compact_outputCutoff := hasCompactSupport_outputCutoff k
  amplitude_zero := hA
  input_zero := hi

end JanetCartan.FiniteChain.Graph.PhysicalShells
