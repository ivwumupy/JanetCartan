module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Limits of finite classical jets

The limit step for the Sobolev regularity assertion in `app:not:fourier`, used
in `app:ch_regular:thm:exact-correction`. Uniform Cauchy convergence of the
classical jets produces a Cᵏ function. A simultaneous L² limit identifies its
almost-everywhere class. The Sobolev estimate establishing the uniform Cauchy
hypothesis is a separate prerequisite.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set
open scoped Topology ContDiff ENNReal

namespace JanetCartan.LocalSobolev.FiniteOrder

/-- The L² Cauchy consequence of convergence used in the approximation argument
for `app:not:fourier`. Both indices tend independently to infinity. -/
theorem tendsto_eLpNorm_sub_pair {α G : Type*} [MeasurableSpace α]
    [NormedAddCommGroup G] {μ : Measure α} {u : ℕ → α → G} {f : α → G}
    (h : Tendsto (fun i ↦ eLpNorm (u i - f) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun p : ℕ × ℕ ↦ eLpNorm (u p.1 - u p.2) 2 μ) atTop (𝓝 0) := by
  rw [← prod_atTop_atTop_eq]
  have hsum := (h.comp tendsto_fst).add (h.comp tendsto_snd)
  simp only [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ ↦ bot_le) ?_
  intro p
  have heq : u p.1 - u p.2 = (u p.1 - f) - (u p.2 - f) := by abel
  change eLpNorm (u p.1 - u p.2) 2 μ ≤
    eLpNorm (u p.1 - f) 2 μ + eLpNorm (u p.2 - f) 2 μ
  rw [heq]
  exact eLpNorm_sub_le (by norm_num)

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- In the regularity argument of `app:not:fourier`, a smooth Sobolev estimate
upgrades L² convergence of the full jets to uniform Cauchy convergence of the
lower jets. The estimate is an explicit premise here and must be proved
separately before this criterion gives Sobolev regularity. -/
theorem uniformCauchySeqOn_iteratedFDeriv_of_smooth_estimate
    [MeasurableSpace E] {μ : Measure E} {u : ℕ → E → F}
    {J : (j : ℕ) → E → E [×j]→L[ℝ] F} {k m : ℕ}
    (hu : ∀ i, ContDiff ℝ ∞ (u i))
    (hL : ∀ i j, j ≤ m → MemLp (iteratedFDeriv ℝ j (u i)) 2 μ)
    (hconv : ∀ j ≤ m,
      Tendsto (fun i ↦ eLpNorm (iteratedFDeriv ℝ j (u i) - J j) 2 μ) atTop (𝓝 0))
    (C : ℝ)
    (hest : ∀ v : E → F, ContDiff ℝ ∞ v →
      (∀ l ≤ m, MemLp (iteratedFDeriv ℝ l v) 2 μ) →
      ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j v x‖ ≤
        C * ∑ l ∈ Finset.range (m + 1), (eLpNorm (iteratedFDeriv ℝ l v) 2 μ).toReal) :
    ∀ j ≤ k, UniformCauchySeqOn (fun i ↦ iteratedFDeriv ℝ j (u i)) atTop univ := by
  have hpair (l : ℕ) (hl : l ≤ m) :
      Tendsto (fun p : ℕ × ℕ ↦
        (eLpNorm (iteratedFDeriv ℝ l (u p.1 - u p.2)) 2 μ).toReal) atTop (𝓝 0) := by
    simp_rw [iteratedFDeriv_sub ((hu _).of_le (by simp)) ((hu _).of_le (by simp))]
    simpa only [Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp
        (tendsto_eLpNorm_sub_pair (hconv l hl))
  have hsum : Tendsto (fun p : ℕ × ℕ ↦ C *
      ∑ l ∈ Finset.range (m + 1),
        (eLpNorm (iteratedFDeriv ℝ l (u p.1 - u p.2)) 2 μ).toReal)
      atTop (𝓝 0) := by
    simpa using (tendsto_finsetSum (Finset.range (m + 1))
      (fun l hl ↦ hpair l (by simpa using Finset.mem_range.mp hl))).const_mul C
  intro j hj
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  have he := hsum.eventually (gt_mem_nhds hε)
  obtain ⟨N, hN⟩ := eventually_atTop.1 he
  refine ⟨max N.1 N.2, fun a ha b hb x _ ↦ ?_⟩
  have hmem : ∀ l ≤ m, MemLp (iteratedFDeriv ℝ l (u a - u b)) 2 μ := by
    intro l hl
    rw [iteratedFDeriv_sub ((hu a).of_le (by simp)) ((hu b).of_le (by simp))]
    exact (hL a l hl).sub (hL b l hl)
  have hbnd := hest (u a - u b) ((hu a).sub (hu b)) hmem j hj x
  rw [iteratedFDeriv_sub ((hu a).of_le (by simp)) ((hu b).of_le (by simp))] at hbnd
  rw [dist_eq_norm]
  exact hbnd.trans_lt
    (hN (a, b) ⟨(le_max_left _ _).trans ha, (le_max_right _ _).trans hb⟩)

/-- The finite-jet limit step of `app:not:fourier`: uniform Cauchy convergence
of derivatives through order `k` yields a Cᵏ limit of the underlying functions. -/
theorem exists_contDiff_of_uniformCauchySeqOn_iteratedFDeriv {u : ℕ → E → F} {k : ℕ}
    (hu : ∀ i, ContDiff ℝ ∞ (u i))
    (hC : ∀ j ≤ k, UniformCauchySeqOn (fun i ↦ iteratedFDeriv ℝ j (u i)) atTop univ) :
    ∃ g : E → F, ContDiff ℝ k g ∧ TendstoUniformly u g atTop := by
  have hex : ∀ j : ℕ, ∃ G : E → E [×j]→L[ℝ] F,
      j ≤ k → TendstoUniformly (fun i ↦ iteratedFDeriv ℝ j (u i)) G atTop := by
    intro j
    by_cases hj : j ≤ k
    · have hp : ∀ x : E, ∃ v, Tendsto (fun i ↦ iteratedFDeriv ℝ j (u i) x)
          atTop (𝓝 v) := fun x ↦
        cauchySeq_tendsto_of_complete ((hC j hj).cauchySeq (mem_univ x))
      choose G hG using hp
      refine ⟨G, fun _ ↦ ?_⟩
      rw [← tendstoUniformlyOn_univ]
      exact (hC j hj).tendstoUniformlyOn_of_tendsto (fun x _ ↦ hG x)
    · exact ⟨0, fun h ↦ (hj h).elim⟩
  choose G hG using hex
  let g : E → F := fun x ↦ (G 0 x).curry0
  have ht : HasFTaylorSeriesUpTo (k : ℕ∞ω) g (fun x j ↦ G j x) := by
    refine ⟨fun _ ↦ rfl, ?_, ?_⟩
    · intro j hj x
      have hjk : j < k := by exact_mod_cast hj
      have hnext := (continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (j + 1) ↦ E) F).isometry.uniformContinuous.comp_tendstoUniformly
          (hG (j + 1) (by omega))
      exact hasFDerivAt_of_tendstoUniformly hnext
        (fun i x ↦ (hu i).ftaylorSeries.fderiv j (by exact_mod_cast ENat.natCast_lt_top j) x)
        (fun x ↦ (hG j (by omega)).tendsto_at x) x
    · intro j hj
      exact (hG j (by exact_mod_cast hj)).continuous
        (Eventually.of_forall fun i ↦ (hu i).continuous_iteratedFDeriv (by simp)).frequently
  refine ⟨g, ht.contDiff, ?_⟩
  have hzero := (continuousMultilinearCurryFin0 ℝ E F).isometry.uniformContinuous
    |>.comp_tendstoUniformly (hG 0 (Nat.zero_le k))
  simpa [Function.comp_def, g] using hzero

omit [NormedSpace ℝ F] [CompleteSpace F] in
/-- Identification of the representative in `app:not:fourier`: a pointwise
limit and an L² limit of the same sequence agree almost everywhere. -/
theorem ae_eq_of_tendsto_eLpNorm_of_tendsto {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {u : ℕ → α → F} {f g : α → F}
    (hL : Tendsto (fun i ↦ eLpNorm (u i - f) 2 μ) atTop (𝓝 0))
    (hpt : ∀ x, Tendsto (fun i ↦ u i x) atTop (𝓝 (g x))) : g =ᵐ[μ] f := by
  obtain ⟨s, hs, hsf⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hL).exists_seq_tendsto_ae
  filter_upwards [hsf] with x hx
  exact tendsto_nhds_unique ((hpt x).comp hs.tendsto_atTop) hx

end JanetCartan.LocalSobolev.FiniteOrder
