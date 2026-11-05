module

public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.NormalizedTerminalRecut

/-!
# Terminal source bounds for the literal nested-cutoff datum

Apply the retained `χ₃ = 1` plateau to the actual zero extension of `χ₂ u`.
The input norm is the original local L² norm, with the original measure and
both nested cutoffs. The normalized source, its literal adjoint and both real
quadratures keep the complete low collar and fixed frequency loss. Consumer:
`finiteChain_observation_rapidDecayAt.hBnear`
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:resolved-angular-tail`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric MeasureTheory
open scoped ContDiff NNReal ENNReal
namespace JanetCartan.SignedProductEstimates
open RegularSector.FiniteMasks.ActualFamily RegularSector.NormalizedSolver
open ArbitraryAccuracy.ResidualLocalization.IdentityDefect Pseudodifferential LocalSobolev
open RegularSector.Characteristic.RetardedLocalization FourierIntegral LowBounds FiniteChain.Graph
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x₀ : Euclidean (d+1)} {RQ C₀ : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "V" => EuclideanSpace ℂ (Fin (d+1))
local notation "H" => Lp V 2 (volume : Measure E)

local instance : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩

/-- The actual nested-cutoff source supplies the support premise of the
normalized terminal estimate. The SAME original `χ₂` is cut on the local
space and then zero-extended; the norm is that of the original local datum.
Constants precede that datum and the inner cutoff. The only cutoff relation
is the one supplied by `SmallSupport.exists_cutoffs_norm_lt`
(`app:ch_regular:thm:exact-correction`, `app:ch_regular:lem:finite-chain`). -/
theorem exists_normalizedSource_recut_terminal_bounds
    (f : ActualMaskFamily Ω x₀ RQ A₀ K C₀) (hK : IsCompact K)
    (hsym : ∀ η ∈ K, -η ∈ K) (L₀ : ℝ) (hL₀ : f.radialThreshold ≤ L₀)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hor : ∀ y, output y ∈ Icc (0 : ℝ) 1)
    (χ₃ : ContDiffBump x₀) (U : Set E) (hU : IsOpen U)
    (hχ₃ : tsupport (χ₃ : E → ℝ) ⊆ U)
    (hcore : U ⊆ ball x₀ f.physicalRadius)
    (houtput : ∀ y ∈ U, output y = 1)
    (mi : LocalizerSymbol (d+1)) (hi : ContDiff ℝ ∞ mi) (hic : HasCompactSupport mi)
    {lo : ℝ} (hlo : 0 < lo) (hann : ∀ p ∈ tsupport mi, lo ≤ ‖p.2‖)
    (hterminal : ∀ p ∈ tsupport mi, NormedSpace.normalize p.2 ∈ K)
    (s : ℕ) :
    ∃ (C Cr : ℕ → ℝ), (∀ q, 0 ≤ C q) ∧ (∀ q, 0 ≤ Cr q) ∧
      ∀ ρ L : ℝ, 1 ≤ L → L ≤ ρ → ∀ M : H →L[ℂ] H,
        (∀ u : H, M u =ᵐ[volume] fun x ↦ WithLp.toLp 2
          (rightLocalizer ρ mi (fun y ↦ (u y).ofLp) x)) →
      ∀ χ₂ : ContDiffBump x₀, (∀ y ∈ tsupport (χ₂ : E → ℝ), χ₃ y = 1) →
      ∀ q (D : Set E) (hD : MeasurableSet D) (W : Set E) (hW : MeasurableSet W)
        (u : LocalL2 D V) (backward : Bool),
        let w := SmallSupport.zeroExtend hD (SmallSupport.bumpL2 (p := 2) le_rfl χ₂ u)
        let S := pairedSource f hK L₀ output ho.continuous
          (fun y ↦ (Real.norm_of_nonneg (hor y).1).trans_le (hor y).2)
        let P := if backward then S.adjoint else S
        let v := restrictL2 W ((P-1) (M w))
        (v ∈ (restrictionSobolevScale W V hW).level s ∧
          (restrictionSobolevScale W V hW).gradeNorm s v ≤
            C q * ρ^((d+1+s : ℕ) : ℝ) * L^(0 : ℕ) * (L/ρ)^q * ‖u‖) ∧
        ∀ c : ℂ, ‖c‖ = 1 →
          let vr := l2RealPart (volume.restrict W) (c • v)
          vr ∈ (restrictionSobolevScale W (EuclideanSpace ℝ (Fin (d+1))) hW).level s ∧
          (restrictionSobolevScale W (EuclideanSpace ℝ (Fin (d+1))) hW).gradeNorm s vr ≤
            Cr q * ρ^((d+1+s : ℕ) : ℝ) * L^(0 : ℕ) * (L/ρ)^q * ‖u‖ := by
  obtain ⟨C, Cr, hC, hCr, hbound⟩ := exists_normalizedSource_supported_terminal_bounds
    f hK hsym L₀ hL₀ output ho hoc hor χ₃ U hU hχ₃ hcore houtput mi hi hic hlo hann hterminal s
  refine ⟨C, Cr, hC, hCr, ?_⟩
  intro ρ L hL hLρ M hM χ₂ hnest q D hD W hW u backward w S P v
  have hfixed : sourceCutMultiplier χ₃ χ₃.continuous (SmallSupport.bump_norm_le_one χ₃) w = w := by
    dsimp only [w]
    rw [← ArbitraryAccuracy.ResidualLocalization.sourceCutMultiplier_zeroExtend_bump χ₂ hD u]
    exact DFunLike.congr_fun (RegularSector.FiniteAssembly.sourceCutMultiplier_plateau_comp
      χ₂ χ₃ χ₂.continuous χ₃.continuous (SmallSupport.bump_norm_le_one χ₂)
      (SmallSupport.bump_norm_le_one χ₃) hnest).2 (SmallSupport.zeroExtend hD u)
  have hn : ‖w‖ ≤ ‖u‖ := by
    change ‖SmallSupport.zeroExtend hD (SmallSupport.bumpL2 (p := 2) le_rfl χ₂ u)‖ ≤ ‖u‖
    rw [LinearIsometry.norm_map]
    exact (ContinuousLinearMap.le_of_opNorm_le _
      (SmallSupport.norm_bumpL2_two_le_one χ₂) u).trans_eq (one_mul _)
  have hρ : 0 < ρ := zero_lt_one.trans_le (hL.trans hLρ)
  have hCq := hC q
  have hCrq := hCr q
  have hb := hbound ρ L hL hLρ M hM q W hW w hfixed backward
  refine ⟨⟨hb.1.1, hb.1.2.trans ?_⟩, ?_⟩
  · exact mul_le_mul_of_nonneg_left hn (by positivity)
  · intro c hc
    have hr := hb.2 c hc
    exact ⟨hr.1, hr.2.trans (mul_le_mul_of_nonneg_left hn (by positivity))⟩

end JanetCartan.SignedProductEstimates