module

public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.NormalizedTerminalRestriction
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.RestrictionBounds.Support.Multipliers

/-!
# The normalized terminal source on the original recut data

The original nested cutoff `χ₃` equals one on the support of the recut source
and is supported inside the SAME selected family's physical core and common
output plateau. Multiplying the right-localizer symbol at its input base by
this cutoff leaves its action on that datum unchanged. The existing terminal
estimate therefore applies without a spatial-support assumption on the entire
uncut proof symbol. Consumers: `finiteChain_observation_rapidDecayAt.hBnear`
and the signed-source inverse expansion (`app:ch_regular:lem:finite-chain`,
`app:ch_regular:eq:resolved-angular-tail`).

The cutoff geometry is supplied by `SmallSupport.exists_cutoffs_norm_lt` in the
fixed inverse construction. This deduction retains the supplied cutoffs; it
makes no new choice of family, reference, inverse or complete residual.
-/

@[expose] public noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff
namespace JanetCartan.SignedProductEstimates
open RegularSector.FiniteMasks.ActualFamily RegularSector.NormalizedSolver
open ArbitraryAccuracy.ResidualLocalization.IdentityDefect Pseudodifferential LocalSobolev
open RegularSector.Characteristic.RetardedLocalization FourierIntegral LowBounds FiniteChain.Graph
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x₀ : Euclidean (d+1)} {RQ C₀ : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "V" => EuclideanSpace ℂ (Fin (d+1))
local notation "H" => Lp V 2 (volume : Measure E)

/-- Recutting the input base of the right proof symbol is EXACTLY right
composition with the same physical cutoff, on all L² data. The literal
oscillatory integration order is preserved (`app:ch_regular:eq:joint-kernel-phase`,
`app:ch_regular:lem:finite-chain`). -/
theorem rightLocalizer_sourceCut_realization
    (ρ : ℝ) (mi : LocalizerSymbol (d+1)) (M : H →L[ℂ] H)
    (hM : ∀ u : H, M u =ᵐ[volume] fun x ↦ WithLp.toLp 2
      (rightLocalizer ρ mi (fun y ↦ (u y).ofLp) x))
    (χ : E → ℝ) (hχ : Continuous χ) (hχb : ∀ y, ‖χ y‖ ≤ 1) :
    ∀ u : H, (M.comp (sourceCutMultiplier χ hχ hχb)) u =ᵐ[volume]
      fun x ↦ WithLp.toLp 2
        (rightLocalizer ρ (fun p ↦ χ p.1 * mi p) (fun y ↦ (u y).ofLp) x) := by
  intro u
  refine (hM (sourceCutMultiplier χ hχ hχb u)).trans (Filter.Eventually.of_forall ?_)
  intro x
  apply congrArg (WithLp.toLp 2)
  simp only [rightLocalizer, graphOperator, Matrix.smul_mulVec, Matrix.one_mulVec]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with ξ
  apply integral_congr_ae
  filter_upwards [sourceCutMultiplier_coeFn χ hχ hχb u] with y hy
  rw [hy]
  simp only [WithLp.ofLp_smul, Complex.ofReal_mul, smul_smul]
  congr 1
  ring

/-- The recut proof symbol keeps the original angular support and gains
only the original cutoff's physical support. This supplies the physical inputs
of the normalized terminal estimate (`app:ch_regular:lem:finite-chain`). -/
theorem sourceCut_localizer_support
    (χ : E → ℝ) (mi : LocalizerSymbol (d+1)) :
    tsupport (fun p : E × E ↦ χ p.1 * mi p) ⊆
      Prod.fst ⁻¹' tsupport χ ∩ tsupport mi := by
  intro p hp
  exact ⟨tsupport_comp_subset_preimage χ continuous_fst
      (tsupport_mul_subset_left hp), tsupport_mul_subset_right hp⟩


set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

/-- Apply the actual normalized source to the SAME right-localizer output
of a datum fixed by the original outer cutoff. Its physical and output plateau
hypotheses follow from that cutoff's support, even if the original proof mask
has a larger base projection. Both literal orientations and real quadratures
retain loss `d+1+s`, the original low collar and all three output/input masks
(`app:ch_regular:eq:resolved-angular-tail`). -/
theorem exists_normalizedSource_supported_terminal_bounds
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
      ∀ q (W : Set E) (hW : MeasurableSet W) (u : H),
        sourceCutMultiplier χ₃ χ₃.continuous (SmallSupport.bump_norm_le_one χ₃) u = u →
      ∀ backward : Bool,
        let S := pairedSource f hK L₀ output ho.continuous
          (fun y ↦ (Real.norm_of_nonneg (hor y).1).trans_le (hor y).2)
        let P := if backward then S.adjoint else S
        let v := restrictL2 W ((P-1) (M u))
        (v ∈ (restrictionSobolevScale W V hW).level s ∧
          (restrictionSobolevScale W V hW).gradeNorm s v ≤
            C q * ρ^((d+1+s : ℕ) : ℝ) * L^(0 : ℕ) * (L/ρ)^q * ‖u‖) ∧
        ∀ c : ℂ, ‖c‖ = 1 →
          let vr := l2RealPart (volume.restrict W) (c • v)
          vr ∈ (restrictionSobolevScale W (EuclideanSpace ℝ (Fin (d+1))) hW).level s ∧
          (restrictionSobolevScale W (EuclideanSpace ℝ (Fin (d+1))) hW).gradeNorm s vr ≤
            Cr q * ρ^((d+1+s : ℕ) : ℝ) * L^(0 : ℕ) * (L/ρ)^q * ‖u‖ := by
  let mχ : LocalizerSymbol (d+1) := fun p ↦ χ₃ p.1 * mi p
  have hmχ : ContDiff ℝ ∞ mχ := (χ₃.contDiff.comp contDiff_fst).mul hi
  have hcmχ : HasCompactSupport mχ := hic.mul_left
  have hsupport := sourceCut_localizer_support (χ₃ : E → ℝ) mi
  have hamχ : ∀ p ∈ tsupport mχ, lo ≤ ‖p.2‖ := fun p hp ↦ hann p (hsupport hp).2
  have htmχ : ∀ p ∈ tsupport mχ, NormedSpace.normalize p.2 ∈ K :=
    fun p hp ↦ hterminal p (hsupport hp).2
  have hbase : Prod.fst '' tsupport mχ ⊆ U := by
    rintro _ ⟨p, hp, rfl⟩
    exact hχ₃ (hsupport hp).1
  have hbcore := hbase.trans (hcore.trans ball_subset_closedBall)
  have hboutput : Prod.fst '' tsupport mχ ⊆ interior {y | output y = 1} :=
    hbase.trans (interior_maximal houtput hU)
  obtain ⟨C, hC, hcdata⟩ := exists_normalizedSource_rightLocalizer_restriction_bound f hK hsym L₀ hL₀
    output ho hoc hor mχ hmχ hcmχ hlo hamχ htmχ hbcore hboutput s
  obtain ⟨Cr, hCr, hrdata⟩ := exists_normalizedSource_rightLocalizer_quadrature_bound f hK hsym L₀ hL₀
    output ho hoc hor mχ hmχ hcmχ hlo hamχ htmχ hbcore hboutput s
  refine ⟨C, Cr, hC, hCr, ?_⟩
  intro ρ L hL hLρ M hM q W hW u hu backward S P v
  let Mχ := M.comp (sourceCutMultiplier χ₃ χ₃.continuous (SmallSupport.bump_norm_le_one χ₃))
  have hMχ := rightLocalizer_sourceCut_realization ρ mi M hM
    χ₃ χ₃.continuous (SmallSupport.bump_norm_le_one χ₃)
  have he : Mχ u = M u := by simp only [Mχ, ContinuousLinearMap.comp_apply, hu]
  have hc := hcdata ρ L hL hLρ Mχ hMχ q W hW u backward
  have hr := hrdata ρ L hL hLρ Mχ hMχ q W hW u backward
  refine ⟨?_, ?_⟩
  · simpa only [he] using hc
  · intro c hc
    simpa only [he] using hr c hc

end JanetCartan.SignedProductEstimates
