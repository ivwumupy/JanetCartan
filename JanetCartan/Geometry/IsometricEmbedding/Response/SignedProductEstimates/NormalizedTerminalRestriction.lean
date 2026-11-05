module

public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.NormalizedTerminalDecay
public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.NormalizedRestriction
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.LocalizerAdjoint

/-!
# Restricted terminal estimates for the corrected complete source

The actual right quantization is identified by the existing adjoint uniqueness
lemma. Restriction and both real quadratures retain the normalized source's
three physical masks and its unchanged low collar. The fixed frequency loss
supplies `finiteChain_observation_rapidDecayAt.hBnear`; it is independent of
accuracy (`app:ch_regular:eq:chain-tail`, `resolved-angular-tail`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric MeasureTheory
open scoped ContDiff
namespace JanetCartan.SignedProductEstimates
open RegularSector.FiniteMasks.ActualFamily RegularSector.NormalizedSolver
open ArbitraryAccuracy.ResidualLocalization.IdentityDefect Pseudodifferential LocalSobolev
open RegularSector.Characteristic.RetardedLocalization FourierIntegral LowBounds FiniteChain.Graph
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {center : Euclidean (d+1)} {RQ C₀ : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "V" => EuclideanSpace ℂ (Fin (d+1))
local notation "RV" => EuclideanSpace ℝ (Fin (d+1))
local notation "H" => Lp V 2 (volume : Measure E)

/-- The normalized source minus ONE identity has arbitrary-accuracy terminal
restriction bounds on the SAME right localizer, in both literal orientations.
Only the original geometric terminal and physical-support inclusions enter;
the Fourier plateau and tail estimate are proved (`resolved-angular-tail`). -/
theorem exists_normalizedSource_rightLocalizer_restriction_bound
    (f : ActualMaskFamily Ω center RQ A₀ K C₀) (hK : IsCompact K)
    (hsym : ∀ η ∈ K, -η ∈ K) (L₀ : ℝ) (hL₀ : f.radialThreshold ≤ L₀)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hor : ∀ y, output y ∈ Icc (0 : ℝ) 1)
    (mi : LocalizerSymbol (d+1)) (hi : ContDiff ℝ ∞ mi) (hic : HasCompactSupport mi)
    {lo : ℝ} (hlo : 0 < lo) (hann : ∀ p ∈ tsupport mi, lo ≤ ‖p.2‖)
    (hterminal : ∀ p ∈ tsupport mi, NormedSpace.normalize p.2 ∈ K)
    (hcore : Prod.fst '' tsupport mi ⊆ closedBall center f.physicalRadius)
    (houtput : Prod.fst '' tsupport mi ⊆ interior {y | output y = 1})
    (s : ℕ) :
    let hob := fun y ↦ (Real.norm_of_nonneg (hor y).1).trans_le (hor y).2
    ∃ C : ℕ → ℝ, (∀ q, 0 ≤ C q) ∧ ∀ ρ L : ℝ, 1 ≤ L → L ≤ ρ →
      ∀ M : H →L[ℂ] H,
        (∀ u : H, M u =ᵐ[volume] fun x ↦ WithLp.toLp 2
          (rightLocalizer ρ mi (fun y ↦ (u y).ofLp) x)) →
      ∀ q (W : Set E) (hW : MeasurableSet W) (u : H) (backward : Bool),
        let S := pairedSource f hK L₀ output ho.continuous hob
        let P := if backward then S.adjoint else S
        restrictL2 W ((P-1) (M u)) ∈ (restrictionSobolevScale W V hW).level s ∧
        (restrictionSobolevScale W V hW).gradeNorm s (restrictL2 W ((P-1) (M u))) ≤
          C q * ρ^((d+1+s : ℕ) : ℝ) * L^(0 : ℕ) * (L/ρ)^q * ‖u‖ := by
  intro hob
  choose A hA hbound using fun q ↦ exists_normalizedSource_terminal_sobolev_decay
    f hK hsym L₀ hL₀ output ho hoc hor mi hi hic hlo hann hterminal hcore houtput s q
  obtain ⟨B, hB, hrestrict⟩ := vector_restrictionSobolev_nat_bounds (d+1) (d+1) s
  refine ⟨fun q ↦ B*A q, fun q ↦ mul_nonneg hB.le (hA q), ?_⟩
  intro ρ L hL hLρ M hM q W hW u backward S P
  have hleft := leftLocalizer_adjoint_ae_of_rightLocalizer
    (ne_of_gt (zero_lt_one.trans_le (hL.trans hLρ))) mi hi.continuous hic M hM
  have hh := hbound q ρ L hL hLρ M.adjoint hleft u
  have hb : MemVectorFourierSobolev (s : ℝ) ((P-1) (M u)) ∧
      vectorFourierSobolevNorm (s : ℝ) ((P-1) (M u)) ≤
        A q * ρ^(d+1+s) * (L/ρ)^q * ‖u‖ := by
    cases backward
    · simpa only [P, Bool.false_eq_true, ↓reduceIte, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.adjoint_adjoint] using hh.1
    · simpa only [P, ↓reduceIte, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.adjoint_adjoint] using hh.2
  obtain ⟨hm, hn⟩ := hrestrict _ hb.1 W (restrictL2 W ((P-1) (M u)))
    (restrictL2_coeFn W ((P-1) (M u))).symm
  refine ⟨hm, ?_⟩
  rw [restrictionSobolevScale_gradeNorm hW hm]
  exact (hn.trans (mul_le_mul_of_nonneg_left hb.2 hB.le)).trans_eq (by
    rw [Real.rpow_natCast, pow_zero, mul_one]
    ring)

/-- Both real quadratures of the actual normalized terminal error have the
same restriction estimate. Rotation is performed on the complete source error,
retaining all physical masks, the literal adjoint and the original low shoulder
(`app:ch_pairs:prop:pairs-lag-sum`, `resolved-angular-tail`). -/
theorem exists_normalizedSource_rightLocalizer_quadrature_bound
    (f : ActualMaskFamily Ω center RQ A₀ K C₀) (hK : IsCompact K)
    (hsym : ∀ η ∈ K, -η ∈ K) (L₀ : ℝ) (hL₀ : f.radialThreshold ≤ L₀)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hor : ∀ y, output y ∈ Icc (0 : ℝ) 1)
    (mi : LocalizerSymbol (d+1)) (hi : ContDiff ℝ ∞ mi) (hic : HasCompactSupport mi)
    {lo : ℝ} (hlo : 0 < lo) (hann : ∀ p ∈ tsupport mi, lo ≤ ‖p.2‖)
    (hterminal : ∀ p ∈ tsupport mi, NormedSpace.normalize p.2 ∈ K)
    (hcore : Prod.fst '' tsupport mi ⊆ closedBall center f.physicalRadius)
    (houtput : Prod.fst '' tsupport mi ⊆ interior {y | output y = 1})
    (s : ℕ) :
    let hob := fun y ↦ (Real.norm_of_nonneg (hor y).1).trans_le (hor y).2
    ∃ C : ℕ → ℝ, (∀ q, 0 ≤ C q) ∧ ∀ ρ L : ℝ, 1 ≤ L → L ≤ ρ →
      ∀ M : H →L[ℂ] H,
        (∀ u : H, M u =ᵐ[volume] fun x ↦ WithLp.toLp 2
          (rightLocalizer ρ mi (fun y ↦ (u y).ofLp) x)) →
      ∀ q (W : Set E) (hW : MeasurableSet W) (u : H) (backward : Bool)
        (c : ℂ), ‖c‖ = 1 →
        let S := pairedSource f hK L₀ output ho.continuous hob
        let P := if backward then S.adjoint else S
        let v := l2RealPart (volume.restrict W) (c • restrictL2 W ((P-1) (M u)))
        v ∈ (restrictionSobolevScale W RV hW).level s ∧
        (restrictionSobolevScale W RV hW).gradeNorm s v ≤
          C q * ρ^((d+1+s : ℕ) : ℝ) * L^(0 : ℕ) * (L/ρ)^q * ‖u‖ := by
  intro hob
  choose A hA hbound using fun q ↦ exists_normalizedSource_terminal_sobolev_decay
    f hK hsym L₀ hL₀ output ho hoc hor mi hi hic hlo hann hterminal hcore houtput s q
  obtain ⟨B, hB, hrestrict⟩ := exists_source_quadrature_restriction_comparison (d := d) s
  refine ⟨fun q ↦ B*A q, fun q ↦ mul_nonneg hB (hA q), ?_⟩
  intro ρ L hL hLρ M hM q W hW u backward c hc S P v
  have hleft := leftLocalizer_adjoint_ae_of_rightLocalizer
    (ne_of_gt (zero_lt_one.trans_le (hL.trans hLρ))) mi hi.continuous hic M hM
  have hh := hbound q ρ L hL hLρ M.adjoint hleft u
  have hb : MemVectorFourierSobolev (s : ℝ) ((P-1) (M u)) ∧
      vectorFourierSobolevNorm (s : ℝ) ((P-1) (M u)) ≤
        A q * ρ^(d+1+s) * (L/ρ)^q * ‖u‖ := by
    cases backward
    · simpa only [P, Bool.false_eq_true, ↓reduceIte, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.adjoint_adjoint] using hh.1
    · simpa only [P, ↓reduceIte, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.adjoint_adjoint] using hh.2
  obtain ⟨hm, hn⟩ := hrestrict _ hb.1 W c hc
  refine ⟨hm, ?_⟩
  rw [restrictionSobolevScale_gradeNorm hW hm]
  exact (hn.trans (mul_le_mul_of_nonneg_left hb.2 hB)).trans_eq (by
    rw [Real.rpow_natCast, pow_zero, mul_one]
    ring)

end JanetCartan.SignedProductEstimates
