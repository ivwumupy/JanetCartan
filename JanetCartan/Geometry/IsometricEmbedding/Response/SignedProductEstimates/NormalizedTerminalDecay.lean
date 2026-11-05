module

public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.NormalizedTerminalBounds

/-!
# Full-frequency normalized terminal discrepancy

The original low shoulder is absorbed using the actual normalized source's
order-zero bound and the original right localizer's Sobolev bound. Constants
precede data and frequency; no all-word decay or inverse estimate is assumed.
Consumer: `finiteChain_observation_rapidDecayAt.hBnear`, with the original
fixed loss (`app:ch_regular:eq:chain-tail`, `resolved-angular-tail`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric MeasureTheory
open scoped ContDiff
namespace JanetCartan.SignedProductEstimates
open RegularSector.FiniteMasks.ActualFamily RegularSector.NormalizedSolver RegularSector.FiniteAssembly
open ArbitraryAccuracy.ResidualLocalization.IdentityDefect Pseudodifferential
open FourierIntegral LowBounds FiniteChain.Graph
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {center : Euclidean (d+1)} {RQ C₀ : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "H" => Lp (EuclideanSpace ℂ (Fin (d+1))) 2 (volume : Measure E)

/-- The corrected terminal source minus one identity, in either literal
orientation, has arbitrary accuracy on the original right localizer at ALL
frequencies `ρ≥L≥1`. The coefficient loss is zero and the frequency loss
`d+1+s` is independent of accuracy. Terminal coverage and physical support are
geometric inputs of the original protected-localizer construction
(`app:ch_regular:eq:resolved-angular-tail`). -/
theorem exists_normalizedSource_terminal_sobolev_decay
    (f : ActualMaskFamily Ω center RQ A₀ K C₀) (hK : IsCompact K)
    (hsym : ∀ η ∈ K, -η ∈ K) (L₀ : ℝ) (hL₀ : f.radialThreshold ≤ L₀)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hor : ∀ y, output y ∈ Icc (0 : ℝ) 1)
    (mi : LocalizerSymbol (d+1)) (hi : ContDiff ℝ ∞ mi) (hic : HasCompactSupport mi)
    {lo : ℝ} (hlo : 0 < lo) (hann : ∀ p ∈ tsupport mi, lo ≤ ‖p.2‖)
    (hterminal : ∀ p ∈ tsupport mi, NormedSpace.normalize p.2 ∈ K)
    (hcore : Prod.fst '' tsupport mi ⊆ closedBall center f.physicalRadius)
    (houtput : Prod.fst '' tsupport mi ⊆ interior {y | output y = 1})
    (s q : ℕ) :
    let hob := fun y ↦ (Real.norm_of_nonneg (hor y).1).trans_le (hor y).2
    ∃ D : ℝ, 0 ≤ D ∧ ∀ ρ L : ℝ, 1 ≤ L → L ≤ ρ →
      ∀ M : H →L[ℂ] H,
        (∀ u : H, (∀ i, Integrable (fun y ↦ u y i)) → M u =ᵐ[volume]
          fun x ↦ WithLp.toLp 2 (leftLocalizer ρ mi (fun y ↦ (u y).ofLp) x)) →
      ∀ u : H,
        let P := pairedSource f hK L₀ output ho.continuous hob
        (MemVectorFourierSobolev (s : ℝ) (((P-1).comp M.adjoint) u) ∧
          vectorFourierSobolevNorm (s : ℝ) (((P-1).comp M.adjoint) u) ≤
            D * ρ^(d+1+s) * (L/ρ)^q * ‖u‖) ∧
        (MemVectorFourierSobolev (s : ℝ) (((P.adjoint-1).comp M.adjoint) u) ∧
          vectorFourierSobolevNorm (s : ℝ) (((P.adjoint-1).comp M.adjoint) u) ≤
            D * ρ^(d+1+s) * (L/ρ)^q * ‖u‖) := by
  intro hob
  let dataA := exists_normalizedSource_terminal_decay_high f hK hsym output ho hoc hor
    mi hi hic hlo hann hterminal hcore houtput s q
  let A := dataA.choose
  have hA := dataA.choose_spec.1
  have hhigh := dataA.choose_spec.2
  let dataB := exists_normalizedSource_discrepancy_uniform_sobolev_constants
    f hK output ho hoc hob
  let B := dataB.choose
  have hB := dataB.choose_spec.1
  have hcost := dataB.choose_spec.2
  let dataS := exists_leftLocalizer_adjoint_sobolev_bound (r := d+1) mi hi hic s
  let S := dataS.choose
  have hS := dataS.choose_spec.1
  have hlocalizer := dataS.choose_spec.2
  let cutoff := max 1 (4*L₀/lo)
  have hcutoff : 1 ≤ cutoff := le_max_left _ _
  refine ⟨max A (B s*S*cutoff^q), hA.trans (le_max_left _ _), ?_⟩
  intro ρ L hL hLρ M hM u P
  have hρ : 1 ≤ ρ := hL.trans hLρ
  have hρpos : 0 < ρ := zero_lt_one.trans_le hρ
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  by_cases hlarge : 4*L₀/lo < ρ
  · let hh := hhigh L₀ hL₀ ρ L hL hLρ hlarge M hM u
    have hf := hh.1
    have ha := hh.2
    have hb : A*ρ^(d+1+s)*(L/ρ)^q*‖u‖ ≤
        max A (B s*S*cutoff^q)*ρ^(d+1+s)*(L/ρ)^q*‖u‖ := by
      gcongr
      exact le_max_left _ _
    exact ⟨⟨hf.1, hf.2.trans hb⟩, ⟨ha.1, ha.2.trans hb⟩⟩
  · let hlocal := hlocalizer ρ hρ M hM u
    have hm := hlocal.1
    have hn := hlocal.2
    have hρcutoff : ρ ≤ cutoff := (le_of_not_gt hlarge).trans (le_max_right _ _)
    have hratio : 1 ≤ cutoff*(L/ρ) := by
      rw [← mul_div_assoc]
      apply (le_div_iff₀ hρpos).mpr
      calc
        1*ρ = ρ := one_mul _
        _ ≤ cutoff := hρcutoff
        _ ≤ cutoff*L := le_mul_of_one_le_right (zero_le_one.trans hcutoff) hL
    have hpow : 1 ≤ cutoff^q*(L/ρ)^q := by simpa only [mul_pow] using one_le_pow₀ hratio (n := q)
    have hbound : B s*(S*ρ^(d+1+s)*‖u‖) ≤
        max A (B s*S*cutoff^q)*ρ^(d+1+s)*(L/ρ)^q*‖u‖ := by
      calc
        _ = (B s*S*ρ^(d+1+s)*‖u‖)*1 := by ring
        _ ≤ (B s*S*ρ^(d+1+s)*‖u‖)*(cutoff^q*(L/ρ)^q) :=
          mul_le_mul_of_nonneg_left hpow (by have := hB s; positivity)
        _ = (B s*S*cutoff^q)*ρ^(d+1+s)*(L/ρ)^q*‖u‖ := by ring
        _ ≤ _ := by gcongr; exact le_max_right _ _
    let hforward := hcost L₀ hL₀ s (P-1) (Or.inl rfl) (M.adjoint u) hm
    have he : P.adjoint-1 = (P-1).adjoint := by
      rw [map_sub, ContinuousLinearMap.adjoint_one]
    let hbackward := hcost L₀ hL₀ s (P.adjoint-1) (Or.inr he) (M.adjoint u) hm
    have hf := hforward.2.trans ((mul_le_mul_of_nonneg_left hn (hB s)).trans hbound)
    have ha := hbackward.2.trans ((mul_le_mul_of_nonneg_left hn (hB s)).trans hbound)
    exact ⟨⟨hforward.1, hf⟩, ⟨hbackward.1, ha⟩⟩

end JanetCartan.SignedProductEstimates
