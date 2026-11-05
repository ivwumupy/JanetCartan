module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.TerminalTails
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.TerminalBounds.Physical
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.TerminalBounds.Multiplier

/-! # The actual terminal defect above the angular cancellation threshold

Both physical tails are estimated for the literal operator and its Hilbert
adjoint, keeping source multiplication before the original Fourier factor.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open MeasureTheory Set
open scoped ContDiff

namespace JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect
open FourierIntegral FiniteChain.Graph LowBounds Pseudodifferential RegularSector.FiniteMasks
variable {d r : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)

/-- Combine the two concrete physical tails in their original order for
`app:ch_regular:eq:resolved-angular-tail`. This private step has only primitive
mask and scalar-symbol inputs; the public theorem identifies its sum with the
actual terminal defect. -/
private theorem exists_terminalPhysicalTails_sobolev_decay
    (mi : LocalizerSymbol (d + 1)) (hi : ContDiff ℝ ∞ mi) (his : HasCompactSupport mi)
    (χo χs : E → ℝ) (ho : ContDiff ℝ ∞ χo) (hs : ContDiff ℝ ∞ χs)
    (hoc : HasCompactSupport χo) (hsc : HasCompactSupport χs)
    (hor : ∀ x, χo x ∈ Icc (0 : ℝ) 1) (hsr : ∀ x, χs x ∈ Icc (0 : ℝ) 1)
    (hop : ∀ y ∈ Prod.fst '' tsupport mi, y ∈ interior {x | χo x = 1})
    (hsp : ∀ y ∈ Prod.fst '' tsupport mi, y ∈ interior {x | χs x = 1})
    (b : E → ℝ) (hb : Continuous b) (hbb : ∀ ξ, ‖b ξ‖ ≤ 1) (m N : ℕ) :
    let To := sourceCutMultiplier (r := r) χo ho.continuous
      (fun x ↦ (Real.norm_of_nonneg (hor x).1).trans_le (hor x).2)
    let Ts := sourceCutMultiplier (r := r) χs hs.continuous
      (fun x ↦ (Real.norm_of_nonneg (hsr x).1).trans_le (hsr x).2)
    let B := scalarPhysicalFrequencyOperator (r := r) b hb hbb
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ L : ℝ), 1 ≤ L → L ≤ ρ → ∀ M : H →L[ℂ] H,
      (∀ u : H, (∀ i, Integrable (fun y ↦ u y i)) → M u =ᵐ[volume]
        fun x ↦ WithLp.toLp 2 (leftLocalizer ρ mi (fun y ↦ (u y).ofLp) x)) →
      ∀ u : H,
        MemVectorFourierSobolev (m : ℝ)
          (To (B (((Ts - 1).comp M.adjoint) u)) + (((To - 1).comp M.adjoint) u)) ∧
        vectorFourierSobolevNorm (m : ℝ)
          (To (B (((Ts - 1).comp M.adjoint) u)) + (((To - 1).comp M.adjoint) u)) ≤
            C * ρ ^ (d + 1 + m) * (L / ρ) ^ N * ‖u‖ := by
  intro To Ts B
  obtain ⟨D, hD, hd⟩ := exists_sourceCutMultiplier_fourierSobolev_bound (r := r) χo ho hoc
    (fun x ↦ (Real.norm_of_nonneg (hor x).1).trans_le (hor x).2) m
  obtain ⟨Co, hCo, hco⟩ := exists_leftLocalizer_adjoint_physicalTail_sobolev_decay
    (r := r) mi hi his χo ho hoc hor hop m N
  obtain ⟨Cs, hCs, hcs⟩ := exists_leftLocalizer_adjoint_physicalTail_sobolev_decay
    (r := r) mi hi his χs hs hsc hsr hsp m N
  refine ⟨D * Cs + Co, by positivity, ?_⟩
  intro ρ L hL hLρ M hM u
  obtain ⟨hsm, hsn⟩ := hcs ρ L hL hLρ M hM u
  obtain ⟨hom, hon⟩ := hco ρ L hL hLρ M hM u
  obtain ⟨hbm, hbn⟩ := scalarPhysicalFrequencyOperator_fourierSobolev_bound b hb hbb
    (m : ℝ) (((Ts - 1).comp M.adjoint) u) hsm
  obtain ⟨hmm, hmn⟩ := hd _ hbm
  obtain ⟨hm, hn⟩ := TerminalBounds.add_bound hmm hom
  refine ⟨hm, hn.trans ?_⟩
  calc
    _ ≤ D * (Cs * ρ ^ (d + 1 + m) * (L / ρ) ^ N * ‖u‖) +
        Co * ρ ^ (d + 1 + m) * (L / ρ) ^ N * ‖u‖ :=
      add_le_add (hmn.trans (mul_le_mul_of_nonneg_left (hbn.trans hsn) hD)) hon
    _ = _ := by ring

/-- The full actual terminal angular PDO minus identity, in either literal
orientation, has rapid Sobolev decay on the protected right localizer above
the explicit low-bump threshold. All analytic inputs are derived from the
fixed original masks and symbol. Consumer: `finiteChain_observation_rapidDecayAt.hBnear`
(`app:ch_regular:eq:resolved-angular-tail`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_actualAngularPDO_sub_identity_sobolev_decay_high
    {Ω : Set E} {center : E} {RQ Mbound : ℝ}
    {A₀ : Fin (d + 1) → MetricTensor (d + 1)} {K : Set E}
    (f : ActualFamily.ActualMaskFamily Ω center RQ A₀ K Mbound) (backward : Bool)
    (mi : LocalizerSymbol (d + 1)) (hi : ContDiff ℝ ∞ mi) (his : HasCompactSupport mi)
    {lo : ℝ} (hlo : 0 < lo)
    (hann : ∀ p ∈ tsupport mi, lo ≤ ‖p.2‖)
    (hang : ∀ p ∈ tsupport mi,
      NormedSpace.normalize p.2 ∈ interior {η | ∑ i, f.angularMask i η = 1})
    (hout : ∀ y ∈ Prod.fst '' tsupport mi, y ∈ interior {x | f.outputMask x = 1})
    (hsource : ∀ y ∈ Prod.fst '' tsupport mi, y ∈ interior {x | f.inputMask x = 1})
    (m N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ L : ℝ), 1 ≤ L → L ≤ ρ →
      2 * f.radialThreshold / lo < ρ → ∀ M : H →L[ℂ] H,
      (∀ u : H, (∀ i, Integrable (fun y ↦ u y i)) → M u =ᵐ[volume]
        fun x ↦ WithLp.toLp 2 (leftLocalizer ρ mi (fun y ↦ (u y).ofLp) x)) →
      ∀ u : H,
        let P := if backward then (actualAngularPDO (r := r) f).adjoint else actualAngularPDO f
        MemVectorFourierSobolev (m : ℝ) (((P - 1).comp M.adjoint) u) ∧
        vectorFourierSobolevNorm (m : ℝ) (((P - 1).comp M.adjoint) u) ≤
          C * ρ ^ (d + 1 + m) * (L / ρ) ^ N * ‖u‖ := by
  let χo := if backward then f.inputMask else f.outputMask
  let χs := if backward then f.outputMask else f.inputMask
  have ho : ContDiff ℝ ∞ χo := by
    cases backward <;> first | exact f.outputMask_smooth | exact f.inputMask_smooth
  have hs : ContDiff ℝ ∞ χs := by
    cases backward <;> first | exact f.outputMask_smooth | exact f.inputMask_smooth
  have hoc : HasCompactSupport χo := by
    cases backward <;> first | exact f.outputMask_compact | exact f.inputMask_compact
  have hsc : HasCompactSupport χs := by
    cases backward <;> first | exact f.outputMask_compact | exact f.inputMask_compact
  have hor : ∀ x, χo x ∈ Icc (0 : ℝ) 1 := by
    cases backward <;> first | exact f.outputMask_range | exact f.inputMask_range
  have hsr : ∀ x, χs x ∈ Icc (0 : ℝ) 1 := by
    cases backward <;> first | exact f.outputMask_range | exact f.inputMask_range
  have hop : ∀ y ∈ Prod.fst '' tsupport mi, y ∈ interior {x | χo x = 1} := by
    cases backward <;> assumption
  have hsp : ∀ y ∈ Prod.fst '' tsupport mi, y ∈ interior {x | χs x = 1} := by
    cases backward <;> assumption
  let hob := fun x ↦ (Real.norm_of_nonneg (hor x).1).trans_le (hor x).2
  let hsb := fun x ↦ (Real.norm_of_nonneg (hsr x).1).trans_le (hsr x).2
  let To := sourceCutMultiplier (r := r) χo ho.continuous hob
  let Ts := sourceCutMultiplier (r := r) χs hs.continuous hsb
  let b := fun ξ ↦ ∑ p, dilatedConicMask (f.angularMask p) f.radialThreshold ξ
  have hb : Continuous b := continuous_finsetSum _ (fun p _ ↦
    (contDiff_dilatedConicMask (f.angularMask_smooth p) f.radialThreshold).continuous)
  have hbb : ∀ ξ, ‖b ξ‖ ≤ 1 := fun ξ ↦
    (Real.norm_of_nonneg (actualFamily_sum_dilatedConicMask_mem_Icc f ξ).1).trans_le
      (actualFamily_sum_dilatedConicMask_mem_Icc f ξ).2
  let B := scalarPhysicalFrequencyOperator (r := r) b hb hbb
  obtain ⟨C, hC, hbound⟩ := exists_terminalPhysicalTails_sobolev_decay
    (r := r) mi hi his χo χs ho hs hoc hsc hor hsr hop hsp b hb hbb m N
  refine ⟨C, hC, ?_⟩
  intro ρ L hL hLρ hρ M hM u P
  have he : (P - 1).comp M.adjoint =
      To.comp (B.comp ((Ts - 1).comp M.adjoint)) + (To - 1).comp M.adjoint := by
    have h := actualAngularPDO_sub_identity_comp_rightLocalizer_eq_tails f backward
      hlo hρ mi M hM hann hang
    dsimp only [P, To, Ts, χo, χs]
    split_ifs with hback <;> simpa only [hback, Bool.false_eq_true, ↓reduceIte] using h
  rw [he]
  exact hbound ρ L hL hLρ M hM u

end JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect
