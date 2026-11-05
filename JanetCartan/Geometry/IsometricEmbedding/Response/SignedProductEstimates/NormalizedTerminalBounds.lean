module

public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.NormalizedTerminal
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.TerminalBounds
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.SourceBounds.Normalized

/-!
# Terminal bounds for the actual normalized source defect

The corrected same-family source and its literal adjoint act on the original
right localizer. Fourier cancellation and the existing physical-tail producer
control the three retained physical tails. The fixed low collar is handled by
the actual normalized order-zero bound. This is the terminal factor input to
`finiteChain_observation_rapidDecayAt`, not an estimate for complete residual
words (`app:ch_regular:eq:resolved-angular-tail`).
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

/-- Sobolev bookkeeping for the three physical tails in the corrected source
and its literal adjoint (`app:ch_regular:eq:resolved-angular-tail`). The public
application below supplies every operator bound from the actual masks. -/
private theorem normalized_terminal_three_tail_bound
    (s : ℕ) (F Mi Mo Mc : H →L[ℂ] H)
    {Di Do Dc Ci Co Cc Z : ℝ} (hDi : 0 ≤ Di) (hDo : 0 ≤ Do) (hDc : 0 ≤ Dc)
    (hCi : 0 ≤ Ci) (hCo : 0 ≤ Co) (hCc : 0 ≤ Cc) (hZ : 0 ≤ Z)
    (hfreq : ∀ v : H, MemVectorFourierSobolev (s : ℝ) v →
      MemVectorFourierSobolev (s : ℝ) (F v) ∧
        vectorFourierSobolevNorm (s : ℝ) (F v) ≤ vectorFourierSobolevNorm (s : ℝ) v)
    (hmi : ∀ v : H, MemVectorFourierSobolev (s : ℝ) v →
      MemVectorFourierSobolev (s : ℝ) (Mi v) ∧
        vectorFourierSobolevNorm (s : ℝ) (Mi v) ≤ Di*vectorFourierSobolevNorm (s : ℝ) v)
    (hmo : ∀ v : H, MemVectorFourierSobolev (s : ℝ) v →
      MemVectorFourierSobolev (s : ℝ) (Mo v) ∧
        vectorFourierSobolevNorm (s : ℝ) (Mo v) ≤ Do*vectorFourierSobolevNorm (s : ℝ) v)
    (hmc : ∀ v : H, MemVectorFourierSobolev (s : ℝ) v →
      MemVectorFourierSobolev (s : ℝ) (Mc v) ∧
        vectorFourierSobolevNorm (s : ℝ) (Mc v) ≤ Dc*vectorFourierSobolevNorm (s : ℝ) v)
    (vi vo vc : H)
    (him : MemVectorFourierSobolev (s : ℝ) vi)
    (hom : MemVectorFourierSobolev (s : ℝ) vo)
    (hcm : MemVectorFourierSobolev (s : ℝ) vc)
    (hiZ : vectorFourierSobolevNorm (s : ℝ) vi ≤ Ci*Z)
    (hoZ : vectorFourierSobolevNorm (s : ℝ) vo ≤ Co*Z)
    (hcZ : vectorFourierSobolevNorm (s : ℝ) vc ≤ Cc*Z) :
    let D := (Dc*Do*Ci + Dc*Co + Cc) + (Di*Do*Cc + Di*Co + Ci)
    (MemVectorFourierSobolev (s : ℝ) (Mc (Mo (F vi)) + Mc vo + vc) ∧
      vectorFourierSobolevNorm (s : ℝ) (Mc (Mo (F vi)) + Mc vo + vc) ≤ D*Z) ∧
    (MemVectorFourierSobolev (s : ℝ) (Mi (F (Mo vc)) + Mi (F vo) + vi) ∧
      vectorFourierSobolevNorm (s : ℝ) (Mi (F (Mo vc)) + Mi (F vo) + vi) ≤ D*Z) := by
  intro D
  have hadd {v w z : H} {A B C : ℝ}
      (hv : MemVectorFourierSobolev (s : ℝ) v) (hw : MemVectorFourierSobolev (s : ℝ) w)
      (hz : MemVectorFourierSobolev (s : ℝ) z)
      (hvn : vectorFourierSobolevNorm (s : ℝ) v ≤ A*Z)
      (hwn : vectorFourierSobolevNorm (s : ℝ) w ≤ B*Z)
      (hzn : vectorFourierSobolevNorm (s : ℝ) z ≤ C*Z) :
      MemVectorFourierSobolev (s : ℝ) (v+w+z) ∧
        vectorFourierSobolevNorm (s : ℝ) (v+w+z) ≤ (A+B+C)*Z := by
    obtain ⟨hm, hn⟩ := TerminalBounds.add_bound hv hw
    obtain ⟨hm', hn'⟩ := TerminalBounds.add_bound hm hz
    exact ⟨hm', hn'.trans ((add_le_add (hn.trans (add_le_add hvn hwn)) hzn).trans_eq (by ring))⟩
  constructor
  · obtain ⟨hfim, hfin⟩ := hfreq _ him
    obtain ⟨hmoim, hmoin⟩ := hmo _ hfim
    obtain ⟨hmcim, hmcin⟩ := hmc _ hmoim
    obtain ⟨hmcom, hmcon⟩ := hmc _ hom
    have hb₁ := hmcin.trans (mul_le_mul_of_nonneg_left
      (hmoin.trans (mul_le_mul_of_nonneg_left (hfin.trans hiZ) hDo)) hDc)
    have hb₂ := hmcon.trans (mul_le_mul_of_nonneg_left hoZ hDc)
    obtain ⟨hm, hn⟩ := hadd hmcim hmcom hcm
      (hb₁.trans_eq (by ring : Dc*(Do*(Ci*Z)) = (Dc*Do*Ci)*Z))
      (hb₂.trans_eq (by ring : Dc*(Co*Z) = (Dc*Co)*Z)) hcZ
    exact ⟨hm, hn.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by
      positivity : 0 ≤ Di*Do*Cc + Di*Co + Ci)) hZ)⟩
  · obtain ⟨hmocm, hmocn⟩ := hmo _ hcm
    obtain ⟨hfmocm, hfmocn⟩ := hfreq _ hmocm
    obtain ⟨himocm, himocn⟩ := hmi _ hfmocm
    obtain ⟨hfom, hfon⟩ := hfreq _ hom
    obtain ⟨hiom, hion⟩ := hmi _ hfom
    have hb₁ := himocn.trans (mul_le_mul_of_nonneg_left
      (hfmocn.trans (hmocn.trans (mul_le_mul_of_nonneg_left hcZ hDo))) hDi)
    have hb₂ := hion.trans (mul_le_mul_of_nonneg_left (hfon.trans hoZ) hDi)
    obtain ⟨hm, hn⟩ := hadd himocm hiom him
      (hb₁.trans_eq (by ring : Di*(Do*(Cc*Z)) = (Di*Do*Cc)*Z))
      (hb₂.trans_eq (by ring : Di*(Co*Z) = (Di*Co)*Z)) hiZ
    exact ⟨hm, hn.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by
      positivity : 0 ≤ Dc*Do*Ci + Dc*Co + Cc)) hZ)⟩

/-- Apply the existing physical-tail estimates to each of the three masks.
The scalar Fourier factor has its proved order-zero norm, and all constants
precede it (`app:ch_regular:eq:resolved-angular-tail`). -/
private theorem exists_normalized_terminal_physical_tail_bounds
    (χi χo χc : E → ℝ)
    (hi : ContDiff ℝ ∞ χi) (ho : ContDiff ℝ ∞ χo) (hc : ContDiff ℝ ∞ χc)
    (hic : HasCompactSupport χi) (hoc : HasCompactSupport χo) (hcc : HasCompactSupport χc)
    (hir : ∀ y, χi y ∈ Icc (0 : ℝ) 1)
    (hor : ∀ y, χo y ∈ Icc (0 : ℝ) 1)
    (hcr : ∀ y, χc y ∈ Icc (0 : ℝ) 1)
    (mi : LocalizerSymbol (d+1)) (hmi : ContDiff ℝ ∞ mi) (hmic : HasCompactSupport mi)
    (hip : Prod.fst '' tsupport mi ⊆ interior {y | χi y = 1})
    (hop : Prod.fst '' tsupport mi ⊆ interior {y | χo y = 1})
    (hcp : Prod.fst '' tsupport mi ⊆ interior {y | χc y = 1}) (s q : ℕ) :
    let Mi := sourceCutMultiplier (r := d+1) χi hi.continuous
      (fun y ↦ (Real.norm_of_nonneg (hir y).1).trans_le (hir y).2)
    let Mo := sourceCutMultiplier (r := d+1) χo ho.continuous
      (fun y ↦ (Real.norm_of_nonneg (hor y).1).trans_le (hor y).2)
    let Mc := sourceCutMultiplier (r := d+1) χc hc.continuous
      (fun y ↦ (Real.norm_of_nonneg (hcr y).1).trans_le (hcr y).2)
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (b : E → ℝ) (hb : Continuous b) (hbb : ∀ ξ, ‖b ξ‖ ≤ 1),
      ∀ ρ L : ℝ, 1 ≤ L → L ≤ ρ → ∀ M : H →L[ℂ] H,
      (∀ u : H, (∀ i, Integrable (fun y ↦ u y i)) → M u =ᵐ[volume]
        fun x ↦ WithLp.toLp 2 (leftLocalizer ρ mi (fun y ↦ (u y).ofLp) x)) →
      ∀ u : H,
        let F := scalarPhysicalFrequencyOperator (r := d+1) b hb hbb
        let v := Mc (Mo (F ((Mi-1) (M.adjoint u)))) + Mc ((Mo-1) (M.adjoint u)) + (Mc-1) (M.adjoint u)
        let w := Mi (F (Mo ((Mc-1) (M.adjoint u)))) + Mi (F ((Mo-1) (M.adjoint u))) + (Mi-1) (M.adjoint u)
        (MemVectorFourierSobolev (s : ℝ) v ∧ vectorFourierSobolevNorm (s : ℝ) v ≤
          D*ρ^(d+1+s)*(L/ρ)^q*‖u‖) ∧
        (MemVectorFourierSobolev (s : ℝ) w ∧ vectorFourierSobolevNorm (s : ℝ) w ≤
          D*ρ^(d+1+s)*(L/ρ)^q*‖u‖) := by
  intro Mi Mo Mc
  let dataDi := exists_sourceCutMultiplier_fourierSobolev_bound
    (r := d+1) χi hi hic (fun y ↦ (Real.norm_of_nonneg (hir y).1).trans_le (hir y).2) s
  let Di := dataDi.choose
  have hDi := dataDi.choose_spec.1
  have hMi := dataDi.choose_spec.2
  let dataDo := exists_sourceCutMultiplier_fourierSobolev_bound
    (r := d+1) χo ho hoc (fun y ↦ (Real.norm_of_nonneg (hor y).1).trans_le (hor y).2) s
  let Do := dataDo.choose
  have hDo := dataDo.choose_spec.1
  have hMo := dataDo.choose_spec.2
  let dataDc := exists_sourceCutMultiplier_fourierSobolev_bound
    (r := d+1) χc hc hcc (fun y ↦ (Real.norm_of_nonneg (hcr y).1).trans_le (hcr y).2) s
  let Dc := dataDc.choose
  have hDc := dataDc.choose_spec.1
  have hMc := dataDc.choose_spec.2
  let dataCi := exists_leftLocalizer_adjoint_physicalTail_sobolev_decay
    (r := d+1) mi hmi hmic χi hi hic hir (fun _ hy ↦ hip hy) s q
  let Ci := dataCi.choose
  have hCi := dataCi.choose_spec.1
  have hti := dataCi.choose_spec.2
  let dataCo := exists_leftLocalizer_adjoint_physicalTail_sobolev_decay
    (r := d+1) mi hmi hmic χo ho hoc hor (fun _ hy ↦ hop hy) s q
  let Co := dataCo.choose
  have hCo := dataCo.choose_spec.1
  have hto := dataCo.choose_spec.2
  let dataCc := exists_leftLocalizer_adjoint_physicalTail_sobolev_decay
    (r := d+1) mi hmi hmic χc hc hcc hcr (fun _ hy ↦ hcp hy) s q
  let Cc := dataCc.choose
  have hCc := dataCc.choose_spec.1
  have htc := dataCc.choose_spec.2
  let D := (Dc*Do*Ci + Dc*Co + Cc) + (Di*Do*Cc + Di*Co + Ci)
  refine ⟨D, by dsimp [D]; positivity, ?_⟩
  intro b hb hbb ρ L hL hLρ M hM u F v w
  let Z := ρ^(d+1+s)*(L/ρ)^q*‖u‖
  have hρ : 0 < ρ := zero_lt_one.trans_le (hL.trans hLρ)
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  obtain ⟨him, hin⟩ := hti ρ L hL hLρ M hM u
  obtain ⟨hom, hon⟩ := hto ρ L hL hLρ M hM u
  obtain ⟨hcm, hcn⟩ := htc ρ L hL hLρ M hM u
  have hiZ : vectorFourierSobolevNorm (s : ℝ) ((Mi-1) (M.adjoint u)) ≤ Ci*Z := by
    simpa only [Mi, Ci, dataCi, Z, mul_assoc, ContinuousLinearMap.comp_apply] using hin
  have hoZ : vectorFourierSobolevNorm (s : ℝ) ((Mo-1) (M.adjoint u)) ≤ Co*Z := by
    simpa only [Mo, Co, dataCo, Z, mul_assoc, ContinuousLinearMap.comp_apply] using hon
  have hcZ : vectorFourierSobolevNorm (s : ℝ) ((Mc-1) (M.adjoint u)) ≤ Cc*Z := by
    simpa only [Mc, Cc, dataCc, Z, mul_assoc, ContinuousLinearMap.comp_apply] using hcn
  have hh := normalized_terminal_three_tail_bound s F Mi Mo Mc
    hDi hDo hDc hCi hCo hCc hZ
    (fun v hv ↦ scalarPhysicalFrequencyOperator_fourierSobolev_bound b hb hbb (s : ℝ) v hv)
    hMi hMo hMc ((Mi-1) (M.adjoint u)) ((Mo-1) (M.adjoint u)) ((Mc-1) (M.adjoint u))
    him hom hcm hiZ hoZ hcZ
  have he : D*Z = D*ρ^(d+1+s)*(L/ρ)^q*‖u‖ := by dsimp only [Z]; ring
  exact ⟨⟨hh.1.1, hh.1.2.trans_eq he⟩, ⟨hh.2.1, hh.2.2.trans_eq he⟩⟩

/-- The actual normalized terminal defect has arbitrary accuracy above its
original low collar, with the same constant for the forward and adjoint
operators. All constants precede the final threshold, source frequency and
source datum. Geometric terminal coverage is supplied by the original
no-return/localizer construction (`app:ch_regular:eq:chain-tail`). -/
theorem exists_normalizedSource_terminal_decay_high
    (f : ActualMaskFamily Ω center RQ A₀ K C₀) (hK : IsCompact K)
    (hsym : ∀ η ∈ K, -η ∈ K)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hor : ∀ y, output y ∈ Icc (0 : ℝ) 1)
    (mi : LocalizerSymbol (d+1)) (hi : ContDiff ℝ ∞ mi) (hic : HasCompactSupport mi)
    {lo : ℝ} (hlo : 0 < lo) (hann : ∀ p ∈ tsupport mi, lo ≤ ‖p.2‖)
    (hterminal : ∀ p ∈ tsupport mi, NormedSpace.normalize p.2 ∈ K)
    (hcore : Prod.fst '' tsupport mi ⊆ closedBall center f.physicalRadius)
    (houtput : Prod.fst '' tsupport mi ⊆ interior {y | output y = 1})
    (s q : ℕ) :
    let hob := fun y ↦ (Real.norm_of_nonneg (hor y).1).trans_le (hor y).2
    ∃ D : ℝ, 0 ≤ D ∧ ∀ L₀ : ℝ, f.radialThreshold ≤ L₀ →
      ∀ ρ L : ℝ, 1 ≤ L → L ≤ ρ → 4*L₀/lo < ρ →
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
  have hop : Prod.fst '' tsupport mi ⊆ interior {x | f.outputMask x = 1} :=
    fun _ hy ↦ f.outputMask_plateau (hcore hy)
  have hip : Prod.fst '' tsupport mi ⊆ interior {x | f.inputMask x = 1} := by
    intro y hy
    exact f.inputMask_plateau (closedBall_subset_closedBall
      (by linarith [f.physicalRadius_pos] : f.physicalRadius ≤ 2*f.physicalRadius) (hcore hy))
  let dataD := exists_normalized_terminal_physical_tail_bounds
    f.inputMask f.outputMask output f.inputMask_smooth f.outputMask_smooth ho
    f.inputMask_compact f.outputMask_compact hoc f.inputMask_range f.outputMask_range hor
    mi hi hic hip hop houtput s q
  let D := dataD.choose
  have hD := dataD.choose_spec.1
  have hbound := dataD.choose_spec.2
  refine ⟨D, hD, ?_⟩
  intro L₀ hL₀ ρ L hL hLρ hhigh M hM u P
  let hexact := normalizedSource_comp_rightLocalizer_eq_physical_tails
    f hK hsym hL₀ hlo hhigh output ho.continuous hob mi M hM hann hterminal u
  have hf := hexact.1
  have ha := hexact.2
  have hh := hbound (normalizedSourceMask f hK L₀)
    (normalizedSourceMask_properties f hK L₀).1.continuous
    (fun ξ ↦ (Real.norm_of_nonneg ((normalizedSourceMask_properties f hK L₀).2 ξ).1).trans_le
      ((normalizedSourceMask_properties f hK L₀).2 ξ).2)
    ρ L hL hLρ M hM u
  let Q : H → Prop := fun v ↦ MemVectorFourierSobolev (s : ℝ) v ∧
    vectorFourierSobolevNorm (s : ℝ) v ≤ D*ρ^(d+1+s)*(L/ρ)^q*‖u‖
  exact ⟨Eq.mpr (congrArg Q hf) hh.1, Eq.mpr (congrArg Q ha) hh.2⟩

end JanetCartan.SignedProductEstimates
