module

public import JanetCartan.Analysis.Microlocal.SelectedEvenProofMasks.EvenConclusion
public import JanetCartan.Analysis.Microlocal.SelectedEvenProofMasks.ResidualPhaseGaps

/-!
# Supported phase gaps for the supplied terminal-protected masks

The actual short-time geometric gaps and retained conic phase germ are kept
on their original masks. The clock estimate supplies the remaining supported
times without selecting a second existential family.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open SelectedEvenProofMasks
open RegularSector.Characteristic RegularSector.Characteristic.ConicPhase
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.FiniteMasks RegularSector.FiniteMasks.ActualFamily
open EvolutionIntegratedLocalization FiniteChain.Graph JanetCartan.Localization
open ProtectedMasks
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x₀ : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "V" => ℝ × JointVariables E
local notation "Z" => RootState (Euclidean d)
local notation "T" => TwoTimePoint (Euclidean d)

/-- Positive normalization avoids the spatial cone vertex at the actual
point. The smooth singleton extension is used only for differentiability,
and its germ is pulled back through both elapsed times
(`app:ch_regular:eq:joint-kernel-phase`). -/
private theorem differentiableAt_prescribedExtension_jointElapsedPhase
    (G : T → ℝ) (hG : ContDiffOn ℝ ∞ G {q | q.2.2.2 ≠ 0})
    {ρ : ℝ} (hρ : 0 < ρ) (o : Bool) (x y : E) (v : V) (hv : spatialPart v.2.2.1 ≠ 0) :
    DifferentiableAt ℝ (jointElapsedPhase o
      (SymbolBudgets.normalizedTwoTimePhase ρ (fun t s u η ↦ G (t,s,u,η))) x y) v := by
  let Ψ := fun t s u η ↦ G (t,s,u,η)
  let W := {w : SymbolBudgets.TwoTimePoint d | w.2 ≠ 0}
  have hW : IsOpen W := isOpen_ne_fun continuous_snd continuous_const
  have hΨ : ContDiffOn ℝ ∞ (SymbolBudgets.jointPhase Ψ) W :=
    hG.comp budgetCoordinates.contDiff.contDiffOn (fun _ h ↦ h)
  have hn : ContDiffOn ℝ ∞ (SymbolBudgets.jointPhase (SymbolBudgets.normalizedTwoTimePhase ρ Ψ)) W :=
    (hΨ.comp (contDiff_fst.prodMk (contDiff_snd.const_smul ρ)).contDiffOn
      (fun _ h ↦ smul_ne_zero hρ.ne' h)).const_smul ρ⁻¹
  obtain ⟨P, hP, hsame⟩ := exists_supported_twoTimePhase_extension
    (SymbolBudgets.normalizedTwoTimePhase ρ Ψ) (J := {elapsedJointCoordinates v}) isClosed_singleton
      hW (singleton_subset_iff.mpr hv) hn
  exact ((contDiff_jointElapsedPhase o P x y hP).differentiable (by simp) v).congr_of_eventuallyEq
    (jointElapsedPhase_eventuallyEq_of_twoTimePhase o _ P x y v
      (hsame _ (mem_singleton _))).symm

/-- The actual short-time geometric gaps extend to every nonnegative
point of the retained residual carrier for the prescribed masks. At later
times the original clock supplies both gaps. The phase germ is the one returned
with these masks by terminal protection; no existential mask is recovered
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:joint-kernel-phase`). -/
theorem exists_prescribed_retained_phase_gaps
    (f : ActualMaskFamily Ω x₀ RQ A₀ K M) (j : f.centers)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (eT : Module.Basis ι ℝ (JointVariables E)) (eI : Module.Basis κ ℝ V)
    (output : E → ℝ) (aPhase bPhase θ a b εcollar δT δI : ℝ)
    (hT : 0 < δT) (hI : 0 < δI)
    (threshold c C : ℝ) (ht : f.radialThreshold ≤ threshold)
    (hout : tsupport output ⊆ ball x₀ f.physicalRadius) (Θ : ℝ → ℂ)
    (ra rb : ℝ) {tlo thi : ℝ} (hlo : 0 < tlo) (hra : 0 < ra)
    (hleft : aPhase ≤ ra / thi) (hright : ra / tlo ≤ bPhase) :
    ∃ dT dI : ℝ, 0 < dT ∧ 0 < dI ∧
      ∀ (Cphase : OpenPartialHomeomorph T T) (Gext : T → ℝ),
      ContDiffOn ℝ ∞ Gext {q | q.2.2.2 ≠ 0} →
      (∀ q ∈ ConicPhase.domain (f.chart j).radialSection
        (closedBall ((coordinateSplit (f.chart j).index x₀).1,
          ((coordinateSplit (f.chart j).index x₀).1,
            ((coordinateSplit (f.chart j).index x₀).2,
              (coordinateSplit (f.chart j).index j.val.val).2)))
          (2*(f.chart j).maskRadius)),
        Gext =ᶠ[𝓝 q] ConicPhase.phase (f.chart j).radialSection Cphase) →
      ∀ mi mo : LocalizerSymbol (d+1),
      (∀ (o : Bool) (ρ : ℝ), 0 < ρ → ∀ (x y : E) (r' : ℝ) (p : JointVariables E),
        r' ∈ Icc 0 (6*f.physicalRadius) → r' ≤ (f.chart j).maskRadius →
        p.1.1 0 ∈ closedBall (coordinateSplit (f.chart j).index x₀).1 ((f.chart j).maskRadius/2) →
        spatialPart p.1.1 ∈ closedBall (coordinateSplit (f.chart j).index x₀).2 ((f.chart j).maskRadius/2) →
        spatialPart p.2.1 ∈ ConicPhase.radialSectionBand (f.chart j).radialSection
          (coordinateSplit (f.chart j).index j.val.val).2 ((f.chart j).maskRadius/2) aPhase bPhase →
        (y,p.2.2.1) ∈ cthickening (θ/2) (tsupport mi) →
        (x,p.2.2.2) ∈ tsupport (fun q ↦ 1-mo q) →
        (δI ≤ phaseGradientSquare eI (jointElapsedPhase o
            (SymbolBudgets.normalizedTwoTimePhase ρ
              (curriedPhase (f.chart j).radialSection Cphase)) x y) (r',p) ∧
          (r' ≤ εcollar → δT ≤ phaseGradientSquare eT (fun w ↦ jointElapsedPhase o
            (SymbolBudgets.normalizedTwoTimePhase ρ
              (curriedPhase (f.chart j).radialSection Cphase)) x y (r',w)) p)) ∧
        (δI ≤ phaseGradientSquare eI (jointElapsedPhase o
            (SymbolBudgets.normalizedTwoTimePhase ρ (fun t s u η ↦ Gext (t,s,u,η))) x y) (r',p) ∧
          (r' ≤ εcollar → δT ≤ phaseGradientSquare eT (fun w ↦ jointElapsedPhase o
            (SymbolBudgets.normalizedTwoTimePhase ρ (fun t s u η ↦ Gext (t,s,u,η))) x y (r',w)) p))) →
      let Kjet := selectedRetainedResidualCarrier f j output threshold c C a b Θ ra rb tlo thi
      ∀ o (ρ : ℝ), 0 < ρ → ∀ x y (v : V), v ∈ elapsedOutputJetCarrier Kjet mi mo x y → 0 ≤ v.1 →
        let gap := fun Ψ : TwoTimePhase d ↦
          let F := jointElapsedPhase o (SymbolBudgets.normalizedTwoTimePhase ρ Ψ) x y
          dI ≤ phaseGradientSquare eI F v ∧
            (v.1 ≤ εcollar → dT ≤ phaseGradientSquare eT (fun w ↦ F (v.1,w)) v.2)
        gap (curriedPhase (f.chart j).radialSection Cphase) ∧
          gap (fun t s u η ↦ Gext (t,s,u,η)) := by
  obtain ⟨δclock, hclock, hlate⟩ := exists_late_elapsed_clock_phase_gap eI f.physicalRadius_pos
  let δct := (f.physicalRadius / jointDirectionLoss eT)^2
  have hct : 0 < δct := sq_pos_of_pos (div_pos f.physicalRadius_pos (jointDirectionLoss_pos eT))
  refine ⟨min δT δct, min δI δclock, lt_min hT hct, lt_min hI hclock, ?_⟩
  intro Cphase Gext hG hgerm mi mo hgap Kjet o ρ hρ x y v hv hr gap
  have hcar : v ∈ Kjet := hv.1
  have hγpos := (f.chart j).maskRadius_pos
  have hγ : v.1 ≤ (f.chart j).maskRadius := hcar.2.trans (by linarith)
  obtain ⟨htimebox, hy', htime⟩ := selectedResidualComparableCarrier_positions f j hout hcar.1.1.2
  have hη := retainedResidualJetCarrier_phase_band f j ht hlo hra hleft hright hcar.1
  by_cases hshort : v.1 ≤ 6 * f.physicalRadius
  · obtain ⟨⟨hIi, hTt⟩, hIext, hText⟩ := hgap o ρ hρ x y v.1 v.2 ⟨hr, hshort⟩
      hγ htimebox hy' hη (self_subset_cthickening _ hv.2.1) hv.2.2
    exact ⟨⟨(min_le_left _ _).trans hIi, fun h ↦ (min_le_left _ _).trans (hTt h)⟩,
      (min_le_left _ _).trans hIext, fun h ↦ (min_le_left _ _).trans (hText h)⟩
  · have hη' := retainedResidualJetCarrier_phase_band f j ht hlo hra le_rfl le_rfl hcar.1
    have hhi : 0 < thi := by
      obtain ⟨_, t, h, _⟩ := hcar.1
      exact (hlo.trans_le h.1).trans_le h.2
    have hpos := (radialSectionBand_normalizes (div_pos hra hhi) hη').1
    have hne : spatialPart v.2.2.1 ≠ 0 := by intro hz; simp [hz] at hpos
    let G := Gext
    let Ψ := SymbolBudgets.normalizedTwoTimePhase ρ (fun t s u η ↦ G (t,s,u,η))
    have hd : DifferentiableAt ℝ (jointElapsedPhase o Ψ x y) v :=
      differentiableAt_prescribedExtension_jointElapsedPhase G hG hρ o x y v hne
    have hIext := hlate o Ψ x y v hd htime (le_of_not_ge hshort)
    have hs := hd.comp v.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) v.1 v.2).differentiableAt
    have hb := elapsed_clock_defect_le_norm_tangential_fderiv o Ψ x y v.1 v.2 hs
    have hText := jointDerivative_gap_phaseGradientSquare eT
      (fun w ↦ jointElapsedPhase o Ψ x y (v.1,w)) v.2 f.physicalRadius_pos.le (by
        linarith only [hshort, hb, htime, f.physicalRadius_pos,
          neg_le_abs (v.2.1.1 0 - v.2.1.2 0 - v.1), le_abs_self (v.2.1.1 0 - v.2.1.2 0)])
    let e := coordinateSplit (f.chart j).index
    let z : Z := ((e x₀).1, ((e x₀).2, (e j.val.val).2))
    have he := phaseGradientSquare_normalized_extension_eq eT eI (f.chart j).radialSection
      Cphase hgerm hρ o x y v (elapsedChartPoint_mem_conic_boundary_buffer
        (f.chart j).radialSection z hγpos (div_pos hra hhi) v.2 ⟨hr,hγ⟩ htimebox hy' hη')
    have hext : gap (fun t s u η ↦ G (t,s,u,η)) :=
      ⟨(min_le_right _ _).trans hIext, fun _ ↦ (min_le_right _ _).trans hText⟩
    exact ⟨⟨he.1 ▸ hext.1, fun h ↦ he.2 ▸ hext.2 h⟩, hext⟩

end JanetCartan.ArbitraryAccuracy.SelectedLocalization

