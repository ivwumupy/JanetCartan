module

public import JanetCartan.Analysis.Microlocal.SelectedEvenProofMasks.EvenConclusion
public import JanetCartan.Analysis.Microlocal.SelectedEvenProofMasks.ElapsedClock

/-!
# The two selected phase gaps on the original residual support

The original source-time buffer puts the entire nonnegative support in the
local mask slab. Thus the retained conic extension and original conic phase
have the same joint germs even where elapsed time exceeds the protected
physical interval. At those times the clock gives nonstationarity in each
orientation. This pointwise result needs no auxiliary phase, primitive
profile or upper-gradient bound.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedEvenProofMasks
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
private theorem differentiableAt_normalized_extension_jointElapsedPhase
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

/-- A positive full gap at every nonnegative supported time and tangential
gap throughout the selected collar, simultaneously for the original conic
phase and its actual `Gext` witness. The radii and masks are those of the
selected solver. Both bounds precede the varying coefficient and frequency;
no gradient estimate or extension germ is an input. The lower and upper
scalar comparisons are reflexive with the phase radii supplied by
`exists_selected_direct_residual_phase_carriers`
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_selected_even_retained_phase_gaps
    (f : ActualMaskFamily Ω x₀ RQ A₀ K M) (j : f.centers)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (eT : Module.Basis ι ℝ (JointVariables E)) (eI : Module.Basis κ ℝ V)
    (χ₂ : E → ℝ) (Ksource : Set E) (Vsource : Set (E × E)) (Γ : Set E)
    (output : E → ℝ) (N : ℕ) (aPhase bPhase : f.centers → ℝ)
    (n : f.centers → ℕ) (cRad : (p : f.centers) → Fin (n p) → ℝ)
    (hcRad : ∀ p k, 0 < cRad p k) (Urad : (p : f.centers) → Fin (n p) → Set Z)
    (θ a b Rbase εcollar δT δI : ℝ) (H : ℕ → ℝ) (hT : 0 < δT) (hI : 0 < δI)
    (threshold c C : ℝ) (ht : f.radialThreshold ≤ threshold)
    (hout : tsupport output ⊆ ball x₀ f.physicalRadius) (Θ : ℝ → ℂ)
    (ra rb : f.centers → ℝ) {tlo thi : ℝ} (hlo : 0 < tlo) (hra : 0 < ra j)
    (hleft : aPhase j ≤ ra j / thi) (hright : ra j / tlo ≤ bPhase j) :
    ∃ dT dI : ℝ, 0 < dT ∧ 0 < dI ∧
      ∀ (Q : E → Fin (d+1) → MetricTensor (d+1))
        (Φ : f.centers → Z × ℝ → Z) (Cphase : f.centers → OpenPartialHomeomorph T T)
        (hEven : SelectedSectorEvenNestedMaskConclusion f eT eI χ₂ Ksource Vsource Γ output
          N aPhase bPhase n cRad hcRad Urad θ a b Rbase εcollar δT δI H Q Φ Cphase) (k : Fin N),
      let m := hEven.choose_spec.choose
      let mi := canonicalProofLocalizer (coordinateSplit (f.chart j).index) (m k.castSucc)
      let mo := canonicalProofLocalizer (coordinateSplit (f.chart j).index) (m k.succ)
      let Kjet := selectedRetainedResidualCarrier f j output threshold c C a b Θ
        (ra j) (rb j) tlo thi
      ∀ o (ρ : ℝ), 0 < ρ → ∀ x y (v : V), v ∈ elapsedOutputJetCarrier Kjet mi mo x y → 0 ≤ v.1 →
        let gap := fun Ψ : TwoTimePhase d ↦
          let F := jointElapsedPhase o (SymbolBudgets.normalizedTwoTimePhase ρ Ψ) x y
          dI ≤ phaseGradientSquare eI F v ∧
            (v.1 ≤ εcollar → dT ≤ phaseGradientSquare eT (fun w ↦ F (v.1,w)) v.2)
        gap (curriedPhase (f.chart j).radialSection (Cphase j)) ∧
          gap (fun t s u η ↦ hEven.choose j (t,s,u,η)) := by
  obtain ⟨δclock, hclock, hlate⟩ := exists_late_elapsed_clock_phase_gap eI f.physicalRadius_pos
  let δct := (f.physicalRadius / jointDirectionLoss eT)^2
  have hct : 0 < δct := sq_pos_of_pos (div_pos f.physicalRadius_pos (jointDirectionLoss_pos eT))
  refine ⟨min δT δct, min δI δclock, lt_min hT hct, lt_min hI hclock, ?_⟩
  intro Q Φ Cphase hEven k m mi mo Kjet o ρ hρ x y v hv hr gap
  obtain ⟨_, hG, _, _, _, _, _, _, _, _, _, _, _, _, hgap⟩ := hEven.choose_spec.choose_spec
  have hcar : v ∈ Kjet := hv.1
  have hγpos := (f.chart j).maskRadius_pos
  have hγ : v.1 ≤ (f.chart j).maskRadius := hcar.2.trans (by linarith)
  obtain ⟨htimebox, hy', htime⟩ := selectedResidualComparableCarrier_positions f j hout hcar.1.1.2
  have hη := retainedResidualJetCarrier_phase_band f j ht hlo hra hleft hright hcar.1
  by_cases hshort : v.1 ≤ 6 * f.physicalRadius
  · obtain ⟨⟨hIi, hTt⟩, hIext, hText, _⟩ := hgap k j o ρ hρ x y v.1 v.2 ⟨hr, hshort⟩
      hγ htimebox hy' hη (self_subset_cthickening _ hv.2.1) hv.2.2
    exact ⟨⟨(min_le_left _ _).trans hIi, fun h ↦ (min_le_left _ _).trans (hTt h)⟩,
      (min_le_left _ _).trans hIext, fun h ↦ (min_le_left _ _).trans (hText h)⟩
  · have hη' := retainedResidualJetCarrier_phase_band f j ht hlo hra le_rfl le_rfl hcar.1
    have hhi : 0 < thi := by
      obtain ⟨_, t, h, _⟩ := hcar.1
      exact (hlo.trans_le h.1).trans_le h.2
    have hpos := (radialSectionBand_normalizes (div_pos hra hhi) hη').1
    have hne : spatialPart v.2.2.1 ≠ 0 := by intro hz; simp [hz] at hpos
    let G := hEven.choose j
    let Ψ := SymbolBudgets.normalizedTwoTimePhase ρ (fun t s u η ↦ G (t,s,u,η))
    have hd : DifferentiableAt ℝ (jointElapsedPhase o Ψ x y) v :=
      differentiableAt_normalized_extension_jointElapsedPhase G (hG j).2.1 hρ o x y v hne
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
      (Cphase j) (hG j).2.2.2 hρ o x y v (elapsedChartPoint_mem_conic_boundary_buffer
        (f.chart j).radialSection z hγpos (div_pos hra hhi) v.2 ⟨hr,hγ⟩ htimebox hy' hη')
    have hext : gap (fun t s u η ↦ G (t,s,u,η)) :=
      ⟨(min_le_right _ _).trans hIext, fun _ ↦ (min_le_right _ _).trans hText⟩
    exact ⟨⟨he.1 ▸ hext.1, fun h ↦ he.2 ▸ hext.2 h⟩, hext⟩

end JanetCartan.ArbitraryAccuracy.SelectedEvenProofMasks
