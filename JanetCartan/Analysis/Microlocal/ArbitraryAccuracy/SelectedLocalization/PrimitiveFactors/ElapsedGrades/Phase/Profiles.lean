module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.ElapsedGrades.Phase.SmoothConstruction
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.ElapsedGrades.Phase.PhysicalGrades

/-!
# Uniform grades on one constructed smooth selected phase

The normalized and physical estimates are transferred by joint germs to the
same auxiliary. Constants precede all current coefficient arrays and scales.
The compact normalized carrier is the geometric input produced from the
retained chart and protected proof masks. Consumer: phase inputs of
`ResidualLocalization.exists_completePhysicalResidual_restriction_bound`
(`app:ch_regular:eq:high-phase`, `app:ch_regular:eq:chain-tail`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open RegularSector RegularSector.FiniteAssembly
open RegularSector.FiniteMasks RegularSector.FiniteMasks.ActualFamily
open RegularSector.Characteristic RegularSector.Characteristic.ConicPhase
open RegularSector.Characteristic.EvolutionIntegral
variable {d : ℕ}

private theorem exists_phase_cutoff_radius
    {S : Set (SymbolBudgets.TwoTimePoint d)} (hS : IsCompact S)
    (hzero : ∀ w ∈ S, w.2 ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1/2 ∧ ∀ w ∈ S, δ < ‖w.2‖ := by
  by_cases hne : S.Nonempty
  · obtain ⟨w, hw, hmin⟩ := hS.exists_isMinOn hne continuous_snd.norm.continuousOn
    have hn : 0 < ‖w.2‖ := norm_pos_iff.mpr (hzero w hw)
    refine ⟨min (‖w.2‖ / 2) (1/4), lt_min (half_pos hn) (by norm_num),
      (min_le_right _ _).trans_lt (by norm_num), ?_⟩
    intro v hv
    exact ((min_le_left _ _).trans_lt (half_lt_self hn)).trans_le (hmin hv)
  · exact ⟨1/4, by norm_num, by norm_num, fun w hw ↦ (hne ⟨w, hw⟩).elim⟩

variable {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "T" => Characteristic.TwoTimePoint (Euclidean d)
local notation "Z" => RootState (Euclidean d)
local notation "Mat" => MetricTensor (d+1)

/-- Construct one smooth auxiliary per retained chart with both quantitative
phase profiles, preserving the actual `twoTimePhase C`. The constants precede
`Q`, `L`, `ρ`, and accuracy. The local smoothness, buffer and `phaseCost`
estimates are precisely retained outputs of
`RegularSector.FiniteAssembly.exists_finite_direct_operator_bounds`; `hmap`
and `hpos` are geometric inclusions for the protected-mask assembly.
No estimate of any extended phase is assumed. The physical frequency collar
`1/2` is the one furnished by the actual doubled selected multiplier.
Consumer: `CompleteFactor.hprimitivePhase`, `hauxPhaseGrades`, and supported
phase replacement (`app:ch_regular:eq:initial-coefficient-profile`,
`app:ch_regular:eq:high-phase`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_selected_smooth_auxiliaryPhase_profiles
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    (Kphase : f.centers → Set (SymbolBudgets.TwoTimePoint d))
    (hKphase : ∀ p, IsCompact (Kphase p))
    (hpos : ∀ p, ∀ w ∈ Kphase p, 0 < (f.chart p).radialSection w.2)
    (hmap : ∀ p,
      let e := coordinateSplit (f.chart p).index
      let z : Z := ((e x).1, ((e x).2, (e p.val.val).2))
      MapsTo (normalize (f.chart p).radialSection ∘ budgetCoordinates) (Kphase p)
        (closedBall (z.1, z) (f.chart p).targetRadius))
    (A : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j) :
    ∃ P₀ Pbase : ℕ → ℝ, (∀ j, 0 ≤ P₀ j) ∧ (∀ j, 0 ≤ Pbase j) ∧
      ∀ (Rstar : ℕ), 3 ≤ Rstar → ∀ L : ℝ, 1 ≤ L →
      ∀ (Q : E → Fin (d+1) → Mat),
      (∀ j, cNorm (closedBall x RQ) j Q ≤ A j * L ^ (j - Rstar)) →
      ∀ C : f.centers → OpenPartialHomeomorph T T,
      (∀ p, ContDiffOn ℝ ∞ (twoTimePhase (C p)) (C p).target) →
      (∀ p,
        let e := coordinateSplit (f.chart p).index
        let z : Z := ((e x).1, ((e x).2, (e p.val.val).2))
        closedBall (z.1, z) (f.chart p).targetRadius ⊆ (C p).target) →
      (∀ p m,
        let e := coordinateSplit (f.chart p).index
        let z : Z := ((e x).1, ((e x).2, (e p.val.val).2))
        cNorm (closedBall (z.1, z) (f.chart p).targetRadius) m (twoTimePhase (C p)) ≤
          (f.chart p).phaseCost m * (1 + cNorm (closedBall x RQ) (m+1) Q)) →
      let J := fun p ↦
        let e := coordinateSplit (f.chart p).index
        let z : Z := ((e x).1, ((e x).2, (e p.val.val).2))
        closedBall (z.1, z) (f.chart p).targetRadius
      ∃ Ψ : f.centers → TwoTimePhase d,
        (∀ p, ContDiff ℝ ∞ (SymbolBudgets.jointPhase (Ψ p))) ∧
        (∀ p w, budgetCoordinates w ∈ domain (f.chart p).radialSection (J p) →
          (w ∈ Kphase p ∨ (1/2 : ℝ) < ‖w.2‖) →
          SymbolBudgets.jointPhase (Ψ p) =ᶠ[𝓝 w]
            SymbolBudgets.jointPhase (curriedExtend (f.chart p).radialSection (twoTimePhase (C p)))) ∧
        (∀ ρ : ℝ, 1 ≤ ρ → ∀ p, ∀ w ∈ Kphase p,
          SymbolBudgets.jointPhase (SymbolBudgets.normalizedTwoTimePhase ρ (Ψ p)) =ᶠ[𝓝 w]
            SymbolBudgets.jointPhase (curriedExtend (f.chart p).radialSection (twoTimePhase (C p)))) ∧
        (∀ ρ : ℝ, 1 ≤ ρ → ∀ p, ∀ w ∈ Kphase p, ∀ j,
          ‖iteratedFDeriv ℝ j (fderiv ℝ (SymbolBudgets.jointPhase
            (SymbolBudgets.normalizedTwoTimePhase ρ (Ψ p)))) w‖ ≤ P₀ j * L ^ (j-1)) ∧
        ∀ p η v, budgetCoordinates (v, η) ∈ domain (f.chart p).radialSection (J p) →
          (1/2 : ℝ) < ‖η‖ → ∀ k,
          ‖iteratedFDeriv ℝ (k+1) (fun w : ℝ × ℝ × Euclidean d ↦
            Ψ p w.1 w.2.1 w.2.2 η) v‖ ≤ ‖η‖ * Pbase k * L ^ k := by
  classical
  obtain ⟨P₀, hP₀, hn⟩ := exists_selected_normalizedPhase_jet_profile f Kphase hKphase hpos hmap A hA
  obtain ⟨Pbase, hPbase, hb⟩ := exists_selected_physicalPhase_base_profile f A hA
  have hδ p : ∃ δ : ℝ, 0 < δ ∧ δ < 1/2 ∧ ∀ w ∈ Kphase p, δ < ‖w.2‖ := by
    apply exists_phase_cutoff_radius (hKphase p)
    intro w hw he
    have := hpos p w hw
    simp [he] at this
  choose δ hδpos hδhalf hδK using hδ
  refine ⟨P₀, Pbase, hP₀, hPbase, ?_⟩
  intro Rstar hRstar L hL Q hQ C hC hbuffer hphase J
  have hex p := exists_smooth_truncated_conicPhase (f.chart p).radialSection (C p)
    (isCompact_closedBall _ _) (hbuffer p) (hC p) (hδpos p)
  choose Ψ hΨ he hnΨ using hex
  have hdomain p w (hw : w ∈ Kphase p) :
      budgetCoordinates w ∈ domain (f.chart p).radialSection (J p) :=
    ⟨hpos p w hw, hmap p hw⟩
  refine ⟨Ψ, hΨ, ?_, ?_, ?_, ?_⟩
  · intro p w hw hc
    exact he p w hw (hc.elim (hδK p w) ((hδhalf p).trans ·))
  · intro ρ hρ p w hw
    exact hnΨ p ρ hρ w (hdomain p w hw) (hδK p w hw)
  · intro ρ hρ p w hw j
    have heq := ((hnΨ p ρ hρ w (hdomain p w hw) (hδK p w hw)).fderiv (𝕜 := ℝ) |>.iteratedFDeriv ℝ j).eq_of_nhds
    rw [heq]
    have h := hn Rstar hRstar L ρ hL (zero_lt_one.trans_le hρ) Q hQ C hC hbuffer hphase p w hw j
    rwa [normalizedTwoTimePhase_curriedExtend _ _ (zero_lt_one.trans_le hρ)] at h
  · intro p η v hv hη k
    have heq := (he p (v, η) hv ((hδhalf p).trans hη)).comp_tendsto
      ((continuous_id.prodMk continuous_const).tendsto v)
    have hj := (heq.iteratedFDeriv ℝ (k+1)).eq_of_nhds
    change iteratedFDeriv ℝ (k+1) (fun w : ℝ × ℝ × Euclidean d ↦ Ψ p w.1 w.2.1 w.2.2 η) v = _ at hj
    rw [hj]
    exact hb Rstar hRstar L hL Q hQ C hC hbuffer hphase p η v hv.2 k

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
