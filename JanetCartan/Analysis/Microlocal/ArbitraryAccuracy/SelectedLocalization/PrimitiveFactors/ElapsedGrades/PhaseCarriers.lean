module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.ElapsedGrades.Phase
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.ElapsedGrades.Geometry
public import JanetCartan.Geometry.IsometricEmbedding.Response.Compatible.Cutoffs

/-!
# Buffered elapsed cutoffs and normalized phase carriers

The phase profile is evaluated on the image of the actual compact comparable
carrier. Its normalization stays in the retained local phase chart, including
negative elapsed times in the smooth extension cutoff. This closes the geometric
premises of `exists_selected_smooth_auxiliaryPhase_profiles` without assuming
any quantitative grade of the retained global extension.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open RegularSector RegularSector.FiniteAssembly RegularSector.FinitePdo
open Characteristic Characteristic.ConicPhase Characteristic.UniformEvolution
open Characteristic.EvolutionIntegral Characteristic.EvolutionIntegral.SymbolBudgets
open FiniteMasks FiniteMasks.ActualFamily FiniteAlgebraic
open EvolutionLocalization EvolutionIntegratedLocalization FourierIntegral FiniteChain.Graph
open FiniteChain.Graph.PhysicalShells
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "V" => ℝ × JointVariables E

/-- Choose the smooth elapsed extension cutoffs inside each retained phase
buffer and equal to one on its entire original retarded slab. These fixed
cutoffs precede coefficients, frequency and accuracy. Consumer: `hθone` in
`CompleteFactor` and the phase-carrier inclusion below
(`app:ch_regular:eq:chain-tail`). -/
theorem exists_selected_buffered_elapsed_cutoffs
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    (hρb : ∀ p, (f.chart p).bufferRadius ≤ (f.chart p).targetRadius)
    (hsrcρ : ∀ p, (f.chart p).maskRadius ≤ (f.chart p).bufferRadius / 4) :
    ∃ θ : f.centers → ℝ → ℂ, ∀ p,
      ContDiff ℝ ∞ (θ p) ∧ HasCompactSupport (θ p) ∧
      (∀ r ∈ Icc 0 (3*(f.chart p).maskRadius/4), θ p r = 1) ∧
      tsupport (θ p) ⊆ ball 0 (retainedRadius (f.chart p).targetRadius (f.chart p).bufferRadius) := by
  classical
  have hex p : ∃ θ : ℝ → ℂ, ContDiff ℝ ∞ θ ∧ HasCompactSupport θ ∧
      (∀ r ∈ Icc 0 (3*(f.chart p).maskRadius/4), θ r = 1) ∧
      tsupport θ ⊆ ball 0 (retainedRadius (f.chart p).targetRadius (f.chart p).bufferRadius) := by
    have hΔ := (Characteristic.UniformAmplitudes.retained_source_slab_bounds
      (f.chart p).maskRadius_pos (hρb p) (hsrcρ p)).2
    have hin : Icc 0 (3*(f.chart p).maskRadius/4) ⊆
        ball 0 (retainedRadius (f.chart p).targetRadius (f.chart p).bufferRadius) := by
      intro r hr
      simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg hr.1] using hr.2.trans_lt hΔ
    obtain ⟨χ, hs, _, hc, hu, hp⟩ := CompatibleResponse.exists_compact_family_cutoff
      isCompact_Icc isOpen_ball hin
    refine ⟨fun r ↦ (χ r : ℂ), Complex.ofRealCLM.contDiff.comp hs,
      hc.comp_left Complex.ofReal_zero, ?_, ?_⟩
    · intro r hr
      have he : r ∈ {r | χ r = 1} := interior_subset (hp hr)
      change χ r = 1 at he
      simp only [he, Complex.ofReal_one]
    · exact (tsupport_comp_subset Complex.ofReal_zero χ).trans hu
  choose θ hθ using hex
  exact ⟨θ, hθ⟩

/-- Normalize the actual comparable carrier into the original phase buffer.
The compact set is the image of `tsupport θ × Kglobal`, not an assumed
new analytic domain. The cutoff premise is produced by
`exists_selected_buffered_elapsed_cutoffs`; `hglobal` is the literal equality
returned by `exists_selected_elapsed_comparable_carriers` and the residual
profile assembly. This supplies `hKphase`, `hpos`, `hmap`, and `hjet` for
`exists_selected_completeFactor_phase_inputs`
(`app:ch_regular:eq:high-phase`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_selected_normalized_phase_carriers
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    (hρb : ∀ p, (f.chart p).bufferRadius ≤ (f.chart p).targetRadius)
    (hsrcρ : ∀ p, (f.chart p).maskRadius ≤ (f.chart p).bufferRadius / 4)
    (output : E → ℝ) (hout : tsupport output ⊆ ball x f.physicalRadius)
    (threshold : ℝ) (hthreshold : f.radialThreshold ≤ threshold)
    (c C a₀ b₀ : ℝ) (ha₀ : 0 < a₀)
    (Kg : f.centers → Set (JointVariables E)) (hKg : ∀ p, IsCompact (Kg p))
    (hglobal : ∀ p, Kg p = Comparable.comparableJointCarrier c C a₀ b₀
      (elapsedComparableCarrier (endpointOutputMask f p output)
        (selectedEndpointMultiplier f p threshold) univ c C a₀ b₀)
      (tsupport (endpointOutputMask f p output) ×ˢ tsupport (chartInputMask f p))
      (frequencyAnnulus a₀ b₀))
    (θ : f.centers → ℝ → ℂ) (hθ : ∀ p, HasCompactSupport (θ p))
    (hθbuffer : ∀ p, tsupport (θ p) ⊆
      ball 0 (retainedRadius (f.chart p).targetRadius (f.chart p).bufferRadius)) :
    ∃ Kphase : f.centers → Set (SymbolBudgets.TwoTimePoint d),
      (∀ p, IsCompact (Kphase p)) ∧
      (∀ p, ∀ w ∈ Kphase p, 0 < (f.chart p).radialSection w.2) ∧
      (∀ p,
        let e := coordinateSplit (f.chart p).index
        let z : RootState (Euclidean d) := ((e x).1, ((e x).2, (e p.val.val).2))
        MapsTo (normalize (f.chart p).radialSection ∘ budgetCoordinates) (Kphase p)
          (closedBall (z.1, z) (f.chart p).targetRadius)) ∧
      ∀ p (mi mo : LocalizerSymbol (d+1)) u y,
        MapsTo elapsedJointCoordinates
          (elapsedOutputJetCarrier (tsupport (θ p) ×ˢ Kg p) mi mo u y) (Kphase p) := by
  obtain ⟨lo, hi, hlo, _, hradial⟩ :=
    exists_selected_elapsed_radial_bounds f hρb hsrcρ c C a₀ b₀ ha₀
  let S := fun p ↦ tsupport (θ p) ×ˢ Kg p
  let Kphase := fun p ↦ elapsedJointCoordinates '' S p
  have hcompact p : IsCompact (Kphase p) :=
    ((hθ p).prod (hKg p)).image (elapsedJointCoordinates (d := d)).continuous
  have hrad p v (hv : v ∈ S p) := hradial threshold hthreshold output p v.2
    ((hglobal p) ▸ hv.2)
  refine ⟨Kphase, hcompact, ?_, ?_, ?_⟩
  · intro p w hw
    obtain ⟨v, hv, rfl⟩ := hw
    exact hlo.trans_le (hrad p v hv).1.1
  · intro p e z w hw
    obtain ⟨v, hv, rfl⟩ := hw
    have hvKg := hv.2
    rw [hglobal p] at hvKg
    have ho : v.2.1.1 ∈ tsupport (endpointOutputMask f p output) := hvKg.1.1.1
    have hx := (RegularSector.FiniteResidual.SelectedChart.selected_output_retained_geometry
      f p (hρb p) (hsrcρ p)).1
      (endpointOutputMask_tsupport_subset_chartOutputMask f p output hout ho)
    let ε := retainedRadius (f.chart p).targetRadius (f.chart p).bufferRadius
    have hε := retainedRadius_bounds (f.chart p).targetRadius_pos (f.chart p).bufferRadius_pos
    have hr : |v.1| < ε := by simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs] using hθbuffer p hv.1
    have ht : dist (v.2.1.1 0) z.1 < ε/2 := hx.1
    have hy : dist (spatialPart v.2.1.1) z.2.1 < ε/2 := hx.2
    have hs : dist (v.2.1.1 0-v.1) z.1 < 2*ε := by
      calc
        _ ≤ dist (v.2.1.1 0-v.1) (v.2.1.1 0) + dist (v.2.1.1 0) z.1 := dist_triangle _ _ _
        _ = |v.1| + dist (v.2.1.1 0) z.1 := by simp [Real.dist_eq]
        _ < 2*ε := by linarith
    have hang : dist (((f.chart p).radialSection (spatialPart v.2.2.1))⁻¹ • spatialPart v.2.2.1) z.2.2 ≤ (f.chart p).bufferRadius / 2 :=
      (show dist _ _ < _ from (hrad p v hv).2.2).le
    change normalize _ (budgetCoordinates (elapsedJointCoordinates v)) ∈ _
    change (v.2.1.1 0, (v.2.1.1 0-v.1, (spatialPart v.2.1.1,
      ((f.chart p).radialSection (spatialPart v.2.2.1))⁻¹ • spatialPart v.2.2.1))) ∈ _
    simp only [mem_closedBall, Prod.dist_eq, max_le_iff]
    exact ⟨by linarith [hε.2.1], hs.le.trans hε.2.1,
      by linarith [hε.2.1], hang.trans (by linarith [hρb p, (f.chart p).bufferRadius_pos])⟩
  · intro p mi mo u y v hv
    exact mem_image_of_mem _ hv.1

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
