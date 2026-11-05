module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.ElapsedGrades.PhysicalResidual
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionLocalization.SupportedCarriers.Carriers
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.CompactSupport

/-!
# Selected compact elapsed carriers and source-time buffer

These are the `hs`, `hglobalSupport`, `hb`, and `hslabOut` inputs to
`ResidualLocalization.exists_completePhysicalResidual_restriction_bound`.
Both orientations have the same physical positions, and the multiplier is
literally `selectedEndpointMultiplier f p threshold` at `2 * threshold`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open RegularSector RegularSector.FiniteResidual.SelectedChart RegularSector.FinitePdo
open Characteristic Characteristic.ConicPhase Characteristic.UniformEvolution
open Characteristic.ResidualCoordinates Characteristic.EvolutionIntegral
open Characteristic.EvolutionIntegral.KernelIdentification
open FiniteMasks FiniteMasks.ActualFamily FiniteAlgebraic
open EvolutionLocalization EvolutionIntegratedLocalization
open FourierIntegral FiniteChain.Graph FiniteChain.Graph.PhysicalShells
open FiniteChain.Graph.PhysicalShells.Noncomparable
open FiniteChain.Graph.KernelEstimates.NoncomparableGeometry
variable {d q : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "T" => Characteristic.TwoTimePoint (Euclidean d)
local notation "V" => ℝ × JointVariables E

/-- The literal auxiliary furnished by `selected_common_smooth_direct_residual`
inherits the original lower source-time buffer of `W₂`. The SAME endpoint
output vanishes above the original upper slab, whose length is unchanged.
The inverse source-time identity and amplitude support are retained outputs
of `exists_finite_direct_operator_bounds`
(`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem selected_common_residual_retarded_buffer
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (hρb : (f.chart p).bufferRadius ≤ (f.chart p).targetRadius)
    (hsrcρ : (f.chart p).maskRadius ≤ (f.chart p).bufferRadius / 4)
    (output : E → ℝ) (hout : tsupport output ⊆ ball x f.physicalRadius)
    (C : OpenPartialHomeomorph T T)
    (hsourceTime : ∀ v ∈ C.target, (C.symm v).2.1 = v.2.1)
    (W₂ : T → Matrix (Fin q) (Fin q) ℂ)
    (hsupport :
      let c := f.chart p
      let e := coordinateSplit c.index
      let z : RootState (Euclidean d) := ((e x).1, ((e x).2, (e p.val.val).2))
      tsupport W₂ ⊆ ConicPhase.domain c.radialSection
        (C.target ∩ C.symm ⁻¹' (ball z.1 (c.maskRadius / 2) ×ˢ
          (ball z.1 (c.maskRadius / 2) ×ˢ ball z.2 (c.maskRadius / 2))))) :
    let c := f.chart p
    let a := (coordinateSplit c.index x).1 - c.maskRadius / 2
    let upper := a + 3 * c.maskRadius / 4
    let b := fun t s y η ↦ chartOutputMask f p (timeSpacePoint t y) • W₂ (t, (s, (y, η)))
    (∀ t s y η, s ≤ a → b t s y η = 0) ∧
      (∀ u, upper < u 0 → endpointOutputMask f p output u = 0) ∧
      upper - a = 3 * c.maskRadius / 4 := by
  intro c a upper b
  refine ⟨?_, ?_, by dsimp [upper]; ring⟩
  · intro t s y η hs
    have hz := retained_amplitude_zero_before_source_half c.radialSection
      ((coordinateSplit c.index x).1,
        ((coordinateSplit c.index x).2, (coordinateSplit c.index p.val.val).2))
      c.maskRadius C hsourceTime W₂ hsupport (p := (t, (s, (y, η)))) hs
    simp only [b, hz, smul_zero]
  · intro u hu
    apply image_eq_zero_of_notMem_tsupport
    intro hm
    have hh := (selected_output_retained_geometry f p hρb hsrcρ).2.1 u
      (endpointOutputMask_tsupport_subset_chartOutputMask f p output hout hm)
    exact (not_lt_of_ge hh.2) hu

/-- One compact joint carrier contains every comparable shell in both
orientations, uniformly in `ρ`, elapsed time, the amplitude and the external
positions. Its source covector is bounded away from zero. The only proof-mask
input is the full closed input annulus supplied by
`ProtectedMasks.exists_uniform_conic_nested_localization_data`.
This supplies `hglobalSupport`, `hs`, and the compact nonzero carrier for
`exists_selected_elapsed_mask_profiles` (`app:ch_regular:eq:chain-tail`). -/
theorem exists_selected_elapsed_comparable_carriers
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output)
    (hoc : HasCompactSupport output) (hout : tsupport output ⊆ ball x f.physicalRadius)
    (threshold c C a b₀ : ℝ) (ha : 0 < a)
    (θ : ℝ → ℂ) (hθ : HasCompactSupport θ) :
    ∃ Kglobal : f.centers → Set (JointVariables E),
      ∃ Kelapsed : f.centers → Set V,
        (∀ p, IsCompact (Kglobal p)) ∧ (∀ p, IsCompact (Kelapsed p)) ∧
        (∀ p, ∀ v ∈ Kelapsed p, v.2.2.1 ≠ 0) ∧
        (∀ p, Kelapsed p = tsupport θ ×ˢ Kglobal p) ∧
        (∀ p, Kglobal p = Comparable.comparableJointCarrier c C a b₀
          (elapsedComparableCarrier (endpointOutputMask f p output)
            (selectedEndpointMultiplier f p threshold) univ c C a b₀)
          (tsupport (endpointOutputMask f p output) ×ˢ tsupport (chartInputMask f p))
          (frequencyAnnulus a b₀)) ∧
        ∀ p (mi mo : LocalizerSymbol (d+1)) (Ki : Set E),
          tsupport mi ⊆ Ki ×ˢ frequencyAnnulus a b₀ →
          ∀ (b : TwoTimeAmplitude d q) (backward : Bool) ρ, 1 ≤ ρ →
          ∀ low j k, IsComparablePair c C a b₀ ρ low j k →
          ∀ u y,
            (∀ r, tsupport (FiniteChain.Graph.jointAmplitude ρ
              (orientedElapsedAmplitude backward b (endpointOutputMask f p output)
                (chartInputMask f p) (selectedEndpointMultiplier f p threshold) r)
              mi mo (graphBranchCutoff low j) (outputCutoff k) u y) ⊆ Kglobal p) ∧
            tsupport (fun v : V ↦ θ v.1 • jointElapsedAmplitude backward ρ b
              (endpointOutputMask f p output) (chartInputMask f p)
              (selectedEndpointMultiplier f p threshold) mi mo
              (graphBranchCutoff low j) (outputCutoff k) u y v) ⊆ Kelapsed p := by
  let χout := fun p ↦ endpointOutputMask f p output
  let β := fun p ↦ selectedEndpointMultiplier f p threshold
  let Z := fun p ↦ elapsedComparableCarrier (χout p) (β p) univ c C a b₀
  let Kg := fun p ↦ Comparable.comparableJointCarrier c C a b₀ (Z p)
    (tsupport (χout p) ×ˢ tsupport (chartInputMask f p)) (frequencyAnnulus a b₀)
  have hco p : HasCompactSupport (χout p) := (endpointOutputMask_properties f p ho hoc hout).2.1
  have hcs p : HasCompactSupport (chartInputMask f p) := (chartPhysicalMasks_properties f p).2.2.2.1
  have hZ p : IsCompact (Z p) := isCompact_elapsedComparableCarrier (hco p) (β p) univ c C a b₀
  have hKg p : IsCompact (Kg p) := Comparable.isCompact_comparableJointCarrier c C a b₀
    (hZ p) ((hco p).prod (hcs p)) (isCompact_frequencyAnnulus a b₀)
  refine ⟨Kg, fun p ↦ tsupport θ ×ˢ Kg p, hKg, fun p ↦ hθ.prod (hKg p), ?_,
    fun _ ↦ rfl, fun _ ↦ rfl, ?_⟩
  · intro p v hv hz
    have hn := hv.2.1.2.1.1
    change a / (16 * annulusFactor c C) ≤ ‖v.2.2.1‖ at hn
    rw [hz, norm_zero] at hn
    have hf := two_le_annulusFactor c C
    have : 0 < a / (16 * annulusFactor c C) := div_pos ha (by linarith)
    linarith
  · intro p mi mo Ki hi b backward ρ hρ low j k hpair u y
    have hzero (r : ℝ) (u z ξ : E)
        (hz : elapsedAmplitude b (χout p) (chartInputMask f p) (β p) r u z ξ = 0) :
        orientedElapsedAmplitude backward b (χout p) (chartInputMask f p) (β p) r u z ξ = 0 := by
      cases backward <;> simp [orientedElapsedAmplitude, hz]
    have hs r : tsupport (FiniteChain.Graph.jointAmplitude ρ
        (orientedElapsedAmplitude backward b (χout p) (chartInputMask f p) (β p) r)
        mi mo (graphBranchCutoff low j) (outputCutoff k) u y) ⊆ Kg p := by
      apply Comparable.tsupport_jointAmplitude_subset_comparableJointCarrier hρ hpair
        _ mi mo u y (hZ p) ((hco p).prod (hcs p)) (isCompact_frequencyAnnulus a b₀)
      · intro u z ξ huz
        exact hzero r u z ξ (elapsedAmplitude_eq_zero_off_physical_carrier b
          (χout p) (chartInputMask f p) (β p) r u z ξ huz)
      · apply closure_minimal _ (isCompact_frequencyAnnulus a b₀).isClosed
        intro η hη
        exact (hi (subset_tsupport mi hη)).2
      · intro u z ξ hA hg
        exact elapsedAmplitude_mem_comparableCarrier b (χout p) (chartInputMask f p) (β p)
          isClosed_univ (fun _ _ _ _ hh ↦ False.elim (hh (mem_univ _))) hρ hpair r u z ξ
          (fun hz ↦ hA (hzero r u z (ρ • ξ) hz)) hg
    refine ⟨hs, ?_⟩
    apply closure_minimal _ (hθ.prod (hKg p)).isClosed
    intro v hv
    refine ⟨subset_tsupport θ ?_, ?_⟩
    · intro hz
      exact hv (by simp only [hz, zero_smul])
    · apply hs v.1
      apply subset_tsupport
      intro hz
      exact hv ((congrArg (fun A ↦ θ v.1 • A) hz).trans (smul_zero _))

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
