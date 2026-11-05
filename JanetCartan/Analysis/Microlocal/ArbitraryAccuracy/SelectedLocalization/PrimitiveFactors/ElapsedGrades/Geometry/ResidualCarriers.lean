module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.ElapsedGrades.Geometry.RadialBand

/-!
# Geometry for the literal common-mask direct residual

Both original coefficients are multiplied by the chart output plateau, with
the same retained `W₀` and `W₁`. The resulting direct residual has the original
source buffer, and every nonzero normalized jet on its compact comparable
carrier admits a bounded positive dilation into the original amplitude band.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open RegularSector RegularSector.FiniteAssembly RegularSector.Characteristic
open RegularSector.FinitePdo
open Characteristic.ConicPhase Characteristic.ConicAmplitude Characteristic.UniformEvolution
open Characteristic.ResidualCoordinates Characteristic.EvolutionIntegral
open Characteristic.EvolutionIntegral.KernelIdentification Characteristic.EvolutionIntegral.SymbolBudgets
open FiniteMasks FiniteMasks.ActualFamily FiniteAlgebraic
open EvolutionLocalization EvolutionIntegratedLocalization FourierIntegral
open FiniteChain.Graph FiniteChain.Graph.PhysicalShells
open FiniteChain.Graph.PhysicalShells.Noncomparable
open FiniteChain.Graph.KernelEstimates.NoncomparableGeometry
open JanetCartan.CharacteristicTransport.CompleteResidual
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "T" => Characteristic.TwoTimePoint (Euclidean d)
local notation "Z" => RootState (Euclidean d)
local notation "V" => ℝ × JointVariables E
local notation "Mat" => MetricTensor (d+1)

/-- The compact support, source buffer, and retained-band geometry of the
SAME auxiliary direct residual constructed by
`selected_common_smooth_direct_residual`. All radial constants are chosen
before threshold, coefficients, accuracy, `L`, and `ρ`. Both orientations
use the exact carrier and the literal `selectedEndpointMultiplier` at
`2 * threshold`, with the chart source cutoff before the Fourier multiplier.

The smoothness, physical column identity, inverse source-time identity, and
two amplitude support inclusions are the retained fields of
`exists_finite_direct_operator_bounds` for its literal
`selectedBufferedAmplitude`. The only proof-mask input to the support
conclusion is the input annulus, produced by
`ProtectedMasks.exists_uniform_conic_nested_localization_data`.
No radial-band inclusion is assumed: where a jet is nonzero we construct a
dilation, preserving both original times and position, into the original
`ra, rb`. The analytic transfer along this dilation belongs to
`jc-selected-complete-elapsed-grades`.

Consumers: `hs`, `hglobalSupport`, `hb`, `hslabOut`, `hslab`, and the carrier
for `hprimitiveMasks` in
`ResidualLocalization.exists_completePhysicalResidual_restriction_bound`
(`app:ch_regular:eq:high-amplitude`, `app:ch_regular:eq:chain-tail`,
`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem exists_selected_direct_residual_carriers
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    (hρb : ∀ p, (f.chart p).bufferRadius ≤ (f.chart p).targetRadius)
    (hsrcρ : ∀ p, (f.chart p).maskRadius ≤ (f.chart p).bufferRadius / 4)
    (c C a₀ b₀ : ℝ) (ha₀ : 0 < a₀)
    (ra rb : f.centers → ℝ) (hra : ∀ p, 0 < ra p) (hab : ∀ p, ra p ≤ rb p) :
    ∃ tlo thi : ℝ, 0 < tlo ∧ 0 < thi ∧
      ∀ output : E → ℝ, ContDiff ℝ ∞ output → HasCompactSupport output →
      tsupport output ⊆ ball x f.physicalRadius →
      ∀ threshold, f.radialThreshold ≤ threshold →
      ∀ θ : ℝ → ℂ, HasCompactSupport θ →
      ∃ Kglobal : f.centers → Set (JointVariables E),
      ∃ Kelapsed : f.centers → Set V,
        (∀ p, IsCompact (Kglobal p)) ∧ (∀ p, IsCompact (Kelapsed p)) ∧
        (∀ p, ∀ v ∈ Kelapsed p, v.2.2.1 ≠ 0) ∧
        (∀ p, Kelapsed p = tsupport θ ×ˢ Kglobal p) ∧
        (∀ p, Kglobal p = Comparable.comparableJointCarrier c C a₀ b₀
          (elapsedComparableCarrier (endpointOutputMask f p output)
            (selectedEndpointMultiplier f p threshold) univ c C a₀ b₀)
          (tsupport (endpointOutputMask f p output) ×ˢ tsupport (chartInputMask f p))
          (frequencyAnnulus a₀ b₀)) ∧
        (∀ p (mi mo : LocalizerSymbol (d+1)) (Ki : Set E),
          tsupport mi ⊆ Ki ×ˢ frequencyAnnulus a₀ b₀ →
          ∀ (b : TwoTimeAmplitude d (d+1)) (backward : Bool) ρ, 1 ≤ ρ →
          ∀ low j k, IsComparablePair c C a₀ b₀ ρ low j k → ∀ u y,
            (∀ r, tsupport (FiniteChain.Graph.jointAmplitude ρ
              (orientedElapsedAmplitude backward b (endpointOutputMask f p output)
                (chartInputMask f p) (selectedEndpointMultiplier f p threshold) r)
              mi mo (graphBranchCutoff low j) (outputCutoff k) u y) ⊆ Kglobal p) ∧
            tsupport (fun v : V ↦ θ v.1 • jointElapsedAmplitude backward ρ b
              (endpointOutputMask f p output) (chartInputMask f p)
              (selectedEndpointMultiplier f p threshold) mi mo
              (graphBranchCutoff low j) (outputCutoff k) u y v) ⊆ Kelapsed p) ∧
        ∀ p (Q : E → Fin (d+1) → Mat) (B : E → Mat)
          (Φ : Z × ℝ → Z) (Cchart : OpenPartialHomeomorph T T) (angular : Euclidean d → ℝ),
        let lc := f.chart p
        let e := coordinateSplit lc.index
        let z : Z := ((e x).1, ((e x).2, (e p.val.val).2))
        let Fs := selectedBufferedAmplitude f p Q B Φ Cchart
        let W := fun j : Fin 3 ↦ collared lc.radialSection (if j=0 then 0 else 1) angular (Fs j)
        let Aoriginal := fun y i ↦ (coefficient lc.index Q y i).map Complex.ofReal
        let Boriginal := fun y ↦ (zeroth lc.index B y).map Complex.ofReal
        let Ac := fun y i ↦ chartOutputMask f p y • Aoriginal y i
        let Bc := fun y ↦ chartOutputMask f p y • Boriginal y
        let b := directRetardedAmplitudes Ac Bc
          (selectedConicAmplitude f p Q B Φ Cchart angular 0)
          (selectedConicAmplitude f p Q B Φ Cchart angular 1) true
        (∀ η ∈ tsupport angular, 0 < lc.radialSection η) →
        (∀ j, ContDiff ℝ ∞ (W j)) →
        (∀ v : T, lc.timeMask =ᶠ[𝓝 v.1] (fun _ ↦ 1) →
          ∀ j : Fin (d+1), (fun k ↦ W 2 v k j) =
            WKB.firstOrderApply (complexPencilCoefficient Q) (complexPencilZeroth B)
              (fun y k ↦ W 1 (physicalSlice e v.2.1 v.2.2.2 y) k j)
              (e.symm (v.1, v.2.2.1))) →
        (∀ v ∈ Cchart.target, (Cchart.symm v).2.1 = v.2.1) →
        tsupport (Fs 2) ⊆ closedBall (z.1, z) (lc.bufferRadius/2) →
        tsupport (W 2) ⊆ ConicPhase.domain lc.radialSection
          (Cchart.target ∩ Cchart.symm ⁻¹' (ball z.1 (lc.maskRadius/2) ×ˢ
            (ball z.1 (lc.maskRadius/2) ×ˢ ball z.2 (lc.maskRadius/2)))) →
        let a := z.1 - lc.maskRadius/2
        let upper := a + 3*lc.maskRadius/4
        b = (fun t s y η ↦ chartOutputMask f p (timeSpacePoint t y) • W 2 (t, (s, (y, η)))) ∧
        ContDiff ℝ ∞ (SymbolBudgets.jointAmplitude b) ∧
        (∀ r, elapsedAmplitude b (endpointOutputMask f p output) (chartInputMask f p)
          (selectedEndpointMultiplier f p threshold) r =
          elapsedAmplitude (directRetardedAmplitudes Aoriginal Boriginal
            (selectedConicAmplitude f p Q B Φ Cchart angular 0)
            (selectedConicAmplitude f p Q B Φ Cchart angular 1) true)
            (endpointOutputMask f p output) (chartInputMask f p)
            (selectedEndpointMultiplier f p threshold) r) ∧
        (∀ t s y η, s ≤ a → b t s y η = 0) ∧
        (∀ u, upper < u 0 → endpointOutputMask f p output u = 0) ∧
        upper - a = 3*lc.maskRadius/4 ∧
        ∀ v ∈ Kelapsed p,
          let t := ra p / lc.radialSection (spatialPart v.2.2.1)
          0 < t ∧ t ∈ Icc tlo thi ∧ lc.radialSection (t • spatialPart v.2.2.1) = ra p ∧
          ∀ ρ : ℝ, 0 < ρ → ∀ m : ℕ,
            ((elapsedJointCoordinates v).1, t • spatialPart v.2.2.1) ∈
              bufferedJetSet lc.radialSection z (lc.bufferRadius/2) (ra p) (rb p) ∨
              iteratedFDeriv ℝ m (normalizedElapsedSymbol ρ b) v = 0 := by
  obtain ⟨tlo, thi, htlo, hthi, hdilate⟩ :=
    exists_selected_elapsed_retained_radial_dilations (q := d+1) f hρb hsrcρ c C a₀ b₀ ha₀ ra rb hra hab
  refine ⟨tlo, thi, htlo, hthi, ?_⟩
  intro output ho hoc hout threshold hthreshold θ hθ
  obtain ⟨Kglobal, Kelapsed, hKg, hKe, hzero, heq, hglobal, hsupport⟩ :=
    exists_selected_elapsed_comparable_carriers (q := d+1) f output ho hoc hout
      threshold c C a₀ b₀ ha₀ θ hθ
  refine ⟨Kglobal, Kelapsed, hKg, hKe, hzero, heq, hglobal, hsupport, ?_⟩
  intro p Q B Φ Cchart angular lc e z Fs W Aoriginal Boriginal Ac Bc b
    hang hW hphysical hsourceTime hFs hWs a upper
  have haux := selected_common_smooth_direct_residual f p (hρb p) (hsrcρ p)
    output hout Q B W hW hphysical
  change b = _ ∧ ContDiff ℝ ∞ (SymbolBudgets.jointAmplitude b) ∧ _ at haux
  have hbuffer := selected_common_residual_retarded_buffer f p (hρb p) (hsrcρ p)
    output hout Cchart hsourceTime (W 2) hWs
  refine ⟨haux.1, haux.2.1, fun r ↦ haux.2.2 (selectedEndpointMultiplier f p threshold) r,
    ?_, hbuffer.2.1, hbuffer.2.2, ?_⟩
  · rw [haux.1]
    exact hbuffer.1
  · intro v hv t
    have hv' : v.2 ∈ Comparable.comparableJointCarrier c C a₀ b₀
        (elapsedComparableCarrier (endpointOutputMask f p output)
          (selectedEndpointMultiplier f p threshold) univ c C a₀ b₀)
        (tsupport (endpointOutputMask f p output) ×ˢ tsupport (chartInputMask f p))
        (frequencyAnnulus a₀ b₀) := by
      rw [heq p] at hv
      rw [← hglobal p]
      exact hv.2
    have hd := hdilate threshold hthreshold output p v hv'
    refine ⟨hd.1, hd.2.1, hd.2.2.1, ?_⟩
    intro ρ hρ m
    rw [haux.1]
    exact hd.2.2.2 angular hang (Fs 2) hFs ρ hρ m

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
