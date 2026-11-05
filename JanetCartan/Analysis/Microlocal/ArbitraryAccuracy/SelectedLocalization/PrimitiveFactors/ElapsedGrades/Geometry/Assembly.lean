module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.ElapsedGrades.Geometry.Noncomparable
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.ElapsedGrades.Geometry.RadialBand

/-!
# Noncomparable geometry on the actual selected carriers

The retained original phase estimates yield one pair of covector constants
for the finite family. The open domains and compact carriers are constructed
from the actual endpoint output and doubled multiplier before the auxiliary
phase is supplied. In particular, no carrier inclusion or covector comparison
is left as an input to the supported-phase implication.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open RegularSector RegularSector.Characteristic RegularSector.Characteristic.ConicPhase
open RegularSector.FinitePdo
open Characteristic.UniformEvolution Characteristic.EvolutionIntegral
open Characteristic.EvolutionIntegral.SymbolBudgets Characteristic.ResidualCoordinates
open FiniteMasks FiniteMasks.ActualFamily FiniteAlgebraic
open EvolutionLocalization FourierIntegral FiniteChain.Graph FiniteChain.Graph.PhysicalShells
variable {d q : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "T" => Characteristic.TwoTimePoint (Euclidean d)
local notation "Z" => RootState (Euclidean d)

/-- Assemble `hauxAmplitudeCarrier`, `hVphase`, `hKphase`, `hKV`, `hcarrier`,
`hSphase`, `hg`, and `hcomp` for
`ResidualLocalization.exists_completePhysicalResidual_restriction_bound`.
The constants are uniform over the fixed family and precede all scales and
coefficients. The geometric premises of the covector comparison are discharged
by the actual physical carriers, including the strict spatial collar.

The original analytic chart fields are retained outputs of
`exists_finite_direct_operator_bounds`. The only auxiliary phase premise is
germ agreement on the constructed `Ua`, to be instantiated by
`jc-selected-complete-elapsed-grades` with
`jc-selected-elapsed-quantitative-phase`. This implication does not assert
the existence of that auxiliary or any amplitude grade
(`app:ch_regular:eq:high-phase`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_selected_elapsed_noncomparable_geometry
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    (hρb : ∀ p, (f.chart p).bufferRadius ≤ (f.chart p).targetRadius)
    (hsrcρ : ∀ p, (f.chart p).maskRadius ≤ (f.chart p).bufferRadius / 4)
    (A : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j) :
    ∃ c₀ C₀ : ℝ, 0 < c₀ ∧ 0 < C₀ ∧
      ∀ output : E → ℝ, ContDiff ℝ ∞ output → HasCompactSupport output →
      tsupport output ⊆ ball x f.physicalRadius → ∀ p : f.centers,
      let c := f.chart p
      let e := coordinateSplit c.index
      let z : Z := ((e x).1, ((e x).2, (e p.val.val).2))
      let ε := retainedRadius c.targetRadius c.bufferRadius
      let Δ := 3*c.maskRadius/4
      ∃ Vphase : Set (E × E), ∃ Ua : Set (SymbolBudgets.TwoTimePoint d),
        IsOpen Vphase ∧ IsOpen Ua ∧
        Vphase ⊆ elapsedPhysicalBox z ε ×ˢ
          (spatialPart ⁻¹' angularCone c.radialSection z.2.2 ε) ∧
        Ua ⊆ bufferedBase z ε ×ˢ angularCone c.radialSection z.2.2 ε ∧
        (∀ w ∈ Ua, (1/2 : ℝ) < ‖w.2‖) ∧
        (∀ r ∈ Icc 0 Δ, ∀ w ∈ Vphase, elapsedPhasePoint r w ∈ Ua) ∧
        (∀ threshold, f.radialThreshold ≤ threshold →
          ∃ Kphase : Bool → ℕ → Set (E × E),
            (∀ low j, IsCompact (Kphase low j)) ∧
            (∀ low j, Kphase low j ⊆ Vphase) ∧
            (∀ ρ r, r ∈ Icc 0 Δ → ∀ low j,
              ∀ ξ ∈ normalizedGraphCarrier ρ low j,
              ∀ w ∈ tsupport (endpointOutputMask f p output) ×ˢ tsupport (chartInputMask f p),
              selectedEndpointMultiplier f p threshold (ρ • ξ) ≠ 0 →
                SymbolBudgets.elapsedPoint r (w, ρ • ξ) ∈ Ua) ∧
            ∀ (b : TwoTimeAmplitude d q) ρ, ρ ≠ 0 → ∀ r ∈ Icc 0 Δ,
              ∀ low j, ∀ ξ ∈ normalizedGraphCarrier ρ low j,
              ∀ w ∈ tsupport (fun w : E × E ↦ elapsedAmplitude b
                (endpointOutputMask f p output) (chartInputMask f p)
                (selectedEndpointMultiplier f p threshold) r w.1 w.2 (ρ • ξ)),
                (w.1, ρ • ξ) ∈ Kphase low j ∧
                  SymbolBudgets.elapsedPoint r (w, ρ • ξ) ∈ Ua) ∧
        ∀ Rstar : ℕ, 10 ≤ Rstar → ∀ L : ℝ, 1 ≤ L →
        ∀ Q : E → Fin (d+1) → MetricTensor (d+1),
        (∀ j, cNorm (closedBall x RQ) j Q ≤ A j * L ^ (j-Rstar)) →
        ∀ (h : Z → ℝ) (Φ : Z × ℝ → Z) (C : OpenPartialHomeomorph T T),
        closedBall (z.1, z) c.targetRadius ⊆ C.target →
        ContDiffOn ℝ ∞ (twoTimePhase C) C.target →
        (∀ v ∈ C.target, HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C v) v) →
        (∀ v ∈ closedBall (z.1, z) c.targetRadius, ‖twoTimePhaseMixed C v - 1‖ ≤ 1/2) →
        (∀ m, cNorm (closedBall (z.1, z) c.targetRadius) m (twoTimePhase C) ≤
          c.phaseCost m * (1+cNorm (closedBall x RQ) (m+1) Q)) →
        ∀ Ψ : TwoTimePhase d,
        (∀ w ∈ Ua, jointPhase Ψ =ᶠ[𝓝 w] jointPhase (curriedPhase c.radialSection C)) →
        ∃ g : ℝ → E → E → E,
          (∀ r ∈ Icc 0 Δ, ContDiffOn ℝ ∞ (Function.uncurry (elapsedPhase Ψ r)) Vphase) ∧
          (∀ r ∈ Icc 0 Δ, ∀ u ξ, (u, ξ) ∈ Vphase →
            fderiv ℝ (fun v ↦ elapsedPhase Ψ r v ξ) u = innerSL ℝ (g r u ξ)) ∧
          (∀ r ∈ Icc 0 Δ, ∀ u ξ, (u, ξ) ∈ Vphase →
            c₀*‖ξ‖ ≤ ‖g r u ξ‖ ∧ ‖g r u ξ‖ ≤ C₀*‖ξ‖) := by
  obtain ⟨c₀, C₀, hc₀, hC₀, hcomp⟩ := exists_selected_elapsed_covector_comparison f A hA
  refine ⟨c₀, C₀, hc₀, hC₀, ?_⟩
  intro output ho hoc hout p c e z ε Δ
  obtain ⟨Vphase, Ua, hVopen, hUaopen, hV, hUa, hcollar, hmap, hcar⟩ :=
    exists_selected_elapsed_physical_carriers (q := q) f p (hρb p) (hsrcρ p) output ho hoc hout
  refine ⟨Vphase, Ua, hVopen, hUaopen, hV, hUa, hcollar, hmap, ?_, ?_⟩
  · intro threshold hthreshold
    obtain ⟨Kphase, hK, hKV, hphysical, hcarrier⟩ := hcar threshold hthreshold
    refine ⟨Kphase, hK, hKV, ?_, hcarrier⟩
    intro ρ r hr low j ξ _hξ w hw hβ
    exact hphysical r hr (ρ • ξ) (subset_tsupport _ hβ) w hw
  · intro Rstar hRstar L hL Q hQ h Φ C hbuffer hs hdiff hnear hphase Ψ heq
    exact hcomp Rstar hRstar L hL Q hQ p (hρb p) (hsrcρ p)
      h Φ C hbuffer hs hdiff hnear hphase Ψ Vphase Ua hV hUa hmap heq

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
