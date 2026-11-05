module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AlgebraicChart.ProtectionCertificates

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformAmplitudes.ProtectionCertificates.Geometry
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteMasks.ActualFamily.LocalCharts

/-!
# Retained protection certificates for the finite direct construction

The same local root, masks and evolution are retained through this deduction.
Consumer: `exists_finite_direct_operator_bounds_with_protection_certificates`,
then `SelectedSectorProtection.exists_selectedSector_nested_proof_masks`.
Sources: `app:ch_regular:thm:no-return`, `app:ch_regular:lem:finite-chain`
and `app:ch_regular:eq:chain-tail` in `paper.tex`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.UniformAmplitudes
open ActualCarriers AmplitudeBounds RootFamily ConicAmplitude ResidualCoordinates
open EvolutionIntegral EvolutionIntegral.KernelIdentification
open JanetCartan.CharacteristicTransport.CompleteResidual
open EvolutionIntegral.SymbolBudgets hiding TwoTimePoint
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Z" => RootState (Euclidean d)
local notation "T" => Characteristic.TwoTimePoint (Euclidean d)
local notation "Mat" => MetricTensor (d + 1)

/-- The flow and global normalized-root evidence on the SAME witnesses used
by the finite amplitudes. The local certificate producer proves all fields;
this names its retained conclusion for `app:ch_regular:thm:no-return` and
`app:ch_regular:lem:finite-chain`. -/
def SelectedProtectionData {Ω : Set E} {x ξ : E} {RQ M : ℝ}
    {A₀ : Fin (d+1) → Mat} (lc : FiniteMasks.ActualFamily.LocalChart Ω x RQ A₀ ξ M)
    (evolutionTime speedGap rootSize : ℝ) (rootCost : ℕ → ℝ)
    (Q : E → Fin (d+1) → Mat) (Φ : Z × ℝ → Z) (C : OpenPartialHomeomorph T T) : Prop :=
  let e := coordinateSplit lc.index
  let z : Z := ((e x).1, ((e x).2, (e ξ).2))
  let h := fieldRoot e Q lc.root
  let U := fieldDomain e Ω lc.radialSection z.2.2 lc.coefficientRadius
  let ℓ := lc.radialSection
  RootProtectionBounds Q e h U ℓ speedGap rootSize ∧
  ODE.IsSmoothFlowOn (rootHamiltonField h) z lc.rootRadius (lc.rootRadius / 2) evolutionTime Φ ∧
  C.source ⊆ twoTimeDomain z (lc.rootRadius / 2) evolutionTime ∧
  ContDiffOn ℝ ∞ (twoTimeState Φ) (twoTimeDomain z (lc.rootRadius / 2) evolutionTime) ∧
  ContDiffOn ℝ ∞ (twoTimeProjection Φ) (twoTimeDomain z (lc.rootRadius / 2) evolutionTime) ∧
  ContDiffOn ℝ ∞ C C.source ∧
  (∀ q ∈ twoTimeDomain z (lc.rootRadius / 2) evolutionTime,
    HasDerivAt (fun t ↦ twoTimeState Φ (t, q.2))
      (rootHamiltonField h (twoTimeState Φ q)) q.1) ∧
  (∀ q ∈ twoTimeDomain z (lc.rootRadius / 2) evolutionTime, ∀ u ∈ uIcc q.2.1 q.1,
    (u, q.2) ∈ twoTimeDomain z (lc.rootRadius / 2) evolutionTime ∧
      twoTimeState Φ (u, q.2) ∈ closedBall z lc.rootRadius ∧
      (twoTimeState Φ (u, q.2)).1 = u) ∧
  (∀ q ∈ C.target, ∀ u ∈ uIcc q.2.1 q.1,
    (u, (C.symm q).2) ∈ twoTimeDomain z (lc.rootRadius / 2) evolutionTime ∧
      HasDerivAt (fun t ↦ twoTimeState Φ (t, (C.symm q).2))
        (rootHamiltonField h (twoTimeState Φ (u, (C.symm q).2))) u ∧
      twoTimeState Φ (u, (C.symm q).2) ∈ closedBall z lc.rootRadius ∧
      (twoTimeState Φ (u, (C.symm q).2)).1 = u) ∧
  (∀ m, cNorm (closedBall z lc.rootRadius) m h ≤
    rootCost m * (1 + cNorm (closedBall x RQ) m Q)) ∧
  (∀ (R₀ : ℕ) (M₀ : ℝ), cNorm (closedBall x RQ) R₀ Q ≤ M₀ →
    ∀ j ≤ R₀, cNorm (closedBall z lc.rootRadius) j h ≤ rootCost R₀ * (1 + M₀)) ∧
  (∀ (cost : ℕ → ℝ) (R₀ : ℕ) (scale : ℝ), 1 ≤ scale →
    (∀ m, cNorm (closedBall x RQ) m Q ≤ cost m * scale ^ (m - R₀)) →
    ∀ m, cNorm (closedBall z lc.rootRadius) m h ≤
      (rootCost m * (1 + cost m)) * scale ^ (m - R₀)) ∧
  (∀ m, cNorm (closedBall z (lc.rootRadius / 4) ×ˢ
      Icc (-evolutionTime / 4) (evolutionTime / 4)) m Φ +
    (cNorm (closedBall (z.1, z) lc.sourceRadius) m (twoTimeState Φ) +
      cNorm (closedBall (z.1, z) lc.sourceRadius) m (twoTimeProjection Φ)) +
    (cNorm (closedBall (z.1, z) lc.targetRadius) m C.symm +
      cNorm (closedBall (z.1, z) lc.targetRadius) m (twoTimePhase C)) ≤
        lc.phaseCost m * (1 + cNorm (closedBall x RQ) (m + 1) Q)) ∧
  (∀ w ∈ ball z lc.sourceRadius, Φ (w, 0) = w)

end JanetCartan.RegularSector.Characteristic.UniformAmplitudes
