module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.Incidence.RootGeometry.Placement
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.Incidence.RootGeometry.Inverse

/-!
# Frozen frequency geometry of the same constructed incidence roots

The local geometric inputs `hp` and `hmask` of
`exists_canonicalFrozen_weight_threshold` are proved here, for the original
angular masks and exact frozen inverse domain. The refinement `R`, quantitative
Hamilton family `T`, and actual root family `g` are retained throughout.
Finite-family coverage, the primitive thresholds for the pivot and minors,
and the final spectral gap remain with the spectral parent.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.FrozenModel
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic
open ContinuumNormalReduction TransportSymbol ConicChart

/-- Around any nonzero reference frequency in a retained refined chart, choose
a positive frequency radius and an explicit smaller positive root tolerance.
For EVERY constructed root family at that tolerance or smaller, the literal
root and `η = t • embedding.adjoint κ` solve the actual frozen frequency equation
for every `t > 0`, belong to the original conic input/output domains, and are
recovered by the SAME inverse with the ORIGINAL angular mask equal to one
(`app:ch_seed:eq:seed-actual-detection`, `app:ch_background:prop:bg-frame`).

The last clause of `exists_constructed_incidence_roots`, applied to the returned
positive tolerance (or a finite smaller positive minimum), produces the primitive
componentwise frame threshold and the SAME `g` required here.
`NullTransport.exists_actual_null_gaps` produces `hpivot` at physical zero;
`exists_frozen_conic_inputs` produces the retained carrier buffer, `hInv`, and
`htrans`. Those primitive thresholds are combined by the parent. No mask
positivity, domain membership, or frequency equation is an input. Shrinking
these local balls makes no claim that the original finite cover survives. -/
theorem exists_constructed_incidence_frozen_inverse {n : ℕ} {D : CoverData n}
    {c₀ C₀ : ℝ} (hD : D.IsValid c₀ C₀) {R : IncidenceRefinement D} (hR : R.IsValid)
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) →
      PatchQuantitativeFamily (D.patches i.1 i.2) U hU)
    (j : Fin R.chartCount) (a : Fin (D.patchCount (R.sourceChart j)))
    {κ₀ : Euclidean n} (hκ₀ : κ₀ ∈ ball (R.center j) (2 * R.radius j))
    (hκ₀ne : κ₀ ≠ 0) {r a₀ c εmax : ℝ} (hr : 0 < r) (ha : 0 < a₀)
    (hc : 0 < c) (hεmax : 0 < εmax) :
    let T₀ := T ⟨R.sourceChart j, a⟩
    let z₀ := D.roots (R.sourceChart j) a κ₀
    let ηb := T₀.data.adapted.embedding.toContinuousLinearMap.adjoint κ₀
    ∃ hηb : ηb ≠ 0, ∃ ρ ε₀ : ℝ, 0 < ρ ∧ 0 < ε₀ ∧ ε₀ ≤ εmax ∧ ε₀ / c ≤ a₀ / 8 ∧
      ∀ {s B ε : ℝ}, 0 < s → ε ≤ ε₀ →
      ∀ (Q : Euclidean n → Fin n → MetricTensor n) (hQ : ContDiffOn ℝ ∞ Q U)
        (hlow : ∀ i, cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < (T i).family.threshold)
        (g : (j : Fin R.chartCount) → Fin (D.patchCount (R.sourceChart j)) →
          Euclidean n × Euclidean n → ℝ),
      IsConstructedIncidenceRootFamily D R s c B ε Q
        (fun j a ↦ (T ⟨j, a⟩).carrier ⟨Q, hQ, hlow ⟨j, a⟩⟩) g →
      let Q₀ : {Q' : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q' U ∧
          cNorm (closedBall (0 : Euclidean n) T₀.data.localReference.stateRadius) 6
            (Q' - fun _ ↦ cubeStress n) < T₀.family.threshold} :=
        ⟨Q, hQ, hlow ⟨R.sourceChart j, a⟩⟩
      ∀ {b cJ : ℝ} {V L : Set (ℝ × Euclidean (n - 1))}
        {G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1))},
      6 * a₀ ≤ 3 * r →
      (closedBall (spectatorCenter z₀) (3 * r) ×ˢ closedBall (z₀ 0) (3 * r) ⊆
        carrierParameters ⁻¹' parameterInterior (3 * (D.patches (R.sourceChart j) a).radius / 2)) →
      BufferedPhaseInverse (adaptedTransportChart T₀ Q₀) (physicalParameterSet z₀ (6 * a₀))
        (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r)) V L b cJ G →
      (∀ p ∈ physicalParameterSet z₀ (6 * a₀),
        ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r),
          ‖(adaptedTransportChart T₀ Q₀ p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖) →
      ∀ κ ∈ ball κ₀ ρ,
        let z := incidenceParameter (D.roots (R.sourceChart j) a (R.center j)) (g j a (0, κ))
        fderiv ℝ (determinant (Q 0)) (T₀.carrierGradient Q₀ 0 z) T₀.data.adapted.normal ≠ 0 →
        ∀ t > (0 : ℝ),
          let η := t • T₀.data.adapted.embedding.toContinuousLinearMap.adjoint κ
          let p : InputVariables n := ((0, 0), (z 0, spectatorCenter z₀), η)
          let u := frozenSymbolInverse T₀ Q₀ z₀ ηb r (6 * a₀)
          transportAveragedGradient (normalizedTransportPosition T₀ Q₀ 0) p = t • κ ∧
          p ∈ frozenInputDomain z₀ ηb r (6 * a₀) ∧
          ((0, 0, t • κ), spectatorCenter z₀) ∈ frozenSymbolDomain T₀ Q₀ z₀ ηb r (6 * a₀) ∧
          u ((0, 0, t • κ), spectatorCenter z₀) = (z 0, η) ∧
          parameter ((u ((0, 0, t • κ), spectatorCenter z₀)).1, spectatorCenter z₀) = z ∧
          angularMask z₀ (NormedSpace.normalize ηb) ha (angularWidth_spec hηb hr).1
            ((u ((0, 0, t • κ), spectatorCenter z₀)).1, spectatorCenter z₀)
            (‖(u ((0, 0, t • κ), spectatorCenter z₀)).2‖⁻¹ •
              (u ((0, 0, t • κ), spectatorCenter z₀)).2) = 1 := by
  dsimp only
  obtain ⟨hηb, ρ, ε₀, hρ, he₀, hemax, hec, hplace⟩ :=
    exists_constructed_incidence_plateau_tolerance hD hR T j a hκ₀ hκ₀ne hr ha hc hεmax
  refine ⟨hηb, ρ, ε₀, hρ, he₀, hemax, hec, ?_⟩
  intro s B ε hs hε Q hQ hlow g hg b cJ V L G har hcarrier hInv htrans κ hκ hpivot t ht
  let T₀ := T ⟨R.sourceChart j, a⟩
  let Q₀ : {Q' : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q' U ∧
          cNorm (closedBall (0 : Euclidean n) T₀.data.localReference.stateRadius) 6
            (Q' - fun _ ↦ cubeStress n) < T₀.family.threshold} :=
        ⟨Q, hQ, hlow ⟨R.sourceChart j, a⟩⟩
  let z := incidenceParameter (D.roots (R.sourceChart j) a (R.center j)) (g j a (0, κ))
  obtain ⟨hκchart, hη, hθ, hzplateau, hv, _⟩ := hplace hs hε Q _ g hg κ hκ
  have hp : (0, κ) ∈ ball (0 : Euclidean n) (3 * s) ×ˢ
      ball (R.center j) (2 * R.radius j) := ⟨by simpa using (show 0 < 3 * s by positivity), hκchart⟩
  have hroot := (hg j a).2.2.1 (0, κ) hp
  have hP := (hD.2.2.2.2.1 (R.sourceChart j) a).1
  have hz : z ∈ parameterCube (3 * (D.patches (R.sourceChart j) a).radius / 2) := by
    intro i
    exact (hroot.2.1 i).le.trans (by linarith [hP.1])
  have hinc : fderiv ℝ (determinant (Q 0)) (T₀.carrierGradient Q₀ 0 z) κ = 0 :=
    hroot.2.2.2.2.1
  obtain ⟨hforward, hpin, hout, hinv, hmask⟩ := frozen_tangent_plateau_inverse T₀ Q₀ hP
    hηb hr ha har hcarrier hInv htrans hz hpivot hinc hη hzplateau hv hθ ht
  refine ⟨hforward, hpin, hout, hinv, ?_, ?_⟩
  · rw [hinv]
    change parameter (z 0, spectatorCenter (D.roots (R.sourceChart j) a κ₀)) = z
    rw [← hv, parameter_apply, carrierParameters_spectatorCenter]
  · rw [hinv]
    exact hmask
end JanetCartan.ContinuumNormal.FrozenModel
