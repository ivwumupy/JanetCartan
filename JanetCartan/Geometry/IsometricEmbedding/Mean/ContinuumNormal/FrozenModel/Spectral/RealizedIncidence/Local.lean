module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.RealizedIncidence.LocalData
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.RealizedIncidence.Weights

/-!
# Construct one realized frozen incidence patch

At each original sphere-chart frequency, first choose a small positive radial
representative. Construct the outer conic data, then the actual supported
carrier and its smaller canonical inverse. Only then select the frequency
neighborhood and root tolerance for those SAME smaller masks. This is the
local producer for the finite realized sphere cover; no coverage is inferred
by shrinking a previously selected finite cover
(`new:lem:scaling`, `app:ch_background:prop:bg-frame`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.FrozenModel
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic
open ContinuumNormalReduction TransportSymbol ConicChart
open ProjectedStressFrame

/-- Construct the local unit carrier, exact inverse/mask/spectator data,
Fourier identity, and positive-root neighborhood from the primitive immersion
hypotheses. The representative has norm `1/4`, whereas the frequency neighborhood
is still centered at the original `κ₀`. All radii, thresholds and the minor are
chosen before the immersion. `UnitRealization` is proved for the SAME `d` used
in `Geometry` and `RootAt`; no independent operator family is substituted.
Consumer: the common finite realized incidence cover and final frozen spectral
assembly (`app:ch_background:prop:bg-frame`, `app:ch_seed:eq:seed-actual-detection`). -/
theorem exists_realized_frozen_incidence_patch {n : ℕ} (hn : 5 ≤ n)
    {D : CoverData n} {c₀ C₀ : ℝ} (hD : D.IsValid c₀ C₀)
    {R : IncidenceRefinement D} (hR : R.IsValid)
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) →
      PatchQuantitativeFamily (D.patches i.1 i.2) U hU)
    (j : Fin R.chartCount) (a : Fin (D.patchCount (R.sourceChart j)))
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n)
      (T ⟨R.sourceChart j, a⟩).data.localReference.stateRadius ⊆ K)
    (M : ℝ) {κmet κnormal : ℝ} (hκmet : 0 < κmet) (hκnormal : 0 < κnormal)
    {κ₀ : Euclidean n} (hκ₀ : κ₀ ∈ ball (R.center j) (2 * R.radius j))
    (hκ₀ne : κ₀ ≠ 0) {c εmax cap : ℝ} (hc : 0 < c) (hemax : 0 < εmax)
    (hcap : 0 < cap) :
    let T₀ := T ⟨R.sourceChart j, a⟩
    let z₀ := D.roots (R.sourceChart j) a κ₀
    ∃ t > (0 : ℝ), ‖t • κ₀‖ = 1 / 4 ∧
    NormedSpace.normalize (t • κ₀) = NormedSpace.normalize κ₀ ∧
    NormedSpace.normalize (T₀.data.adapted.embedding.toContinuousLinearMap.adjoint (t • κ₀)) =
      NormedSpace.normalize (T₀.data.adapted.embedding.toContinuousLinearMap.adjoint κ₀) ∧
    ∃ d : FrozenIncidencePatchData T₀ z₀
        (T₀.data.adapted.embedding.toContinuousLinearMap.adjoint (t • κ₀)),
    ∃ hcell : 4 * d.a < 1 / 2,
      6 * d.a < cap ∧ d.rootTolerance ≤ εmax ∧ d.rootTolerance / c ≤ d.a / 8 ∧
      ∀ (F : Euclidean n → Euclidean (embeddingDimension n))
        (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        cNorm K 4 F ≤ M →
        (∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ K, ∀ w ∈ normalSpace F x,
          κnormal * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        cNorm K 6 (projectedStress F - fun _ ↦ cubeStress n) < d.frameThreshold →
        ∀ hlow : ∀ i, cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
            (projectedStress F - fun _ ↦ cubeStress n) < (T i).family.threshold,
        let hQ := contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank)
        let Q₀ := ⟨projectedStress F, hQ, hlow ⟨R.sourceChart j, a⟩⟩
        d.Geometry Q₀ ∧ d.UnitRealization Q₀ F hcell ∧
        ∀ {s B ε : ℝ}, 0 < s → ε ≤ d.rootTolerance →
        ∀ g : (j : Fin R.chartCount) → Fin (D.patchCount (R.sourceChart j)) →
            Euclidean n × Euclidean n → ℝ,
          IsConstructedIncidenceRootFamily D R s c B ε (projectedStress F)
            (fun j a ↦ (T ⟨j, a⟩).carrier ⟨projectedStress F, hQ, hlow ⟨j, a⟩⟩) g →
          ∀ k ∈ ball κ₀ d.frequencyRadius, ∀ t > (0 : ℝ),
            frozenHighFrequencyRadius T₀ d.G ≤ ‖t • k‖ →
            d.RootAt Q₀ F (t • k)
              (incidenceParameter (D.roots (R.sourceChart j) a (R.center j)) (g j a (0, k))) := by
  dsimp only
  have hP := (hD.2.2.2.2.1 (R.sourceChart j) a).1
  have hdom := hR.2.1 j (ball_subset_closedBall hκ₀)
  have hsection := (hD.2.2.2.2.1 (R.sourceChart j) a).2
  have hz := hsection.2.1 κ₀ hdom
  have hd : fderiv ℝ (fun z ↦ incidence κ₀ ((D.patches (R.sourceChart j) a).toFun z))
      (D.roots (R.sourceChart j) a κ₀) (EuclideanSpace.single 0 1) ≠ 0 :=
    abs_pos.mp (hD.1.trans_le (hsection.2.2 κ₀ hdom _ (fun i ↦ (hz.1 i).le)))
  let T₀ := T ⟨R.sourceChart j, a⟩
  let z₀ := D.roots (R.sourceChart j) a κ₀
  obtain ⟨t, ht, htnorm, htk, htinc, htd, htdir, hdir⟩ :=
    exists_small_incidence_representative T₀ hκ₀ne hz.2.2.2 hd
  let ηb := T₀.data.adapted.embedding.toContinuousLinearMap.adjoint (t • κ₀)
  have hηb : ηb ≠ 0 := FrozenIncidence.tangential_direction_ne_zero T₀ hP hz.1 htk htinc
  obtain ⟨r, hr, a₀, ha, hacap, har, haR, hphys, hcarrier, δg, hδg,
    cJ, hcJ, b, hb, V, L, hV, hVc, hLc, hLV, hgeom⟩ :=
    exists_frozen_conic_inputs T₀ hP hz.1 htk htinc htd
      (N := embeddingDimension n) hK hKU hball M hκmet hκnormal hcap
  obtain ⟨r', a', hr', ha', hcell, hrr, haa, har', cJ', hcJ', b', hb',
    V', L', hV', hVc', hLc', hLV', δr, hδr, hrealize⟩ :=
    exists_canonicalFrozen_supported_carrier_unit (N := embeddingDimension n) T₀ hP hz.1 htk
      (by rw [htnorm]; norm_num) htinc htd hr ha (by linarith) hcarrier
  obtain ⟨row, col, ρ, ε₀, δw, hρ, hε₀, hεmax, hεc, hδw, hweights⟩ :=
    exists_constructed_incidence_positive_weights_of_direction hn hD hR T j a hK hKU hball M
      hκ₀ hκ₀ne hηb hdir hr' ha' hc hemax
  have hcarrier' : closedBall (spectatorCenter z₀) (3 * r') ×ˢ closedBall (z₀ 0) (3 * r') ⊆
      carrierParameters ⁻¹' parameterInterior (3 * (D.patches (R.sourceChart j) a).radius / 2) :=
    (prod_mono (closedBall_subset_closedBall (by linarith : 3 * r' ≤ 3 * r))
      (closedBall_subset_closedBall (by linarith : 3 * r' ≤ 3 * r))).trans hcarrier
  let d : FrozenIncidencePatchData T₀ z₀ ηb := {
    r := r', a := a', frequencyRadius := ρ, rootTolerance := ε₀,
    frameThreshold := min δg (min δr δw), inverseRadius := b', cJ := cJ', V := V', L := L',
    G := FrozenIncidence.referenceEquiv T₀ hP hz.1 htinc htd,
    row := row, col := col, hr := hr', ha := ha', hηb := hηb,
    frequencyRadius_pos := hρ, rootTolerance_pos := hε₀,
    frameThreshold_pos := lt_min hδg (lt_min hδr hδw), inverseRadius_pos := hb', hcJ := hcJ',
    hV := hV', hVc := hVc', hLc := hLc', hLV := hLV', har := har',
    haR := lt_of_le_of_lt (by linarith : 6 * a' ≤ 6 * a₀) haR,
    hphys := lt_of_le_of_lt (by linarith : 3 * r' ≤ 3 * r) hphys, hcarrier := hcarrier' }
  refine ⟨t, ht, htnorm, htdir, hdir, d, hcell,
    lt_of_le_of_lt (by linarith : 6 * a' ≤ 6 * a₀) hacap, hεmax, hεc, ?_⟩
  intro F hF hi hrank hM hmet hnormal hclose hlow
  have hQ := contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank)
  let Q₀ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T₀.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T₀.family.threshold} :=
    ⟨projectedStress F, hQ, hlow ⟨R.sourceChart j, a⟩⟩
  have hreg : ∀ x ∈ K, ContDiffAt ℝ 6 (projectedStress F - fun _ ↦ cubeStress n) x :=
    fun x hx ↦ ((hQ.contDiffAt (hU.mem_nhds (hKU hx))).sub contDiffAt_const).of_le (by simp)
  have hmono := cNorm_mono_set_of_contDiffAt hball hK hreg
  have hlocal := hmono.trans_lt (hclose.trans_le (min_le_left δg (min δr δw)))
  obtain ⟨hf, hgap, hInv, htrans, _⟩ :=
    hgeom F hF hi hrank hM hmet hnormal (hlow ⟨R.sourceChart j, a⟩) hlocal
  obtain ⟨hf', hgap', hInv', htrans', hoperator⟩ :=
    hrealize Q₀ (hmono.trans_lt (hclose.trans_le
      ((min_le_right δg (min δr δw)).trans (min_le_left δr δw))))
      hf hInv htrans hgap hV hLV hcJ
  have hdgeom : d.Geometry Q₀ := ⟨hf', hgap', hInv', htrans'⟩
  refine ⟨hdgeom, ?_, ?_⟩
  · intro Φ Y s hs
    obtain ⟨hn', hsupp, B, hB, hb, hA, Vcarrier, htest, hsupport, hunique, hadjoint, hnormal⟩ :=
      hoperator F row col Φ Y s hs
    refine ⟨hn', hsupp, B, hB, hb, hA, Vcarrier, htest, hsupport, hunique, hadjoint, hnormal, ?_⟩
    intro W hW w
    exact canonicalFrozenCarrierExtension_adjoint_norm_sq_eq_energy_unit T₀ Q₀ d hP hdgeom
      F Φ Y ha' hcell hn' (4 * a') hsupp hb B
      (fun i j ξ is his ↦ hA i j ξ is (his.trans hs)) Vcarrier hnormal htest W hW w
  · intro s B ε hs hε g hg k hk t ht hhigh
    have hw := hweights hs hε F hF hi hrank hM
      (hclose.trans_le ((min_le_right δg (min δr δw)).trans (min_le_right δr δw))) hlow g hg
      (by linarith : 6 * a' ≤ 3 * r') hcarrier' hf' hInv' htrans' hgap' hcJ' k hk t ht hhigh
    have hunit := hw (fun _ ↦ 0) (fun _ ↦ 0) (fun _ ↦ 1) (by norm_num)
    refine ⟨hunit.2.2.1, hunit.2.2.2.2.1, ?_⟩
    intro Φ Y initial hi₀
    exact (hw Φ Y initial hi₀).2.2.2.2.2.2.2

end JanetCartan.ContinuumNormal.FrozenModel
