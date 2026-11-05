module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.FiniteIncidence.LocalData

/-!
# Construct one frozen incidence patch before the immersion

This combines `exists_frozen_conic_inputs` with
`exists_constructed_incidence_positive_weights`. Its consumer takes a common
neighborhood for all patches before extracting a finite sphere subcover
(`app:ch_background:prop:bg-frame`, `app:ch_seed:eq:seed-actual-detection`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.FrozenModel
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic
open ContinuumNormalReduction TransportSymbol ConicChart
open ProjectedStressFrame

/-- Construct the fixed conic geometry, minor, root tolerance and neighborhood
of one original patch. Every analytic conclusion is proved for the SAME
Hamilton family and any constructed root family at the selected tolerance or
smaller. No current inverse or detection premise is introduced
(`app:ch_background:prop:bg-frame`, `app:ch_seed:eq:seed-actual-detection`). -/
theorem exists_frozen_incidence_patch {n : ℕ} (hn : 5 ≤ n)
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
    let ηb := T₀.data.adapted.embedding.toContinuousLinearMap.adjoint κ₀
    ∃ d : FrozenIncidencePatchData T₀ z₀ ηb,
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
        d.Geometry Q₀ ∧
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
  obtain ⟨r, hr, a₀, ha, hacap, har, haR, hphys, hcarrier, δg, hδg,
    cJ, hcJ, b, hb, V, L, hV, hVc, hLc, hLV, hgeom⟩ :=
    exists_frozen_conic_inputs (T ⟨R.sourceChart j, a⟩) hP hz.1 hκ₀ne hz.2.2.2 hd
      (N := embeddingDimension n) hK hKU hball M hκmet hκnormal hcap
  obtain ⟨hηb, row, col, ρ, ε₀, δw, hρ, hε₀, hεmax, hεc, hδw, hweights⟩ :=
    exists_constructed_incidence_positive_weights hn hD hR T j a hK hKU hball M
      hκ₀ hκ₀ne hr ha hc hemax
  let d : FrozenIncidencePatchData (T ⟨R.sourceChart j, a⟩)
      (D.roots (R.sourceChart j) a κ₀)
      ((T ⟨R.sourceChart j, a⟩).data.adapted.embedding.toContinuousLinearMap.adjoint κ₀) := {
    r := r, a := a₀, frequencyRadius := ρ, rootTolerance := ε₀,
    frameThreshold := min δg δw, inverseRadius := b, cJ := cJ, V := V, L := L,
    G := FrozenIncidence.referenceEquiv (T ⟨R.sourceChart j, a⟩) hP hz.1 hz.2.2.2 hd,
    row := row, col := col, hr := hr, ha := ha, hηb := hηb,
    frequencyRadius_pos := hρ, rootTolerance_pos := hε₀,
    frameThreshold_pos := lt_min hδg hδw, inverseRadius_pos := hb, hcJ := hcJ,
    hV := hV, hVc := hVc, hLc := hLc, hLV := hLV, har := har, haR := haR,
    hphys := hphys, hcarrier := hcarrier }
  refine ⟨d, hacap, hεmax, hεc, ?_⟩
  intro F hF hi hrank hM hmet hnormal hclose hlow
  have hQ := contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank)
  have hreg : ∀ x ∈ K, ContDiffAt ℝ 6 (projectedStress F - fun _ ↦ cubeStress n) x :=
    fun x hx ↦ ((hQ.contDiffAt (hU.mem_nhds (hKU hx))).sub contDiffAt_const).of_le (by simp)
  have hlocal := (cNorm_mono_set_of_contDiffAt hball hK hreg).trans_lt
    (hclose.trans_le (min_le_left δg δw))
  obtain ⟨hf, hgap, hInv, htrans, _⟩ :=
    hgeom F hF hi hrank hM hmet hnormal (hlow ⟨R.sourceChart j, a⟩) hlocal
  refine ⟨⟨hf, hgap, hInv, htrans⟩, ?_⟩
  intro s B ε hs hε g hg k hk t ht hhigh
  have hw := hweights hs hε F hF hi hrank hM
    (hclose.trans_le (min_le_right δg δw)) hlow g hg
    (by linarith : 6 * a₀ ≤ 3 * r) hcarrier hf hInv htrans hgap hcJ k hk t ht hhigh
  have hunit := hw (fun _ ↦ 0) (fun _ ↦ 0) (fun _ ↦ 1) (by norm_num)
  refine ⟨hunit.2.2.1, hunit.2.2.2.2.1, ?_⟩
  intro Φ Y initial hi₀
  exact (hw Φ Y initial hi₀).2.2.2.2.2.2.2

end JanetCartan.ContinuumNormal.FrozenModel
