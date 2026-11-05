module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.WideDensity.WeightedCanonical

/-!
# Applying the wider-density estimate to the actual scalar carrier

The current coefficient is the literal canonical carrier with its prescribed
initial scalar multiplied by `sqrt (1 + v)`. The reference may be the normalized
zero slice or a fixed positive carrier. Both current density labels are the
actual ODE inverse labels. Smoothness and range after conic substitution are
derived from their primitive field chart and the genuine inverse range.

Consumer: the same-seed assembly in `SeedAssembly` and the retained-leading
identification, for `app:ch_background:prop:bg-normalized` and
`app:ch_osc:prop:osc-normal`, Step 4'. The primitive bounds and differences in
this application still have to be supplied on the same concrete family; this
lemma does not assert an unconditional family construction.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.WideDensity
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport
open ContinuumRow CanonicalCarrier PositiveReference
open ContinuumNormalReduction.TransportSymbol

/-- The full matrix comparison for the actual prescribed scalar times the
original wider density. It instantiates the primitive multiplication theorem
and the checked ambient-jet factorization, with no density-continuity premise.
In particular `initial = fun _ ↦ σ` is retained unchanged. The reference label
`g₀` can be the divided seed ODE extension at zero. Sources:
`app:ch_background:eq:bg-Nsigma`, `app:ch_background:eq:bg-full-complex-amplitude`,
`app:ch_background:prop:bg-normalized`. -/
theorem exists_canonical_weighted_sub_le_of_primitive_norms
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) (D : CoefficientNormCharts n)
    {K W : Set (InputVariables n)} {Q Ω : Set (Variables n × Euclidean 2)}
    {L : Set (Euclidean (n - 1) × Euclidean 3)}
    (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W)
    (hQ : IsCompact Q) (hΩ : IsOpen Ω) (hQΩ : Q ⊆ Ω)
    (hL : IsCompact L) (hconv : Convex ℝ L)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hη : ∀ p ∈ K, ε ≤ ‖p.2.2‖) (hrange : ∀ p ∈ K, D.Contains p)
    {J₀ : InputVariables n → ℝ} (hJ₀ : ContDiffOn ℝ ∞ J₀ W)
    (hgap₀ : ∀ p ∈ K, δ ≤ |J₀ p|)
    (s : ℕ) {M : ℝ} (hM : 0 ≤ M) (hJ₀M : cNorm K s J₀ ≤ M) :
    ∃ C > 0, ∀
      (QF : {QF : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ QF U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (QF - fun _ ↦ cubeStress n) < T.family.threshold})
      (F : Euclidean n → Euclidean N) (row col : Fin n)
      (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
      (r : ℝ) (hr : 0 < r) (hcell : 4 * r < 1 / 2)
      (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)
      (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
      (a₀ : Coefficients n N) (J : InputVariables n → ℝ)
      (u u₀ : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
      (g₀ : Bool → Variables n × Euclidean 2 → Euclidean (n - 1) × Euclidean 3)
      (d : ℝ),
      let a := TransportKernel.coefficientsOfCarrier
        (data T QF F row col Φ Y initial hr hcell angular high) (FixedCutoffs.physical hr 1)
      let g := fun b p ↦ densityFootpoint T Y (densityEndpoint b (inverseCoordinates u p))
      0 ≤ d → D.Controls s M (M + 1) 1 a → D.Controls (s + 1) M (M + 1) 1 a₀ →
      ContDiffOn ℝ ∞ J W → (∀ p ∈ K, δ ≤ |J p|) → cNorm K s J ≤ M →
      ContDiffOn ℝ ∞ u Ω → ContDiffOn ℝ ∞ u₀ Ω →
      MapsTo (inverseCoordinates u) Q K → MapsTo (inverseCoordinates u₀) Q K →
      cNorm Q s (inverseCoordinates u) ≤ M → cNorm Q s (inverseCoordinates u₀) ≤ M →
      ContDiffOn ℝ ∞ (densityFootpoint T Y) D.field.region →
      MapsTo (densityFootpoint T Y) D.field.carrier L →
      (∀ b p, p ∈ Q → ContDiffAt ℝ ∞ (g₀ b) p) →
      (∀ b, MapsTo (g₀ b) Q L) →
      (∀ b, cNorm Q s (g b) ≤ M) → (∀ b, cNorm Q s (g₀ b) ≤ M) →
      cNorm D.measurement.carrier s (a.measurement - a₀.measurement) ≤ d →
      cNorm D.angular.carrier s (a.angular - a₀.angular) ≤ d →
      cNorm D.high.carrier s (a.high - a₀.high) ≤ d →
      cNorm D.field.carrier s (a.normal - a₀.normal) ≤ d →
      cNorm D.field.carrier s (a.reduced - a₀.reduced) ≤ d →
      cNorm K s (J - J₀) ≤ d →
      cNorm Q s (inverseCoordinates u - inverseCoordinates u₀) ≤ d →
      (∀ b, cNorm Q s (g b - g₀ b) ≤ d) →
      ∀ (d₀ : ℕ), s + 1 ≤ d₀ →
      ∀ (v : Euclidean (n - 1) × Euclidean 3 → ℝ),
      (∀ y ∈ L, ContDiffAt ℝ ∞ v y) → cNorm L d₀ v ≤ 1 →
      (∀ y ∈ L, (1 / 2 : ℝ) ≤ 1 + v y) →
      let av := TransportKernel.coefficientsOfCarrier
        (data T QF F row col Φ Y (fun y ↦ initial y * Real.sqrt (1 + v y))
          hr hcell angular high) (FixedCutoffs.physical hr 1)
      let b := fun p ↦ inputDensity av J (inverseCoordinates u p)
      let b₀ := fun p ↦ densityPair v g₀ p • inputDensity a₀ J₀ (inverseCoordinates u₀ p)
      cNorm Q s b ≤ C ∧ cNorm Q s b₀ ≤ C ∧ cNorm Q s (b - b₀) ≤ C * d ∧
      ∀ p ∈ Q, ∀ j ≤ s, ‖iteratedFDeriv ℝ j (b - b₀) p‖ ≤ C * d := by
  obtain ⟨C, hC, hcompare⟩ := exists_weighted_inputDensity_inverse_sub_le_of_primitive_norms
    (N := N) D hK hW hKW hQ hΩ hQΩ hL hconv hε hδ hη hrange hJ₀ hgap₀ s hM hJ₀M
  refine ⟨C, hC, ?_⟩
  intro QF F row col Φ Y r hr hcell angular high initial a₀ J u u₀ g₀ d a g
    hd ha ha₀ hJ hgap hJM hu hu₀ huK hu₀K huM hu₀M hY hYL hg₀ hgr₀ hgm hgm₀
    hm hang hh hn hq hj hi hgd d₀ horder v hv hvm hpos av b b₀
  have hend (side) (p) (hp : p ∈ Q) :
      densityEndpoint side (inverseCoordinates u p) ∈ D.field.carrier := by
    have h := hrange _ (huK hp)
    cases side
    · exact h.2.2.2.2.1
    · exact h.2.2.2.2.2
  have hg (side) (p) (hp : p ∈ Q) : ContDiffAt ℝ ∞ (g side) p := by
    have harg : ContDiffAt ℝ ∞ (fun q ↦ densityEndpoint side (inverseCoordinates u q)) p :=
      (densityEndpoint_contDiff side).contDiffAt.comp p
        ((inverseCoordinates_contDiffOn hu).contDiffAt (hΩ.mem_nhds (hQΩ hp)))
    exact (hY.contDiffAt (D.field.isOpen_region.mem_nhds (D.field.ball_subset (hend side p hp)))).comp
      (f := fun q ↦ densityEndpoint side (inverseCoordinates u q)) p harg
  have hgr (side) : MapsTo (g side) Q L := fun p hp ↦ hYL (hend side p hp)
  have hb := hcompare a a₀ J u u₀ g g₀ d hd ha ha₀ hJ hgap hJM hu hu₀ huK hu₀K
    huM hu₀M hg hg₀ hgr hgr₀ hgm hgm₀ hm hang hh hn hq hj hi hgd d₀ horder v hv hvm
  let bw := fun p ↦ densityPair v g p • inputDensity a J (inverseCoordinates u p)
  have heq (p) (hp : p ∈ Q) : b =ᶠ[𝓝 p] bw := by
    exact canonical_substitutedDensity_initial_mul_sqrtDensity_eventuallyEq T QF F row col Φ Y
      hr hcell angular high initial v J u p
      (fun side ↦ (hg side p hp).continuousAt)
      (fun side ↦ (hv _ (hgr side hp)).continuousAt)
      (fun side ↦ lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) (hpos _ (hgr side hp)))
  have hnorm : cNorm Q s b = cNorm Q s bw := GeometricProfile.cNorm_eq_of_eventuallyEq heq s
  have hsub : cNorm Q s (b - b₀) = cNorm Q s (bw - b₀) :=
    canonical_substitutedDensity_initial_mul_sqrtDensity_cNorm_sub T QF F row col Φ Y
      hr hcell angular high initial v J u (fun side p hp ↦ (hg side p hp).continuousAt)
      (fun side p hp ↦ hgr side hp) hv hpos b₀ s
  refine ⟨hnorm ▸ hb.1, hb.2.1, hsub ▸ hb.2.2.1, ?_⟩
  intro p hp j hj'
  rw [(((heq p hp).sub (Filter.EventuallyEq.refl _ b₀)).iteratedFDeriv ℝ j).eq_of_nhds]
  exact hb.2.2.2 p hp j hj'

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.WideDensity
