module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.WholeImageGeometry
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.PrimitiveRetarded
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformEvolution.RetardedGeometry
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformEvolution.AmplitudeBudgets

/-!
# Actual graph regularizations on the capped retained chart

The original retained phase bounds construct the whole-image inverse. The
finite normalized cover of the SAME physical masks and multiplier converts
the original amplitude seminorm into the full source-symbol bound. Applying
the low graph constructor then gives the literal regularizations and both
strong limits on the complete elapsed interval. No graph bound is assumed.
Consumer: the regularization inputs of both `IntegratedEnvelope.Assembly`
endpoints (`app:ch_response:eq:fixed-factor-transfer`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.RetainedFactors
open RegularSector.Characteristic ConicPhase UniformEvolution EvolutionIntegral
open SymbolBudgets FourierIntegral WholeImageGeometry NormalComparison LowBounds
open FullLowBounds SourceExpansion FrequencyCutoff AmplitudeBound PrimitiveProfiles
open FullAmplitudePrimitiveBudget.Local RegularSector.FiniteMasks
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Z" => RootState (Euclidean d)
local notation "TC" => RegularSector.Characteristic.TwoTimePoint (Euclidean d)
local notation "H" => SpacetimeL2 d q

/-- Output of the concrete capped graph construction. The cutoff sequence,
operator bound, test actions and both strong limits concern one unchanged
full amplitude and its literal adjoint (`fixed-factor-transfer`). -/
def CappedGraphRealizations (Δ : ℝ) (Ψ : TwoTimePhase d)
    (W : TwoTimeAmplitude d q) (χout χsource β : E → ℂ) (Cbound : ℝ) : Prop :=
  ∃ χ : ℕ → E → ℂ, (∀ j, ContDiff ℝ ∞ (χ j)) ∧
    (∀ j, HasCompactSupport (χ j)) ∧
  ∃ Treg : ℕ → ℝ → H →L[ℂ] H,
    (∀ t ∈ Icc 0 Δ, ‖elapsedGraph Ψ W χout χsource β t‖ ≤ Cbound) ∧
    (∀ j t, t ∈ Icc 0 Δ → ‖Treg j t‖ ≤ Cbound) ∧
    (∀ j t, t ∈ Icc 0 Δ → ∀ u : graphTestSpace (d + 1) q,
      Treg j t (graphTestToLp u) =ᵐ[volume] graphTestOutput (elapsedPhase Ψ t)
        (frequencyCutFullAmplitude (χ j) (elapsedAmplitude W χout χsource β t)) u) ∧
    (∀ j t, t ∈ Icc 0 Δ → ∀ u : graphTestSpace (d + 1) q,
      (Treg j t).adjoint (graphTestToLp u) =ᵐ[volume] fun y ↦ WithLp.toLp 2
        (reverseGraphOperator (elapsedPhase Ψ t)
          (frequencyCutFullAmplitude (fun ξ ↦ star (χ j ξ))
            (fun x y ξ ↦ (elapsedAmplitude W χout χsource β t x y ξ).conjTranspose))
          (fun x ↦ (u.val x).ofLp) y)) ∧
    (∀ j t, frequencyCutFullAmplitude (χ j) (elapsedAmplitude W χout χsource β t) =
      frequencyCutFullAmplitude (complexPhysicalCutoff j) (elapsedAmplitude W χout χsource β t)) ∧
    (∀ t ∈ Icc 0 Δ, ∀ u, Tendsto (fun j ↦ Treg j t u) atTop
      (𝓝 (elapsedGraph Ψ W χout χsource β t u))) ∧
    (∀ t ∈ Icc 0 Δ, ∀ u, Tendsto (fun j ↦ (Treg j t).adjoint u) atTop
      (𝓝 ((elapsedGraph Ψ W χout χsource β t).adjoint u)))

/-- Output of the complete capped elapsed integration: one bounded linear
operator, its norm and both literal actions. Used only as a proved output by
`CappedConstruction`, with the original conic phase (`fixed-factor-transfer`). -/
def CappedIntegralRealization (Δ : ℝ) (Ψ : TwoTimePhase d)
    (W : TwoTimeAmplitude d q) (χout χsource β : E → ℂ) (Cbound : ℝ) : Prop :=
  ∃ Op : H →L[ℂ] H, ‖Op‖ ≤ Δ * Cbound ∧
    (∀ u, Op u = elapsedGraphIntegral Δ Ψ W χout χsource β u) ∧
    (∀ u, Op.adjoint u = ∫ t in Icc 0 Δ, (elapsedGraph Ψ W χout χsource β t).adjoint u)

/-- The constructed graph regularizations give a bounded operator on the
COMPLETE elapsed interval and the integral of its literal adjoints. This
closes the Bochner realization before applying either envelope theorem
(`app:ch_response:eq:fixed-factor-transfer`). -/
theorem CappedGraphRealizations.exists_bounded_integral
    {Δ Cbound : ℝ} {Ψ : TwoTimePhase d} {W : TwoTimeAmplitude d q}
    {χout χsource β : E → ℂ}
    (hgraphs : CappedGraphRealizations Δ Ψ W χout χsource β Cbound)
    (hΔ : 0 ≤ Δ)
    (hΨ : Continuous (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      Ψ p.1.1 p.1.2 p.2.1 p.2.2))
    (hW : ContDiff ℝ ∞ (jointAmplitude W))
    (ho : Continuous χout) (hs : Continuous χsource) (hβ : Continuous β)
    (hoc : HasCompactSupport χout) (hsc : HasCompactSupport χsource) :
    (∀ u, AEStronglyMeasurable (fun t ↦ elapsedGraph Ψ W χout χsource β t u)
      (volume.restrict (Icc 0 Δ))) ∧
    (∀ u, AEStronglyMeasurable (fun t ↦ (elapsedGraph Ψ W χout χsource β t).adjoint u)
      (volume.restrict (Icc 0 Δ))) ∧
    ∃ Op : H →L[ℂ] H, ‖Op‖ ≤ Δ * Cbound ∧
      (∀ u, Op u = elapsedGraphIntegral Δ Ψ W χout χsource β u) ∧
      (∀ u, Op.adjoint u = ∫ t in Icc 0 Δ, (elapsedGraph Ψ W χout χsource β t).adjoint u) := by
  obtain ⟨χ, hχ, hχcs, Treg, hlow, hbound, hreal, hrealAdj, _, hlim, hlimAdj⟩ := hgraphs
  have hb := (hW.comp ((contDiff_fst.fst.prodMk
    (contDiff_fst.snd.prodMk contDiff_snd.fst)).prodMk contDiff_snd.snd)).continuous
  obtain ⟨hm, hmAdj, _, _⟩ := KernelIdentification.supported_elapsedGraph_measurability_and_integral_limits
    Ψ W χout χsource β Δ hΔ (fun _ _ _ _ _ _ ↦ hΨ.continuousAt)
    (fun _ _ _ _ _ _ ↦ hb.continuousAt) ho hs hβ hoc hsc χ
    (fun j ↦ (hχ j).continuous) hχcs Treg hreal hrealAdj hbound hlim hlimAdj
  have hC : 0 ≤ Cbound := (norm_nonneg _).trans (hlow 0 ⟨le_rfl, hΔ⟩)
  exact ⟨hm, hmAdj, strongIntegral _ Δ Cbound hm hlow,
    norm_strongIntegral_le hΔ hC hm hlow, fun _ ↦ rfl,
    strongIntegral_adjoint_apply hm hlow hmAdj⟩

/-- The original graph certificates give datum-wise integrability of both
orientations on the COMPLETE elapsed interval. This discharges the two
integrability inputs of `elapsed_integrals_common_physical_masks_of_realizes`
without changing the low constant or the measure
(`app:ch_response:eq:fixed-factor-transfer`). -/
theorem CappedGraphRealizations.integrableOn_elapsed_and_adjoint
    {Δ Cbound : ℝ} {Ψ : TwoTimePhase d} {W : TwoTimeAmplitude d q}
    {χout χsource β : E → ℂ}
    (hgraphs : CappedGraphRealizations Δ Ψ W χout χsource β Cbound)
    (hΔ : 0 ≤ Δ)
    (hΨ : Continuous (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      Ψ p.1.1 p.1.2 p.2.1 p.2.2))
    (hW : ContDiff ℝ ∞ (jointAmplitude W))
    (ho : Continuous χout) (hs : Continuous χsource) (hβ : Continuous β)
    (hoc : HasCompactSupport χout) (hsc : HasCompactSupport χsource) :
    (∀ u : H, IntegrableOn (fun t ↦ elapsedGraph Ψ W χout χsource β t u) (Icc 0 Δ)) ∧
    (∀ u : H, IntegrableOn (fun t ↦ (elapsedGraph Ψ W χout χsource β t).adjoint u) (Icc 0 Δ)) := by
  obtain ⟨hm, hmAdj, _⟩ := hgraphs.exists_bounded_integral hΔ hΨ hW ho hs hβ hoc hsc
  obtain ⟨_, _, _, _, hlow, _⟩ := hgraphs
  have hlowAdj t (ht : t ∈ Icc 0 Δ) :
      ‖(elapsedGraph Ψ W χout χsource β t).adjoint‖ ≤ Cbound := by
    simpa only [ContinuousLinearMap.adjoint.norm_map] using hlow t ht
  exact ⟨integrableOn_apply_of_uniform_bound hm hlow,
    integrableOn_apply_of_uniform_bound hmAdj hlowAdj⟩

/-- Restrict the original amplitude seminorm to the finite mask-cover band.
The source cap changes neither the amplitude nor its normalization
(`app:ch_response:eq:fixed-factor-transfer`). -/
theorem retained_amplitude_restriction_band
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : Z) {ε ρ a b ra rb : ℝ}
    (hερ : ε ≤ ρ / 2) (ha : ra ≤ a) (hb : b ≤ rb)
    {o j : ℕ} {W : TwoTimeAmplitude d q}
    (hW : ContDiff ℝ ∞ (jointAmplitude W))
    (hf : BoundedTwoTimeOrderSeminorm o (bufferedJetSet ℓ z (ρ / 2) ra rb) j W) :
    BoundedTwoTimeOrderSeminorm o (bufferedJetSet ℓ z ε a b) j W ∧
      twoTimeOrderSeminorm o (bufferedJetSet ℓ z ε a b) j W ≤
        twoTimeOrderSeminorm o (bufferedJetSet ℓ z (ρ / 2) ra rb) j W := by
  obtain ⟨hf', hle⟩ := retained_amplitude_restriction ℓ z hερ hW hf
  have hsub := retained_bufferedJetSet_mono_band ℓ z ε ha hb
  have hbound R (hR : 1 ≤ R) :
      cNorm (bufferedJetSet ℓ z ε a b) j (twoTimeOrderField o R W) ≤
        twoTimeOrderSeminorm o (bufferedJetSet ℓ z ε ra rb) j W := by
    apply le_trans (cNorm_mono_set hsub (isCompact_bufferedJetSet _ _ _ _ _) ?_)
      (cNorm_twoTimeOrderField_le hf' hR)
    exact (((hW.comp (contDiff_fst.prodMk (contDiff_snd.const_smul R))).const_smul
      (R ^ o)).of_le (by simp))
  refine ⟨⟨twoTimeOrderSeminorm o (bufferedJetSet ℓ z ε ra rb) j W, ?_⟩, ?_⟩
  · rintro _ ⟨R, rfl⟩
    exact hbound R R.2
  · apply le_trans (Real.sSup_le ?_ (twoTimeOrderSeminorm_nonneg _ _ _ _)) hle
    rintro _ ⟨R, rfl⟩
    exact hbound R R.2

/-- Construct the complete capped graph family from the retained phase and
original normalized amplitude budgets. The finite radial band and constant
precede the coefficients, chart, amplitude and elapsed time. `CappedConstruction`
instantiates these inputs on its actual solver and full residual. The source
interval is exactly `[0,3*src/4]`; it is never shortened here
(`app:ch_response:eq:fixed-factor-transfer`). -/
theorem exists_capped_retained_graph_realizations_with_test_action
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : Z) {ε b src aperture : ℝ}
    (hε : 0 < ε) (hεb : 2 * ε < b) (hsrc : src ≤ ε) (hAp : 0 ≤ aperture)
    (χout χsource : E → ℂ) (ho : ContDiff ℝ ∞ χout) (hs : ContDiff ℝ ∞ χsource)
    (hoc : HasCompactSupport χout) (hsc : HasCompactSupport χsource)
    (hout : tsupport χout ⊆ elapsedPhysicalBox z (ε / 2))
    (R : ℝ) (hR : 0 < R)
    (hXbox : ∀ x ∈ elapsedPhysicalBox z (ε / 2), ‖x‖ ≤ R)
    (hYbox : ∀ y ∈ tsupport χsource, ∀ i : Fin (d + 1), |y i| ≤ R)
    (mask : E → ℝ) (hm : ContDiff ℝ ∞ mask)
    (hcarrier : ∀ ξ ∈ tsupport mask ∩ sphere (0 : E) 1,
      spatialPart ξ ∈ angularCone ℓ z.2.2 (ε / 2))
    (threshold : ℝ) (hthreshold : 1 ≤ threshold)
    (hβsub : tsupport (fun ξ ↦ (dilatedConicMask mask threshold ξ : ℂ)) ⊆
      retainedFrequencyDomain ℓ z ε aperture (1 / 2))
    (phaseCost : ℕ → ℝ) (hcost : ∀ j, 0 < phaseCost j) (Mphase : ℝ) :
    ∃ ra > (0 : ℝ), ∃ rb > ra, ∃ Cgraph > (0 : ℝ),
    ∀ (KQ : Set E) (Q : E → Fin (d + 1) → MetricTensor (d + 1)),
      cNorm KQ (wholeImagePhaseReserve (d + 1) + 1) Q ≤ Mphase →
    ∀ (h : Z → ℝ) (Φ : Z × ℝ → Z) (C : OpenPartialHomeomorph TC TC),
      closedBall (z.1, z) b ⊆ C.target →
      ContDiffOn ℝ ∞ (twoTimePhase C) C.target →
      (∀ p ∈ C.target, HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C p) p) →
      (∀ p ∈ closedBall (z.1, z) b, ‖twoTimePhaseMixed C p - 1‖ ≤ 1 / 2) →
      (∀ j, cNorm (closedBall (z.1, z) b) j (twoTimePhase C) ≤
        phaseCost j * (1 + cNorm KQ (j + 1) Q)) →
    ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 / 2 →
    ∀ χphase : TC → ℝ, ContDiff ℝ ∞ χphase → HasCompactSupport χphase →
      tsupport χphase ⊆ ball (z.1, z) b →
      (∀ p ∈ closedBall (z.1, z) (4 * ε), χphase =ᶠ[𝓝 p] (fun _ ↦ 1)) →
    ∀ (o : ℕ) (Mamp : ℝ) (W : TwoTimeAmplitude d q),
      ContDiff ℝ ∞ (jointAmplitude W) →
      BoundedTwoTimeOrderSeminorm o (bufferedJetSet ℓ z ε ra rb)
        (fullLowReserve (d + 1)) W →
      twoTimeOrderSeminorm o (bufferedJetSet ℓ z ε ra rb)
        (fullLowReserve (d + 1)) W ≤ Mamp →
      CappedGraphRealizations (3 * src / 4)
        (SmoothRepresentative.curriedRepresentative ℓ δ hδ χphase (twoTimePhase C)) W
        χout χsource (fun ξ ↦ (dilatedConicMask mask threshold ξ : ℂ)) (Cgraph * Mamp) ∧
      let Ψ := SmoothRepresentative.curriedRepresentative ℓ δ hδ χphase (twoTimePhase C)
      ∀ t ∈ Icc 0 (3 * src / 4), ∀ u : graphTestSpace (d + 1) q,
        elapsedGraph Ψ W χout χsource (fun ξ ↦ (dilatedConicMask mask threshold ξ : ℂ)) t
          (graphTestToLp u) =ᵐ[volume]
        graphTestOutput (elapsedPhase Ψ t)
          (elapsedAmplitude W χout χsource (fun ξ ↦ (dilatedConicMask mask threshold ξ : ℂ)) t) u := by
  classical
  let Δ := 3 * src / 4
  let β : E → ℂ := fun ξ ↦ (dilatedConicMask mask threshold ξ : ℂ)
  have hβ : ContDiff ℝ ∞ β :=
    Complex.ofRealCLM.contDiff.comp (contDiff_dilatedConicMask hm threshold)
  have hβzero : (0 : E) ∉ tsupport β := by
    intro hz
    have hh := retainedFrequencyDomain_norm_lt ℓ (hβsub hz)
    norm_num at hh
  have htε t (ht : t ∈ Icc 0 Δ) : t ∈ Icc 0 ε :=
    ⟨ht.1, by dsimp only [Δ] at ht; linarith only [ht.2, hsrc, hε]⟩
  obtain ⟨gap, hgap, a, ha, bfreq, hab, Mg, hMg, Gg, hGg, cg, hcg,
    growth, hgrowth, hgeometry⟩ :=
    exists_retained_representative_wholeImage_geometry ℓ z hε hεb hAp phaseCost hcost Mphase
  obtain ⟨Cg, hCg, hfamily⟩ := exists_fullGraphFamily_of_primitive_inputs
    (r := q) (Nat.succ_pos d) R (4 * R) Mg Gg cg (by positivity)
    (by apply (div_lt_iff₀ (by positivity : 0 < 4 * R)).mpr; linarith)
    hgap hgrowth.le hcg
  obtain ⟨χ, hχ, hχcs, _, hχeq, hfamily⟩ := hfamily
    (tsupport χout) (tsupport χsource) (tsupport β) hoc hYbox (isClosed_tsupport _) hβzero
  obtain ⟨ra, hra, rb, hrab, s, radii, _, _, hmap, hmult, hcover⟩ :=
    exists_retained_finite_shell_cover ℓ z hε (hoc.prod hsc)
      (fun _ hp ↦ hout hp.1) mask hm hcarrier
  let ι := {p // p ∈ s}
  let centers : ι → Point (d + 1) := fun p ↦ p.val.val
  let radii' : ι → ℝ := fun p ↦ radii p.val
  let Jamp := bufferedJetSet ℓ z ε ra rb
  obtain ⟨Ca, hCa, hbudget⟩ := exists_elapsed_fullLowReserve_constant
    (q := q) centers radii' (isCompact_bufferedJetSet _ _ _ _ _)
    ((isOpen_ball (x := (z.1, (z.1, z.2.1)))).prod (isOpen_angularCone ℓ z.2.2 (2 * ε)))
    (retained_bufferedJetSet_subset_open_product ℓ z hε hra)
    χout χsource β ho hs hβ isClosed_univ
    (by
      intro p hp
      obtain ⟨i, hi, t, ht, v, hv, he, ht', _⟩ := hcover threshold hthreshold p ⟨hp.1, hp.2.1⟩
      exact ⟨⟨i, hi⟩, t, ht, v, hv, he, ht'⟩)
    (fun i ↦ hmult threshold hthreshold i.val i.property (fullLowReserve (d + 1))) Δ
    (fun t ht i ↦ hmap t (htε t ht) i.val i.property)
  refine ⟨ra, hra, rb, hrab, Cg * Ca, mul_pos hCg (zero_lt_one.trans_le hCa), ?_⟩
  intro KQ Q hQ h Φ C hbuffer hsmooth hdiff hnear hphase δ hδ hδhalf
    χphase hχphase hcχphase hsχphase heχphase o Mamp W hW hf hM
  let Ψ := SmoothRepresentative.curriedRepresentative ℓ δ hδ χphase (twoTimePhase C)
  have hS t : ContDiff ℝ ∞ (Function.uncurry (elapsedPhase Ψ t)) :=
    SmoothRepresentative.contDiff_elapsed_representative ℓ hδ hχphase hcχphase
      C.open_target (hsχphase.trans (ball_subset_closedBall.trans hbuffer)) hsmooth t
  have hl t (ht : t ∈ Icc 0 Δ) := by
    obtain ⟨chart, hopen, hη, hηmap, hJ, hJgap, hinverse, hgrowth', hclosed, hjets⟩ :=
      hgeometry KQ Q hQ h Φ C hbuffer hsmooth hdiff hnear hphase src δ hsrc hδ hδhalf
        χphase heχphase t ht
    let X := elapsedPhysicalBox z (ε / 2)
    let D := retainedFrequencyDomain ℓ z ε aperture (1 / 2)
    let Kn := tsupport χout ×ˢ (tsupport χout ×ˢ tsupport β)
    have hKn : Kn ⊆ X ×ˢ (X ×ˢ D) := fun _ hp ↦ ⟨hout hp.1, hout hp.2.1, hβsub hp.2.2⟩
    obtain ⟨hclosed', hbuffer'⟩ := hclosed Kn
      (hoc.isClosed.prod (hoc.isClosed.prod (isClosed_tsupport β))) hKn
    have hg := hfamily (elapsedPhase Ψ t) (hS t) (K := Kn) chart hopen hη hηmap hJ
      (fun p hp ↦ abs_pos.mp (hgap.trans_le (hJgap p hp))) hinverse
      (fun _ _ hx hy hξ ↦ ⟨hx, hy, hξ⟩) hclosed' hbuffer' hXbox hgrowth'
      (fun l ↦ X ×ˢ (X ×ˢ normalizedSourceBand D ((2 : ℝ)^l) a bfreq))
      (fun l ↦ (hjets l).1) (fun l ↦ (hjets l).2.1) (fun l ↦ (hjets l).2.2.1)
      (fun l ↦ (hjets l).2.2.2.1) (fun l ↦ (hjets l).2.2.2.2.1)
      (fun l ↦ (hjets l).2.2.2.2.2.1) (fun l ↦ (hjets l).2.2.2.2.2.2.1)
      (fun l ↦ (hjets l).2.2.2.2.2.2.2.1) (fun l ↦ (hjets l).2.2.2.2.2.2.2.2) hout hβsub
    exact hg.1 (elapsedAmplitude W χout χsource β t)
      (elapsedAmplitude_forwardAdmissible W χout χsource β hW ho hs hβ t) (Ca * Mamp)
      (hbudget o Mamp W hW (fun _ _ _ _ h ↦ (h (mem_univ _)).elim) hf hM t ht)
  choose T ht hta htr hreal hrealAdj hlim hlimAdj htest hdist hdistAdj using hl
  let Treg : ℕ → ℝ → H →L[ℂ] H := fun j t ↦ if ht : t ∈ Icc 0 Δ then T t ht j else 0
  have hTreg j t (ht : t ∈ Icc 0 Δ) : Treg j t = T t ht j := dite_eq_left ht
  constructor
  · refine ⟨χ, hχ, hχcs, Treg, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro t ht'
      simpa only [elapsedGraph, mul_assoc] using ht t ht'
    · intro j t ht'
      simpa only [hTreg _ _ ht', mul_assoc] using htr t ht' j
    · intro j t ht' u
      simpa only [hTreg _ _ ht'] using hreal t ht' j u
    · intro j t ht' u
      simpa only [hTreg _ _ ht'] using hrealAdj t ht' j u
    · intro j t
      exact hχeq _ (fun x y ξ hξ ↦ elapsedAmplitude_eq_zero_of_mask W χout χsource β t x y ξ
        (Or.inr (Or.inr (image_eq_zero_of_notMem_tsupport hξ)))) j
    · intro t ht' u
      simpa only [hTreg _ _ ht', elapsedGraph] using hlim t ht' u
    · intro t ht' u
      simpa only [hTreg _ _ ht', elapsedGraph] using hlimAdj t ht' u
  · intro Ψ' t ht' u
    simpa only [elapsedGraph] using htest t ht' u


/-- The original capped graph-family API is the projection of the construction
that also retains its unregularized test action. All radial choices, constants
and full elapsed intervals are unchanged
(`app:ch_response:eq:fixed-factor-transfer`). -/
theorem exists_capped_retained_graph_realizations
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : Z) {ε b src aperture : ℝ}
    (hε : 0 < ε) (hεb : 2 * ε < b) (hsrc : src ≤ ε) (hAp : 0 ≤ aperture)
    (χout χsource : E → ℂ) (ho : ContDiff ℝ ∞ χout) (hs : ContDiff ℝ ∞ χsource)
    (hoc : HasCompactSupport χout) (hsc : HasCompactSupport χsource)
    (hout : tsupport χout ⊆ elapsedPhysicalBox z (ε / 2))
    (R : ℝ) (hR : 0 < R)
    (hXbox : ∀ x ∈ elapsedPhysicalBox z (ε / 2), ‖x‖ ≤ R)
    (hYbox : ∀ y ∈ tsupport χsource, ∀ i : Fin (d + 1), |y i| ≤ R)
    (mask : E → ℝ) (hm : ContDiff ℝ ∞ mask)
    (hcarrier : ∀ ξ ∈ tsupport mask ∩ sphere (0 : E) 1,
      spatialPart ξ ∈ angularCone ℓ z.2.2 (ε / 2))
    (threshold : ℝ) (hthreshold : 1 ≤ threshold)
    (hβsub : tsupport (fun ξ ↦ (dilatedConicMask mask threshold ξ : ℂ)) ⊆
      retainedFrequencyDomain ℓ z ε aperture (1 / 2))
    (phaseCost : ℕ → ℝ) (hcost : ∀ j, 0 < phaseCost j) (Mphase : ℝ) :
    ∃ ra > (0 : ℝ), ∃ rb > ra, ∃ Cgraph > (0 : ℝ),
    ∀ (KQ : Set E) (Q : E → Fin (d + 1) → MetricTensor (d + 1)),
      cNorm KQ (wholeImagePhaseReserve (d + 1) + 1) Q ≤ Mphase →
    ∀ (h : Z → ℝ) (Φ : Z × ℝ → Z) (C : OpenPartialHomeomorph TC TC),
      closedBall (z.1, z) b ⊆ C.target →
      ContDiffOn ℝ ∞ (twoTimePhase C) C.target →
      (∀ p ∈ C.target, HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C p) p) →
      (∀ p ∈ closedBall (z.1, z) b, ‖twoTimePhaseMixed C p - 1‖ ≤ 1 / 2) →
      (∀ j, cNorm (closedBall (z.1, z) b) j (twoTimePhase C) ≤
        phaseCost j * (1 + cNorm KQ (j + 1) Q)) →
    ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 / 2 →
    ∀ χphase : TC → ℝ, ContDiff ℝ ∞ χphase → HasCompactSupport χphase →
      tsupport χphase ⊆ ball (z.1, z) b →
      (∀ p ∈ closedBall (z.1, z) (4 * ε), χphase =ᶠ[𝓝 p] (fun _ ↦ 1)) →
    ∀ (o : ℕ) (Mamp : ℝ) (W : TwoTimeAmplitude d q),
      ContDiff ℝ ∞ (jointAmplitude W) →
      BoundedTwoTimeOrderSeminorm o (bufferedJetSet ℓ z ε ra rb)
        (fullLowReserve (d + 1)) W →
      twoTimeOrderSeminorm o (bufferedJetSet ℓ z ε ra rb)
        (fullLowReserve (d + 1)) W ≤ Mamp →
      CappedGraphRealizations (3 * src / 4)
        (SmoothRepresentative.curriedRepresentative ℓ δ hδ χphase (twoTimePhase C)) W
        χout χsource (fun ξ ↦ (dilatedConicMask mask threshold ξ : ℂ)) (Cgraph * Mamp) := by
  obtain ⟨ra, hra, rb, hrab, Cgraph, hCgraph, hfamily⟩ :=
    exists_capped_retained_graph_realizations_with_test_action (q := q)
      ℓ z hε hεb hsrc hAp χout χsource ho hs hoc hsc hout R hR hXbox hYbox
      mask hm hcarrier threshold hthreshold hβsub phaseCost hcost Mphase
  refine ⟨ra, hra, rb, hrab, Cgraph, hCgraph, ?_⟩
  intro KQ Q hQ h Φ C hbuffer hsmooth hdiff hnear hphase δ hδ hδhalf
    χphase hχphase hcχphase hsχphase heχphase o Mamp W hW hf hM
  exact (hfamily KQ Q hQ h Φ C hbuffer hsmooth hdiff hnear hphase δ hδ hδhalf
    χphase hχphase hcχphase hsχphase heχphase o Mamp W hW hf hM).1

end JanetCartan.ResponseTransfer.RetainedFactors
