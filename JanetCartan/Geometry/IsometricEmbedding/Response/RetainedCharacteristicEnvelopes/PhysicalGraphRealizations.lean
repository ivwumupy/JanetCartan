module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.CappedGraphFamily
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteEvolution.PhysicalCutoff.Multiplier
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.PrimitiveRetarded
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformEvolution.RetardedGeometry
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformEvolution.AmplitudeBudgets

/-!
# Physical-cutoff graph realizations on the retained chart

Use the original whole-image primitive construction with the literal physical
multiplier. The actual canonical shell cover covers its closed support, and
its own normalized multiplier bounds pay for the unchanged cutoff shoulder.
The constants and radial band precede the varying chart and coefficient field.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.RetainedCharacteristicEnvelopes
open RetainedFactors
open RegularSector.Characteristic ConicPhase UniformEvolution EvolutionIntegral ResidualCoordinates
open SymbolBudgets FourierIntegral WholeImageGeometry NormalComparison LowBounds
open FullLowBounds SourceExpansion FrequencyCutoff AmplitudeBound PrimitiveProfiles
open FullAmplitudePrimitiveBudget.Local RegularSector.FiniteMasks
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Z" => RootState (Euclidean d)
local notation "TC" => RegularSector.Characteristic.TwoTimePoint (Euclidean d)
local notation "H" => SpacetimeL2 d q

/-- Construct the compact-frequency regularizations, both literal adjoints
and both strong limits for the retained physical cutoff at `2*threshold`.
The original finite shell cover and the proved physical multiplier seminorms
supply all cutoff inputs. The complete interval and whole-image inverse
geometry are unchanged. The radial band and graph constant precede every
coefficient field, chart, and physical matrix; its low symbol estimate is
supplied by the selected amplitude producer
(`app:ch_response:eq:fixed-factor-transfer`,
`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_physical_capped_graph_realizations_with_test_action
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : Z) {ε b src aperture : ℝ}
    (hε : 0 < ε) (hεb : 2 * ε < b) (hsrc : src ≤ ε) (hAp : 0 ≤ aperture)
    (χout χsource : E → ℂ) (ho : ContDiff ℝ ∞ χout) (hs : ContDiff ℝ ∞ χsource)
    (hoc : HasCompactSupport χout) (hsc : HasCompactSupport χsource)
    (hout : tsupport χout ⊆ elapsedPhysicalBox z (ε / 2))
    (R : ℝ) (hR : 0 < R)
    (hXbox : ∀ x ∈ elapsedPhysicalBox z (ε / 2), ‖x‖ ≤ R)
    (hYbox : ∀ y ∈ tsupport χsource, ∀ i : Fin (d + 1), |y i| ≤ R)
    (index : Fin (d + 1)) (mask : E → ℝ) (hm : ContDiff ℝ ∞ mask)
    (hcarrier : ∀ ξ ∈ tsupport (mask ∘ physicalCoordinates index) ∩ sphere (0 : E) 1,
      spatialPart ξ ∈ angularCone ℓ z.2.2 (ε / 2))
    (threshold : ℝ) (hthreshold : 1 ≤ threshold)
    (hβsub : tsupport (fun ξ ↦ (dilatedConicMask mask (2 * threshold) (physicalCoordinates index ξ) : ℂ)) ⊆
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
        χout χsource (fun ξ ↦ (dilatedConicMask mask (2 * threshold) (physicalCoordinates index ξ) : ℂ)) (Cgraph * Mamp) ∧
      let Ψ := SmoothRepresentative.curriedRepresentative ℓ δ hδ χphase (twoTimePhase C)
      ∀ t ∈ Icc 0 (3 * src / 4), ∀ u : graphTestSpace (d + 1) q,
        elapsedGraph Ψ W χout χsource (fun ξ ↦ (dilatedConicMask mask (2 * threshold) (physicalCoordinates index ξ) : ℂ)) t
          (graphTestToLp u) =ᵐ[volume]
        graphTestOutput (elapsedPhase Ψ t)
          (elapsedAmplitude W χout χsource (fun ξ ↦ (dilatedConicMask mask (2 * threshold) (physicalCoordinates index ξ) : ℂ)) t) u := by
  classical
  let Δ := 3 * src / 4
  let β : E → ℂ := fun ξ ↦ (dilatedConicMask mask (2 * threshold) (physicalCoordinates index ξ) : ℂ)
  have hβ : ContDiff ℝ ∞ β :=
    Complex.ofRealCLM.contDiff.comp ((contDiff_dilatedConicMask hm (2 * threshold)).comp
      (physicalCoordinates index).contDiff)
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
  obtain ⟨ra, hra, rb, hrab, s, radii, _, hball, hmap, _, hcover⟩ :=
    exists_retained_finite_shell_cover ℓ z hε (hoc.prod hsc)
      (fun _ hp ↦ hout hp.1) (mask ∘ physicalCoordinates index)
      (hm.comp (physicalCoordinates index).contDiff) hcarrier
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
      obtain ⟨i, hi, t, ht, v, hv, he, ht', _⟩ := hcover threshold hthreshold p
        ⟨hp.1, RegularSector.FiniteEvolution.PhysicalCutoff.tsupport_complex_physical_dilatedConicMask_subset
          mask index (zero_lt_one.trans_le hthreshold) hp.2.1⟩
      exact ⟨⟨i, hi⟩, t, ht, v, hv, he, ht'⟩)
    (fun i ↦ RegularSector.FiniteEvolution.PhysicalCutoff.boundedNormalizedSeminorm_physical_dilatedConicMask
      hm index hthreshold (isCompact_closedBall _ _) (fun p hp ↦ by
        have hg := (hball i.val i.property hp).2.1
        intro hz
        change 0 < ℓ (spatialPartCLM p.2) at hg
        rw [hz, map_zero, map_zero] at hg
        exact (lt_irrefl _ hg)) (fullLowReserve (d + 1))) Δ
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


end JanetCartan.ResponseTransfer.RetainedCharacteristicEnvelopes
