module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.PrimitiveIntegerBounds
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.PrimitiveTestAction
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.SobolevIntegration

/-!
# The retarded kernel theorem from primitive data

This assembly constructs the same bounded retarded operator as
`PrimitiveRetarded`, identifies its original uncut fixed-time and retarded
actions, and proves its forward and literal-adjoint integer bounds. Constants
precede the varying phase and amplitude. One common annulus contains the low
and integer constructors' annuli; a buffered inner homogeneous cone is used
inside the larger smoothness cone. No operator bound, orbit measurability,
uncut action, raw mixed-jet bound, or Sobolev conclusion is an input.

The sector constructor supplies the actual Hamilton phase and transport
symbols on these fixed charts. This theorem supplies the evolution factors
in `app:ch_regular_base:eq:energy-complete-residual`; the complete residual
and its restriction-space conversion remain with that constructor.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 6400000
open Set MeasureTheory Filter JanetCartan.Pseudodifferential
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral
open FourierIntegral SymbolBudgets KernelIdentification UncutTestAction
open FullLowBounds WholeImageGeometry FullAmplitudePrimitiveBudget
open FullAmplitudePrimitiveBudget.Local PrimitiveProfiles
open LowBounds.FrequencyCutoff
variable {d q : ℕ} {ι : Type*} [Fintype ι]
local notation "E" => Euclidean (d + 1)
local notation "P" => ℝ × ℝ × Euclidean d

/-- Primitive realization of the retarded kernel, its original test action,
and all integer bounds for the SAME operator and literal Hilbert adjoint.
Spatial orders zero and minus one use the fixed shift
`fullLowReserve (d+1)+2`, independent of the requested Sobolev order or any
accuracy. Integration costs exactly `Δ`; the coefficient budget stays the
sum of one original amplitude seminorm and one original phase seminorm.
Both masks, the initial buffer and both retarded endpoints are retained.
The inner cone is convex and buffered inside the outer smoothness cone;
all carrier inclusions are fixed geometric data, not analytic conclusions.
Sources: `app:ch_regular_base:lem:retarded-kernel`,
`app:ch_regular_base:eq:fixed-time-representation`, and
`app:ch_regular_base:eq:energy-complete-residual`. -/
theorem exists_retardedOperator_integer_bounds_of_primitive_data
    (R ℓ Btime Bφ Δ : ℝ) (hΔ : 0 ≤ Δ) (hBφ : 0 ≤ Bφ)
    (hℓ : 0 < ℓ) (hRcell : R / ℓ < 1 / 2) {ε : ℝ} (hε : 0 < ε)
    (z : ι → Point (d + 1)) (δ : ι → ℝ) (hδ : ∀ i, 0 < δ i)
    {J U : Set (TwoTimePoint d)} (hJ : IsCompact J) (hU : IsOpen U) (hJU : J ⊆ U)
    (χout χsource β : E → ℂ)
    (ho : ContDiff ℝ ∞ χout) (hs : ContDiff ℝ ∞ χsource) (hβ : ContDiff ℝ ∞ β)
    (hocs : HasCompactSupport χout) (hscs : HasCompactSupport χsource)
    (hβzero : (0 : E) ∉ tsupport β)
    (hYbox : ∀ y ∈ tsupport χsource, ∀ i : Fin (d + 1), |y i| ≤ R)
    (hβbound : ∀ i j, BoundedNormalizedSeminorm (Metric.closedBall (z i) (δ i)) j
      (jointMultiplier β))
    (c : ℝ) (hc : 1 ≤ c)
    (hcover : ∀ p ∈ (tsupport χout ×ˢ tsupport χsource) ×ˢ tsupport β,
      ∃ i, ∃ t : ℝ, 1 ≤ t ∧ ∃ v ∈ Metric.closedBall (z i) (δ i),
        p = (v.1, t • v.2) ∧ 1 + ‖p.2‖ ≤ t ∧ t ≤ c * (1 + ‖p.2‖))
    (hmap : ∀ r ∈ Icc 0 Δ, ∀ i, MapsTo (elapsedPoint r) (Metric.closedBall (z i) (δ i)) J) :
    ∃ a > 0, ∃ b > a, ∃ C₀ > 0,
      ∀ (Ug : ι → Set (Point (d + 1))) (Vg : Set (Point (d + 1))),
        (∀ i, IsOpen (Ug i)) → IsOpen Vg →
        (∀ i, Metric.closedBall (z i) (δ i) ⊆ Ug i) →
        (∀ i, ∀ t : ℝ, 1 ≤ t → ∀ p ∈ Ug i, (p.1, t • p.2) ∈ Vg) →
      ∀ (Xouter X Dnormal : Set E) (Douter Dcore : Set (Euclidean d)) (Ω : Set P),
        IsOpen Xouter → IsOpen Douter → Convex ℝ Xouter → Convex ℝ Douter →
        IsOpen X → IsOpen Dnormal → Convex ℝ X → IsOpen Ω →
        IsOpen Dcore → Convex ℝ Dcore → Dcore ⊆ Douter →
        closure X ⊆ Xouter → closure Dnormal ⊆ spatialPart ⁻¹' Dcore →
        (∀ t : ℝ, 0 < t → ∀ η ∈ Douter, t • η ∈ Douter) →
        (∀ t : ℝ, 0 < t → ∀ η ∈ Dcore, t • η ∈ Dcore) →
        (∀ p ∈ Vg, p.1.1 ∈ X ∧ spatialPart p.2 ∈ Dcore) →
        (∀ r ∈ Icc 0 Δ, ∀ x ∈ Xouter, (x 0, x 0-r, spatialPart x) ∈ Ω) →
        (∀ x ∈ X, ‖x‖ ≤ R) → (∀ ξ ∈ Dnormal, ε < ‖ξ‖) →
        U ⊆ Ω ×ˢ Douter →
        (∀ r ∈ Icc 0 Δ, ∀ x ∈ X, ∀ η ∈ Dcore,
          ∃ t : ℝ, 0 < t ∧ ∃ ζ ∈ Douter,
            ((x 0, x 0-r, spatialPart x), ζ) ∈ J ∧ η = t • ζ) →
        tsupport χout ⊆ X → tsupport β ⊆ Dnormal →
      ∀ M : ℝ, 0 ≤ M → ∀ o : ℕ, (o = 0 ∨ o = 1) →
      ∃ C : ℕ → ℝ, (∀ s, 0 < C s) ∧
      ∀ K : Set (Point (d + 1)), IsCompact K →
        phaseTimeConstant K (wholeImagePhaseReserve (d + 1)) Δ ≤ Btime →
        (∀ j : ℕ, ∀ p ∈ X ×ˢ normalizedSourceBand Dnormal ((2 : ℝ)^j) a b,
          phasePairInclusion p ∈ K) →
        (∀ r ∈ Icc 0 Δ, MapsTo (elapsedPoint r) K J) →
      ∀ Ψ : TwoTimePhase d,
        ContDiffOn ℝ ∞ (jointPhase Ψ) (Ω ×ˢ Douter) →
        (∀ t : ℝ, 0 < t → ∀ p ∈ Ω, ∀ η ∈ Douter,
          Ψ p.1 p.2.1 p.2.2 (t • η) = t * Ψ p.1 p.2.1 p.2.2 η) →
        (∀ r ∈ Icc 0 Δ, ∀ x ∈ Xouter, ∀ η ∈ Douter,
          ‖mixedPhaseMatrix (Ψ (x 0) (x 0-r)) (spatialPart x) η - 1‖ ≤ 1/2) →
        cNorm J (max (wholeImagePhaseReserve (d + 1)) (fullLowReserve (d + 1) + o + 2))
          (jointPhase Ψ) ≤ Bφ →
      ∀ b : TwoTimeAmplitude d q, ContDiff ℝ ∞ (jointAmplitude b) →
        (∀ j, BoundedTwoTimeOrderSeminorm o J j b) →
        twoTimeOrderSeminorm o J (fullLowReserve (d + 1) + o) b ≤ M →
      ∀ a₀ : ℝ, (∀ x, χout x ≠ 0 → x 0 ∈ Icc a₀ (a₀ + Δ)) →
        (∀ t s y η, s ≤ a₀ → b t s y η = 0) →
      (∀ r ∈ Icc 0 Δ, ‖elapsedGraph Ψ b χout χsource β r‖ ≤ C₀ * M) ∧
      (∀ u, AEStronglyMeasurable (fun r ↦ elapsedGraph Ψ b χout χsource β r u)
        (volume.restrict (Icc 0 Δ))) ∧
      (∀ u, AEStronglyMeasurable (fun r ↦ (elapsedGraph Ψ b χout χsource β r).adjoint u)
        (volume.restrict (Icc 0 Δ))) ∧
      (∀ r ∈ Icc 0 Δ, ∀ u : graphTestSpace (d + 1) q,
        elapsedGraph Ψ b χout χsource β r (graphTestToLp u) =ᵐ[volume]
          fun x ↦ WithLp.toLp 2 (χout x • graphOperator (Ψ (x 0) (x 0-r))
            (fun y _ η ↦ b (x 0) (x 0-r) y η)
            (fun z ↦ physicalMultiplierIntegral β
              (graphTestToSchwartz (complexSourceMaskTest χsource hs u))
              (timeSpacePoint (x 0-r) z)) (spatialPart x))) ∧
      ∃ Q : SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q,
        ‖Q‖ ≤ Δ * (C₀ * M) ∧
        (∀ u, Q u = elapsedGraphIntegral Δ Ψ b χout χsource β u) ∧
        (∀ u, Q.adjoint u = ∫ r in Icc 0 Δ, (elapsedGraph Ψ b χout χsource β r).adjoint u) ∧
        (∀ s : ℕ, ∀ W : SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q,
          (W = Q ∨ W = Q.adjoint) → ∀ u : SpacetimeL2 d q,
          MemVectorFourierSobolev ((s-o : ℕ) : ℝ) u →
            MemVectorFourierSobolev (s : ℝ) (W u) ∧
            vectorFourierSobolevNorm (s : ℝ) (W u) ≤ (Δ * C s) *
              (vectorFourierSobolevNorm ((s-o : ℕ) : ℝ) u +
                (1 + twoTimeOrderSeminorm o J (s + (fullLowReserve (d + 1) + 2)) b +
                  cNorm J (s + (fullLowReserve (d + 1) + 2)) (jointPhase Ψ)) * ‖u‖)) ∧
        ∀ u : graphTestSpace (d + 1) q,
          (Q (graphTestToLp u) =ᵐ[volume] fun x ↦ WithLp.toLp 2
            (retardedPhysicalIntegral Ψ b χout χsource β hs a₀ u x)) ∧
          ∀ v : graphTestSpace (d + 1) q,
            Integrable (fun ξ ↦ inner ℂ (WithLp.toLp 2 (sourceInputFourierTransform
              (graphTestToSchwartz (complexSourceMaskTest χsource hs v)) ξ))
              (WithLp.toLp 2 (reverseRetardedFrequency Ψ b χout β
                (fun x ↦ (u.val x).ofLp) a₀ (a₀ + Δ) ξ))) ∧
            inner ℂ (graphTestToLp v) (Q.adjoint (graphTestToLp u)) =
              ((2 * Real.pi) ^ (d + 1) : ℂ)⁻¹ * ∫ ξ,
                inner ℂ (WithLp.toLp 2 (sourceInputFourierTransform
                  (graphTestToSchwartz (complexSourceMaskTest χsource hs v)) ξ))
                  (WithLp.toLp 2 (reverseRetardedFrequency Ψ b χout β
                    (fun x ↦ (u.val x).ofLp) a₀ (a₀ + Δ) ξ)) := by
  classical
  have hcoverLow : ∀ p ∈ (tsupport χout ×ˢ tsupport χsource) ×ˢ tsupport β,
      ∃ i, ∃ t : ℝ, 1 ≤ t ∧ ∃ v ∈ Metric.closedBall (z i) (δ i),
        p = (v.1, t • v.2) ∧ 1 + ‖p.2‖ ≤ t := by
    intro p hp
    obtain ⟨i, t, ht, v, hv, he, hl, _⟩ := hcover p hp
    exact ⟨i, t, ht, v, hv, he, hl⟩
  obtain ⟨aL, haL, bL, habL, C₀, hC₀, hlow⟩ :=
    exists_retardedOperator_of_primitive_data R ℓ Bφ Btime Bφ Δ hΔ hℓ hRcell hε
      z δ hJ hU hJU χout χsource β ho hs hβ hocs hscs hβzero hYbox
      hcoverLow (fun i ↦ hβbound i _) hmap
  obtain ⟨aS, haS, bS, habS, hsob⟩ :=
    exists_elapsedGraph_integer_sobolev_constants_of_primitive_data
      (q := q) (ι := ι) R ℓ Btime Bφ Δ hΔ hBφ hℓ hRcell hε
  refine ⟨min aL aS, lt_min haL haS, max bL bS,
    (min_le_left _ _).trans_lt (habL.trans_le (le_max_left _ _)), C₀, hC₀, ?_⟩
  intro Ug Vg hUg hVg hball hrad Xouter X Dnormal Douter Dcore Ω
    hXouter hDouter hcXouter hcDouter hX hDn hcX hΩ hDcore hcDcore hCoreSub
    hXX hDDcore hcone hcoreCone hchart hposition hR hcollar hUΩ hcoverMixed
    hXsub hFsub M hM o ho'
  have hnormalCore : Dnormal ⊆ spatialPart ⁻¹' Dcore := subset_closure.trans hDDcore
  have hDD : closure Dnormal ⊆ spatialPart ⁻¹' Douter :=
    fun ξ hξ ↦ hCoreSub (hDDcore hξ)
  choose C hC using fun s ↦ hsob z δ hδ Ug Vg hUg hVg hball hrad
    Xouter X Dnormal Douter Dcore Ω hXouter hDouter hcXouter hcDouter
    hX hDn hcX hΩ hDcore hCoreSub hnormalCore hXX hDD hcone hcoreCone
    hchart hposition hR hcollar J U hJ hU hJU hUΩ hmap hcoverMixed
    χout χsource β ho hs hβ hocs hscs hβzero hXsub hFsub hYbox hβbound c hc hcover M hM o ho' s
  refine ⟨C, fun s ↦ (hC s).1, ?_⟩
  intro K hK htime hshell hmapK Ψ hΨ hhom hnear hφ b hb hbfinite hbM a₀ hout hzero
  have hshellL : ∀ j : ℕ, ∀ p ∈ X ×ˢ normalizedSourceBand Dnormal ((2 : ℝ)^j) aL bL,
      phasePairInclusion p ∈ K := by
    intro j p hp
    exact hshell j p ⟨hp.1, hp.2.1,
      (min_le_left _ _).trans_lt hp.2.2.1, hp.2.2.2.trans_le (le_max_left _ _)⟩
  have hshellS : ∀ j : ℕ, ∀ p ∈ X ×ˢ normalizedSourceBand Dnormal ((2 : ℝ)^j) aS bS,
      phasePairInclusion p ∈ K := by
    intro j p hp
    exact hshell j p ⟨hp.1, hp.2.1,
      (min_le_right _ _).trans_lt hp.2.2.1, hp.2.2.2.trans_le (le_max_right _ _)⟩
  have hXX' : X ⊆ Xouter := subset_closure.trans hXX
  have hΨU : ContDiffOn ℝ ∞ (jointPhase Ψ) U := hΨ.mono hUΩ
  have hhomU : ∀ t : ℝ, 0 < t → ∀ p ∈ U,
      Ψ p.1.1 p.1.2.1 p.1.2.2 (t • p.2) = t * jointPhase Ψ p :=
    fun t ht p hp ↦ hhom t ht p.1 (hUΩ hp).1 p.2 (hUΩ hp).2
  have hnormalized (j : ℕ) : ContDiffOn ℝ ∞
      (jointPhase (normalizedTwoTimePhase ((2 : ℝ)^j) Ψ)) U :=
    hΨU.congr (joint_normalizedTwoTimePhase_eqOn Ψ hhomU (by positivity))
  have hbudget (j : ℕ) : cNorm J (wholeImagePhaseReserve (d + 1))
      (jointPhase (normalizedTwoTimePhase ((2 : ℝ)^j) Ψ)) ≤ Bφ := by
    rw [cNorm_normalizedTwoTimePhase_eq Ψ hU hJU hhomU (by positivity)]
    exact (cNorm_mono_order (Nat.le_max_left _ _)).trans hφ
  have hφ2 : cNorm J 2 (jointPhase Ψ) ≤ Bφ :=
    (cNorm_mono_order (show 2 ≤ max (wholeImagePhaseReserve (d+1))
      (fullLowReserve (d+1)+o+2) by omega)).trans hφ
  have hprimitive (r : ℝ) (hr : r ∈ Icc 0 Δ) (x : E) (hx : x ∈ Xouter)
      (η : Euclidean d) (hη : η ∈ Douter) :
      ContDiffAt ℝ ∞ (jointPhase Ψ) ((x 0, x 0-r, spatialPart x), η) :=
    hΨ.contDiffAt ((hΩ.prod hDouter).mem_nhds ⟨hposition r hr x hx, hη⟩)
  have hmix : ∀ r ∈ Icc 0 Δ, ∀ x ∈ X, ∀ η ∈ Dcore,
      ‖fderiv ℝ (fun ζ ↦ fderiv ℝ (fun p : P ↦ Ψ p.1 p.2.1 p.2.2 ζ)
        (x 0, x 0-r, spatialPart x)) η‖ ≤ Bφ := by
    intro r hr x hx η hη
    exact (norm_twoTimePhase_mixed_le_of_normalized_cover Ψ hΩ hDouter hcone hΨ hhom
      hJ hU hJU hΨU (hposition r hr x (hXX' hx)) (hcoverMixed r hr x hx η hη)
      (le_refl 2)).trans hφ2
  have hbLow : twoTimeOrderSeminorm o J (fullLowReserve (d+1)) b ≤ M := by
    apply le_trans _ hbM
    apply Real.sSup_le _ (twoTimeOrderSeminorm_nonneg _ _ _ _)
    rintro _ ⟨t, rfl⟩
    exact (cNorm_mono_order (Nat.le_add_right _ _)).trans
      (cNorm_twoTimeOrderField_le (hbfinite _) t.2)
  obtain ⟨hlowBound, hmeas, hmeasAdj, χ, hχ, hχcs, hcut, hfixed,
    Q, hQnorm, hQ, hQadj, hstrong⟩ := hlow Xouter Dcore X Dnormal
      hXouter hDcore hcXouter hcDcore hX hDn hcX hXX hDDcore hXsub hFsub hR hcollar
      K hK htime hshellL hmapK Ψ
      (fun r hr x hx η hη ↦ hprimitive r hr x hx η (hCoreSub hη))
      (fun r hr x hx η hη ↦ hnear r hr x hx η (hCoreSub hη))
      (fun r hr x hx η hη t ht ↦ hhom t ht _ (hposition r hr x (hXX' hx)) _ (hCoreSub hη))
      hmix hnormalized hbudget o M b hb (hbfinite _) hbLow a₀ hout hzero
  have hsΨ : ∀ r ∈ Icc 0 Δ, ∀ x ∈ tsupport χout, ∀ ξ ∈ tsupport β,
      ContinuousAt (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
        Ψ p.1.1 p.1.2 p.2.1 p.2.2) ((x 0, x 0-r), (spatialPart x, spatialPart ξ)) := by
    intro r hr x hx ξ hξ
    exact ((hprimitive r hr x (hXX' (hXsub hx)) _
      (hCoreSub (hnormalCore (hFsub hξ)))).comp ((x 0, x 0-r), (spatialPart x, spatialPart ξ))
      (f := fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦ ((p.1.1, p.1.2, p.2.1), p.2.2))
      ((contDiffAt_fst.fst.prodMk (contDiffAt_fst.snd.prodMk contDiffAt_snd.fst)).prodMk
        contDiffAt_snd.snd)).continuousAt
  have hQS : Q = strongIntegral (elapsedGraph Ψ b χout χsource β) Δ (C₀ * M)
      hmeas hlowBound := by
    apply ContinuousLinearMap.ext
    intro u
    exact hQ u
  have hper := fun s ↦ (hC s).2 K hK htime hshellS hmapK Ψ hΨ hhom hnear hφ
    b hb hbfinite hbM
  have hintegrated := strongIntegral_and_adjoint_integer_sobolev_bounds hΔ
    hmeas hlowBound hmeasAdj o (fullLowReserve (d+1)+2) C
    (fun j ↦ 1 + twoTimeOrderSeminorm o J j b + cNorm J j (jointPhase Ψ))
    (fun s r hr u hu ↦ hper s r hr _ (Or.inl rfl) u hu)
    (fun s r hr u hu ↦ hper s r hr _ (Or.inr rfl) u hu)
  rw [← hQS] at hintegrated
  refine ⟨hlowBound, hmeas, hmeasAdj, ?_, Q, hQnorm, hQ, hQadj, ?_, ?_⟩
  · intro r hr u
    exact elapsedGraph_eq_uncutSpatialGraph_of_primitive_budgets z δ hJ
      Ψ b χout χsource β Δ hsΨ hb hs hβ hcoverLow (fun i ↦ hβbound i _) hmap
      o (hbfinite _) χ hχ hχcs hcut r hr u (hfixed r hr u)
  · intro s W hW u hu
    rcases hW with rfl | rfl
    · exact (hintegrated s u hu).1
    · exact (hintegrated s u hu).2
  · intro u
    obtain ⟨Rt, Ra, hRt, hRa, hRtlim, hRalim⟩ := hstrong u
    refine ⟨?_, ?_⟩
    · exact retardedOperator_eq_uncutPhysicalIntegral_of_primitive_budgets z δ hJ
        Ψ b χout χsource β Δ hΔ hsΨ hb ho.continuous hs hβ hocs hscs
        hcoverLow (fun i ↦ hβbound i _) hmap o (hbfinite _) χ hχ hχcs hcut
        a₀ hout hzero Q u ⟨Rt, hRt, hRtlim⟩
    · intro v
      exact retardedOperator_adjoint_pairing_reverseTriangle_of_primitive_budgets z δ hJ
        Ψ b χout χsource β Δ hΔ hsΨ hb ho.continuous hs hβ hocs
        hcoverLow (fun i ↦ hβbound i _) hmap o (hbfinite _) χ hχ hχcs hcut
        a₀ hout hzero Q u v ⟨Ra, hRa, hRalim⟩

end JanetCartan.RegularSector.Characteristic.EvolutionIntegral
