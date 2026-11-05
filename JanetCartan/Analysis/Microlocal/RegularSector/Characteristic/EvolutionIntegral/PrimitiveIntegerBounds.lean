module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.PrimitiveIntegerBounds.MixedJets
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.PrimitiveRetarded
public import JanetCartan.Analysis.Microlocal.FourierIntegral.PrimitiveRealization.Sobolev

/-!
# Primitive integer bounds for the actual elapsed graphs

The original smooth homogeneous two-time phase and spatial symbol supply every
analytic input of the whole-image integer theorem. The homogeneous frequency
cone and the buffered normal chart with its positive collar are distinct.
`Dcore` is the inner homogeneous spatial cone used by the integer theorem;
`Douter` is the larger convex smoothness cone. The compact normalized cover
lies inside the latter and covers rays of the former, retaining an angular margin.
The full masks, both physical positions, and the evaluation at the original
lower time `t-r` are retained. In particular, an original lower-time buffer
is preserved without a new truncation.

The same estimate holds for the literal Hilbert adjoint. Constants precede
the varying phase, symbol, and elapsed time. The consumer is
`strongIntegral_and_adjoint_integer_sobolev_bounds`; the parent still instantiates
these fixed charts together with its low retarded realization and integrates
in elapsed time. Sources: `app:ch_regular_base:lem:retarded-kernel`,
`app:ch_regular_base:eq:fixed-time-representation`, and
`app:ch_regular_base:eq:fio-input`.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 3200000
open Set MeasureTheory Filter JanetCartan.Pseudodifferential
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral
open FourierIntegral SymbolBudgets FullLowBounds WholeImageGeometry
open FullAmplitudePrimitiveBudget FullAmplitudePrimitiveBudget.Local PrimitiveProfiles GainOneProfiles
variable {d q : ℕ} {ι : Type*} [Fintype ι]
local notation "E" => Euclidean (d + 1)
local notation "P" => ℝ × ℝ × Euclidean d

/-- Uniform integer estimates for the actual elapsed graph and its literal
adjoint, from original primitive phase and symbol budgets. No per-time
operator bound, branch realization, elapsed seminorm, or raw mixed-jet bound
is an input. The original homogeneous phase and the fixed normalized cover
produce the latter. Both spatial orders use the same high reserve
`fullLowReserve (d+1)+2`, and natural-number subtraction gives `max(s-o,0)`.
The fixed chart inclusions and normalized carrier cover are geometric data;
the original phase and symbol producers supply the displayed primitive
smoothness, homogeneity, near-identity and seminorm assumptions. The phase
low order is the maximum of the whole-image reserve and
`fullLowReserve (d+1)+o+2`; it is independent of `s`.
Sources: `app:ch_regular_base:lem:retarded-kernel`,
`app:ch_regular_base:eq:fixed-time-representation`, and
`app:ch_regular_base:eq:fio-input`. -/
theorem exists_elapsedGraph_integer_sobolev_constants_of_primitive_data
    (R ℓ Btime Bφ Δ : ℝ) (hΔ : 0 ≤ Δ) (hBφ : 0 ≤ Bφ)
    (hℓ : 0 < ℓ) (hRcell : R / ℓ < 1 / 2) {ε : ℝ} (hε : 0 < ε) :
    ∃ a > 0, ∃ b > a,
      ∀ (z : ι → Point (d + 1)) (δ : ι → ℝ), (∀ i, 0 < δ i) →
      ∀ (Ug : ι → Set (Point (d + 1))) (Vg : Set (Point (d + 1))),
        (∀ i, IsOpen (Ug i)) → IsOpen Vg →
        (∀ i, Metric.closedBall (z i) (δ i) ⊆ Ug i) →
        (∀ i, ∀ t : ℝ, 1 ≤ t → ∀ p ∈ Ug i, (p.1, t • p.2) ∈ Vg) →
      ∀ (Xouter X Dnormal : Set E) (Douter Dcore : Set (Euclidean d)) (Ω : Set P),
        IsOpen Xouter → IsOpen Douter → Convex ℝ Xouter → Convex ℝ Douter →
        IsOpen X → IsOpen Dnormal → Convex ℝ X → IsOpen Ω →
        IsOpen Dcore → Dcore ⊆ Douter → Dnormal ⊆ spatialPart ⁻¹' Dcore →
        closure X ⊆ Xouter → closure Dnormal ⊆ spatialPart ⁻¹' Douter →
        (∀ t : ℝ, 0 < t → ∀ η ∈ Douter, t • η ∈ Douter) →
        (∀ t : ℝ, 0 < t → ∀ η ∈ Dcore, t • η ∈ Dcore) →
        (∀ p ∈ Vg, p.1.1 ∈ X ∧ spatialPart p.2 ∈ Dcore) →
        (∀ r ∈ Icc 0 Δ, ∀ x ∈ Xouter, (x 0, x 0-r, spatialPart x) ∈ Ω) →
        (∀ x ∈ X, ‖x‖ ≤ R) → (∀ ξ ∈ Dnormal, ε < ‖ξ‖) →
      ∀ (J U : Set (TwoTimePoint d)), IsCompact J → IsOpen U →
        J ⊆ U → U ⊆ Ω ×ˢ Douter →
        (∀ r ∈ Icc 0 Δ, ∀ i, MapsTo (elapsedPoint r) (Metric.closedBall (z i) (δ i)) J) →
        (∀ r ∈ Icc 0 Δ, ∀ x ∈ X, ∀ η ∈ Dcore,
          ∃ t : ℝ, 0 < t ∧ ∃ ζ ∈ Douter,
            ((x 0, x 0-r, spatialPart x), ζ) ∈ J ∧ η = t • ζ) →
      ∀ (χout χsource β : E → ℂ),
        ContDiff ℝ ∞ χout → ContDiff ℝ ∞ χsource → ContDiff ℝ ∞ β →
        HasCompactSupport χout → HasCompactSupport χsource →
        (0 : E) ∉ tsupport β →
        tsupport χout ⊆ X → tsupport β ⊆ Dnormal →
        (∀ y ∈ tsupport χsource, ∀ i : Fin (d + 1), |y i| ≤ R) →
        (∀ i j, BoundedNormalizedSeminorm (Metric.closedBall (z i) (δ i)) j (jointMultiplier β)) →
      ∀ c : ℝ, 1 ≤ c →
        (∀ p ∈ (tsupport χout ×ˢ tsupport χsource) ×ˢ tsupport β,
          ∃ i, ∃ t : ℝ, 1 ≤ t ∧ ∃ v ∈ Metric.closedBall (z i) (δ i),
            p = (v.1, t • v.2) ∧ 1 + ‖p.2‖ ≤ t ∧ t ≤ c * (1 + ‖p.2‖)) →
      ∀ M : ℝ, 0 ≤ M → ∀ o : ℕ, (o = 0 ∨ o = 1) →
      ∀ s : ℕ, ∃ C > 0,
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
      ∀ r ∈ Icc 0 Δ, ∀ W : SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q,
        (W = elapsedGraph Ψ b χout χsource β r ∨
          W = (elapsedGraph Ψ b χout χsource β r).adjoint) →
      ∀ u : SpacetimeL2 d q, MemVectorFourierSobolev ((s-o : ℕ) : ℝ) u →
        MemVectorFourierSobolev (s : ℝ) (W u) ∧
          vectorFourierSobolevNorm (s : ℝ) (W u) ≤ C *
            (vectorFourierSobolevNorm ((s-o : ℕ) : ℝ) u +
              (1 + twoTimeOrderSeminorm o J (s + (fullLowReserve (d + 1) + 2)) b +
                cNorm J (s + (fullLowReserve (d + 1) + 2)) (jointPhase Ψ)) * ‖u‖) := by
  classical
  obtain ⟨gap, hgap, hgeometry⟩ := exists_elapsedPhase_buffered_geometry d
  obtain ⟨_, _, B, _hB, hmixed⟩ := exists_elapsedPhase_mixed_bounds d Bφ
  obtain ⟨a, ha, bShell, hab, hbound⟩ :=
    exists_fullGraph_integer_sobolev_constants_of_wholeImage_phase (r := q) (ι := ι)
      (Nat.succ_pos d) R ℓ (1 + Bφ) (Btime + Bφ) hℓ hRcell hgap hε
  refine ⟨a, ha, bShell, hab, ?_⟩
  intro z δ hδ Ug Vg hUg hVg hball hrad Xouter X Dnormal Douter Dcore Ω
    hXouter hDouter hcXouter hcDouter hX hDn hcX hΩ hDcore hCoreSub hnormalCore hXX hDD hcone hcoreCone hchart hposition
    hR hcollar J U hJ hU hJU hUΩ hmap hcoverMixed χout χsource β ho hs hβ
    hocs hscs hβzero hXsub hFsub hYbox hβbound c hc hcover M hM o ho' s
  let ca := ∑ i, amplitudeMaskConstant (Metric.closedBall (z i) (δ i))
    (fullLowReserve (d + 1) + o) χout χsource β
  let ct := ∑ i, phaseTimeConstant (Metric.closedBall (z i) (δ i))
    (fullLowReserve (d + 1) + o + 2) Δ
  have hca : 0 ≤ ca := Finset.sum_nonneg fun _ _ ↦ amplitudeMaskConstant_nonneg _ _ _ _ _
  have hct : 0 ≤ ct := Finset.sum_nonneg fun _ _ ↦ phaseTimeConstant_nonneg _ _ hΔ
  have hD : IsOpen (spatialPart ⁻¹' Dcore : Set E) :=
    hDcore.preimage spatialProjection.continuous
  have hcone' : ∀ t : ℝ, 0 < t → ∀ ξ ∈ (spatialPart ⁻¹' Dcore : Set E),
      t • ξ ∈ (spatialPart ⁻¹' Dcore : Set E) := by
    intro t ht ξ hξ
    change spatialPart (t • ξ) ∈ Dcore
    rw [spatialPart_smul]
    exact hcoreCone t ht _ hξ
  obtain ⟨Cg, hCg, hg⟩ := hbound z δ hδ Ug Vg hUg hVg hball hrad
    X (spatialPart ⁻¹' Dcore) hX hD hcX hchart hcone' (ct + Bφ + ca * M) B c
    (by positivity) hc o ho' s
  obtain ⟨Ch, hCh, hh⟩ := exists_elapsed_graph_high_constant (q := q)
    z δ hJ hU hJU (V := univ) (fun _ _ _ _ ↦ mem_univ _) hΔ hmap
    χout χsource β ho hs hβ (s + (fullLowReserve (d + 1) + 2))
    (fun i ↦ hβbound i _)
  refine ⟨Cg * Ch, mul_pos hCg (lt_of_lt_of_le zero_lt_one hCh), ?_⟩
  intro K hK htime hshell hmapK Ψ hΨ hhom hnear hφ b hb hbfinite hbM r hr W hW u hu
  have hXX' : X ⊆ Xouter := subset_closure.trans hXX
  have hsp : Dnormal ⊆ spatialPart ⁻¹' Dcore := hnormalCore
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
  have hφlow : cNorm J (fullLowReserve (d + 1) + o + 2) (jointPhase Ψ) ≤ Bφ :=
    (cNorm_mono_order (Nat.le_max_right _ _)).trans hφ
  have hφ2 : cNorm J 2 (jointPhase Ψ) ≤ Bφ :=
    (cNorm_mono_order (by omega : 2 ≤ fullLowReserve (d + 1) + o + 2)).trans hφlow
  have hprimitive (r : ℝ) (hr : r ∈ Icc 0 Δ) (x : E) (hx : x ∈ Xouter)
      (η : Euclidean d) (hη : η ∈ Douter) :
      ContDiffAt ℝ ∞ (jointPhase Ψ) ((x 0, x 0-r, spatialPart x), η) :=
    hΨ.contDiffAt ((hΩ.prod hDouter).mem_nhds ⟨hposition r hr x hx, hη⟩)
  have hsΨ : ∀ r ∈ Icc 0 Δ, ∀ x ∈ Xouter, ∀ η ∈ Douter, ContDiffAt ℝ ∞
      (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦ Ψ p.1.1 p.1.2 p.2.1 p.2.2)
      ((x 0, x 0-r), (spatialPart x, η)) := by
    intro r hr x hx η hη
    exact (hprimitive r hr x hx η hη).comp ((x 0, x 0-r), (spatialPart x, η))
      (f := fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦ ((p.1.1, p.1.2, p.2.1), p.2.2))
      ((contDiffAt_fst.fst.prodMk (contDiffAt_fst.snd.prodMk contDiffAt_snd.fst)).prodMk contDiffAt_snd.snd)
  have hmix : ∀ r ∈ Icc 0 Δ, ∀ x ∈ X, ∀ η ∈ Dcore,
      ‖fderiv ℝ (fun ζ ↦ fderiv ℝ (fun p : P ↦ Ψ p.1 p.2.1 p.2.2 ζ)
        (x 0, x 0-r, spatialPart x)) η‖ ≤ Bφ := by
    intro r hr x hx η hη
    exact (norm_twoTimePhase_mixed_le_of_normalized_cover Ψ hΩ hDouter hcone hΨ hhom
      hJ hU hJU hΨU (hposition r hr x (hXX' hx)) (hcoverMixed r hr x hx η hη)
      (le_refl 2)).trans hφ2
  have hi := hmixed Ψ Δ X Dcore hDcore
    (fun r hr x hx η hη ↦ hsΨ r hr x (hXX' hx) η (hCoreSub hη))
    (fun r hr x hx η hη ↦ hnear r hr x (hXX' hx) η (hCoreSub hη))
    (fun r hr x hx η hη ↦ (norm_elapsedTimeDerivative_row_le Ψ r x η hDouter (hCoreSub hη)
      (hprimitive r hr x (hXX' hx))).trans (hmix r hr x hx η hη))
  obtain ⟨hO, hbuffer, hgeom⟩ := hgeometry Ψ Δ Xouter Douter
    hXouter hDouter hcXouter hcDouter hsΨ hnear X Dnormal hXX hDD
  have hphase := wholeImagePhaseReserve_elapsedPhase hK hJ hU hJU Ψ hnormalized
    hbudget a bShell hshell hr (hmapK r hr)
  have hchartBall (i : ι) (p : Point (d + 1)) (hp : p ∈ Metric.closedBall (z i) (δ i)) :
      p.1.1 ∈ X ∧ spatialPart p.2 ∈ Dcore := by
    have hv := hrad i 1 le_rfl p (hball i hp)
    simp only [one_smul] at hv
    exact hchart p hv
  have hlS (i : ι) : cNorm (Metric.closedBall (z i) (δ i))
      (fullLowReserve (d + 1) + o + 2) (fun p ↦ elapsedPhase Ψ r p.1.1 p.2) ≤
        ct + Bφ + ca * M := by
    have ht : phaseTimeConstant (Metric.closedBall (z i) (δ i))
        (fullLowReserve (d + 1) + o + 2) Δ ≤ ct :=
      Finset.single_le_sum (fun k _ ↦ phaseTimeConstant_nonneg
        (Metric.closedBall (z k) (δ k)) (fullLowReserve (d + 1) + o + 2) hΔ) (Finset.mem_univ i)
    exact (cNorm_elapsedPhase_le (isCompact_closedBall _ _) hJ hU hJU Ψ hΨU hr
      (hmap r hr i) _).trans
      ((add_le_add ht hφlow).trans (le_add_of_nonneg_right (mul_nonneg hca hM)))
  have haBudget (i : ι) (j : ℕ) :
      (if o = 0 then BoundedNormalizedSeminorm (Metric.closedBall (z i) (δ i)) j
        (uncurry (elapsedAmplitude b χout χsource β r))
      else BoundedOrderMinusOneSeminorm (Metric.closedBall (z i) (δ i)) j
        (elapsedAmplitude b χout χsource β r)) ∧
      (if o = 0 then normalizedSeminorm (Metric.closedBall (z i) (δ i)) j
        (uncurry (elapsedAmplitude b χout χsource β r))
      else orderMinusOneSeminorm (Metric.closedBall (z i) (δ i)) j
        (elapsedAmplitude b χout χsource β r)) ≤
      amplitudeMaskConstant (Metric.closedBall (z i) (δ i)) j χout χsource β *
        twoTimeOrderSeminorm o J j b := by
    rcases ho' with rfl | rfl
    · simpa only [↓reduceIte, twoTimeOrderSeminorm_zero] using
        elapsedAmplitude_normalizedSeminorm_le (isCompact_closedBall _ _) hJ hU hJU
          (V := univ) (fun _ _ _ _ ↦ mem_univ _) j r b χout χsource β ho hs hβ
          (hβbound i j) hb.contDiffOn
          (by simpa only [BoundedTwoTimeOrderSeminorm, twoTimeOrderField, pow_zero, one_smul,
            BoundedNormalizedSeminorm] using hbfinite j) (hmap r hr i)
    · simpa only [Nat.one_ne_zero, ↓reduceIte] using
        elapsedAmplitude_orderMinusOneSeminorm_le (isCompact_closedBall _ _) hJ hU hJU
          (V := univ) (fun _ _ _ _ ↦ mem_univ _) j r b χout χsource β ho hs hβ
          (hβbound i j) hb.contDiffOn (hbfinite j) (hmap r hr i)
  have hlA (i : ι) : (if o = 0 then
      normalizedSeminorm (Metric.closedBall (z i) (δ i)) (fullLowReserve (d + 1))
        (uncurry (elapsedAmplitude b χout χsource β r))
      else orderMinusOneSeminorm (Metric.closedBall (z i) (δ i)) (fullLowReserve (d + 1) + 1)
        (elapsedAmplitude b χout χsource β r)) ≤ ct + Bφ + ca * M := by
    have hcai : amplitudeMaskConstant (Metric.closedBall (z i) (δ i))
        (fullLowReserve (d + 1) + o) χout χsource β ≤ ca :=
      Finset.single_le_sum (fun k _ ↦ amplitudeMaskConstant_nonneg
        (Metric.closedBall (z k) (δ k)) (fullLowReserve (d + 1) + o) χout χsource β) (Finset.mem_univ i)
    have hh := (haBudget i (fullLowReserve (d + 1) + o)).2
    have hh' := hh.trans (mul_le_mul hcai hbM (twoTimeOrderSeminorm_nonneg _ _ _ _) hca)
    have hh'' := hh'.trans (show ca * M ≤ ct + Bφ + ca * M from le_add_of_nonneg_left (add_nonneg hct hBφ))
    rcases ho' with rfl | rfl <;> simpa only [Nat.add_zero, Nat.one_ne_zero, ↓reduceIte] using hh''
  have hg' := hg (tsupport χout) (tsupport χsource) (tsupport β) hocs hscs hYbox
    (isClosed_tsupport _) hβzero hXsub Dnormal (Xouter ×ˢ (spatialPart ⁻¹' Douter))
    hDn hsp hFsub hO hbuffer (elapsedPhase Ψ r) (hgeom r hr).1
    (elapsedPhase_contDiffOn Ψ r (fun x hx η hη ↦ hsΨ r hr x (hXX' hx) η (hCoreSub hη)))
    (fun t ht x hx ξ hξ ↦ elapsedPhase_smul Ψ r t x ξ
      (hhom t ht _ (hposition r hr x (hXX' hx)) _ (hCoreSub hξ)))
    (fun x hx ξ hξ ↦ (hi r hr x hx ξ hξ).1)
    (fun i p hp ↦ (hi r hr _ (hchartBall i p hp).1 _ (hchartBall i p hp).2).2.2)
    hlS
    (fun x hx ξ hξ ↦ (norm_elapsedPhase_mixed_fderiv_le Ψ r x ξ hDouter (hCoreSub (hsp hξ))
      (hprimitive r hr x (hXX' hx))).trans (add_le_add le_rfl (hmix r hr x hx _ (hsp hξ))))
    (fun x hx y hy ↦ ((hgeom r hr).2 x hx y hy).1)
    (fun x hx y hy ξ hξ ↦ ((hgeom r hr).2 x hx y hy).2 ξ hξ)
    hcollar (fun j p hp k hk ↦ (hphase j p hp k hk).trans (add_le_add htime le_rfl)) hR
    (elapsedAmplitude b χout χsource β r)
    (elapsedAmplitude_forwardAdmissible b χout χsource β hb ho hs hβ r)
    (fun i j ↦ (haBudget i j).1) hlA (fun ξ ↦ 1 + ‖ξ‖)
    (fun ξ ↦ le_add_of_nonneg_right (norm_nonneg ξ))
    (fun ξ ↦ le_add_of_nonneg_left zero_le_one) hcover W hW u hu
  refine ⟨hg'.1, hg'.2.trans ?_⟩
  have hhigh := hh o ho' Ψ b hΨU hb.contDiffOn (hbfinite _) r hr
  have hu0 : 0 ≤ vectorFourierSobolevNorm ((s-o : ℕ) : ℝ) u := by
    exact norm_nonneg _
  calc
    _ ≤ Cg * (vectorFourierSobolevNorm ((s-o : ℕ) : ℝ) u +
        (Ch * (1 + twoTimeOrderSeminorm o J (s + (fullLowReserve (d + 1) + 2)) b +
          cNorm J (s + (fullLowReserve (d + 1) + 2)) (jointPhase Ψ))) * ‖u‖) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl
        (mul_le_mul_of_nonneg_right hhigh (norm_nonneg u))) hCg.le
    _ ≤ Cg * (Ch * vectorFourierSobolevNorm ((s-o : ℕ) : ℝ) u +
        (Ch * (1 + twoTimeOrderSeminorm o J (s + (fullLowReserve (d + 1) + 2)) b +
          cNorm J (s + (fullLowReserve (d + 1) + 2)) (jointPhase Ψ))) * ‖u‖) :=
      mul_le_mul_of_nonneg_left (add_le_add (le_mul_of_one_le_left hu0 hCh) le_rfl) hCg.le
    _ = _ := by ring

end JanetCartan.RegularSector.Characteristic.EvolutionIntegral
