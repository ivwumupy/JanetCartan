module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.SelectedChart.Regularizations.Primitive
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteEvolution.PhysicalCutoff.RetardedOperators

/-!
# Graph regularizations of the retained collared amplitudes

The original physical right multiplier, section, chart and three buffered
matrices supply the primitive inputs. The new compact radial band is used only
to estimate the SAME matrices; no amplitude or chart is reconstructed.
Consumer: the supported-phase regularizations for
`app:ch_regular_base:eq:energy-complete-residual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6400000
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FiniteResidual.SelectedChart
open Characteristic Characteristic.UniformEvolution Characteristic.ResidualCoordinates
open ConicPhase ConicAmplitude FourierIntegral EvolutionIntegral SymbolBudgets
open WholeImageGeometry FullLowBounds KernelIdentification UncutTestAction
open FiniteMasks PrimitiveProfiles AmplitudeBounds FiniteEvolution.PhysicalCutoff
open FullAmplitudePrimitiveBudget.Local LowBounds.FrequencyCutoff
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Z" => RootState (Euclidean d)
local notation "T" => Characteristic.TwoTimePoint (Euclidean d)
local notation "Mat" => MetricTensor (d + 1)
local notation "H" => SpacetimeL2 d q

/-- Instantiate the full graph construction on the retained conic chart for
both the literal solver sum and third collared matrix. Compact smoothness of
the original buffered matrices proves their normalized budgets on the needed
band. Bounds are uniform in elapsed time and cutoff index; every cutoff is
`complexPhysicalCutoff`. The input fields are literal outputs retained by
`SelectedChartEvolutionAt` (`retarded-kernel`, `energy-complete-residual`). -/
theorem exists_retained_collared_graph_regularizations
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : Z) {b ρ src aperture : ℝ}
    (hb : 0 < b) (hρ : 0 < ρ) (hsrc : 0 < src)
    (hρb : ρ ≤ b) (hsrcρ : src ≤ ρ / 4) (hAp : 0 < aperture)
    (χout χsource : E → ℂ) (ho : ContDiff ℝ ∞ χout) (hs : ContDiff ℝ ∞ χsource)
    (hoc : HasCompactSupport χout) (hsc : HasCompactSupport χsource)
    (hout : tsupport χout ⊆ elapsedPhysicalBox z (retainedRadius b ρ / 2))
    (hslab : ∀ x, χout x ≠ 0 → x 0 ∈ Icc (z.1-src/2) ((z.1-src/2)+3*src/4))
    (R : ℝ) (hR : 0 < R)
    (hXbound : ∀ x ∈ elapsedPhysicalBox z (retainedRadius b ρ / 2), ‖x‖ ≤ R)
    (hYbound : ∀ y ∈ tsupport χsource, ∀ i : Fin (d+1), |y i| ≤ R)
    (index : Fin (d+1)) (mask : E → ℝ) (hm : ContDiff ℝ ∞ mask)
    (hcarrier : tsupport (mask ∘ physicalCoordinates index) ∩ sphere (0 : E) 1 ⊆
      fullAngularCone ℓ z.2.2 (retainedRadius b ρ / 4) (aperture / 2))
    (L : ℝ) (hL : 1 ≤ L)
    (hβsub : tsupport (fun ξ ↦ (dilatedConicMask mask (2*L) (physicalCoordinates index ξ) : ℂ)) ⊆
      retainedFrequencyDomain ℓ z (retainedRadius b ρ) aperture (1/2))
    (KQ : Set E) (Q : E → Fin (d+1) → Mat) (phaseCost : ℕ → ℝ)
    (h : Z → ℝ) (Φ : Z × ℝ → Z) (C : OpenPartialHomeomorph T T)
    (hbuffer : closedBall (z.1, z) b ⊆ C.target)
    (hsmooth : ContDiffOn ℝ ∞ (twoTimePhase C) C.target)
    (hdiff : ∀ p ∈ C.target, HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C p) p)
    (hnear : ∀ p ∈ closedBall (z.1, z) b, ‖twoTimePhaseMixed C p - 1‖ ≤ 1/2)
    (hphase : ∀ m, cNorm (closedBall (z.1, z) b) m (twoTimePhase C) ≤
      phaseCost m * (1 + cNorm KQ (m+1) Q))
    (hsourceTime : ∀ p ∈ C.target, (C.symm p).2.1 = p.2.1)
    (angular : Euclidean d → ℝ) (hang : ContDiff ℝ ∞ angular)
    (Fs : Fin 3 → T → Matrix (Fin q) (Fin q) ℂ)
    (hFs : ∀ j, ContDiff ℝ ∞ (Fs j))
    (hWs : ∀ j : Fin 3, ContDiff ℝ ∞ (collared ℓ (if j = 0 then 0 else 1) angular (Fs j)))
    (hsupport : ∀ j : Fin 3, tsupport (collared ℓ (if j = 0 then 0 else 1) angular (Fs j)) ⊆
      ConicPhase.domain ℓ (C.target ∩ C.symm ⁻¹'
        (ball z.1 (src/2) ×ˢ (ball z.1 (src/2) ×ˢ ball z.2 (src/2))))) :
    let β : E → ℂ := fun ξ ↦ (dilatedConicMask mask (2*L) (physicalCoordinates index ξ) : ℂ)
    let W : Bool → TwoTimeAmplitude d q := fun k ↦ if k then
      curryCharacteristicMatrix (collared ℓ 1 angular (Fs 2)) else
      curryCharacteristicMatrix (collared ℓ 0 angular (Fs 0)) +
        curryCharacteristicMatrix (collared ℓ 1 angular (Fs 1))
    ∃ D : Bool → ℝ, ∃ Treg : Bool → ℕ → ℝ → H →L[ℂ] H,
      (∀ k r, r ∈ Icc 0 (3*src/4) → ‖elapsedGraph (curriedPhase ℓ C) (W k) χout χsource β r‖ ≤ D k) ∧
      (∀ k j r, r ∈ Icc 0 (3*src/4) → ‖Treg k j r‖ ≤ D k) ∧
      (∀ k j r, r ∈ Icc 0 (3*src/4) → ∀ u : graphTestSpace (d+1) q,
        Treg k j r (graphTestToLp u) =ᵐ[volume] graphTestOutput (elapsedPhase (curriedPhase ℓ C) r)
          (frequencyCutFullAmplitude (complexPhysicalCutoff j) (elapsedAmplitude (W k) χout χsource β r)) u) ∧
      (∀ k j r, r ∈ Icc 0 (3*src/4) → ∀ u : graphTestSpace (d+1) q,
        (Treg k j r).adjoint (graphTestToLp u) =ᵐ[volume] fun y ↦ WithLp.toLp 2
          (reverseGraphOperator (elapsedPhase (curriedPhase ℓ C) r)
            (frequencyCutFullAmplitude (fun ξ ↦ star (complexPhysicalCutoff j ξ))
              (fun x y ξ ↦ (elapsedAmplitude (W k) χout χsource β r x y ξ).conjTranspose))
            (fun x ↦ (u.val x).ofLp) y)) ∧
      (∀ k r, r ∈ Icc 0 (3*src/4) → ∀ u, Tendsto (fun j ↦ Treg k j r u) atTop
        (𝓝 (elapsedGraph (curriedPhase ℓ C) (W k) χout χsource β r u))) ∧
      (∀ k r, r ∈ Icc 0 (3*src/4) → ∀ u, Tendsto (fun j ↦ (Treg k j r).adjoint u) atTop
        (𝓝 ((elapsedGraph (curriedPhase ℓ C) (W k) χout χsource β r).adjoint u))) ∧
      ∃ Op : Bool → H →L[ℂ] H,
        (∀ k, ‖Op k‖ ≤ (3*src/4) * D k) ∧
        (∀ k u, Op k u = elapsedGraphIntegral (3*src/4) (curriedPhase ℓ C) (W k) χout χsource β u) ∧
        (∀ k u, (Op k).adjoint u = ∫ r in Icc 0 (3*src/4),
          (elapsedGraph (curriedPhase ℓ C) (W k) χout χsource β r).adjoint u) ∧
        (∀ k (u : graphTestSpace (d+1) q), Op k (graphTestToLp u) =ᵐ[volume]
          fun x ↦ WithLp.toLp 2 (retardedPhysicalIntegral (curriedPhase ℓ C) (W k)
            χout χsource β hs (z.1-src/2) u x)) := by
  classical
  let ε := retainedRadius b ρ
  let Δ := 3 * src / 4
  let β : E → ℂ := fun ξ ↦ (dilatedConicMask mask (2*L) (physicalCoordinates index ξ) : ℂ)
  obtain ⟨hε, hεb, _hερ⟩ := retainedRadius_bounds hb hρ
  obtain ⟨hΔ, hΔε⟩ := UniformAmplitudes.retained_source_slab_bounds hsrc hρb hsrcρ
  change 0 < ε at hε
  change 0 < Δ at hΔ
  change Δ < ε at hΔε
  have hr (r : ℝ) (hr : r ∈ Icc 0 Δ) : r ∈ Icc 0 ε := ⟨hr.1, hr.2.trans hΔε.le⟩
  have hβ : ContDiff ℝ ∞ β :=
    Complex.ofRealCLM.contDiff.comp
      ((contDiff_dilatedConicMask hm (2*L)).comp (physicalCoordinates index).contDiff)
  have hβzero : (0 : E) ∉ tsupport β := by
    intro hz
    have := retainedFrequencyDomain_norm_lt ℓ (hβsub hz)
    norm_num at this
  have hcar : ∀ ξ ∈ tsupport (mask ∘ physicalCoordinates index) ∩ sphere (0 : E) 1,
      spatialPart ξ ∈ angularCone ℓ z.2.2 (ε/2) := by
    intro ξ hξ
    exact ⟨(hcarrier hξ).1.1, ball_subset_ball (by dsimp [ε]; linarith) (hcarrier hξ).1.2⟩
  obtain ⟨ca, hca, cb, _hcb, s, δ, _hδ, hball, hmap, _, hcover⟩ :=
    exists_retained_finite_shell_cover ℓ z hε (hoc.prod hsc)
      (fun _ hx ↦ hout hx.1) (mask ∘ physicalCoordinates index)
      (hm.comp (physicalCoordinates index).contDiff) hcar
  let ι := {p // p ∈ s}
  let centers : ι → Point (d+1) := fun p ↦ p.val.val
  let radii : ι → ℝ := fun p ↦ δ p.val
  let mix := retainedPhaseCost ℓ z ε (1/2) 2 phaseCost 2 * (1 + cNorm KQ 3 Q)
  obtain ⟨a, ha, b', hab', hprimitive⟩ :=
    exists_primitive_elapsed_graph_regularizations
      (q := q) (ι := ι) R (4*R) mix Δ (by positivity)
      (by apply (div_lt_iff₀ (by positivity : 0 < 4*R)).mpr; linarith)
      (by norm_num : (0 : ℝ) < 1/2)
  let sa := a / (1 + aperture + ‖z.2.2‖ + ε)
  let sb := (1 + ‖ℓ‖) * b'
  let ra := min ca (min sa (1/2))
  let rb := max cb (max sb 2)
  have hsa : 0 < sa := div_pos ha (by positivity)
  have hra : 0 < ra := lt_min hca (lt_min hsa (by norm_num))
  have hra_ca : ra ≤ ca := min_le_left _ _
  have hra_sa : ra ≤ sa := (min_le_right _ _).trans (min_le_left _ _)
  have hcb_rb : cb ≤ rb := le_max_left _ _
  have hsb_rb : sb ≤ rb := (le_max_left _ _).trans (le_max_right _ _)
  let J := bufferedJetSet ℓ z ε ra rb
  let U := bufferedBase z (2*ε) ×ˢ angularCone ℓ z.2.2 (2*ε)
  let K := elapsedJetSet ℓ z ε sa sb b'
  have hJ : IsCompact J := isCompact_bufferedJetSet _ _ _ _ _
  have hU : IsOpen U := isOpen_ball.prod (isOpen_angularCone _ _ _)
  have hJU : J ⊆ U := retained_bufferedJetSet_subset_open_product ℓ z hε hra
  have hK : IsCompact K := isCompact_elapsedJetSet _ _ _ _ _ _
  have hmapJ : ∀ r ∈ Icc 0 Δ, ∀ i : ι, MapsTo (elapsedPoint r)
      (closedBall (centers i) (radii i)) J := by
    intro r hr' i p hp
    exact retained_bufferedJetSet_mono_band ℓ z ε hra_ca hcb_rb
      (hmap r (hr r hr') i.val i.property hp)
  have hmapshell : ∀ r ∈ Icc 0 Δ, MapsTo (elapsedPoint r) K J := by
    intro r hr' p hp
    exact retained_bufferedJetSet_mono_band ℓ z ε hra_sa hsb_rb
      (elapsedJetSet_mapsTo ℓ (hr r hr') hp)
  have hshell : ∀ j : ℕ, ∀ p ∈ elapsedPhysicalBox z (ε/2) ×ˢ
      normalizedSourceBand (retainedFrequencyDomain ℓ z ε aperture (1/2)) ((2 : ℝ)^j) a b',
      phasePairInclusion p ∈ K :=
    (retained_shell_compacts ℓ hε hAp.le ha 0).2.2.2.1
  let Bφ := retainedPhaseCost ℓ z ε ra rb phaseCost (wholeImagePhaseReserve (d+1)) *
    (1 + cNorm KQ (wholeImagePhaseReserve (d+1)+1) Q)
  obtain ⟨D, _hD, hprim⟩ := hprimitive
    (phaseTimeConstant K (wholeImagePhaseReserve (d+1)) Δ) Bφ centers radii
    hJ hU hJU χout χsource β ho hs hβ hoc hβzero hYbound
    (by
      intro p hp
      obtain ⟨i, hi, t, ht, v, hv, he⟩ := hcover L hL p
        ⟨hp.1, tsupport_complex_physical_dilatedConicMask_subset mask index
          (zero_lt_one.trans_le hL) hp.2⟩
      exact ⟨⟨i, hi⟩, t, ht, v, hv, he.1, he.2.1⟩)
    (fun i ↦ boundedNormalizedSeminorm_physical_dilatedConicMask hm index hL
      (isCompact_closedBall _ _) (fun p hp ↦ by
        have hg := (hball i.val i.property hp).2.1
        intro hz
        change 0 < ℓ (spatialPartCLM p.2) at hg
        rw [hz, map_zero, map_zero] at hg
        exact (lt_irrefl _ hg)) _) hmapJ
  have hproduct := contDiffOn_retained_product ℓ (by positivity : 0 < 2*ε)
    (by have := four_mul_retainedRadius_le b ρ; dsimp [ε] at *; linarith) hbuffer hsmooth
  have hsΨ : ∀ r ∈ Icc 0 Δ, ∀ x ∈ elapsedPhysicalBox z ε,
      ∀ η ∈ angularCone ℓ z.2.2 (ε/2), ContDiffAt ℝ ∞ (jointPhase (curriedPhase ℓ C))
        ((x 0, x 0-r, spatialPart x), η) := by
    intro r hr' x hx η hη
    apply hproduct.contDiffAt (hU.mem_nhds ?_)
    exact ⟨elapsed_mem_bufferedBase (by positivity : 0 < 2*ε)
      ⟨hr'.1, by linarith [hr'.2]⟩
      ⟨ball_subset_ball (by linarith) hx.1, ball_subset_ball (by linarith) hx.2⟩, ⟨hη.1, ball_subset_ball (by linarith) hη.2⟩⟩
  have hmix : ∀ r ∈ Icc 0 Δ, ∀ x ∈ elapsedPhysicalBox z (ε/2),
      ∀ η ∈ angularCone ℓ z.2.2 (ε/2),
      ‖fderiv ℝ (fun ζ ↦ fderiv ℝ
        (fun p : ℝ × ℝ × Euclidean d ↦ curriedPhase ℓ C p.1 p.2.1 p.2.2 ζ)
        (x 0, x 0-r, spatialPart x)) η‖ ≤
          retainedPhaseCost ℓ z ε (1/2) 2 phaseCost 2 * (1 + cNorm KQ 3 Q) := by
    intro r hr' x hx η hη
    exact retained_mixed_coefficient_bound ℓ hε hεb
      hbuffer hsmooth KQ Q phaseCost hphase
      ⟨hr'.1, by linarith [hr'.2]⟩
      ⟨ball_subset_ball (by linarith) hx.1, ball_subset_ball (by linarith) hx.2⟩ hη
  have hrealize := hprim (elapsedPhysicalBox z ε) (angularCone ℓ z.2.2 (ε/2))
    (elapsedPhysicalBox z (ε/2)) (retainedFrequencyDomain ℓ z ε aperture (1/2))
    (isOpen_elapsedPhysicalBox _ _) (isOpen_angularCone _ _ _)
    (convex_elapsedPhysicalBox _ _) (convex_angularCone _ _ _)
    (isOpen_elapsedPhysicalBox _ _) (isOpen_retainedFrequencyDomain _ _ _ _ _)
    (convex_elapsedPhysicalBox _ _) (UniformEvolution.closure_elapsedPhysicalBox_half_subset hε)
    (closure_retainedFrequencyDomain_subset ℓ hε hAp (by norm_num))
    hout hβsub hXbound (fun ξ hξ ↦ retainedFrequencyDomain_norm_lt ℓ hξ)
    K hK le_rfl hshell hmapshell (curriedPhase ℓ C) hsΨ
    (fun r hr' x hx η hη ↦ retained_mixed_half_gap ℓ hb hρ
      hbuffer hsmooth hdiff hnear r (hr r hr') x hx η
        ⟨hη.1, ball_subset_ball (by linarith) hη.2⟩)
    (fun r _ x _ η _ t ht ↦ ConicPhase.extend_smul ℓ (twoTimePhase C)
      (x 0, (x 0-r, (spatialPart x, η))) ht)
    hmix
    (fun j ↦ by
      change ContDiffOn ℝ ∞ (jointPhase (normalizedTwoTimePhase ((2:ℝ)^j)
        (curriedExtend ℓ (twoTimePhase C)))) U
      rw [normalizedTwoTimePhase_curriedExtend ℓ (twoTimePhase C) (by positivity)]
      exact hproduct)
    (fun j ↦ normalized_retained_phase_coefficient_bound ℓ hε.le hra hεb
      hbuffer hsmooth KQ Q phaseCost hphase (by positivity : (0:ℝ) < 2^j) _)
  let V (j : Fin 3) := curryCharacteristicMatrix (collared ℓ (if j = 0 then 0 else 1) angular (Fs j))
  have hv (j : Fin 3) : ContDiff ℝ ∞ (jointAmplitude (V j)) :=
    (hWs j).comp (contDiff_fst.fst.prodMk (contDiff_fst.snd.fst.prodMk
      (contDiff_fst.snd.snd.prodMk contDiff_snd)))
  have hbudget (j : Fin 3) : BoundedTwoTimeOrderSeminorm (if j = 0 then 0 else 1)
      J (fullLowReserve (d+1)) (V j) := by
    apply (twoTimeOrderSeminorm_curry_collared_le ℓ _ hang hJ isOpen_univ
      (f := Fs j) ?_ (hFs j).contDiffOn _).1
    rintro p ⟨v, hv, rfl⟩
    exact ⟨(bufferedJetSet_normalizes ℓ hε.le hra).1 v hv, mem_univ _⟩
  let W : Bool → TwoTimeAmplitude d q := fun k ↦ if k then V 2 else V 0 + V 1
  have hW (k : Bool) : ContDiff ℝ ∞ (jointAmplitude (W k)) := by
    cases k
    · exact (hv 0).add (hv 1)
    · exact hv 2
  have hwbudget (k : Bool) : BoundedTwoTimeOrderSeminorm 0 J (fullLowReserve (d+1)) (W k) := by
    cases k
    · exact (solver_order_zero_bound hJ (hv 0) (hv 1) (hbudget 0) (hbudget 1)).1
    · exact (correction_order_zero_bound (hv 2) (hbudget 2)).1
  have hreg (k : Bool) := hrealize 0 (twoTimeOrderSeminorm 0 J (fullLowReserve (d+1)) (W k))
    (W k) (hW k) (hwbudget k) le_rfl
  choose Treg hl hb hr hra hlim hlima using hreg
  have hzeroV (j : Fin 3) (t s : ℝ) (y η : Euclidean d) (hs' : s ≤ z.1-src/2) :
      V j t s y η = 0 :=
    retained_amplitude_zero_before_source_half ℓ z src C hsourceTime _ (hsupport j) hs'
  have hzero (k : Bool) (t s : ℝ) (y η : Euclidean d) (hs' : s ≤ z.1-src/2) :
      W k t s y η = 0 := by
    cases k
    · change V 0 t s y η + V 1 t s y η = 0
      rw [hzeroV 0 t s y η hs', hzeroV 1 t s y η hs', add_zero]
    · exact hzeroV 2 t s y η hs'
  have hphasecont : ∀ r ∈ Icc 0 Δ, ∀ x ∈ tsupport χout, ∀ ξ ∈ tsupport β,
      ContinuousAt (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
        curriedPhase ℓ C p.1.1 p.1.2 p.2.1 p.2.2) ((x 0, x 0-r), (spatialPart x, spatialPart ξ)) := by
    intro r hr' x hx ξ hξ
    have hx' := hout hx
    have hξ' := closure_retainedFrequencyDomain_subset ℓ hε hAp (by norm_num : (0:ℝ) < 1/2)
      (subset_closure (hβsub hξ))
    exact ((hsΨ r hr' x
      ⟨ball_subset_ball (by linarith) hx'.1, ball_subset_ball (by linarith) hx'.2⟩ _ hξ').comp
      ((x 0, x 0-r), (spatialPart x, spatialPart ξ))
      (f := fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦ ((p.1.1, p.1.2, p.2.1), p.2.2))
      ((contDiffAt_fst.fst.prodMk (contDiffAt_fst.snd.prodMk contDiffAt_snd.fst)).prodMk
        contDiffAt_snd.snd)).continuousAt
  have hret (k : Bool) := exists_retardedOperator_of_regularizations (curriedPhase ℓ C) (W k)
    χout χsource β Δ hΔ.le hphasecont
    (fun _ _ _ _ _ _ ↦ ((hW k).comp ((contDiff_fst.fst.prodMk
      (contDiff_fst.snd.prodMk contDiff_snd.fst)).prodMk contDiff_snd.snd)).continuous.continuousAt)
    ho.continuous hs hβ hoc hsc complexPhysicalCutoff complexPhysicalCutoff_contDiff
    complexPhysicalCutoff_hasCompactSupport (Treg k) (hr k) (hra k) (hb k) (hlim k) (hlima k)
    (z.1-src/2) hslab (hzero k)
  choose Op hOp hOpint hOpadj hOpreg using fun k ↦ (hret k).2.2
  refine ⟨fun k ↦ D * twoTimeOrderSeminorm 0 J (fullLowReserve (d+1)) (W k), Treg,
    hl, hb, hr, hra, hlim, hlima, Op, hOp, hOpint, hOpadj, ?_⟩
  intro k u
  apply retardedOperator_eq_uncutPhysicalIntegral_of_primitive_budgets centers radii hJ
    (curriedPhase ℓ C) (W k) χout χsource β Δ hΔ.le hphasecont (hW k)
    ho.continuous hs hβ hoc hsc
    (by
      intro p hp
      obtain ⟨i, hi, t, ht, v, hv, he⟩ := hcover L hL p
        ⟨hp.1, tsupport_complex_physical_dilatedConicMask_subset mask index
          (zero_lt_one.trans_le hL) hp.2⟩
      exact ⟨⟨i, hi⟩, t, ht, v, hv, he.1, he.2.1⟩)
    (fun i ↦ boundedNormalizedSeminorm_physical_dilatedConicMask hm index hL
      (isCompact_closedBall _ _) (fun p hp ↦ by
        have hg := (hball i.val i.property hp).2.1
        intro hz
        change 0 < ℓ (spatialPartCLM p.2) at hg
        rw [hz, map_zero, map_zero] at hg
        exact (lt_irrefl _ hg)) _) hmapJ 0 (hwbudget k)
    complexPhysicalCutoff complexPhysicalCutoff_contDiff complexPhysicalCutoff_hasCompactSupport
    (fun _ _ _ ↦ rfl) (z.1-src/2) hslab (hzero k) (Op k) u
  obtain ⟨R, _RAdj, hR, _hRAdj, hlimR, _hlimRAdj⟩ := hOpreg k u
  exact ⟨R, hR, hlimR⟩

end JanetCartan.RegularSector.FiniteResidual.SelectedChart
