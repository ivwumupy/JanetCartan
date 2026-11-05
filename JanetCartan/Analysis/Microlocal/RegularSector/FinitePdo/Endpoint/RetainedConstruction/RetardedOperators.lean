module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformEvolution.RetardedOperators
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteEvolution.PhysicalCutoff.Multiplier
public import JanetCartan.Analysis.Microlocal.RegularSector.FinitePdo.Endpoint.RetainedConstruction.Coverage

/-!
# Signed realization with the exact physical shoulder

Specialize the existing separated-budget primitive constructor to the physical
multiplier, using the retained shell geometry, phase budgets and source-time
buffer. The canonical finite cover covers its full closed support, while the
normalized budgets are proved for the physical multiplier itself. Source
multiplication remains inside the two-position amplitude, before the Fourier
multiplier. No operator composition or cutoff commutation is used.
Sources: `app:ch_regular_base:lem:retarded-kernel` and
`app:ch_regular_base:eq:fixed-time-representation` in `paper-v2.tex`.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 6400000
open Set Metric MeasureTheory Filter JanetCartan.Pseudodifferential
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FinitePdo.RetainedConstruction
open Characteristic Characteristic.UniformEvolution Characteristic.ResidualCoordinates
open ConicPhase FourierIntegral EvolutionIntegral SymbolBudgets
open WholeImageGeometry FullLowBounds KernelIdentification UncutTestAction
open FiniteMasks PrimitiveProfiles AmplitudeBounds
open FullAmplitudePrimitiveBudget.Local LowBounds.FrequencyCutoff
open FiniteEvolution.PhysicalCutoff
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Z" => RootState (Euclidean d)
local notation "T" => Characteristic.TwoTimePoint (Euclidean d)
local notation "Mat" => MetricTensor (d + 1)

/-- Construct the signed retarded realization for the literal physical
multiplier at threshold `2*L`. All geometric and amplitude inputs are the
same-witness outputs of `UniformAmplitudes`; the physical multiplier budgets
and cover are discharged here. The fixed low order and single-high profile
are exactly those of `UniformEvolution` (`retarded-kernel`). The actual
finite shell cover also supplies endpoint normalization on these SAME `ra,rb`,
after enlarging the original band by the prescribed positive lower bound
and upper bound, using `ra = min bandFloor (min ca (min sa (1/2)))` and
`rb = max bandCeiling (max cb (max sb 2))`, together with
`retainedRadius b ρ ≤ ρ/2`. The carrier's nonemptiness is supplied by the
output/source plateaux in the local constructor. Consumer:
`exists_physical_local_solver_and_residual_with_diagonal`. -/
theorem exists_physical_signed_retarded_operators_with_diagonal_on_enlarged_band
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : Z) {b ρ src aperture : ℝ}
    (hb : 0 < b) (hρ : 0 < ρ) (hsrc : 0 < src)
    (hρb : ρ ≤ b) (hsrcρ : src ≤ ρ / 4) (hAp : 0 < aperture)
    (χout χsource : E → ℂ) (ho : ContDiff ℝ ∞ χout) (hs : ContDiff ℝ ∞ χsource)
    (hoc : HasCompactSupport χout) (hsc : HasCompactSupport χsource)
    (hXne : (tsupport χout ×ˢ tsupport χsource).Nonempty)
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
    (phaseCost : ℕ → ℝ) (hphaseCost : ∀ m, 0 < phaseCost m)
    (M : ℝ) (hM : 0 ≤ M)
    (bandFloor bandCeiling : ℝ) (hbandFloor : 0 < bandFloor) :
    ∃ ra > (0 : ℝ), ∃ rb > ra,
      ra ≤ bandFloor ∧ bandCeiling ≤ rb ∧
      DiagonalFrequencyCoverage ℓ z.2.2 (ρ/2) ra rb
        (fun ξ ↦ (dilatedConicMask mask (2*L) (physicalCoordinates index ξ) : ℂ)) ∧
      ∀ (D : ℕ → ℝ), (∀ m, 0 < D m) →
      ∀ o : ℕ, (o = 0 ∨ o = 1) → ∃ A₀ > (0 : ℝ), ∃ A : ℕ → ℝ,
        (∀ s, 0 < A s) ∧
      ∀ (KQ : Set E) (Q : E → Fin (d+1) → Mat) (B : E → Mat),
        cNorm KQ (retardedCoefficientOrder d) Q ≤ M →
        cNorm KQ (retardedCoefficientOrder d) B ≤ M →
      ∀ (h : Z → ℝ) (Φ : Z × ℝ → Z) (C : OpenPartialHomeomorph T T),
        closedBall (z.1, z) b ⊆ C.target →
        ContDiffOn ℝ ∞ (twoTimePhase C) C.target →
        (∀ p ∈ C.target, HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C p) p) →
        (∀ p ∈ closedBall (z.1, z) b, ‖twoTimePhaseMixed C p - 1‖ ≤ 1/2) →
        (∀ m, cNorm (closedBall (z.1, z) b) m (twoTimePhase C) ≤
          phaseCost m * (1 + cNorm KQ (m+1) Q)) →
        (∀ p ∈ C.target, (C.symm p).2.1 = p.2.1) →
      ∀ W : T → Matrix (Fin q) (Fin q) ℂ,
        ContDiff ℝ ∞ W →
        tsupport W ⊆ ConicPhase.domain ℓ (C.target ∩ C.symm ⁻¹'
          (ball z.1 (src/2) ×ˢ (ball z.1 (src/2) ×ˢ ball z.2 (src/2)))) →
        (∀ m, BoundedTwoTimeOrderSeminorm o (bufferedJetSet ℓ z (ρ/2) ra rb) m
          (curryCharacteristicMatrix W) ∧
          twoTimeOrderSeminorm o (bufferedJetSet ℓ z (ρ/2) ra rb) m
            (curryCharacteristicMatrix W) ≤ D m * retardedCoefficientProfile KQ Q B m) →
      ∃ Op : SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q,
        RetainedSignedRetardedBounds KQ Q B (3*src/4) (z.1-src/2)
          (curriedPhase ℓ C) (curryCharacteristicMatrix W) χout χsource
          (fun ξ ↦ (dilatedConicMask mask (2*L) (physicalCoordinates index ξ) : ℂ)) hs o A₀ A Op := by
  let ε := retainedRadius b ρ
  let Δ := 3 * src / 4
  let β : E → ℂ := fun ξ ↦ (dilatedConicMask mask (2*L) (physicalCoordinates index ξ) : ℂ)
  obtain ⟨hε, hεb, hερ⟩ := retainedRadius_bounds hb hρ
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
  obtain ⟨ca, hca, cb, hcb, s, δ, hδ, hball, hmap, _, hcover, hdiagonal⟩ :=
    exists_physical_finite_shell_cover_with_diagonal ℓ z hε (hoc.prod hsc) hXne
      (fun _ hx ↦ hout hx.1) index mask hm hcar
  let ι := {p // p ∈ s}
  let centers : ι → Point (d+1) := fun p ↦ p.val.val
  let radii : ι → ℝ := fun p ↦ δ p.val
  let mix := retainedPhaseCost ℓ z ε (1/2) 2 phaseCost 2 * (1+M)
  obtain ⟨a, ha, b', hab', hprimitive⟩ :=
    exists_retardedOperator_signed_integer_bounds_of_separated_budgets
      (q := q) (ι := ι) R (4*R) mix Δ hΔ.le (by positivity)
      (by apply (div_lt_iff₀ (by positivity : 0 < 4*R)).mpr; linarith)
      (by norm_num : (0 : ℝ) < 1/2)
  let sa := a / (1 + aperture + ‖z.2.2‖ + ε)
  let sb := (1 + ‖ℓ‖) * b'
  let ra := min bandFloor (min ca (min sa (1/2)))
  let rb := max bandCeiling (max cb (max sb 2))
  have hsa : 0 < sa := div_pos ha (by positivity)
  have hra : 0 < ra := lt_min hbandFloor (lt_min hca (lt_min hsa (by norm_num)))
  have hra_old : ra ≤ min ca (min sa (1/2)) := min_le_right _ _
  have hra_ca : ra ≤ ca := hra_old.trans (min_le_left _ _)
  have hra_sa : ra ≤ sa := hra_old.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hra_one : ra ≤ 1 := hra_old.trans
    (((min_le_right _ _).trans (min_le_right _ _)).trans (by norm_num))
  have hrb_old : max cb (max sb 2) ≤ rb := le_max_right _ _
  have hcb_rb : cb ≤ rb := (le_max_left _ _).trans hrb_old
  have hsb_rb : sb ≤ rb := ((le_max_left _ _).trans (le_max_right _ _)).trans hrb_old
  have hone_rb : 1 ≤ rb := (by norm_num : (1 : ℝ) ≤ 2).trans
    (((le_max_right _ _).trans (le_max_right _ _)).trans hrb_old)
  have hrab : ra < rb := (hra_ca.trans_lt hcb).trans_le hcb_rb
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
  have hcoverage : DiagonalFrequencyCoverage ℓ z.2.2 ε ca cb β := hdiagonal L hL
  refine ⟨ra, hra, rb, hrab, min_le_left _ _, le_max_left _ _, hcoverage.mono hερ hra_ca hcb_rb, ?_⟩
  intro D hD o ho'
  let n := max (wholeImagePhaseReserve (d+1)) (fullLowReserve (d+1)+o+2)
  let Bφ := retainedPhaseCost ℓ z ε ra rb phaseCost n * (1+M)
  let Mamp := D (fullLowReserve (d+1)+o) * (1+2*M)
  have hBφ : 0 ≤ Bφ := mul_nonneg (retainedPhaseCost_pos ℓ z ε ra rb hphaseCost n).le (by positivity)
  have hMamp : 0 < Mamp := mul_pos (hD _) (by positivity)
  obtain ⟨C₀, hC₀, hprim⟩ := hprimitive
    (phaseTimeConstant K (wholeImagePhaseReserve (d+1)) Δ) Bφ hBφ centers radii
    (fun i ↦ hδ i.val) hJ hU hJU χout χsource β ho hs hβ hoc hsc hβzero hYbound
    (fun i m ↦ boundedNormalizedSeminorm_physical_dilatedConicMask hm index hL
      (isCompact_closedBall _ _) (fun p hp ↦ by
        have hg := (hball i.val i.property hp).2.1
        intro hz
        change 0 < ℓ (spatialPartCLM p.2) at hg
        rw [hz, map_zero, map_zero] at hg
        exact (lt_irrefl _ hg)) m) 1 le_rfl
    (by
      intro p hp
      obtain ⟨i, hi, t, ht, v, hv, he⟩ := hcover L hL p
        ⟨hp.1, tsupport_complex_physical_dilatedConicMask_subset mask index
          (zero_lt_one.trans_le hL) hp.2⟩
      exact ⟨⟨i, hi⟩, t, ht, v, hv, he⟩) hmapJ
  let Vg := retainedGraphDomain ℓ z ε
  have hcore : angularCone ℓ z.2.2 (ε/2) ⊆ angularCone ℓ z.2.2 (2*ε) :=
    fun _ hη ↦ ⟨hη.1, ball_subset_ball (by linarith) hη.2⟩
  obtain ⟨Cbound, hCbound, hrealize⟩ := hprim (fun _ ↦ Vg) Vg
    (fun _ ↦ isOpen_retainedGraphDomain _ _ _) (isOpen_retainedGraphDomain _ _ _)
    (fun i ↦ hball i.val i.property)
    (fun _ t ht _ hp ↦ smul_mem_retainedGraphDomain ℓ z ε hp (zero_lt_one.trans_le ht))
    (elapsedPhysicalBox z ε) (elapsedPhysicalBox z (ε/2))
    (retainedFrequencyDomain ℓ z ε aperture (1/2))
    (angularCone ℓ z.2.2 (2*ε)) (angularCone ℓ z.2.2 (ε/2)) (bufferedBase z (2*ε))
    (isOpen_elapsedPhysicalBox _ _) (isOpen_angularCone _ _ _)
    (convex_elapsedPhysicalBox _ _) (convex_angularCone _ _ _)
    (isOpen_elapsedPhysicalBox _ _) (isOpen_retainedFrequencyDomain _ _ _ _ _)
    (convex_elapsedPhysicalBox _ _) isOpen_ball
    (isOpen_angularCone _ _ _) (convex_angularCone _ _ _) hcore
    (UniformEvolution.closure_elapsedPhysicalBox_half_subset hε)
    (closure_retainedFrequencyDomain_subset ℓ hε hAp (by norm_num))
    (fun _ ht _ hη ↦ smul_mem_angularCone hη ht)
    (fun _ ht _ hη ↦ smul_mem_angularCone hη ht)
    (fun _ hp ↦ hp)
    (by
      intro r hr' x hx
      apply elapsed_mem_bufferedBase (by positivity : 0 < 2*ε)
        ⟨hr'.1, by linarith [hr'.2, hΔε]⟩
      exact ⟨ball_subset_ball (by linarith) hx.1, ball_subset_ball (by linarith) hx.2⟩)
    hXbound (fun _ hξ ↦ retainedFrequencyDomain_norm_lt ℓ hξ) Subset.rfl
    (by
      intro r hr' x hx η hη
      obtain ⟨t, ht, ζ, hζ, hJζ, he⟩ := retained_normalized_representative ℓ hε
        hra_one hone_rb (hr r hr')
        ⟨ball_subset_ball (by linarith) hx.1, ball_subset_ball (by linarith) hx.2⟩ hη
      exact ⟨t, ht, ζ, ⟨hζ.1, ball_subset_ball (by linarith) hζ.2⟩, hJζ, he⟩)
    hout hβsub Mamp hMamp.le o ho'
  let cost := fun m ↦ 2 + D m + retainedPhaseCost ℓ z ε ra rb phaseCost m
  let A := fun s ↦ (1 + (q : ℝ)*q) * (Δ * Cbound s) * cost (s+(fullLowReserve (d+1)+2))
  have hcost m : 0 < cost m := by
    have := hD m
    have := retainedPhaseCost_pos ℓ z ε ra rb hphaseCost m
    dsimp [cost]
    positivity
  have hA s : 0 < A s := by
    have := hCbound s
    have := hcost (s+(fullLowReserve (d+1)+2))
    dsimp [A]
    positivity
  refine ⟨Δ*(C₀*Mamp), by positivity, A, hA, ?_⟩
  intro KQ Q B hQ hB h Φ C hbuffer hsmooth hdiff hnear hphase hsourceTime W hW hWsupport hbudget
  have hW' : ContDiff ℝ ∞ (jointAmplitude (curryCharacteristicMatrix W)) :=
    hW.comp (contDiff_fst.fst.prodMk (contDiff_fst.snd.fst.prodMk
      (contDiff_fst.snd.snd.prodMk contDiff_snd)))
  have hbudget' m : BoundedTwoTimeOrderSeminorm o J m (curryCharacteristicMatrix W) ∧
      twoTimeOrderSeminorm o J m (curryCharacteristicMatrix W) ≤
        D m * retardedCoefficientProfile KQ Q B m := by
    obtain ⟨hf, hle⟩ := retained_amplitude_restriction ℓ z hερ hW' (hbudget m).1
    exact ⟨hf, hle.trans (hbudget m).2⟩
  have hφ m := retained_phase_coefficient_bound ℓ hε.le hra hεb hbuffer hsmooth
    KQ Q phaseCost hphase (rb := rb) m
  have hmix : ∀ r ∈ Icc 0 Δ, ∀ x ∈ elapsedPhysicalBox z (ε/2),
      ∀ η ∈ angularCone ℓ z.2.2 (ε/2),
      ‖fderiv ℝ (fun ζ ↦ fderiv ℝ
        (fun p : ℝ × ℝ × Euclidean d ↦ curriedPhase ℓ C p.1 p.2.1 p.2.2 ζ)
        (x 0, x 0-r, spatialPart x)) η‖ ≤ mix := by
    intro r hr' x hx η hη
    apply (retained_mixed_coefficient_bound ℓ hε hεb hbuffer hsmooth KQ Q phaseCost hphase
      (hr r hr') ⟨ball_subset_ball (by linarith) hx.1,
        ball_subset_ball (by linarith) hx.2⟩ hη).trans
    apply mul_le_mul_of_nonneg_left _ (retainedPhaseCost_pos ℓ z ε (1/2) 2 hphaseCost 2).le
    exact add_le_add le_rfl ((cNorm_mono_order
      (by have := (retardedCoefficientOrder_bounds (d := d) ho').1; omega)).trans hQ)
  obtain ⟨_, _, _, _, Op, hOp, hOpint, hOpadj, hpos, hneg, htest⟩ := hrealize
    K hK le_rfl hshell hmapshell (curriedPhase ℓ C)
    (contDiffOn_retained_product ℓ (by positivity : 0 < 2*ε)
      (by have := four_mul_retainedRadius_le b ρ; dsimp [ε] at *; linarith) hbuffer hsmooth)
    (fun t ht p _ η _ ↦ extend_smul ℓ (twoTimePhase C) (p.1, (p.2.1, (p.2.2, η))) ht)
    (retained_mixed_half_gap_doubled ℓ hε (four_mul_retainedRadius_le b ρ) hΔε.le
      hbuffer hsmooth hdiff hnear)
    hmix (retained_phase_low_bound ℓ hε.le hra hεb hbuffer hsmooth
      KQ Q phaseCost hphaseCost hphase hQ ho')
    (curryCharacteristicMatrix W) hW' (fun m ↦ (hbudget' m).1)
    (retained_amplitude_low_bound KQ Q B ho' D hD (fun m ↦ (hbudget' m).2) hQ hB)
    (z.1-src/2) hslab
    (fun t s y η hs' ↦ retained_amplitude_zero_before_source_half ℓ z src C
      hsourceTime W hWsupport (p := (t, (s, (y, η)))) hs')
  have hprofile m : 1 ≤ retardedCoefficientProfile KQ Q B m := by
    dsimp [retardedCoefficientProfile]
    linarith [cNorm_nonneg KQ (m+10) Q, cNorm_nonneg KQ (m+9) B]
  have hsum m : 2 + twoTimeOrderSeminorm o J m (curryCharacteristicMatrix W) +
      cNorm J m (jointPhase (curriedPhase ℓ C)) ≤ cost m * retardedCoefficientProfile KQ Q B m := by
    have hp : 1 + cNorm KQ (m+1) Q ≤ retardedCoefficientProfile KQ Q B m := by
      have := cNorm_mono_order (f := Q) (s := KQ) (show m+1 ≤ m+10 by omega)
      dsimp [retardedCoefficientProfile]
      linarith [cNorm_nonneg KQ (m+9) B]
    have hφ' := (hφ m).trans (mul_le_mul_of_nonneg_left hp
      (retainedPhaseCost_pos ℓ z ε ra rb hphaseCost m).le)
    have hw := (hbudget' m).2
    dsimp [cost]
    nlinarith [hprofile m]
  refine ⟨Op, hOp, hOpint, hOpadj, ?_, ?_, htest⟩
  · intro s V hV u hu
    obtain ⟨hmem, hnorm⟩ := hpos s V hV u hu
    refine ⟨hmem, hnorm.trans ?_⟩
    have hnorm0 : 0 ≤ vectorFourierSobolevNorm ((s-o : ℕ) : ℝ) u := norm_nonneg _
    have hn := norm_nonneg u
    have hc := (hcost (s+(fullLowReserve (d+1)+2))).le
    have hc1 : 1 ≤ cost (s+(fullLowReserve (d+1)+2)) := by
      dsimp [cost]; linarith [hD (s+(fullLowReserve (d+1)+2)),
        retainedPhaseCost_pos ℓ z ε ra rb hphaseCost (s+(fullLowReserve (d+1)+2))]
    have hp := hprofile (s+(fullLowReserve (d+1)+2))
    have hsum' := hsum (s+(fullLowReserve (d+1)+2))
    have hscale : 0 ≤ Δ * Cbound s := mul_nonneg hΔ.le (hCbound s).le
    calc
      _ ≤ (Δ*Cbound s) * (cost (s+(fullLowReserve (d+1)+2)) *
          (vectorFourierSobolevNorm ((s-o : ℕ) : ℝ) u +
            retardedCoefficientProfile KQ Q B (s+(fullLowReserve (d+1)+2)) * ‖u‖)) := by
        apply mul_le_mul_of_nonneg_left _ hscale
        nlinarith
      _ ≤ A s * (vectorFourierSobolevNorm ((s-o : ℕ) : ℝ) u +
          retardedCoefficientProfile KQ Q B (s+(fullLowReserve (d+1)+2)) * ‖u‖) := by
        dsimp [A]
        have : 0 ≤ (q : ℝ)*q := mul_self_nonneg _
        nlinarith [mul_nonneg hscale hc,
          mul_nonneg (mul_nonneg hscale hc) (add_nonneg hnorm0 (mul_nonneg (by linarith) hn))]
  · intro k V hV u
    obtain ⟨hmem, hnorm⟩ := hneg k V hV u
    refine ⟨hmem, hnorm.trans ?_⟩
    have hn : 0 ≤ vectorFourierSobolevNorm (-((k+o : ℕ) : ℝ)) u := norm_nonneg _
    have hp := hprofile (k+o+(fullLowReserve (d+1)+2))
    have hs' := hsum (k+o+(fullLowReserve (d+1)+2))
    have hscale : 0 ≤ Δ * Cbound (k+o) := mul_nonneg hΔ.le (hCbound _).le
    calc
      _ ≤ ((q : ℝ)*q*(Δ*Cbound (k+o))) *
          (cost (k+o+(fullLowReserve (d+1)+2)) *
            retardedCoefficientProfile KQ Q B (k+o+(fullLowReserve (d+1)+2))) *
          vectorFourierSobolevNorm (-((k+o : ℕ) : ℝ)) u := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hs' (mul_nonneg (mul_self_nonneg _) hscale)) hn
      _ ≤ A (k+o) * retardedCoefficientProfile KQ Q B (k+o+(fullLowReserve (d+1)+2)) *
          vectorFourierSobolevNorm (-((k+o : ℕ) : ℝ)) u := by
        dsimp [A]
        have hc := (hcost (k+o+(fullLowReserve (d+1)+2))).le
        nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hscale hc) (by linarith :
          0 ≤ retardedCoefficientProfile KQ Q B (k+o+(fullLowReserve (d+1)+2)))) hn]

/-- Forget only the requested band margins, retaining the exact multiplier
and the same operator construction (`app:ch_regular_base:lem:retarded-kernel`). -/
theorem exists_physical_signed_retarded_operators_with_diagonal
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : Z) {b ρ src aperture : ℝ}
    (hb : 0 < b) (hρ : 0 < ρ) (hsrc : 0 < src)
    (hρb : ρ ≤ b) (hsrcρ : src ≤ ρ / 4) (hAp : 0 < aperture)
    (χout χsource : E → ℂ) (ho : ContDiff ℝ ∞ χout) (hs : ContDiff ℝ ∞ χsource)
    (hoc : HasCompactSupport χout) (hsc : HasCompactSupport χsource)
    (hXne : (tsupport χout ×ˢ tsupport χsource).Nonempty)
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
    (phaseCost : ℕ → ℝ) (hphaseCost : ∀ m, 0 < phaseCost m)
    (M : ℝ) (hM : 0 ≤ M) :
    ∃ ra > (0 : ℝ), ∃ rb > ra,
      DiagonalFrequencyCoverage ℓ z.2.2 (ρ/2) ra rb
        (fun ξ ↦ (dilatedConicMask mask (2*L) (physicalCoordinates index ξ) : ℂ)) ∧
      ∀ (D : ℕ → ℝ), (∀ m, 0 < D m) →
      ∀ o : ℕ, (o = 0 ∨ o = 1) → ∃ A₀ > (0 : ℝ), ∃ A : ℕ → ℝ,
        (∀ s, 0 < A s) ∧
      ∀ (KQ : Set E) (Q : E → Fin (d+1) → Mat) (B : E → Mat),
        cNorm KQ (retardedCoefficientOrder d) Q ≤ M →
        cNorm KQ (retardedCoefficientOrder d) B ≤ M →
      ∀ (h : Z → ℝ) (Φ : Z × ℝ → Z) (C : OpenPartialHomeomorph T T),
        closedBall (z.1, z) b ⊆ C.target →
        ContDiffOn ℝ ∞ (twoTimePhase C) C.target →
        (∀ p ∈ C.target, HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C p) p) →
        (∀ p ∈ closedBall (z.1, z) b, ‖twoTimePhaseMixed C p - 1‖ ≤ 1/2) →
        (∀ m, cNorm (closedBall (z.1, z) b) m (twoTimePhase C) ≤
          phaseCost m * (1 + cNorm KQ (m+1) Q)) →
        (∀ p ∈ C.target, (C.symm p).2.1 = p.2.1) →
      ∀ W : T → Matrix (Fin q) (Fin q) ℂ,
        ContDiff ℝ ∞ W →
        tsupport W ⊆ ConicPhase.domain ℓ (C.target ∩ C.symm ⁻¹'
          (ball z.1 (src/2) ×ˢ (ball z.1 (src/2) ×ˢ ball z.2 (src/2)))) →
        (∀ m, BoundedTwoTimeOrderSeminorm o (bufferedJetSet ℓ z (ρ/2) ra rb) m
          (curryCharacteristicMatrix W) ∧
          twoTimeOrderSeminorm o (bufferedJetSet ℓ z (ρ/2) ra rb) m
            (curryCharacteristicMatrix W) ≤ D m * retardedCoefficientProfile KQ Q B m) →
      ∃ Op : SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q,
        RetainedSignedRetardedBounds KQ Q B (3*src/4) (z.1-src/2)
          (curriedPhase ℓ C) (curryCharacteristicMatrix W) χout χsource
          (fun ξ ↦ (dilatedConicMask mask (2*L) (physicalCoordinates index ξ) : ℂ)) hs o A₀ A Op := by
  obtain ⟨ra, hra, rb, hrab, _, _, hcoverage, hconstruct⟩ :=
    exists_physical_signed_retarded_operators_with_diagonal_on_enlarged_band
      ℓ z hb hρ hsrc hρb hsrcρ hAp χout χsource ho hs hoc hsc hXne hout hslab
      R hR hXbound hYbound index mask hm hcarrier L hL hβsub phaseCost hphaseCost M hM
      1 1 zero_lt_one
  exact ⟨ra, hra, rb, hrab, hcoverage, hconstruct⟩

end JanetCartan.RegularSector.FinitePdo.RetainedConstruction
