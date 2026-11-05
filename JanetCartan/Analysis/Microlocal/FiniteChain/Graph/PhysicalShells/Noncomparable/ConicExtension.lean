module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Noncomparable.ConicExtension.Summation
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Noncomparable.ConicExtension.Grades
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Carriers
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Regimes

/-!
# Noncomparable physical pairs from an actual conic phase

This support-local version of `exists_physicalPair_summable_majorant` closes
the phase-extension obligation in `app:ch_regular:eq:joint-kernel-phase` and
`app:ch_regular:eq:chain-tail`. The original phase is smooth only on its open
conic domain. Compact buffered geometry locates the amplitude support there.
We construct a global smooth extension and restrict the base integration domain
to its equality locus; every quantitative phase grade is then inherited from
the original phase. No quantitative bound on an unconstructed extension occurs.

The parent supplies the actual primitive geometry, physical phase/full-symbol
grades and carriers, then performs the final summation. The physical base-phase
grades below are precisely the first and higher derivatives of the manuscript's
literal phase with its three physical covectors frozen. Constants and the fixed
loss precede every varying scale, phase, shell index and external base.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Pointwise Topology Matrix.Norms.Frobenius
namespace JanetCartan.FiniteChain.Graph.PhysicalShells.Noncomparable
open FourierIntegral KernelEstimates KernelEstimates.Noncomparable
  KernelEstimates.NoncomparableGeometry ConicExtension
variable {n r : ℕ}
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 256

/-- Support-local physical pair bounds from the original open conic phase.
The compact `Kphase` contains only the projected amplitude support at graph
frequencies in `Kξ`; it need not contain a full angular annulus. Its sole role
is to construct a smooth extension, so its size and cutoff derivatives do not
enter the constants. The higher physical phase grades are required only on the
amplitude support. The same estimate holds for every external base, including
`m = q = 0`, and retains both orientations, both amplitude positions, arbitrary
real symbol orders, shrinking graph shells and the bounded output ball.
Source: `app:ch_regular:eq:joint-kernel-phase`, `app:ch_regular:eq:chain-tail`. -/
theorem exists_conicPhysicalPair_summable_majorant {ι κ : Type*} [Fintype ι] [Fintype κ]
    (eu : OrthonormalBasis ι ℝ (Euclidean n)) (ez : OrthonormalBasis κ ℝ (Euclidean n))
    (backward : Bool) {c C G Ci ε : ℝ} (hc : 0 < c) (hCi : 0 ≤ Ci) (hε : 0 < ε)
    {Kb : Set (Euclidean n × Euclidean n)} {Bwave Bξ Bη Bζ : Set (Euclidean n)}
    (hKb : IsCompact Kb) (hBwave : IsCompact Bwave)
    (hBξ : IsCompact Bξ) (hBη : IsCompact Bη) (hBζ : IsCompact Bζ)
    (P B O : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) (hO : ∀ j, 0 ≤ O j)
    (sA si so : ℝ) (bi bo bA m : ℕ) :
    ∃ (threshold : ℕ) (D : ℕ → ℝ), (∀ q, 0 ≤ D q) ∧
    ∀ (ρ R L σA σi σo : ℝ), 0 < ρ → 1 ≤ R → 1 ≤ L →
      1 ≤ σA → 1 ≤ σi → 1 ≤ σo → σA ≤ R → σi ≤ R → σo ≤ R → ρ ≤ R →
    ∀ (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
      (mi mo : LocalizerSymbol n) (low : Bool) (j k : ℕ) (x y : Euclidean n)
      (Kξ Kη Kζ : Set (Euclidean n))
      (U : (Euclidean n × Euclidean n × Euclidean n) → Set (Euclidean n × Euclidean n))
      (g : (Euclidean n × Euclidean n × Euclidean n) →
        (Euclidean n × Euclidean n) → Euclidean n)
      (V Kphase : Set (Euclidean n × Euclidean n))
      (a b lξ uξ lζ uζ : ℝ),
    IsCompact Kξ → IsCompact Kη → IsCompact Kζ →
    branchRadius low j ≤ R → (2 : ℝ) ^ k ≤ R →
    Kξ ⊆ (branchRadius low j / ρ) • Bξ → Kη ⊆ Bη →
    Kζ ⊆ (((2 : ℝ) ^ k) / ρ) • Bζ →
    (∀ u z ξ, (u, z) ∉ Kb → A u z ξ = 0) →
    tsupport (fun ξ => graphBranchCutoff low j (ρ • ξ)) ⊆ Kξ →
    tsupport (fun η => mi (y, η)) ⊆ Kη →
    tsupport (fun ζ => outputCutoff k (ρ • ζ)) ⊆ Kζ →
    (∀ ξ ∈ Kξ, lξ ≤ ‖ρ • ξ‖ ∧ ‖ρ • ξ‖ ≤ uξ) →
    (∀ η ∈ Kη, a ≤ ‖ρ • η‖ ∧ ‖ρ • η‖ ≤ b) →
    (∀ ζ ∈ Kζ, lζ ≤ ‖ρ • ζ‖ ∧ ‖ρ • ζ‖ ≤ uζ) →
    SeparatedRanges c C a b lξ uξ lζ uζ → ε * R ≤ max lξ (max a lζ) →
    (∀ w ∈ Kξ ×ˢ Kη ×ˢ Kζ, IsOpen (U w)) →
    IsOpen V → IsCompact Kphase → Kphase ⊆ V →
    ContDiffOn ℝ ∞ (Function.uncurry S) V →
    (∀ ξ ∈ Kξ, ∀ z ∈ tsupport (fun z : Euclidean n × Euclidean n => A z.1 z.2 (ρ • ξ)),
      (z.1, ρ • ξ) ∈ Kphase) →
    ContDiff ℝ ∞ mo →
    ContDiff ℝ ∞ (fun p : JointVariables (Euclidean n) => A p.1.1 p.1.2 (ρ • p.2.1)) →
    ContDiff ℝ ∞ (fun η => mi (y, η)) →
    (∀ w ∈ Kξ ×ˢ Kη ×ˢ Kζ,
      tsupport (fun z : Euclidean n × Euclidean n => A z.1 z.2 (ρ • w.1)) ⊆ U w) →
    (∀ w ∈ Kξ ×ˢ Kη ×ˢ Kζ, ∀ z ∈ U w,
      fderiv ℝ (fun u => S u (ρ • w.1)) z.1 = innerSL ℝ (g w z)) →
    (∀ w ∈ Kξ ×ˢ Kη ×ˢ Kζ, ∀ z ∈ U w,
      c * ‖ρ • w.1‖ ≤ ‖g w z‖ ∧ ‖g w z‖ ≤ C * ‖ρ • w.1‖) →
    (∀ w ∈ Kξ ×ˢ Kη ×ˢ Kζ, ∀ z ∈ U w,
      ‖fderiv ℝ (basePhase backward S x y
        (ρ • w.1) (ρ • w.2.1) (ρ • w.2.2)) z‖ ≤ R * G) →
    (∀ w ∈ Kξ ×ˢ Kη ×ˢ Kζ,
      ∀ z ∈ tsupport (fun z : Euclidean n × Euclidean n => A z.1 z.2 (ρ • w.1)),
      ∀ d, 1 ≤ d →
      ‖iteratedFDeriv ℝ (d + 1) (basePhase backward S x y
        (ρ • w.1) (ρ • w.2.1) (ρ • w.2.2)) z‖ ≤ R * (P d * L ^ d)) →
    (∀ w ∈ Kξ ×ˢ Kη ×ˢ Kζ, ∀ z ∈ Kb, ∀ d,
      ‖iteratedFDeriv ℝ d (fun z : Euclidean n × Euclidean n => A z.1 z.2 (ρ • w.1)) z‖ ≤
        σA ^ sA * B d * L ^ (d + bA)) →
    (∀ η ∈ Kη, ‖mi (y, η)‖ ≤ (σi ^ si * Ci) * L ^ bi) →
    (∀ ζ ∈ Kζ, (ρ / R) • ζ ∈ Bwave) →
    (∀ ζ ∈ Kζ, ∀ d,
      ‖iteratedFDeriv ℝ d (fun t => mo (t, ζ)) x‖ ≤ σo ^ so * O d * L ^ (d + bo)) →
    Continuous (fun p : (Euclidean n × Euclidean n) × Euclidean n => A p.1.1 p.1.2 p.2) →
    Continuous mi →
    ∀ (_carriers : KernelLimits.RegularizedCarriers A mi (graphBranchCutoff low j) (outputCutoff k)),
    ∀ (q : ℕ) (v : Fin m → Euclidean n), (∀ i, ‖v i‖ ≤ 1) →
      ‖iteratedFDeriv ℝ m (fun t => KernelLimits.regularizedJointKernel backward S A
          (fun z => mi (z.1, ρ⁻¹ • z.2)) (fun z => mo (z.1, ρ⁻¹ • z.2))
            (graphBranchCutoff low j) (outputCutoff k) t y) x v‖ ≤
        D q * ρ ^ n * L ^ (bi + (m + bo) + bA + threshold + 2) *
          (L / ρ) ^ q * pairWeight low n j k := by
  obtain ⟨threshold, D, hD, hbound⟩ := exists_normalizedPair_summable_majorant_on_support (r := r)
    eu ez backward hc hCi hε hKb hBwave hBξ hBη hBζ P B O hB hO sA si so bi bo bA m
  refine ⟨threshold, D, hD, ?_⟩
  intro ρ R L σA σi σo hρ hR hL hσA hσi hσo hσAR hσiR hσoR hρR
    S A mi mo low j k x y Kξ Kη Kζ U g V Kphase a b lξ uξ lζ uζ hKξ hKη hKζ
    hj hk hvξ hvη hvζ hAzero hχA hmi hχo hξ hη hζ hsep hlarge hU
    hV hKphase hKV hS hcarrier ho hAsmooth hismooth hsU hg hcomp hupper hp ha hi hw hb
    hAcont hicont carriers q v hv
  obtain ⟨f, hf, _, _, _, heq⟩ :=
    JanetCartan.NormalComparison.exists_contDiff_localization hV hKphase hKV hS
  let Φ : Euclidean n → Euclidean n → ℝ := fun u ξ => f (u, ξ)
  let φ := normalizedPhysicalPhase ρ Φ
  have hΦsmooth : ContDiff ℝ ∞ (Function.uncurry Φ) := hf
  have hφsmooth := contDiff_normalizedPhysicalPhase ρ Φ hΦsmooth
  have hhom := fun u ξ => normalizedPhysicalPhase_rescale hρ.ne' Φ u ξ
  let U' := fun w : Euclidean n × Euclidean n × Euclidean n =>
    U w ∩ (fun z : Euclidean n × Euclidean n => (z.1, ρ • w.1)) ⁻¹' phaseEqualityDomain Φ S
  have hU' (w) (hw' : w ∈ Kξ ×ˢ Kη ×ˢ Kζ) : IsOpen (U' w) :=
    (hU w hw').inter ((isOpen_phaseEqualityDomain Φ S).preimage
      (continuous_fst.prodMk continuous_const))
  have hsU' (w) (hw' : w ∈ Kξ ×ˢ Kη ×ˢ Kζ) :
      tsupport (fun z : Euclidean n × Euclidean n => A z.1 z.2 (ρ • w.1)) ⊆ U' w := by
    intro z hz
    exact ⟨hsU w hw' hz, heq _ (hcarrier w.1 hw'.1 z hz)⟩
  have hΦslice (ξ : Euclidean n) : ContDiff ℝ ∞ (fun u => Φ u ξ) :=
    hΦsmooth.comp (contDiff_id.prodMk contDiff_const)
  have hphase : ∀ u z ξ, A u z ξ ≠ 0 → graphBranchCutoff low j ξ ≠ 0 → S u ξ = Φ u ξ := by
    intro u z ξ hA hg'
    have hscale : ρ • (ρ⁻¹ • ξ) = ξ := smul_inv_smul₀ hρ.ne' ξ
    have hmem : ρ⁻¹ • ξ ∈ Kξ := hχA
      (subset_tsupport _ (by simpa only [Function.mem_support, hscale] using hg'))
    have hz : (u, z) ∈ tsupport
        (fun b : Euclidean n × Euclidean n => A b.1 b.2 (ρ • (ρ⁻¹ • ξ))) :=
      subset_tsupport _ (by simpa only [Function.mem_support, hscale] using hA)
    have he := (heq _ (hcarrier _ hmem (u, z) hz)).eq_of_nhds
    simpa only [Function.uncurry_apply_pair, hscale] using he.symm
  rw [iteratedFDeriv_physicalPair_eq_normalized_extension backward S Φ φ A mi mo low j k
    x y hρ hphase hhom hΦsmooth.continuous hAcont hicont ho.continuous carriers m v]
  apply hbound ρ R L σA σi σo hρ hR hL hσA hσi hσo hσAR hσiR hσoR hρR
    Φ φ A mi mo low j k x y Kξ Kη Kζ U' g a b lξ uξ lζ uζ hKξ hKη hKζ
    hj hk hvξ hvη hvζ hAzero hχA hmi hχo hξ hη hζ hsep hlarge hU' hhom
    ho hAsmooth hismooth (contDiff_jointPhase_of_contDiff_phase backward φ hφsmooth 0 y)
    _ _ hsU' _ _ (fun w hw' z hz => hcomp w hw' z hz.1) _ _ ha hi hw hb q v hv
  · intro w hw'
    exact ((contDiff_basePhase backward φ hφsmooth x y w.1 w.2.1 w.2.2).const_smul
      (ρ / R)).contDiffOn
  · intro w hw'
    exact (hAsmooth.comp (contDiff_id.prodMk contDiff_const)).contDiffOn
  · intro w hw' z hz
    exact ((hΦslice (ρ • w.1)).differentiable (by simp)).differentiableAt
  · intro w hw' z hz
    rw [(phaseSlice_eventuallyEq hz.2).fderiv_eq]
    exact hg w hw' z hz.1
  · intro w hw' z hz
    exact (normalizedPhysicalPhase_grades backward ρ (zero_lt_one.trans_le hR) hρ.ne'
      Φ S hΦsmooth x y w z hz.2 (hupper w hw' z hz.1)).1
  · intro w hw' z hz d hd
    exact (normalizedPhysicalPhase_grades backward ρ (zero_lt_one.trans_le hR) hρ.ne'
      Φ S hΦsmooth x y w z (hsU' w hw' hz).2
      (hupper w hw' z (hsU w hw' hz))).2 (d + 1) (P d * L ^ d) (hp w hw' z hz d hd)

/-- Concrete noncomparable physical pairs, using the exact graph/input/output
carriers and `pairRadius`, directly from primitive grades of the original
phase on its open conic domain. The first phase grade is proved from covector
comparison; all higher grades come only from the original phase's base jets.
The full symbol uses `max 1 (branchRadius low j)`, including negative orders.
Constants precede the phase, scale, external bases and both indices. The parent
instantiates its original conic geometry and symbol data, then sums these
unchanged physical kernels (`app:ch_regular:eq:chain-tail`). -/
theorem exists_conicPhysicalPair_bound_of_primitive_grades
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (eu : OrthonormalBasis ι ℝ (Euclidean n)) (ez : OrthonormalBasis κ ℝ (Euclidean n))
    (backward : Bool) {c C Ci a b : ℝ} (hc : 0 < c) (hCi : 0 ≤ Ci) (ha : 0 < a)
    {Kb : Set (Euclidean n × Euclidean n)} (hKb : IsCompact Kb)
    (P B O : ℕ → ℝ) (hP : ∀ d, 0 ≤ P d) (hB : ∀ d, 0 ≤ B d) (hO : ∀ d, 0 ≤ O d)
    (sA si so : ℝ) (bi bo bA m : ℕ) :
    ∃ (threshold : ℕ) (D : ℕ → ℝ), (∀ q, 0 ≤ D q) ∧
    ∀ (ρ L : ℝ), 1 ≤ ρ → 1 ≤ L →
    ∀ (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
      (mi mo : LocalizerSymbol n) (low : Bool) (j k : ℕ) (x y : Euclidean n)
      (V Kphase : Set (Euclidean n × Euclidean n))
      (g : Euclidean n → Euclidean n → Euclidean n),
    IsOpen V → IsCompact Kphase → Kphase ⊆ V →
    ContDiffOn ℝ ∞ (Function.uncurry S) V →
    (∀ ξ ∈ normalizedGraphCarrier ρ low j,
      ∀ z ∈ tsupport (fun z : Euclidean n × Euclidean n => A z.1 z.2 (ρ • ξ)),
      (z.1, ρ • ξ) ∈ Kphase) →
    ContDiff ℝ ∞ (fun p : (Euclidean n × Euclidean n) × Euclidean n => A p.1.1 p.1.2 p.2) →
    ContDiff ℝ ∞ mi → ContDiff ℝ ∞ mo →
    (∀ u z ξ, (u, z) ∉ Kb → A u z ξ = 0) →
    tsupport (fun η => mi (y, η)) ⊆ frequencyAnnulus a b →
    SeparatedRanges c C (a * ρ) (b * ρ)
      (graphLower low j) (graphUpper low j) (outputLower k) (outputUpper k) →
    (∀ u ξ, (u, ξ) ∈ V → fderiv ℝ (fun t => S t ξ) u = innerSL ℝ (g u ξ)) →
    (∀ u ξ, (u, ξ) ∈ V → c * ‖ξ‖ ≤ ‖g u ξ‖ ∧ ‖g u ξ‖ ≤ C * ‖ξ‖) →
    (∀ ξ ∈ normalizedGraphCarrier ρ low j,
      ∀ z ∈ tsupport (fun z : Euclidean n × Euclidean n => A z.1 z.2 (ρ • ξ)),
      ∀ d, 1 ≤ d →
      ‖iteratedFDeriv ℝ (d + 1) (fun z : Euclidean n × Euclidean n => S z.1 (ρ • ξ)) z‖ ≤
        ‖ρ • ξ‖ * P d * L ^ d) →
    (∀ ξ ∈ normalizedGraphCarrier ρ low j, ∀ z ∈ Kb, ∀ d,
      ‖iteratedFDeriv ℝ d (fun z : Euclidean n × Euclidean n => A z.1 z.2 (ρ • ξ)) z‖ ≤
        (max 1 (branchRadius low j)) ^ sA * B d * L ^ (d + bA)) →
    (∀ η ∈ frequencyAnnulus a b, ‖mi (y, η)‖ ≤ (ρ ^ si * Ci) * L ^ bi) →
    (∀ ζ ∈ normalizedOutputCarrier ρ k, ∀ d,
      ‖iteratedFDeriv ℝ d (fun t => mo (t, ζ)) x‖ ≤ ((2 : ℝ) ^ k) ^ so * O d * L ^ (d + bo)) →
    ∀ (_carriers : KernelLimits.RegularizedCarriers A mi (graphBranchCutoff low j) (outputCutoff k)),
    ∀ (q : ℕ) (v : Fin m → Euclidean n), (∀ i, ‖v i‖ ≤ 1) →
      ‖iteratedFDeriv ℝ m (fun t => KernelLimits.regularizedJointKernel backward S A
          (fun z => mi (z.1, ρ⁻¹ • z.2)) (fun z => mo (z.1, ρ⁻¹ • z.2))
            (graphBranchCutoff low j) (outputCutoff k) t y) x v‖ ≤
        D q * ρ ^ n * L ^ (bi + (m + bo) + bA + threshold + 2) *
          (L / ρ) ^ q * pairWeight low n j k := by
  obtain ⟨threshold, D, hD, hbound⟩ := exists_conicPhysicalPair_summable_majorant (r := r)
    eu ez backward (C := C) (G := 4 * max 0 C + 4 + max 0 b + 2) hc hCi
    (lt_min ha (by norm_num : (0 : ℝ) < 1 / 2)) hKb
    (isCompact_closedBall (0 : Euclidean n) 2)
    (isCompact_closedBall (0 : Euclidean n) 4)
    (isCompact_frequencyAnnulus a b) (isCompact_closedBall (0 : Euclidean n) 2)
    (fun d => 4 * P d) B O hB hO sA si so bi bo bA m
  refine ⟨threshold, D, hD, ?_⟩
  intro ρ L hρ hL S A mi mo low j k x y V Kphase g hV hKphase hKV hS hcarrier
    hA hiSmooth ho hAzero hmi hsep hg hcomp hp hsymbol hi hb carriers q v hv
  have hρ0 := zero_lt_one.trans_le hρ
  have hR := pairRadius_bounds hρ low j k
  let U := fun w : Euclidean n × Euclidean n × Euclidean n =>
    (fun z : Euclidean n × Euclidean n => (z.1, ρ • w.1)) ⁻¹' V
  have hslice (w : Euclidean n × Euclidean n × Euclidean n)
      (z : Euclidean n × Euclidean n) (hz : z ∈ U w) :
      ContDiffAt ℝ ∞ (fun u => S u (ρ • w.1)) z.1 :=
    (hS.contDiffAt (hV.mem_nhds hz)).comp z.1 (contDiffAt_id.prodMk contDiffAt_const)
  apply hbound ρ (pairRadius ρ low j k) L (max 1 (branchRadius low j)) ρ ((2 : ℝ) ^ k)
    hρ0 hR.1 hL (le_max_left _ _) hρ (one_le_pow₀ (by norm_num))
    hR.2.2.1 hR.2.1 hR.2.2.2 hR.2.1 S A mi mo low j k x y
    (normalizedGraphCarrier ρ low j) (frequencyAnnulus a b) (normalizedOutputCarrier ρ k)
    U (fun w z => g z.1 (ρ • w.1)) V Kphase (a * ρ) (b * ρ)
    (graphLower low j) (graphUpper low j) (outputLower k) (outputUpper k)
    (isCompact_normalizedGraphCarrier ρ low j) (isCompact_frequencyAnnulus a b)
    (isCompact_normalizedOutputCarrier ρ k)
    ((le_max_right 1 _).trans hR.2.2.1) hR.2.2.2
    (normalizedGraphCarrier_subset_dilate hρ0 low j) Subset.rfl
    (normalizedOutputCarrier_subset_dilate hρ0 k) hAzero
    (tsupport_rescaled_graphBranchCutoff_subset hρ0.ne' low j) hmi
    (tsupport_rescaled_outputCutoff_subset hρ0.ne' k)
    (fun ξ hξ => (mem_normalizedGraphCarrier_iff hρ0.ne' low j ξ).mp hξ)
    _ (fun ζ hζ => (mem_normalizedOutputCarrier_iff hρ0.ne' k ζ).mp hζ)
    hsep (pairRadius_fraction_le_endpoints hρ ha low j k)
    (fun _ _ => hV.preimage (continuous_fst.prodMk continuous_const))
    hV hKphase hKV hS hcarrier ho
    (hA.comp (contDiff_fst.prodMk (contDiff_snd.fst.const_smul ρ)))
    (hiSmooth.comp (contDiff_const.prodMk contDiff_id))
    (fun w hw z hz => hKV (hcarrier w.1 hw.1 z hz))
    (fun w _ z hz => hg z.1 (ρ • w.1) hz)
    (fun w _ z hz => hcomp z.1 (ρ • w.1) hz)
    _ _ (fun w hw => hsymbol w.1 hw.1) hi
    (fun ζ hζ => normalizedOutputCarrier_wave_mem hρ low j k hζ) hb
    hA.continuous hiSmooth.continuous carriers q v hv
  · intro η hη
    rw [norm_smul, Real.norm_of_nonneg hρ0.le]
    exact ⟨by nlinarith [hη.1], by nlinarith [hη.2]⟩
  · intro w hw z hz
    exact basePhase_first_grade_of_carriers backward hρ low j k S x y
      (g z.1 (ρ • w.1)) w z hw ((hslice w z hz).differentiableAt (by simp))
      (hg z.1 (ρ • w.1) hz) (hcomp z.1 (ρ • w.1) hz).2
  · intro w hw z hz d hd
    have hzV : z ∈ U w := hKV (hcarrier w.1 hw.1 z hz)
    exact basePhase_higher_grade_of_graphCarrier backward hρ (zero_le_one.trans hL) (hP d)
      low j k S x y w z d hd hw.1
      (((hslice w z hzV).comp z contDiffAt_fst).of_le (by simp))
      (hp w.1 hw.1 z hz d hd)

end JanetCartan.FiniteChain.Graph.PhysicalShells.Noncomparable
