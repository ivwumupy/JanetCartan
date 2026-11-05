module

public import JanetCartan.Iteration.PhysicalPairs.LocalNormalizedSize
public import JanetCartan.Iteration.PhysicalPairs.Coefficients
public import JanetCartan.Iteration.PhysicalGeometry

/-!
# Actual physical history with an independent source buffer

The SAME physical current map supplies all global extended Q/B profiles and
original reconstruction entries. Only source jets are localized, so the inverse
norm ball need not lie inside a Hamilton phase chart. No output bound or new
inverse is assumed. Consumer: `main:prop:pairs`, localized sampled size.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
open Set Metric MeasureTheory FourierTransform
open scoped SchwartzMap NNReal ENNReal ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.PhysicalPairs
open SignedProductEstimates
local instance : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩
open RegularSector.FiniteMasks.ActualFamily RegularSector.NormalizedSolver
open RegularSector.FiniteAssembly RegularSector.FiniteAssembly.CoefficientNorms
open RegularSector.Characteristic.EvolutionIntegral RegularSector.Characteristic.RetardedLocalization
open LocalSobolev FixedDomainInverse Pseudodifferential
open ResponseTransfer ResponseTransfer.RetainedFactors JanetCartan.Localization
open GeometricProfile RegularSector.FiniteEvolution CurrentCoefficientProfiles ProtectedFlow
open ArbitraryAccuracy.ResidualLocalization ProjectedStressFrame
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {center : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "H" => SpacetimeL2 d (d+1)
variable {ι : Type*}

/-- Apply the actual history's full extended coefficients and geometric
reconstruction profiles to the SAME normalized signed-product response. The
source retains both cutoffs, the complete tensor amplitude and doubled plus
diagonal. The physical size is `D_q * lam^(q+1)` with constants chosen before
initial frequencies, histories and samples. Raw tame/smooth realization inputs
come from the normalized inverse constructor; no individual size is assumed
(`main:prop:current-scale`, `main:prop:pairs`). -/
theorem exists_physical_history_localized_normalized_product_size_constants
    (Gref : FlatReference (d+1)) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hR : R < Gref.domain.chartRadius)
    (ext : BallExtension.Parameters E) (hextcenter : ext.center = 0) (hextradius : ext.radius = r)
    {Cband : ℝ} (hCband : 1 ≤ Cband)
    {rStar reserve kMin : ℕ} (hStar : 8 ≤ rStar) (hreserve : 2+reserve ≤ rStar)
    (hlowReserve : sectorLowOrder d + (d+2) ≤ reserve)
    (horder : RevisedScales.displacementLoss (d+1) + bandExponent * ((rStar : ℝ) + ((d+1 : ℕ) : ℝ)/2) + 2 < kMin)
    (f : ActualMaskFamily Ω center RQ A₀ K M) (hK : IsCompact K) (L₀ : ℝ)
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (χ₂ χ₃ : ContDiffBump center)
    (ψ : E → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψr : tsupport ψ ⊆ ball 0 r)
    {normRadius profileRadius : ℝ} (hnorm : 0 < normRadius) (hbuffer : normRadius < profileRadius)
    {S : Set E} (hS : IsCompact S)
    (P X Y C responseCost : ℕ → ℝ)
    (hP : ∀ q, 0 ≤ P q) (hX : ∀ q, 0 ≤ X q) (hY : ∀ q, 0 ≤ Y q)
    (hC : ∀ q, 0 ≤ C q) (hresponseCost : ∀ q, 0 ≤ responseCost q)
    {Cfreq : ℝ} (hCfreq : 0 ≤ Cfreq) :
    ∃ threshold : ℝ, 2 ≤ threshold ∧ ∃ D : ℕ → ℝ, (∀ q, 0 ≤ D q) ∧
      ∀ R₀, threshold ≤ R₀ →
      ∀ (j : ℕ) (u : Fin j → SchwartzMap E (Euclidean (embeddingDimension (d+1))))
        (ell : Fin j → ℕ), RevisedGlobal.IsAdmissibleHistory Cband R₀ kMin u ell →
      let F := RevisedGlobal.finiteMap Gref.map u
      let Q := extendedProjectedStress ext F
      let B := reducedZerothProjection (d+1) ∘ extendedReducedCoefficients ext (fun _ _ ↦ 0) F
      ∃ hQ : ContDiff ℝ ∞ Q, ∃ hB : ContDiff ℝ ∞ B,
      let W := ball center normRadius
      let uQ := smoothCoefficientL2 isOpen_univ hnorm (show closedBall center normRadius ⊆ Set.univ from subset_univ _) Q hQ.contDiffOn
      let uB := smoothCoefficientL2 isOpen_univ hnorm (show closedBall center normRadius ⊆ Set.univ from subset_univ _) B hB.contDiffOn
      let coeff := fun k ↦ restrictionSobolevNorm W k uQ + restrictionSobolevNorm W k uB
      let β := sectorLowOrder d + (d+2)
      ∀ (W₁ : f.centers → TwoTimeAmplitude d (d+1)) (retarded : ℕ → H →L[ℂ] H),
      let Krecut := localRealCompression (U := W) isOpen_ball.measurableSet W
        (measuredOperator χ₂ χ₃ χ₂.continuous χ₃.continuous
          (SmallSupport.bump_norm_le_one χ₂) (SmallSupport.bump_norm_le_one χ₃)
          (pairedResidual f hK L₀ Q B output ho hob W₁ (retarded 1)))
      let Corr := fun z : LocalL2 W E ↦ neumannInverse Krecut
        (SmallSupport.bumpL2 (p := 2) le_rfl χ₂ z)
      (∀ (q : ℕ) (z : LocalL2 W E), MemRestrictionSobolev W q z → ∀ Vout : Set E,
        let Sz := localRealCompression isOpen_ball.measurableSet Vout
          (pairedSolver f hK L₀ Q B output ho hob (retarded 0)) (Corr z)
        MemRestrictionSobolev Vout q Sz ∧ restrictionSobolevNorm Vout q Sz ≤ responseCost q *
          (restrictionSobolevNorm W q z + (1+coeff (q+β))*‖z‖)) →
      ∀ (Lpair lam ρ : ℝ), currentCoefficientScale R₀ j ≤ Lpair → Lpair ≤ lam →
      0 < ρ → ρ ≤ Cfreq * lam →
      ∀ (Usource : Set E), IsOpen Usource → Usource ⊆ ball center profileRadius →
      ∀ (χ η : E → ℝ) (phases : ι → E → ℝ)
        (amplitudes : ι → E → Matrix (Fin (embeddingDimension (d+1))) (Fin (d+1)) ℂ)
        (minus : Bool) (i k : ι), (minus = true → i ≠ k) →
      let φ := fun y ↦ (if minus then phases i y - phases k y else phases i y + phases k y) / ρ
      ContDiff ℝ ∞ χ → tsupport χ ⊆ S → tsupport χ ⊆ Usource →
      ContDiffOn ℝ ∞ η (Usource) →
      ContDiffOn ℝ ∞ φ (Usource) →
      ContDiffOn ℝ ∞ (amplitudes i) (Usource) →
      ContDiffOn ℝ ∞ (amplitudes k) (Usource) →
      (∀ y ∈ Usource, ∀ q, 1 ≤ q →
        ‖iteratedFDeriv ℝ q φ y‖ ≤ P q * Lpair^(q-1)) →
      (∀ y ∈ Usource, ∀ q, ‖iteratedFDeriv ℝ q χ y‖ ≤ X q * Lpair^q) →
      (∀ y ∈ Usource, ∀ q, ‖iteratedFDeriv ℝ q η y‖ ≤ Y q * Lpair^q) →
      (∀ y ∈ Usource, ∀ q, ‖iteratedFDeriv ℝ q (amplitudes i) y‖ ≤ C q * Lpair^q) →
      (∀ y ∈ Usource, ∀ q, ‖iteratedFDeriv ℝ q (amplitudes k) y‖ ≤ C q * Lpair^q) →
      let source := fun y ↦ WithLp.toLp 2 (AmbientResponse.cutoffSource η
        (AmbientResponse.stressSource Q (fun z ↦ χ z •
          (if minus then ProductSum.minusSource phases amplitudes i k z
            else ProductSum.plusSource phases amplitudes i k z))) y)
      ∃ hsource : MemLp source 2 volume,
        let h := (hsource.mono_measure (Measure.restrict_le_self (s := W))).toLp source
        ∀ g : E → E, ContDiff ℝ ∞ g →
        g =ᵐ[volume] realSolver f hK L₀ Q B output ho hob (retarded 0)
          (SmallSupport.zeroExtend isOpen_ball.measurableSet (Corr h)) →
        ∀ v : 𝓢(E, Euclidean (embeddingDimension (d+1))),
        (∀ x, v x = ψ x • AmbientResponse.completedVariation F g
          (fun y ↦ χ y • (if minus then ProductSum.minusSource phases amplitudes i k y
            else ProductSum.plusSource phases amplitudes i k y)) x) →
        ∀ q : ℕ,
        (eLpNorm (fun ξ ↦ euclideanSobolevWeight q ((2 * Real.pi) • ξ) •
          𝓕 (PhysicalCutoff.complexify v) ξ) 2 volume).toReal ≤ D q * lam^(q+1) := by
  obtain ⟨Tc, hTc, AQ, AB, hAQ, hAB, hcoeff⟩ :=
    PhysicalGeometry.exists_retained_coefficient_profiles Gref hr hrR hR ext
      hextcenter hextradius hCband hStar hreserve horder
  obtain ⟨Tg, hTg, Cgeom, hCgeom, hgeom⟩ :=
    exists_physical_history_reconstruction_entry_profiles Gref hr hrR hR
      hCband hStar (reserve := 0) (by omega) horder
  let Cg := fun q ↦ 1 + Cgeom q
  have hCg q : 1 ≤ Cg q := le_add_of_nonneg_right (hCgeom q)
  obtain ⟨D, hD, hsize⟩ := exists_localized_normalized_product_completedVariation_physicalWeighted_size_constants
    (N := embeddingDimension (d+1)) (ι := ι) f hK L₀ output ho hob χ₂ χ₃ ψ hψ hψc
    hnorm hbuffer hS P X Y AQ AB C Cg responseCost hP hX hY hAQ hAB hC hCg
    hresponseCost hCfreq hlowReserve
  refine ⟨max Tc Tg, hTc.trans (le_max_left _ _), D, hD, ?_⟩
  intro R₀ hR₀ j u ell hu F Q B
  have hcR : Tc ≤ R₀ := (le_max_left _ _).trans hR₀
  have hgR : Tg ≤ R₀ := (le_max_right _ _).trans hR₀
  obtain ⟨hQ, hB, hQB⟩ := hcoeff R₀ hcR j u ell hu
  obtain ⟨hv, hd, hs⟩ := hgeom R₀ hgR j u ell hu
  have hLc : 1 ≤ currentCoefficientScale R₀ j :=
    one_le_currentCoefficientScale ((by norm_num : (1 : ℝ) ≤ 2).trans (hTc.trans hcR)) j
  have hentry {a : E → ℂ} (hasm : ∀ x ∈ closedBall 0 r, ContDiffAt ℝ ∞ a x)
      (hap : HasDerivativeProfile (closedBall 0 r) a 0 (currentCoefficientScale R₀ j) Cgeom) :
      ContDiffOn ℝ ∞ a (ball 0 r) ∧
      ∀ q, ∀ x ∈ ball (0 : E) r,
        ‖iteratedFDeriv ℝ q a x‖ ≤ Cg q * currentCoefficientScale R₀ j ^ q := by
    refine ⟨fun x hx ↦ (hasm x (ball_subset_closedBall hx)).contDiffWithinAt, ?_⟩
    intro q x hx
    apply (norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall _ _)
      (fun y hy ↦ (hasm y hy).of_le (by simp)) (ball_subset_closedBall hx) le_rfl).trans
    apply (hap q).trans
    simp only [Nat.sub_zero]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one)
      (pow_nonneg (zero_le_one.trans hLc) q)
  have hv' l k := hentry (hv l k).1 (hv l k).2
  have hd' l ik := hentry (hd l ik).1 (hd l ik).2
  have hs' l ik := hentry (hs l ik).1 (hs l ik).2
  refine ⟨hQ, hB, ?_⟩
  intro W uQ uB coeff β W₁ retarded Krecut Corr htame Lpair lam ρ hL hLlam hρ hρlam
  exact hsize (currentCoefficientScale R₀ j) Lpair lam ρ hLc hL hLlam hρ hρlam
    Q B hQ hB (hQB (closedBall center profileRadius) (isCompact_closedBall _ _)).1
    (hQB (closedBall center profileRadius) (isCompact_closedBall _ _)).2
    W₁ retarded htame F (ball 0 r) isOpen_ball hψr
    (fun l k ↦ (hv' l k).1) (fun l ik ↦ (hd' l ik).1) (fun l ik ↦ (hs' l ik).1)
    (fun l k ↦ (hv' l k).2) (fun l ik ↦ (hd' l ik).2) (fun l ik ↦ (hs' l ik).2)

end JanetCartan.PhysicalPairs
