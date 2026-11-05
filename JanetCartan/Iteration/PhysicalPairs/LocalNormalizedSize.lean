module

public import JanetCartan.Iteration.PhysicalPairs.ProductSize
public import JanetCartan.Iteration.PhysicalPairs.LocalReducedSize

/-!
# Physical response size from LOCAL complete source jets

Apply the actual normalized inverse and original ambient reconstruction while
keeping source phase/amplitude jets only on a source-cutoff buffer. The norm
ball remains independent, and the SAME tensor, datum and Schwartz output serve
every order. Consumer: `main:prop:pairs` on the retained global mask family.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
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
open ResponseTransfer JanetCartan.Localization GeometricProfile RegularSector.FiniteEvolution
open ArbitraryAccuracy.ResidualLocalization
variable {d N : ℕ} {Ω : Set (Euclidean (d+1))} {center : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "H" => SpacetimeL2 d (d+1)
variable {ι : Type*}

/-- The smooth representative of the SAME normalized inverse on each complete
signed product datum has physical reconstructed size `D_r * lam^(r+1)`.
The reduced size is derived here from the normalized raw tame estimate, its
coefficient profiles and the actual complete source profiles. Constants precede
all varying fields, frequencies and samples, and there is no accuracy parameter.
The plus diagonal is retained (`main:prop:pairs`). -/
theorem exists_localized_normalized_product_completedVariation_physicalWeighted_size_constants
    (f : ActualMaskFamily Ω center RQ A₀ K M) (hK : IsCompact K) (L₀ : ℝ)
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (χ₂ χ₃ : ContDiffBump center)
    (ψ : E → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    {normRadius profileRadius : ℝ} (hnorm : 0 < normRadius) (hbuffer : normRadius < profileRadius)
    {S : Set E} (hS : IsCompact S)
    (P X Y AQ AB C Cgeom responseCost : ℕ → ℝ)
    (hP : ∀ r, 0 ≤ P r) (hX : ∀ r, 0 ≤ X r) (hY : ∀ r, 0 ≤ Y r)
    (hAQ : ∀ r, 0 ≤ AQ r) (hAB : ∀ r, 0 ≤ AB r) (hC : ∀ r, 0 ≤ C r)
    (hCgeom : ∀ r, 1 ≤ Cgeom r) (hresponseCost : ∀ r, 0 ≤ responseCost r)
    {Cfreq : ℝ} (hCfreq : 0 ≤ Cfreq)
    {reserve : ℕ} (hreserve : sectorLowOrder d + (d+2) ≤ reserve) :
    ∃ D : ℕ → ℝ, (∀ r, 0 ≤ D r) ∧
      ∀ (Lc Lpair lam ρ : ℝ), 1 ≤ Lc → Lc ≤ Lpair → Lpair ≤ lam →
      0 < ρ → ρ ≤ Cfreq * lam →
      ∀ (Q : E → Fin (d+1) → MetricTensor (d+1)) (B : E → MetricTensor (d+1))
        (hQ : ContDiff ℝ ∞ Q) (hB : ContDiff ℝ ∞ B),
      HasDerivativeProfile (closedBall center profileRadius) Q reserve Lc AQ →
      HasDerivativeProfile (closedBall center profileRadius) B reserve Lc AB →
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
      let Corr := fun u : LocalL2 W E ↦ neumannInverse Krecut
        (SmallSupport.bumpL2 (p := 2) le_rfl χ₂ u)
      (∀ (r : ℕ) (u : LocalL2 W E), MemRestrictionSobolev W r u → ∀ Vout : Set E,
        let Su := localRealCompression isOpen_ball.measurableSet Vout
          (pairedSolver f hK L₀ Q B output ho hob (retarded 0)) (Corr u)
        MemRestrictionSobolev Vout r Su ∧ restrictionSobolevNorm Vout r Su ≤ responseCost r *
          (restrictionSobolevNorm W r u + (1+coeff (r+β))*‖u‖)) →
      ∀ (F : E → Euclidean N) (G : Set E), IsOpen G → tsupport ψ ⊆ G →
      (∀ l j, ContDiffOn ℝ ∞ (reconstructionValueEntry F l j) G) →
      (∀ l ij, ContDiffOn ℝ ∞ (reconstructionDerivativeEntry F l ij) G) →
      (∀ l ij, ContDiffOn ℝ ∞ (reconstructionSourceEntry F l ij) G) →
      (∀ l j r, ∀ x ∈ G, ‖iteratedFDeriv ℝ r (reconstructionValueEntry F l j) x‖ ≤ Cgeom r * Lc^r) →
      (∀ l ij r, ∀ x ∈ G, ‖iteratedFDeriv ℝ r (reconstructionDerivativeEntry F l ij) x‖ ≤ Cgeom r * Lc^r) →
      (∀ l ij r, ∀ x ∈ G, ‖iteratedFDeriv ℝ r (reconstructionSourceEntry F l ij) x‖ ≤ Cgeom r * Lc^r) →
      ∀ (Usource : Set E), IsOpen Usource → Usource ⊆ ball center profileRadius →
      ∀ (χ η : E → ℝ) (phases : ι → E → ℝ)
        (amplitudes : ι → E → Matrix (Fin N) (Fin (d+1)) ℂ)
        (minus : Bool) (i j : ι), (minus = true → i ≠ j) →
      let φ := fun y ↦ (if minus then phases i y - phases j y else phases i y + phases j y) / ρ
      ContDiff ℝ ∞ χ → tsupport χ ⊆ S → tsupport χ ⊆ Usource →
      ContDiffOn ℝ ∞ η (Usource) →
      ContDiffOn ℝ ∞ φ (Usource) →
      ContDiffOn ℝ ∞ (amplitudes i) (Usource) →
      ContDiffOn ℝ ∞ (amplitudes j) (Usource) →
      (∀ y ∈ Usource, ∀ k, 1 ≤ k →
        ‖iteratedFDeriv ℝ k φ y‖ ≤ P k * Lpair^(k-1)) →
      (∀ y ∈ Usource, ∀ k, ‖iteratedFDeriv ℝ k χ y‖ ≤ X k * Lpair^k) →
      (∀ y ∈ Usource, ∀ k, ‖iteratedFDeriv ℝ k η y‖ ≤ Y k * Lpair^k) →
      (∀ y ∈ Usource, ∀ k, ‖iteratedFDeriv ℝ k (amplitudes i) y‖ ≤ C k * Lpair^k) →
      (∀ y ∈ Usource, ∀ k, ‖iteratedFDeriv ℝ k (amplitudes j) y‖ ≤ C k * Lpair^k) →
      let source := fun y ↦ WithLp.toLp 2 (AmbientResponse.cutoffSource η
        (AmbientResponse.stressSource Q (fun z ↦ χ z •
          (if minus then ProductSum.minusSource phases amplitudes i j z
            else ProductSum.plusSource phases amplitudes i j z))) y)
      ∃ hsource : MemLp source 2 volume,
        let h := (hsource.mono_measure (Measure.restrict_le_self (s := W))).toLp source
        ∀ g : E → E, ContDiff ℝ ∞ g →
        g =ᵐ[volume] realSolver f hK L₀ Q B output ho hob (retarded 0)
          (SmallSupport.zeroExtend isOpen_ball.measurableSet (Corr h)) →
        ∀ u : 𝓢(E, Euclidean N),
        (∀ x, u x = ψ x • AmbientResponse.completedVariation F g
          (fun y ↦ χ y • (if minus then ProductSum.minusSource phases amplitudes i j y
            else ProductSum.plusSource phases amplitudes i j y)) x) →
        ∀ r : ℕ,
        (eLpNorm (fun ξ ↦ euclideanSobolevWeight r ((2 * Real.pi) • ξ) •
          𝓕 (PhysicalCutoff.complexify u) ξ) 2 volume).toReal ≤ D r * lam^(r+1) := by
  obtain ⟨Droot, hDroot, hroot⟩ := exists_localized_normalized_product_reduced_solver_size_constants
    (N := N) (ι := ι) f hK L₀ output ho hob χ₂ χ₃ hnorm hbuffer hS
    P X Y AQ AB C responseCost hP hX hY hAQ hAB hC hresponseCost hCfreq hreserve
  obtain ⟨D, hD, hphysical⟩ := exists_product_completedVariation_physicalWeighted_size_constants
    (N := N) (ι := ι) ψ hψ hψc hS P X C Cgeom Droot
    hP hX hC hCgeom hDroot hCfreq
  refine ⟨D, hD, ?_⟩
  intro Lc Lpair lam ρ hLc hLcPair hLlam hρ hρlam Q B hQ hB hpQ hpB
    W uQ uB coeff β W₁ retarded Krecut Corr htame
    F G hG hψG hV hDer hSrc hVB hDB hSB
    Usource hUsource hUprofile χ η phases amplitudes minus i j hdiag φ hχ hχS hχU hη hφ hAi hAj
    hφb hχb hηb hAib hAjb source
  obtain ⟨hs, hsbound⟩ := hroot Lc Lpair lam ρ hLc hLcPair hLlam hρ hρlam
    Q B hQ hB hpQ hpB W₁ retarded htame Usource hUsource hUprofile χ η phases amplitudes minus i j hdiag
    hχ hχS hχU hη hφ hAi hAj hφb hχb hηb hAib hAjb
  refine ⟨hs, ?_⟩
  intro h g hgsm hgrep u hu r
  let solution := localRealCompression isOpen_ball.measurableSet univ
    (pairedSolver f hK L₀ Q B output ho hob (retarded 0)) (Corr h)
  have hsol : solution =ᵐ[volume.restrict univ] g :=
    (localRealCompression_coeFn isOpen_ball.measurableSet univ
      (pairedSolver f hK L₀ Q B output ho hob (retarded 0)) (Corr h)).trans
      (ae_restrict_of_ae hgrep.symm)
  have hg : MemLp g 2 volume :=
    (Lp.memLp (realSolver f hK L₀ Q B output ho hob (retarded 0)
      (SmallSupport.zeroExtend isOpen_ball.measurableSet (Corr h)))).ae_eq hgrep.symm
  have heq : (hg.restrict univ).toLp g = solution := by
    apply Lp.ext
    exact (hg.restrict univ).coeFn_toLp.trans hsol.symm
  have hraw q : MemRestrictionSobolev univ q ((hg.restrict univ).toLp g) ∧
      restrictionSobolevNorm univ q ((hg.restrict univ).toLp g) ≤ Droot q * lam^q := by
    rw [heq]
    exact hsbound q univ
  have hscale q : Cgeom q * Lc^q ≤ Cgeom q * Lpair^q :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans hLc) hLcPair q)
      (zero_le_one.trans (hCgeom q))
  exact hphysical F G hG hψG hV hDer hSrc
    Lpair lam ρ (hLc.trans hLcPair) hLlam hρ hρlam
    (fun l j q x hx ↦ (hVB l j q x hx).trans (hscale q))
    (fun l ij q x hx ↦ (hDB l ij q x hx).trans (hscale q))
    (fun l ij q x hx ↦ (hSB l ij q x hx).trans (hscale q))
    Usource hUsource χ phases amplitudes minus i j hdiag
    hχ hχS hχU hφ hAi hAj hφb hχb hAib hAjb g hgsm hg hraw u hu r

end JanetCartan.PhysicalPairs
