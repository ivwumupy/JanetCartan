module

public import JanetCartan.Iteration.PhysicalPairs.RestrictionSize
public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.NormalizedProductSize

/-!
# Physical reconstruction of the literal signed product source

Apply the checked reconstruction to `ProductSum.plusSource` and
`ProductSum.minusSource`, retaining the full source cutoff and tensor
amplitudes. The reduced solution is the supplied same smooth solution; its
restriction profile is produced by the normalized product solver with both
original source cutoffs and the full zeroth coefficient. No response is
reselected, and the difference diagonal alone is excluded.

This proves the physical size deduction in `main:prop:pairs`
from that lower reduced estimate and primitive coefficient/source jets.
The actual normalized constructor, history profiles and ambient-extension
identification still must be applied on one initialized family for
`UniformStep.ProductProfiles`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
open Set MeasureTheory FourierTransform
open scoped SchwartzMap ContDiff ComplexConjugate Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.PhysicalPairs
open SignedProductEstimates
open ResponseTransfer ResponseTransfer.SourceNegative Sampling.BackgroundModulation
open LocalSobolev Pseudodifferential
variable {n N : ℕ} {ι : Type*}
local notation "E" => Euclidean n

/-- Each literal signed source has physical completed-response size
`D_r * lam^(r+1)`. Its full tensor source profile is derived from the original
phase and amplitude jets. The same reduced solution is used at all orders;
its raw restriction profile comes from the normalized product inverse, which
retains the auxiliary source cutoff. Constants precede sources, samples and
histories, and no separation or accuracy loss appears
(`main:prop:pairs`). -/
theorem exists_product_completedVariation_physicalWeighted_size_constants
    (ψ : E → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    {S : Set E} (hS : IsCompact S)
    (P X C Cgeom Broot : ℕ → ℝ)
    (hP : ∀ r, 0 ≤ P r) (hX : ∀ r, 0 ≤ X r) (hC : ∀ r, 0 ≤ C r)
    (hCgeom : ∀ r, 1 ≤ Cgeom r) (hBroot : ∀ r, 0 ≤ Broot r)
    {Cfreq : ℝ} (hCfreq : 0 ≤ Cfreq) :
    ∃ D : ℕ → ℝ, (∀ r, 0 ≤ D r) ∧
      ∀ (F : E → Euclidean N) (Ω : Set E), IsOpen Ω → tsupport ψ ⊆ Ω →
      (∀ l j, ContDiffOn ℝ ∞ (reconstructionValueEntry F l j) Ω) →
      (∀ l ij, ContDiffOn ℝ ∞ (reconstructionDerivativeEntry F l ij) Ω) →
      (∀ l ij, ContDiffOn ℝ ∞ (reconstructionSourceEntry F l ij) Ω) →
      ∀ (L lam ρ : ℝ), 1 ≤ L → L ≤ lam → 0 < ρ → ρ ≤ Cfreq*lam →
      (∀ l j r, ∀ x ∈ Ω, ‖iteratedFDeriv ℝ r (reconstructionValueEntry F l j) x‖ ≤ Cgeom r * L^r) →
      (∀ l ij r, ∀ x ∈ Ω, ‖iteratedFDeriv ℝ r (reconstructionDerivativeEntry F l ij) x‖ ≤ Cgeom r * L^r) →
      (∀ l ij r, ∀ x ∈ Ω, ‖iteratedFDeriv ℝ r (reconstructionSourceEntry F l ij) x‖ ≤ Cgeom r * L^r) →
      ∀ (U : Set E), IsOpen U → ∀ (χ : E → ℝ)
        (phases : ι → E → ℝ) (amplitudes : ι → E → Matrix (Fin N) (Fin n) ℂ)
        (minus : Bool) (i j : ι), (minus = true → i ≠ j) →
      let φ := fun y ↦ (if minus then phases i y - phases j y else phases i y + phases j y) / ρ
      ContDiff ℝ ∞ χ → tsupport χ ⊆ S → tsupport χ ⊆ U →
      ContDiffOn ℝ ∞ φ U → ContDiffOn ℝ ∞ (amplitudes i) U → ContDiffOn ℝ ∞ (amplitudes j) U →
      (∀ x ∈ U, ∀ r, 1 ≤ r → ‖iteratedFDeriv ℝ r φ x‖ ≤ P r * L^(r-1)) →
      (∀ x ∈ U, ∀ r, ‖iteratedFDeriv ℝ r χ x‖ ≤ X r * L^r) →
      (∀ x ∈ U, ∀ r, ‖iteratedFDeriv ℝ r (amplitudes i) x‖ ≤ C r * L^r) →
      (∀ x ∈ U, ∀ r, ‖iteratedFDeriv ℝ r (amplitudes j) x‖ ≤ C r * L^r) →
      ∀ (g : E → Euclidean n), ContDiff ℝ ∞ g → ∀ hg : MemLp g 2 volume,
      (∀ r : ℕ, MemRestrictionSobolev univ r ((hg.restrict univ).toLp g) ∧
        restrictionSobolevNorm univ r ((hg.restrict univ).toLp g) ≤ Broot r * lam^r) →
      ∀ u : 𝓢(E, Euclidean N),
      (∀ x, u x = ψ x • AmbientResponse.completedVariation F g
        (fun y ↦ χ y • (if minus then ProductSum.minusSource phases amplitudes i j y
          else ProductSum.plusSource phases amplitudes i j y)) x) →
      ∀ r : ℕ,
      (eLpNorm (fun ξ ↦ euclideanSobolevWeight r ((2 * Real.pi) • ξ) •
        𝓕 (PhysicalCutoff.complexify u) ξ) 2 volume).toReal ≤ D r * lam^(r+1) := by
  obtain ⟨J, hJ, hjets⟩ := exists_signed_modulated_source_jet_constants (n := n) (N := N)
    P X C hP hX hC hCfreq
  obtain ⟨D, hD, hphysical⟩ := exists_completedVariation_physicalWeighted_size_of_restriction
    (N := N) ψ hψ hψc hS Cgeom J Broot hCgeom hJ hBroot
  refine ⟨D, hD, ?_⟩
  intro F Ω hΩ hψΩ hV hDer hSrc L lam ρ hL hLlam hρ hρlam
    hVB hDB hSB U hU χ phases amplitudes minus i j _hdiag φ hχ hχS hχU hφ
    hAi hAj hφb hχb hAib hAjb g hgsm hg hraw u hu r
  have hj := hjets U hU L lam ρ ρ hL hLlam hρ.le hρ.le hρlam hρlam
    χ φ φ (amplitudes i) (amplitudes j) hχ.contDiffOn hφ hφ hAi hAj
    hφb hφb hχb hAib hAjb
  obtain ⟨hap, ham⟩ := contDiffOn_signed_tensor_amplitudes hAi hAj
  have hfinish (a : E → Matrix (Fin n) (Fin n) ℂ) (ha : ContDiffOn ℝ ∞ a U)
      (haj : ∀ x ∈ U, ∀ q,
        ‖iteratedFDeriv ℝ q (modulatedSource χ φ a ρ) x‖ ≤ J q * lam^q)
      (he : (fun x ↦ χ x • (if minus then ProductSum.minusSource phases amplitudes i j x
          else ProductSum.plusSource phases amplitudes i j x)) =
        ResponseSourceExtension.tensorFieldRealPart (modulatedSource χ φ a ρ)) :
      (eLpNorm (fun ξ ↦ euclideanSobolevWeight r ((2 * Real.pi) • ξ) •
        𝓕 (PhysicalCutoff.complexify u) ξ) 2 volume).toReal ≤ D r * lam^(r+1) := by
    have hcarrier : ContDiffOn ℝ ∞ (carrier ρ φ) U := by
      change ContDiffOn ℝ ∞ (fun y ↦ Complex.exp (Complex.I * ((ρ * φ y : ℝ) : ℂ))) U
      exact (contDiffOn_const.mul
        (Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_const.mul hφ))).cexp
    have hsm : ContDiff ℝ ∞ (modulatedSource χ φ a ρ) :=
      PrimarySourceAdmission.contDiff_cutoff_of_support_subset hχ hU (hcarrier.smul ha) hχU
    have hs : tsupport (modulatedSource χ φ a ρ) ⊆ tsupport χ := tsupport_smul_subset_left χ _
    have hglobal x q : ‖iteratedFDeriv ℝ q (modulatedSource χ φ a ρ) x‖ ≤ J q * lam^q := by
      by_cases hx : x ∈ U
      · exact haj x hx q
      · have hz : iteratedFDeriv ℝ q (modulatedSource χ φ a ρ) x = 0 := by
          by_contra hn
          exact hx (hχU (hs (support_iteratedFDeriv_subset q hn)))
        rw [hz, norm_zero]
        exact mul_nonneg (hJ q) (pow_nonneg ((zero_le_one.trans hL).trans hLlam) _)
    apply hphysical F Ω hΩ hψΩ g (modulatedSource χ φ a ρ)
      hgsm hsm (hs.trans hχS) hV hDer hSrc L lam hL hLlam hVB hDB hSB hglobal hg hraw u _ r
    simpa only [he] using hu
  cases minus with
  | false =>
    exact hfinish _ hap (fun x hx q ↦ (hj x hx q).1)
      (cutoff_plusSource_eq_real_modulatedSource χ phases amplitudes i j hρ.ne')
  | true =>
    exact hfinish _ ham (fun x hx q ↦ (hj x hx q).2)
      (cutoff_minusSource_eq_real_modulatedSource χ phases amplitudes i j hρ.ne')

end JanetCartan.PhysicalPairs
