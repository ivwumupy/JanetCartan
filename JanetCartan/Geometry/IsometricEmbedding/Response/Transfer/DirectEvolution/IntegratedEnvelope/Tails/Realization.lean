module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.IntegratedEnvelope.Tails.Measurability
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.PrimitiveSobolev
public import Mathlib.Topology.TietzeExtension

/-!
# Supported demodulation of the actual complementary remainder

Only the original observation support is used to extend the scalar carrier for
the measurability proof. The literal kernel and all its derivatives still use
the original carrier. Consumer: elapsed integration of the complementary term
in `app:ch_response:lem:energy-carrier-jets`.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.DirectEvolution.IntegratedEnvelope.Tails
open FourierIntegral FourierIntegral.FullLowBounds AnnularComplement
open RegularSector.Characteristic.EvolutionIntegral
open JanetCartan.ResponseTransfer.Complement
variable {d r : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "F" => EuclideanSpace ℂ (Fin r)
local notation "H" => SpacetimeL2 d r

/-- A continuous carrier on the fixed observation support suffices for time
measurability of the demodulated remainder. The extension is used only as a
bounded multiplier on already supported L² elements, and has no quantitative
or differentiated role. Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem aestronglyMeasurable_supported_demodulation
    {Δ lam : ℝ} {X : Set E} (hX : IsClosed X) (φ : E → ℝ)
    (hφ : ContinuousOn φ X) (R S : ℝ → H)
    (hm : AEStronglyMeasurable R (volume.restrict (Icc 0 Δ)))
    (hs : ∀ t ∈ Icc 0 Δ, ∀ᵐ x ∂volume, x ∉ X → R t x = 0)
    (he : ∀ t ∈ Icc 0 Δ, S t =ᵐ[volume] fun x => carrier (-lam) φ x • R t x) :
    AEStronglyMeasurable S (volume.restrict (Icc 0 Δ)) := by
  let f : C(X, ℝ) := ⟨fun x => φ x, continuousOn_iff_continuous_domRestrict.mp hφ⟩
  obtain ⟨g, hg⟩ := f.exists_restrict_eq hX
  have hgφ (x : E) (hx : x ∈ X) : g x = φ x :=
    congrArg (fun q : C(X, ℝ) => q ⟨x, hx⟩) hg
  let T : H →L[ℂ] H := carrierMultiplication (-lam) g g.continuous
  have hT (t : ℝ) (ht : t ∈ Icc 0 Δ) : T (R t) = S t := by
    apply Lp.ext
    filter_upwards [carrierMultiplication_ae (-lam) g g.continuous (R t), hs t ht,
      he t ht] with x hx hsx hex
    rw [hx, hex]
    by_cases h : x ∈ X
    · simp only [carrier, hgφ x h]
    · rw [hsx h, smul_zero, smul_zero]
  apply (T.continuous.comp_aestronglyMeasurable hm).congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact hT t ht

/-- The two literal kernel representatives identify physical demodulation
and prove fixed output support. Both masks are retained; the adjoint exchanges
which one enforces output support. The representative premises are exactly
the third conclusion of `originalAnnularComplement_sobolev`, not estimates.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem annularRemainder_support_and_demodulation
    (adj : Bool) (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d r)
    (χout χsource β π : E → ℂ) (φ : E → ℝ) (lam t : ℝ) (a : E → F)
    {X : Set E} (hmask : tsupport χout ∪ tsupport χsource ⊆ X)
    (R : Bool → H)
    (hR : ∀ dm, R dm =ᵐ[volume] fun x => ∫ ξ,
      annularSourceKernelObservation adj dm (elapsedPhase Ψ t)
        (elapsedAmplitude b χout χsource β t) π φ lam a x ξ) :
    (∀ᵐ x ∂volume, x ∉ X → R false x = 0) ∧
    R true =ᵐ[volume] fun x => carrier (-lam) φ x • R false x := by
  constructor
  · filter_upwards [hR false] with x hx hxX
    rw [hx]
    have hzero (ξ : E) : annularSourceKernelObservation adj false (elapsedPhase Ψ t)
        (elapsedAmplitude b χout χsource β t) π φ lam a x ξ = 0 := by
      apply annularSourceKernelObservation_eq_zero_of_amplitude
      intro z
      cases adj
      · exact elapsedAmplitude_eq_zero_of_mask _ _ _ _ _ _ _ _
          (Or.inl (image_eq_zero_of_notMem_tsupport (fun h => hxX (hmask (Or.inl h)))))
      · exact elapsedAmplitude_eq_zero_of_mask _ _ _ _ _ _ _ _
          (Or.inr (Or.inl (image_eq_zero_of_notMem_tsupport
            (fun h => hxX (hmask (Or.inr h))))))
    simp only [hzero, integral_zero]
  · filter_upwards [hR true, hR false] with x hx hy
    rw [hx, hy]
    cases adj <;> simp only [annularSourceKernelObservation, Bool.false_eq_true,
      ↓reduceIte, demodulatedForwardAnnularSourceKernel,
      demodulatedAdjointAnnularSourceKernel, integral_smul]

end JanetCartan.ResponseTransfer.DirectEvolution.IntegratedEnvelope.Tails
