module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ParameterDerivatives.InactiveDerivatives.JetProfiles

/-!
# Original envelope jets with finite carrier order

The envelope input to the mixed original-amplitude estimate in
`app:ch_response:lem:energy-carrier-jets`. The source Sobolev reserve is `n+1`.
Only the indicated carrier derivative is used, regardless of source order.
The support and L² representative are those of the original envelope.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement.AmplitudeJets.OriginalProfiles
open Complement.ParameterDerivatives Complement.InactiveSource JanetCartan.Pseudodifferential
variable {p n r : ℕ}
local notation "P" => Euclidean p
local notation "E" => Euclidean n
local notation "F" => EuclideanSpace ℂ (Fin r)

/-- Original parameter-envelope Sobolev norms imply the actual mixed jets.
The consuming annular Leibniz term uses carrier order `vs.length`, which is
at most its external order; increasing `k` does not change it.
Source: `app:ch_response:lem:energy-carrier-jets` and
`app:ch_response:eq:direct-envelope-profile`. -/
theorem norm_sourceJet_parameterListJet_le_sobolev
    {V : Set P} {S : Set E} (hV : IsOpen V) (hS : IsCompact S)
    {a : P → E → F} (ha : ContDiffOn ℝ ∞ (Function.uncurry a) (V ×ˢ univ))
    (hs : ∀ c ∈ V, tsupport (a c) ⊆ S)
    (vs : List P) {c : P} (hc : c ∈ V) (C : ℕ → ℝ)
    {A₀ K : ℝ} (hA : 0 ≤ A₀) (hK : 1 ≤ K)
    (hmem : ∀ s : ℕ, MemVectorFourierSobolev (s : ℝ)
      ((parameterSource_memLp hS hV ha hs vs.length vs.get hc).toLp
        (fun z => parameterListJet (fun q => a q z) vs c)))
    (hprofile : ∀ s : ℕ, vectorFourierSobolevNorm (s : ℝ)
      ((parameterSource_memLp hS hV ha hs vs.length vs.get hc).toLp
        (fun z => parameterListJet (fun q => a q z) vs c)) ≤
          C s * A₀ * K ^ (s + vs.length))
    (k : ℕ) (z : E) :
    ‖iteratedFDeriv ℝ k (fun y => parameterListJet (fun q => a q y) vs c) z‖ ≤
      envelopeJetProfileConstant n C k * A₀ * K ^ (n + 1 + vs.length) * K ^ k := by
  have hK0 := zero_le_one.trans hK
  have hb (s : ℕ) : vectorFourierSobolevNorm (s : ℝ)
      ((parameterSource_memLp hS hV ha hs vs.length vs.get hc).toLp
        (fun z => parameterListJet (fun q => a q z) vs c)) ≤
      C s * (A₀ * K ^ vs.length) * K ^ s := by
    convert hprofile s using 1
    simp only [pow_add]
    ring
  have h := norm_iteratedFDeriv_le_envelope_profile
    (contDiff_originalSourceListJet hV ha vs hc).continuous
    (parameterSource_memLp hS hV ha hs vs.length vs.get hc)
    (mul_nonneg hA (pow_nonneg hK0 _)) hK hmem hb k z
  convert h using 1
  simp only [pow_add]
  ring

/-- The constants for finite carrier order are chosen before scales, datum,
carrier value or direction tuple. The input at each order `j ≤ l` is the
original `j`th parameter derivative, never a mixed amplitude or normalized
jet. Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem exists_originalEnvelope_finite_mixed_profile (p n r l : ℕ) (C : ℕ → ℕ → ℝ) :
    ∃ Q : ℕ → ℕ → ℝ, (∀ j k, 0 ≤ Q j k) ∧
      ∀ (V : Set (Euclidean p)) (S : Set (Euclidean n))
        (hV : IsOpen V) (hS : IsCompact S)
        (a : Euclidean p → Euclidean n → EuclideanSpace ℂ (Fin r))
        (ha : ContDiffOn ℝ ∞ (Function.uncurry a) (V ×ˢ univ))
        (hs : ∀ c ∈ V, tsupport (a c) ⊆ S)
        (A₀ K : ℝ), 0 ≤ A₀ → 1 ≤ K →
        ∀ (j : ℕ), j ≤ l → ∀ (v : Fin j → Euclidean p), (∀ i, ‖v i‖ ≤ 1) →
        ∀ (c : Euclidean p) (hc : c ∈ V),
        let hm := parameterSource_memLp hS hV ha hs j v hc
        (∀ s : ℕ, MemVectorFourierSobolev (s : ℝ)
          (hm.toLp (fun z => iteratedFDeriv ℝ j (fun q => a q z) c v))) →
        (∀ s : ℕ, vectorFourierSobolevNorm (s : ℝ)
          (hm.toLp (fun z => iteratedFDeriv ℝ j (fun q => a q z) c v)) ≤
            C j s * A₀ * K ^ (s + j)) →
        ∀ k z, ‖iteratedFDeriv ℝ k
          (fun y => iteratedFDeriv ℝ j (fun q => a q y) c v) z‖ ≤
            Q j k * A₀ * K ^ (n + 1 + j) * K ^ k := by
  refine ⟨fun j k => envelopeJetProfileConstant n (C j) k,
    fun j k => envelopeJetProfileConstant_nonneg n (C j) k, ?_⟩
  intro V S hV hS a ha hs A₀ K hA hK j _hj v _hv c hc hm hmem hprofile k z
  have hcont : ContDiff ℝ ∞
      (fun y => iteratedFDeriv ℝ j (fun q => a q y) c v) := by
    simpa only [parameterListJet_ofFn] using
      contDiff_originalSourceListJet hV ha (List.ofFn v) hc
  have hb (s : ℕ) : vectorFourierSobolevNorm (s : ℝ)
      (hm.toLp (fun z => iteratedFDeriv ℝ j (fun q => a q z) c v)) ≤
        C j s * (A₀ * K ^ j) * K ^ s := by
    convert hprofile s using 1
    simp only [pow_add]
    ring
  have h := norm_iteratedFDeriv_le_envelope_profile hcont.continuous hm
    (mul_nonneg hA (pow_nonneg (zero_le_one.trans hK) _)) hK hmem hb k z
  convert h using 1
  simp only [pow_add]
  ring

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement.AmplitudeJets.OriginalProfiles
