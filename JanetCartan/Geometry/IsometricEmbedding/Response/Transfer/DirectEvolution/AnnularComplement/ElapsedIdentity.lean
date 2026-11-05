module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.SupportedIdentity

/-!
# Exact complementary kernels of the elapsed-time factor

The operator is literally `fullGraphOperator (elapsedPhase Ψ t)` with
`elapsedAmplitude b χout χsource β t`. Its annular complement retains both
physical masks and the complete high-pass factor. Lebesgue measure and the
physical `(2π)⁻ⁿ` constant are unchanged. The reverse kernel conjugates the
full scalar factor and transposes the matrix in the original positions.

Consumer: `app:ch_response:eq:direct-envelope-profile` and the frequency
localization of `app:ch_response:lem:energy-carrier-jets`. The identities here
do not assert complementary Sobolev estimates.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement
open FourierIntegral FourierIntegral.FullLowBounds FourierIntegral.SourceExpansion
open RegularSector.Characteristic.EvolutionIntegral
open JanetCartan.Localization JanetCartan.AmplitudeBound
variable {d r : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)

/-- Literal forward outside-annulus elapsed kernel on the original carrier.
All physical factors remain inside the two-position amplitude; there is no
source-multiplier commutation. -/
theorem elapsedGraph_annularComplement_kernel
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d r)
    (χout χsource β π : E → ℂ) (t lam : ℝ)
    (φ : E → ℝ) (a : E → Fin r → ℂ) (x : E) :
    graphOperator (elapsedPhase Ψ t)
      (annularComplementAmplitude π lam (elapsedAmplitude b χout χsource β t))
      (fun z => carrier lam φ z • a z) x =
    ((2 * Real.pi) ^ (d + 1) : ℂ)⁻¹ • ∫ ξ : E, ∫ z : E,
      phaseOscillation (forwardCarrierSourcePhase (elapsedPhase Ψ t) φ lam x ξ) z •
        (((1 - π (lam⁻¹ • ξ)) * (χout x * χsource z * β ξ)) •
          b (x 0) (x 0 - t) (spatialPart x) (spatialPart ξ)).mulVec (a z) := by
  unfold graphOperator
  congr 1
  apply integral_congr_ae
  filter_upwards [] with ξ
  apply integral_congr_ae
  filter_upwards [] with z
  rw [phaseOscillation_forwardCarrierSourcePhase]
  simp only [annularComplementAmplitude, frequencyCutFullAmplitude, elapsedAmplitude,
    Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul]
  congr 1
  ring

/-- Literal reversed outside-annulus kernel, retaining conjugation of both
physical masks and beta and the actual conjugate-transposed transport matrix.
The source gradient is that of `adjointCarrierSourcePhase`, hence contains
`D_z (elapsedPhase Ψ t)`, not the fixed-transverse translation phase. -/
theorem adjointElapsedGraph_annularComplement_kernel
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d r)
    (χout χsource β π : E → ℂ) (t lam : ℝ)
    (φ : E → ℝ) (a : E → Fin r → ℂ) (x : E) :
    reverseGraphOperator (elapsedPhase Ψ t)
      (fun z x ξ => (annularComplementAmplitude π lam
        (elapsedAmplitude b χout χsource β t) z x ξ).conjTranspose)
      (fun z => carrier lam φ z • a z) x =
    ((2 * Real.pi) ^ (d + 1) : ℂ)⁻¹ • ∫ ξ : E, ∫ z : E,
      phaseOscillation (adjointCarrierSourcePhase (elapsedPhase Ψ t) φ lam x ξ) z •
        (star ((1 - π (lam⁻¹ • ξ)) * (χout z * χsource x * β ξ)) •
          (b (z 0) (z 0 - t) (spatialPart z) (spatialPart ξ)).conjTranspose).mulVec (a z) := by
  unfold reverseGraphOperator
  congr 1
  apply integral_congr_ae
  filter_upwards [] with ξ
  apply integral_congr_ae
  filter_upwards [] with z
  rw [phaseOscillation_adjointCarrierSourcePhase]
  simp only [annularComplementAmplitude, frequencyCutFullAmplitude, elapsedAmplitude,
    Matrix.conjTranspose_smul, Matrix.smul_mulVec, Matrix.mulVec_smul, star_mul, smul_smul]
  congr 1
  ring

/-- Exact uncut annular decomposition of the same elapsed graph and its
literal Hilbert adjoint. The constructed smooth normalized selector discharges
all selector smoothness, compactness, and boundedness requirements. Both
physical support conditions are derived from the original masks. The only
operator limit premise is the original strong realization produced by the
actual full-graph construction; no complementary realization or estimate is
an input. Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem elapsedGraph_annularComplement_eq_sub_of_strong_limit
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d r)
    (χout χsource β : E → ℂ) (t : ℝ)
    {D O : Set (E × E)} (hD : IsClosed D) (hO : IsOpen O) (hDO : D ⊆ O)
    (hΨ : ContDiffOn ℝ ∞ (Function.uncurry (elapsedPhase Ψ t)) O)
    (hA : ContDiff ℝ ∞ (fun p : E × E × E =>
      elapsedAmplitude b χout χsource β t p.1 p.2.1 p.2.2))
    (hsD : ∀ x z ξ, elapsedAmplitude b χout χsource β t x z ξ ≠ 0 → (x, ξ) ∈ D)
    (hout : HasCompactSupport χout) (hsource : HasCompactSupport χsource)
    {R : ℝ} (hbox : ∀ z ∈ tsupport χsource, ∀ i, |z i| ≤ R)
    (μ : ℕ) {B : ℝ}
    (hb : HasFullSourceSymbolBound (elapsedAmplitude b χout χsource β t)
      (μ + lowReserve (d + 1)) B)
    (a₀ b₀ : ℝ) (ha₀ : 0 < a₀) (hb₀ : 0 < b₀) {lam : ℝ} (hlam : 0 < lam)
    (χ : ℕ → E → ℂ) (hχ : ∀ j, ContDiff ℝ ∞ (χ j))
    (hχc : ∀ j, HasCompactSupport (χ j)) (hχb : ∀ j ξ, ‖χ j ξ‖ ≤ 1)
    (hχlim : ∀ ξ, Tendsto (fun j => χ j ξ) atTop (𝓝 1))
    (hstrong : ∀ u : H, Tendsto
      (fun j => fullGraphOperator (elapsedPhase Ψ t)
        (frequencyCutFullAmplitude (χ j) (elapsedAmplitude b χout χsource β t)) u)
      atTop (𝓝 (fullGraphOperator (elapsedPhase Ψ t) (elapsedAmplitude b χout χsource β t) u))) :
    let S := elapsedPhase Ψ t
    let A := elapsedAmplitude b χout χsource β t
    let q := physicalAnnularSelector a₀ b₀ ha₀ hb₀ lam
    fullGraphOperator S (frequencyCutFullAmplitude (fun ξ => 1 - q ξ) A) =
      fullGraphOperator S A - fullGraphOperator S (frequencyCutFullAmplitude q A) ∧
    (fullGraphOperator S (frequencyCutFullAmplitude (fun ξ => 1 - q ξ) A)).adjoint =
      (fullGraphOperator S A).adjoint -
        (fullGraphOperator S (frequencyCutFullAmplitude q A)).adjoint := by
  have hs (x z ξ : E) (h : x ∉ tsupport χout ∨ z ∉ tsupport χsource) :
      elapsedAmplitude b χout χsource β t x z ξ = 0 := by
    rcases h with h | h
    · exact elapsedAmplitude_eq_zero_of_mask b χout χsource β t x z ξ
        (Or.inl (image_eq_zero_of_notMem_tsupport h))
    · exact elapsedAmplitude_eq_zero_of_mask b χout χsource β t x z ξ
        (Or.inr (Or.inl (image_eq_zero_of_notMem_tsupport h)))
  have hboxA (x ξ : E) (i j : Fin r) : SupportedInCenteredBox R
      (fun z => elapsedAmplitude b χout χsource β t x z ξ i j) := by
    intro z hz
    apply hbox z
    by_contra h
    exact hz (by simp [hs x z ξ (Or.inr h)])
  exact fullGraphOperator_complement_eq_sub_of_supported_strong_limit
    (Nat.zero_lt_succ d) (elapsedPhase Ψ t) hD hO hDO hΨ
    (elapsedAmplitude b χout χsource β t) hA hsD hout hsource hs hboxA μ hb
    (physicalAnnularSelector a₀ b₀ ha₀ hb₀ lam)
    (contDiff_physicalAnnularSelector a₀ b₀ ha₀ hb₀ lam)
    (hasCompactSupport_physicalAnnularSelector a₀ b₀ ha₀ hb₀ hlam)
    (norm_physicalAnnularSelector_le_one a₀ b₀ ha₀ hb₀ lam)
    χ hχ hχc hχb hχlim hstrong

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement
