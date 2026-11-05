module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.IntegratedEnvelope.Parameter.LocalDomination.Directions
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.IntegratedEnvelope.Parameter.DatumBounds
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.ReverseAssembly.Joint

/-!
# Local domination for the literal Hilbert adjoint

The primitive joint endpoint at spatial order zero and the local L² profile of
the actual original datum give one neighborhood and bound for each arbitrary
parameter word, uniformly over the SAME elapsed-time interval. Geometry may vary
with elapsed time; the scalar primitive profiles and fixed reserve stay fixed.
No time regularity of critical maps or output smoothness is used.

Consumer: the `hb` argument of `orderedTransferAction_elapsedIntegral`.
Sources: `app:ch_response:eq:direct-envelope-profile`,
`app:ch_response:lem:energy-carrier-jets`, and `new:eq:carrier-ibp`.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option cleanup.letToHave false
open Set MeasureTheory Filter LineDeriv
open scoped ContDiff Topology Matrix.Norms.Frobenius SchwartzMap
namespace JanetCartan.ResponseTransfer.DirectEvolution.IntegratedEnvelope.Parameter
open Pseudodifferential FourierIntegral FourierIntegral.FullLowBounds FourierIntegral.LowBounds
open FourierIntegral.SourceExpansion NormalComparison FrequencyCutoff AmplitudeBound
open FullAmplitudePrimitiveBudget.Local CompactTransfer BranchAmplitudes ModifiedLow
open RegularSector.Characteristic.EvolutionIntegral
variable {d r : ℕ} {P ι : Type}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] [Fintype ι]
local notation "E" => Euclidean (d + 1)
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ
local notation "Vf" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp Vf 2 (volume : Measure E)
open AnnularSobolev
local instance localDominationAdjointMatrixTopology : TopologicalSpace Mat :=
  (Matrix.frobeniusNormedAddCommGroup (m := Fin r) (n := Fin r)
    (α := ℂ)).toUniformSpace.toTopologicalSpace

attribute [local irreducible] normalizedTermAmplitude elapsedCarrierPhase
  averagedPhaseHessian modifiedAmplitude fullGraphOperator

/-- The literal Hilbert adjoint on the actual original datum has a locally
uniform L² bound for every parameter word through order `N`, on the full original
elapsed interval. Only the original low reserve plus `N` (and the existing phase
offset two) is used. The neighborhood comes from the common original-datum jet
profile; the bound may depend on the fixed scales and directions. This is exactly
the local domination input for `orderedTransferAction_elapsedIntegral`.
Sources: `app:ch_response:eq:direct-envelope-profile` and `new:eq:carrier-ibp`. -/
theorem exists_annularEnvelope_adjoint_local_word_bounds_of_primitive_jets
    (R ℓ M G c : ℝ) (hℓ : 0 < ℓ) (hRcell : R / ℓ < 1 / 2)
    {δ F : ℝ} (hδ : 0 < δ) (hF : 0 ≤ F) (hc : 1 ≤ c)
    (basis : OrthonormalBasis ι ℝ (CarrierVariables (d + 1)))
    (N : ℕ)
    (Aphase Aamp : ℕ → ℝ) (hphase : ∀ j, 0 ≤ Aphase j) (hamp : ∀ j, 0 ≤ Aamp j)
    {B radius : ℝ} (hB : 0 ≤ B) (hradius : 0 ≤ radius)
    (Ksource Ssource : Set E) (hKsource : IsCompact Ksource)
    (hSsource : IsOpen Ssource) (hKS : Ksource ⊆ Ssource) :
    ∀ (X₀ Y₀ F₀ : Set E), IsCompact X₀ → IsCompact Y₀ →
      (∀ y ∈ Y₀, ∀ i : Fin (d + 1), |y i| ≤ R) → IsClosed F₀ → (0 : E) ∉ F₀ →
    ∀ (Ψ : TwoTimePhase d) (Δ : ℝ) (_hΔ : 0 ≤ Δ)
    (_hS : ∀ t ∈ Icc 0 Δ, ContDiff ℝ ∞ (Function.uncurry (elapsedPhase Ψ t)))
    {X D : ℝ → Set E} {η : ℝ → E → E → E → E} {J : ℝ → E → E → E → E →L[ℝ] E}
    {W K : ℝ → Set (NormalVariables (d + 1))}
    (_chart : ∀ t ∈ Icc 0 Δ, AveragedGradientChart (elapsedPhase Ψ t) (X t) (D t) (η t) (J t) δ)
    (_hopen : ∀ t ∈ Icc 0 Δ, IsOpen (bufferedNormalDomain (X t) (D t) (elapsedPhase Ψ t)))
    (_hηinput : ∀ t ∈ Icc 0 Δ, ContDiffOn ℝ ∞ (normalInverseCoordinates (η t)) (bufferedNormalDomain (X t) (D t) (elapsedPhase Ψ t)))
    (_hmapinput : ∀ t ∈ Icc 0 Δ, MapsTo (normalInverseCoordinates (η t)) (bufferedNormalDomain (X t) (D t) (elapsedPhase Ψ t)) (W t))
    (_hJinput : ∀ t ∈ Icc 0 Δ, ContDiffOn ℝ ∞ (fun q : NormalVariables (d + 1) ↦ (J t) q.1 q.2.1 q.2.2) (W t))
    (_hgapinput : ∀ t ∈ Icc 0 Δ, ∀ q ∈ (W t), ((J t) q.1 q.2.1 q.2.2).det ≠ 0)
    (_hrightInverse : ∀ t ∈ Icc 0 Δ, ∀ q ∈ bufferedNormalDomain (X t) (D t) (elapsedPhase Ψ t),
      normalForwardCoordinates (elapsedPhase Ψ t) (normalInverseCoordinates (η t) q) = q)
    (_hcarrier : ∀ t ∈ Icc 0 Δ, ∀ q ∈ (W t), q.1 ∈ X₀ → q.2.1 ∈ X₀ → q.2.2 ∈ F₀ → q ∈ (K t))
    (_hclosed : ∀ t ∈ Icc 0 Δ, IsClosed (normalForwardCoordinates (elapsedPhase Ψ t) '' (K t)))
    (_hbuffer : ∀ t ∈ Icc 0 Δ, normalForwardCoordinates (elapsedPhase Ψ t) '' (K t) ⊆ bufferedNormalDomain (X t) (D t) (elapsedPhase Ψ t))
    (_hR : ∀ t ∈ Icc 0 Δ, ∀ x ∈ (X t), ‖x‖ ≤ R)
    (_hgrowth : ∀ t ∈ Icc 0 Δ, ∀ x ∈ (X t), ∀ y ∈ (X t), ∀ u ∈ (D t),
      ‖averagedGradient (elapsedPhase Ψ t) x y u‖ ≤ F * (1 + ‖u‖))
    (V : ℝ → ℕ → Set (NormalVariables (d + 1)))
    (_hUopen : ∀ t ∈ Icc 0 Δ, ∀ l, IsOpen (normalDyadicShell (bufferedNormalDomain (X t) (D t) (elapsedPhase Ψ t)) l))
    (_hVopen : ∀ t ∈ Icc 0 Δ, ∀ l, IsOpen ((V t) l))
    (_hη : ∀ t ∈ Icc 0 Δ, ∀ l, ContDiffOn ℝ ∞
      (normalInverseCoordinates (normalizedNormalInverse ((2 : ℝ)^l) (η t)))
      (normalDyadicShell (bufferedNormalDomain (X t) (D t) (elapsedPhase Ψ t)) l))
    (_hmap : ∀ t ∈ Icc 0 Δ, ∀ l, MapsTo
      (normalInverseCoordinates (normalizedNormalInverse ((2 : ℝ)^l) (η t)))
      (normalDyadicShell (bufferedNormalDomain (X t) (D t) (elapsedPhase Ψ t)) l) ((V t) l))
    (_hJ : ∀ t ∈ Icc 0 Δ, ∀ l, ContDiffOn ℝ ∞
      (fun q : NormalVariables (d + 1) ↦
        normalizedNormalJacobian ((2 : ℝ)^l) (J t) q.1 q.2.1 q.2.2) ((V t) l))
    (_hgap : ∀ t ∈ Icc 0 Δ, ∀ l z, z ∈ (V t) l → δ ≤ |(normalizedNormalJacobian
      ((2 : ℝ)^l) (J t) z.1 z.2.1 z.2.2).det|)
    (_hJjet : ∀ t ∈ Icc 0 Δ, ∀ l z, z ∈ (V t) l → ∀ i ≤ primitiveNormalReserve (d + 1),
      ‖iteratedFDeriv ℝ i (fun q : NormalVariables (d + 1) ↦
        normalizedNormalJacobian ((2 : ℝ)^l) (J t) q.1 q.2.1 q.2.2) z‖ ≤ M)
    (_hηjet : ∀ t ∈ Icc 0 Δ, ∀ l z, z ∈ normalDyadicShell (bufferedNormalDomain (X t) (D t) (elapsedPhase Ψ t)) l →
      ∀ i, 1 ≤ i → i ≤ primitiveNormalReserve (d + 1) →
      ‖iteratedFDeriv ℝ i (normalInverseCoordinates
        (normalizedNormalInverse ((2 : ℝ)^l) (η t))) z‖ ≤ G)
    (_hscale : ∀ t ∈ Icc 0 Δ, ∀ l z, z ∈ (V t) l →
      (2 : ℝ)^l ≤ c * (1 + ‖(2 : ℝ)^l • z.2.2‖))
    (_hX₀ : ∀ t ∈ Icc 0 Δ, X₀ ⊆ (X t)) (_hF₀ : ∀ t ∈ Icc 0 Δ, F₀ ⊆ (D t)),
    ∀ (Rstar : ℕ), fullLowReserve (d + 1) + 2 < Rstar →
    ∀ (L lam : ℝ), 1 ≤ L → 1 ≤ lam → ∀ (p : ℤ)
    (φ : E → P → ℝ) (w₀ : ℝ → E × P → CarrierVariables (d + 1))
    (A : TwoTimeAmplitude d r) (χout χsource β π : E → ℂ),
    let α := fun t ↦ normalizedAdjointAnnularElapsedAmplitude (P := P) A χout χsource β π t lam p
    ∀ (U : ℝ → Set (E × P)) (Dcrit : ℝ → Set (CarrierVariables (d + 1))),
    ∀
    (_hU : ∀ t ∈ Icc 0 Δ, IsOpen (U t))
    (_hDcrit : ∀ t ∈ Icc 0 Δ, IsOpen (Dcrit t))
    (_hcD : ∀ t ∈ Icc 0 Δ, Convex ℝ (Dcrit t))
    (_hf : ∀ t ∈ Icc 0 Δ, ContDiffOn ℝ ∞ (Function.uncurry (adjointCarrierPhase (elapsedPhase Ψ t) φ)) ((U t) ×ˢ (Dcrit t)))
    (_hw₀ : ∀ t ∈ Icc 0 Δ, ContDiffOn ℝ ∞ (w₀ t) (U t))
    (_h₀ : ∀ t ∈ Icc 0 Δ, MapsTo (w₀ t) (U t) (Dcrit t))
    (_hcrit : ∀ t ∈ Icc 0 Δ, (∀ q ∈ (U t), gradient (adjointCarrierPhase (elapsedPhase Ψ t) φ q) ((w₀ t) q) = 0))
    (_hvalue : ∀ t ∈ Icc 0 Δ, (∀ q ∈ (U t), adjointCarrierPhase (elapsedPhase Ψ t) φ q ((w₀ t) q) = 0))
    (_hu : ∀ t ∈ Icc 0 Δ, (∀ q ∈ (U t), ∀ w ∈ (Dcrit t), IsUnit (averagedPhaseHessian (adjointCarrierPhase (elapsedPhase Ψ t) φ) (w₀ t) q w)))
    (_hi : ∀ t ∈ Icc 0 Δ, (∀ q ∈ (U t), ∀ w ∈ (Dcrit t),
      ‖Ring.inverse (averagedPhaseHessian (adjointCarrierPhase (elapsedPhase Ψ t) φ) (w₀ t) q w)‖ ≤ B))
    (_hp : ∀ t ∈ Icc 0 Δ, (∀ j ≤ fullLowReserve (d + 1) + N + 2,
      ∀ q ∈ (U t) ×ˢ (Dcrit t),
        ‖iteratedFDeriv ℝ j (Function.uncurry (adjointCarrierPhase (elapsedPhase Ψ t) φ)) q‖ ≤
          Aphase j * L ^ (j - Rstar)))
    (_hα : ∀ t ∈ Icc 0 Δ, ContDiffOn ℝ ∞ (Function.uncurry (α t)) ((U t) ×ˢ (Dcrit t)))
    (_hαjet : ∀ t ∈ Icc 0 Δ, (∀ j ≤ fullLowReserve (d + 1) + N,
      ∀ q ∈ (U t) ×ˢ (Dcrit t),
        ‖iteratedFDeriv ℝ j (Function.uncurry (α t)) q‖ ≤ Aamp j * L ^ (j + 2 - Rstar))),
    ∀ (Kcrit : ℝ → Set (CarrierVariables (d + 1))),
    ∀
    (_hKcrit : ∀ t ∈ Icc 0 Δ, IsCompact (Kcrit t))
    (_hKD : ∀ t ∈ Icc 0 Δ, (Kcrit t) ⊆ (Dcrit t))
    (_hsupportCrit : ∀ t ∈ Icc 0 Δ, (∀ q ∈ (U t), Function.support ((α t) q) ⊆ (Kcrit t)))
    (_houtput : ∀ t ∈ Icc 0 Δ, (∀ q ∈ tsupport (Function.uncurry (α t)), q.1.1 ∈ Y₀)),
    ∀ (Cpar : Set P), IsOpen Cpar → (∀ t ∈ Icc 0 Δ, Y₀ ×ˢ Cpar ⊆ U t) →
    ∀ (hcφ : ∀ param, Continuous (fun x => φ x param)),
    ∀
    (_hs : ∀ t ∈ Icc 0 Δ, (∀ param ∈ Cpar, ∀ q, normalizedSlice param q ∈ tsupport (Function.uncurry (α t)) →
      normalizedSlice param q ∈ (U t) ×ˢ (Dcrit t)))
    (_hsfreq : ∀ t ∈ Icc 0 Δ, (∀ param ∈ Cpar, ∀ q, normalizedSlice param q ∈ tsupport (Function.uncurry (α t)) → ‖q.2‖ ≤ radius))
    (_hsupport : ∀ t ∈ Icc 0 Δ, (∀ param ∈ Cpar, ∀ q, normalizedSlice param q ∈ tsupport (Function.uncurry (α t)) →
      q.1.2 ∈ X₀ ∧ q.1.1 ∈ Y₀ ∧ lam • q.2 ∈ F₀))
    (_hΘ : ∀ t ∈ Icc 0 Δ, (∀ x ∈ X₀, ∀ θ, lam • θ ∈ F₀ →
      elapsedPhase Ψ t x (lam • θ) = lam * elapsedPhase Ψ t x θ)),
    (∀ param ∈ Cpar, ContDiffOn ℝ ∞ (fun x => φ x param) Ssource) →
    ∀ (a : E × P → Vf) (ha : ContDiff ℝ ∞ a)
      (has : ∀ q, q.1 ∉ Ksource → a q = 0),
    ∀ qs : List P, qs.length ≤ N → ∀ param ∈ Cpar,
      ∃ Q ∈ 𝓝 param, Q ⊆ Cpar ∧ ∃ bound : ℝ,
        ∀ t ∈ Icc 0 Δ, ∀ b ∈ Q,
          ‖orderedTransferAction (fun v F c => fderiv ℝ F c v) qs
            (fun c => (annularEnvelopeOperator Ψ A χout χsource β π t lam
              (fun x => φ x c) (hcφ c)).adjoint
              (graphTestToLp (vectorOriginalDatumTest a ha hKsource has [] c))) b‖ ≤ bound := by
  intro X₀ Y₀ F₀ hXcompact hYcompact hYbox hFclosed hFzero Ψ Δ hΔ hS
    X D η J Wnormal Knormal chart hopen hηinput hmapinput hJinput hgapinput
    hrightInverse hcarrier hclosed hbuffer hR hgrowth V hUopen hVopen hη hmap hJ
    hgap hJjet hηjet hscale hX₀ hF₀ Rstar hRstar L lam hL hlam p φ w₀ A χout χsource β π
  dsimp only
  intro U Dcrit hU hDcrit hcD hf hw₀ h₀ hcrit hvalue hu hi hp hα hαjet
    Kcrit hKcrit hKD hsupportCrit houtput Cpar hCpar hXU hcφ hs hsfreq hsupport
    hΘ hφ a ha has qs hqs param hparam
  obtain ⟨us, hlen, hus, k, hrescale⟩ := exists_unitParameterWord_rescaling (F := H) qs
  obtain ⟨C, _hC, hbuild⟩ := exists_annularEnvelope_adjoint_joint_sobolev_of_primitive_jets
    (r := r) R ℓ M G c hℓ hRcell hδ hF hc basis 0 us hus
    Aphase Aamp hphase hamp hB hradius
  obtain ⟨ε, hε, hεCpar, Ddata, hDdata, hdata⟩ :=
    exists_originalDatumJet_local_l2_bounds a ha hKsource has hCpar hparam
  let bound : ℝ := C * lam ^ p *
    (∑ j ∈ Finset.range (us.length + 1), L ^ (us.length - j) * Ddata j)
  refine ⟨Metric.closedBall param ε, Metric.closedBall_mem_nhds _ hε, hεCpar,
    ‖k‖ * bound, ?_⟩
  intro t ht b hb
  have hpoint := hbuild
    X₀ Y₀ F₀ hXcompact hYcompact hYbox hFclosed hFzero Ψ t (hS t ht)
    (chart t ht) (hopen t ht) (hηinput t ht) (hmapinput t ht) (hJinput t ht) (hgapinput t ht)
    (hrightInverse t ht) (hcarrier t ht) (hclosed t ht) (hbuffer t ht) (hR t ht) (hgrowth t ht)
    (V t) (hUopen t ht) (hVopen t ht) (hη t ht) (hmap t ht) (hJ t ht)
    (hgap t ht) (hJjet t ht) (hηjet t ht) (hscale t ht) (hX₀ t ht) (hF₀ t ht)
    Rstar hRstar L lam hL hlam p φ (w₀ t) A χout χsource β π
    (U t) (Dcrit t) (hU t ht) (hDcrit t ht) (hcD t ht) (hf t ht) (hw₀ t ht)
    (h₀ t ht) (hcrit t ht) (hvalue t ht) (hu t ht) (hi t ht)
    (fun j hj => hp t ht j (by omega)) (hα t ht)
    (fun j hj => hαjet t ht j (by omega))
    (Kcrit t) (hKcrit t ht) (hKD t ht) (hsupportCrit t ht) (houtput t ht)
    Cpar hCpar (hXU t ht) hcφ (hs t ht) (hsfreq t ht) (hsupport t ht)
    (hΘ t ht) Ksource Ssource hKsource hSsource hKS hφ a ha has
    b (hεCpar hb) Ddata hDdata (fun j _ => hdata b hb j)
  have hnorm : ‖orderedTransferAction (fun v F c => fderiv ℝ F c v) us
      (fun c => (annularEnvelopeOperator Ψ A χout χsource β π t lam
          (fun x => φ x c) (hcφ c)).adjoint
          (graphTestToLp (vectorOriginalDatumTest a ha hKsource has [] c))) b‖ ≤ bound := by
    simpa only [Nat.cast_zero, vectorFourierSobolevNorm_zero, zero_add] using hpoint.2
  rw [hrescale, Pi.smul_apply, norm_smul]
  exact mul_le_mul_of_nonneg_left hnorm (norm_nonneg k)

end JanetCartan.ResponseTransfer.DirectEvolution.IntegratedEnvelope.Parameter
