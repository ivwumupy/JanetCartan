module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.IntegratedEnvelope.Basic
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.IntegratedEnvelope.Parameter.TimeDifferentiation
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.IntegratedEnvelope.Parameter.LocalDomination.Forward
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.IntegratedEnvelope.Parameter.Regularity.Forward
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.JointEnvelope

/-!
# Joint parameter bounds for the integrated forward annular envelope

The actual ordered L² derivatives commute with elapsed-time integration. Their
measurability, fixed-time smoothness and local domination are all constructed
from the original compact kernels, supported primitive geometry and datum jets.
The primitive joint Sobolev bounds then integrate with exactly the factor `Δ`.
Consumer: `app:ch_response:eq:direct-envelope-profile` and fixed-factor transfer.
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
local instance integratedParameterForwardMatrixTopology : TopologicalSpace Mat :=
  (Matrix.frobeniusNormedAddCommGroup (m := Fin r) (n := Fin r)
    (α := ℂ)).toUniformSpace.toTopologicalSpace

attribute [local irreducible] normalizedTermAmplitude elapsedCarrierPhase
  averagedPhaseHessian modifiedAmplitude fullGraphOperator

/-- Actual parameter differentiation of the SAME annular integral, joint weighted
Sobolev bounds and the original `Kinput^(s+ps.length)` profile. The physical
operator, masks, beta and frequency stay fixed; the parameter derivatives act
on the carrier and original datum. No time regularity of the critical map is
needed. Constants
precede scales and varying fields; the low reserve is fixed, including for
`p = 0` and `p = -1`. All analytic differentiation and integrability premises
are discharged by the concrete annular producers. Sources:
`app:ch_response:eq:direct-envelope-profile`,
`app:ch_response:lem:energy-carrier-jets`, and `new:eq:carrier-ibp`. -/
theorem exists_annularEnvelopeIntegral_joint_envelope_of_primitive_jets
    (R ℓ M G c : ℝ) (hℓ : 0 < ℓ) (hRcell : R / ℓ < 1 / 2)
    {δ F : ℝ} (hδ : 0 < δ) (hF : 0 ≤ F) (hc : 1 ≤ c)
    (basis : OrthonormalBasis ι ℝ (CarrierVariables (d + 1)))
    (s : ℕ) (ps : List P) (hps : ∀ v ∈ ps, ‖v‖ ≤ 1)
    (Aphase Aamp : ℕ → ℝ) (hphase : ∀ j, 0 ≤ Aphase j) (hamp : ∀ j, 0 ≤ Aamp j)
    {B radius : ℝ} (hB : 0 ≤ B) (hradius : 0 ≤ radius)
    (Ksource Ssource : Set E) (hKsource : IsCompact Ksource)
    (hSsource : IsOpen Ssource) (hKS : Ksource ⊆ Ssource) :
    ∃ C ≥ 0, ∀ (X₀ Y₀ F₀ : Set E), IsCompact X₀ →
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
    let α := fun t ↦ normalizedAnnularElapsedAmplitude (P := P) A χout χsource β π t lam p
    ∀ (U : ℝ → Set (E × P)) (Dcrit : ℝ → Set (CarrierVariables (d + 1))),
    ∀
    (_hU : ∀ t ∈ Icc 0 Δ, IsOpen (U t))
    (_hDcrit : ∀ t ∈ Icc 0 Δ, IsOpen (Dcrit t))
    (_hcD : ∀ t ∈ Icc 0 Δ, Convex ℝ (Dcrit t))
    (_hf : ∀ t ∈ Icc 0 Δ, ContDiffOn ℝ ∞ (Function.uncurry (elapsedCarrierPhase Ψ t φ)) ((U t) ×ˢ (Dcrit t)))
    (_hw₀ : ∀ t ∈ Icc 0 Δ, ContDiffOn ℝ ∞ (w₀ t) (U t))
    (_h₀ : ∀ t ∈ Icc 0 Δ, MapsTo (w₀ t) (U t) (Dcrit t))
    (_hcrit : ∀ t ∈ Icc 0 Δ, (∀ q ∈ (U t), gradient (elapsedCarrierPhase Ψ t φ q) ((w₀ t) q) = 0))
    (_hvalue : ∀ t ∈ Icc 0 Δ, (∀ q ∈ (U t), elapsedCarrierPhase Ψ t φ q ((w₀ t) q) = 0))
    (_hu : ∀ t ∈ Icc 0 Δ, (∀ q ∈ (U t), ∀ w ∈ (Dcrit t), IsUnit (averagedPhaseHessian (elapsedCarrierPhase Ψ t φ) (w₀ t) q w)))
    (_hi : ∀ t ∈ Icc 0 Δ, (∀ q ∈ (U t), ∀ w ∈ (Dcrit t),
      ‖Ring.inverse (averagedPhaseHessian (elapsedCarrierPhase Ψ t φ) (w₀ t) q w)‖ ≤ B))
    (_hp : ∀ t ∈ Icc 0 Δ, (∀ j ≤ fullLowReserve (d + 1) + (s + ps.length) + 2,
      ∀ q ∈ (U t) ×ˢ (Dcrit t),
        ‖iteratedFDeriv ℝ j (Function.uncurry (elapsedCarrierPhase Ψ t φ)) q‖ ≤
          Aphase j * L ^ (j - Rstar)))
    (_hα : ∀ t ∈ Icc 0 Δ, ContDiffOn ℝ ∞ (Function.uncurry (α t)) ((U t) ×ˢ (Dcrit t)))
    (_hαjet : ∀ t ∈ Icc 0 Δ, (∀ j ≤ fullLowReserve (d + 1) + (s + ps.length),
      ∀ q ∈ (U t) ×ˢ (Dcrit t),
        ‖iteratedFDeriv ℝ j (Function.uncurry (α t)) q‖ ≤ Aamp j * L ^ (j + 2 - Rstar))),
    ∀ (Kcrit : ℝ → Set (CarrierVariables (d + 1))),
    ∀
    (_hKcrit : ∀ t ∈ Icc 0 Δ, IsCompact (Kcrit t))
    (_hKD : ∀ t ∈ Icc 0 Δ, (Kcrit t) ⊆ (Dcrit t))
    (_hsupportCrit : ∀ t ∈ Icc 0 Δ, (∀ q ∈ (U t), Function.support ((α t) q) ⊆ (Kcrit t)))
    (_houtput : ∀ t ∈ Icc 0 Δ, (∀ q ∈ tsupport (Function.uncurry (α t)), q.1.1 ∈ X₀)),
    ∀ (Cpar : Set P), IsOpen Cpar → (∀ t ∈ Icc 0 Δ, X₀ ×ˢ Cpar ⊆ U t) →
    ∀ (hcφ : ∀ param, Continuous (fun x => φ x param)),
    ∀
    (_hs : ∀ t ∈ Icc 0 Δ, (∀ param ∈ Cpar, ∀ q, normalizedSlice param q ∈ tsupport (Function.uncurry (α t)) →
      normalizedSlice param q ∈ (U t) ×ˢ (Dcrit t)))
    (_hsfreq : ∀ t ∈ Icc 0 Δ, (∀ param ∈ Cpar, ∀ q, normalizedSlice param q ∈ tsupport (Function.uncurry (α t)) → ‖q.2‖ ≤ radius))
    (_hsupport : ∀ t ∈ Icc 0 Δ, (∀ param ∈ Cpar, ∀ q, normalizedSlice param q ∈ tsupport (Function.uncurry (α t)) →
      q.1.1 ∈ X₀ ∧ q.1.2 ∈ Y₀ ∧ lam • q.2 ∈ F₀))
    (_hΘ : ∀ t ∈ Icc 0 Δ, (∀ x ∈ X₀, ∀ θ, lam • θ ∈ F₀ →
      elapsedPhase Ψ t x (lam • θ) = lam * elapsedPhase Ψ t x θ)),
    (∀ param ∈ Cpar, ContDiffOn ℝ ∞ (fun x => φ x param) Ssource) →
    (Continuous (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      Ψ p.1.1 p.1.2 p.2.1 p.2.2)) →
    (Continuous (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      A p.1.1 p.1.2 p.2.1 p.2.2)) →
    Continuous χout → Continuous χsource → Continuous β → Continuous π →
    HasCompactSupport χout → HasCompactSupport χsource → HasCompactSupport π →
    ∀ (a : E × P → Vf) (ha : ContDiff ℝ ∞ a)
      (has : ∀ q, q.1 ∉ Ksource → a q = 0),
    ∀ param ∈ Cpar, ∀ (Ddata : ℕ → ℝ), (∀ j, 0 ≤ Ddata j) →
    (∀ j, j ≤ s + ps.length →
      ∃ hm : MemLp (fun x : E => iteratedFDeriv ℝ j a (x, param)) 2 volume,
        ‖hm.toLp (fun x : E => iteratedFDeriv ℝ j a (x, param))‖ ≤ Ddata j) →
    let f := fun t c => annularEnvelopeOperator Ψ A χout χsource β π t lam
        (fun x => φ x c) (hcφ c)
        (graphTestToLp (vectorOriginalDatumTest a ha hKsource has [] c))
    let output := orderedTransferAction (fun v F c => fderiv ℝ F c v) ps
      (fun c => annularEnvelopeIntegral Δ Ψ A χout χsource β π lam
        (fun x => φ x c) (hcφ c)
        (graphTestToLp (vectorOriginalDatumTest a ha hKsource has [] c))) param
    IntegrableOn (fun t => orderedTransferAction
      (fun v F c => fderiv ℝ F c v) ps (f t) param) (Icc 0 Δ) ∧
    output = ∫ t in Icc 0 Δ,
      orderedTransferAction (fun v F c => fderiv ℝ F c v) ps (f t) param ∧
    MemVectorFourierSobolev (s : ℝ) output ∧
      vectorFourierSobolevNorm (s : ℝ) output ≤ (Δ * C) * lam ^ p *
        (∑ j ∈ Finset.range (s + ps.length + 1), L ^ (s + ps.length - j) * Ddata j) ∧
      ∀ (Kinput nu A₀ : ℝ) (Dprofile : ℕ → ℝ), L ≤ Kinput →
        Kinput ≤ lam ^ (1 - nu) → 0 < nu → nu < 1 →
        (∀ j, j ≤ s + ps.length → Ddata j ≤ A₀ * Dprofile j * Kinput ^ j) →
        output ∈ (Complement.vectorFourierSobolevScale (d := d + 1) (I := Fin r)).level s ∧
          Complement.vectorFourierSobolevScale.gradeNorm s output ≤
            ((Δ * C) * ∑ j ∈ Finset.range (s + ps.length + 1), Dprofile j) *
              lam ^ p * A₀ * Kinput ^ (s + ps.length) := by
  obtain ⟨C, hC, hbuild⟩ := exists_annularEnvelope_joint_envelope_of_primitive_jets
    (r := r) (P := P) R ℓ M G c hℓ hRcell hδ hF hc basis s ps hps
    Aphase Aamp hphase hamp hB hradius
  refine ⟨C, hC, ?_⟩
  intro X₀ Y₀ F₀ hXcompact hYbox hFclosed hFzero Ψ Δ hΔ hS
    X D η J Wnormal Knormal chart hopen hηinput hmapinput hJinput hgapinput
    hrightInverse hcarrier hclosed hbuffer hR hgrowth V hUopen hVopen hη hmap hJ
    hgap hJjet hηjet hscale hX₀ hF₀ Rstar hRstar L lam hL hlam p φ w₀ A χout χsource β π
  dsimp only
  intro U Dcrit hU hDcrit hcD hf hw₀ h₀ hcrit hvalue hu hi hp hα hαjet
    Kcrit hKcrit hKD hsupportCrit houtput Cpar hCpar hXU hcφ hs hsfreq hsupport
    hΘ hφ hΨ hA hχout hχsource hβ hπ hocs hscs hπcs a ha has
    param hparam Ddata hDdata hj
  let f : ℝ → P → H := fun t c => annularEnvelopeOperator Ψ A χout χsource β π t lam
        (fun x => φ x c) (hcφ c)
        (graphTestToLp (vectorOriginalDatumTest a ha hKsource has [] c))
  have hmeas (b : P) (_hb : b ∈ Cpar) :
      AEStronglyMeasurable (fun t => f t b) (volume.restrict (Icc 0 Δ)) :=
    (aestronglyMeasurable_annularEnvelope_and_adjoint Ψ A χout χsource β π
      (zero_lt_one.trans_le hlam).ne' hΨ hA hχout hχsource hβ hπ hocs hscs hπcs
      (fun x => φ x b) (hcφ b) (volume.restrict (Icc 0 Δ))
      (graphTestToLp (vectorOriginalDatumTest a ha hKsource has [] b))).1
  have hregular (t : ℝ) (ht : t ∈ Icc 0 Δ) : ContDiffOn ℝ ∞ (f t) Cpar :=
    contDiffOn_annularEnvelope_originalDatum basis Ψ A χout χsource β π t
      (hS t ht) (zero_lt_one.trans_le hlam) p φ (w₀ t)
      (hU t ht) (hDcrit t ht) (hcD t ht) (hKcrit t ht) (hKD t ht)
      (hf t ht) (hα t ht) (hsupportCrit t ht) (hw₀ t ht) (h₀ t ht) (hu t ht)
      hXcompact (houtput t ht) hCpar (hXU t ht) hcφ (hs t ht) (hsupport t ht)
      (hΘ t ht) hKsource hSsource hKS hφ a ha has
  have hlocal := exists_annularEnvelope_local_word_bounds_of_primitive_jets
    (r := r) (P := P) R ℓ M G c hℓ hRcell hδ hF hc basis ps.length
    Aphase Aamp hphase hamp hB hradius Ksource Ssource hKsource hSsource hKS
    X₀ Y₀ F₀ hXcompact hYbox hFclosed hFzero Ψ Δ hΔ hS
    chart hopen hηinput hmapinput hJinput hgapinput hrightInverse hcarrier
    hclosed hbuffer hR hgrowth V hUopen hVopen hη hmap hJ hgap hJjet hηjet
    hscale hX₀ hF₀ Rstar hRstar L lam hL hlam p φ w₀ A χout χsource β π
    U Dcrit hU hDcrit hcD hf hw₀ h₀ hcrit hvalue hu hi
    (fun t ht j hj => hp t ht j (by omega)) hα
    (fun t ht j hj => hαjet t ht j (by omega))
    Kcrit hKcrit hKD hsupportCrit houtput Cpar hCpar hXU hcφ hs hsfreq hsupport
    hΘ hφ a ha has
  have hpass := orderedTransferAction_elapsedIntegral hCpar hmeas hregular ps.length
    hlocal ps le_rfl hparam
  have hpoint (t : ℝ) (ht : t ∈ Icc 0 Δ) := hbuild
    X₀ Y₀ F₀ hXcompact hYbox hFclosed hFzero Ψ t (hS t ht)
    (chart t ht) (hopen t ht) (hηinput t ht) (hmapinput t ht) (hJinput t ht) (hgapinput t ht)
    (hrightInverse t ht) (hcarrier t ht) (hclosed t ht) (hbuffer t ht) (hR t ht) (hgrowth t ht)
    (V t) (hUopen t ht) (hVopen t ht) (hη t ht) (hmap t ht) (hJ t ht)
    (hgap t ht) (hJjet t ht) (hηjet t ht) (hscale t ht) (hX₀ t ht) (hF₀ t ht)
    Rstar hRstar L lam hL hlam p φ (w₀ t) A χout χsource β π
    (U t) (Dcrit t) (hU t ht) (hDcrit t ht) (hcD t ht) (hf t ht) (hw₀ t ht)
    (h₀ t ht) (hcrit t ht) (hvalue t ht) (hu t ht) (hi t ht)
    (hp t ht) (hα t ht) (hαjet t ht)
    (Kcrit t) (hKcrit t ht) (hKD t ht) (hsupportCrit t ht) (houtput t ht)
    Cpar hCpar (hXU t ht) hcφ (hs t ht) (hsfreq t ht) (hsupport t ht)
    (hΘ t ht) Ksource Ssource hKsource hSsource hKS hφ a ha has
    param hparam Ddata hDdata hj
  have hb := SobolevIntegration.integral_vectorSobolev_bound hΔ (s : ℝ)
    (C * lam ^ p *
      (∑ j ∈ Finset.range (s + ps.length + 1), L ^ (s + ps.length - j) * Ddata j))
    (fun t => orderedTransferAction (fun v F c => fderiv ℝ F c v) ps (f t) param)
    hpass.1 (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact ⟨(hpoint t ht).1, (hpoint t ht).2.1⟩)
  have hmem : MemVectorFourierSobolev (s : ℝ)
      (orderedTransferAction (fun v F c => fderiv ℝ F c v) ps
        (fun c => ∫ t in Icc 0 Δ, f t c) param) := by
    rw [hpass.2]
    exact hb.1
  have hnorm : vectorFourierSobolevNorm (s : ℝ)
      (orderedTransferAction (fun v F c => fderiv ℝ F c v) ps
        (fun c => ∫ t in Icc 0 Δ, f t c) param) ≤ (Δ * C) * lam ^ p *
          (∑ j ∈ Finset.range (s + ps.length + 1), L ^ (s + ps.length - j) * Ddata j) := by
    rw [hpass.2]
    simpa only [mul_assoc] using hb.2
  refine ⟨hpass.1, hpass.2, hmem, hnorm, ?_⟩
  intro Kinput nu A₀ Dprofile hLK hKlam hnu hnu1 hdata
  have hbProfile := SobolevIntegration.integral_vectorSobolev_bound hΔ (s : ℝ)
    ((C * ∑ j ∈ Finset.range (s + ps.length + 1), Dprofile j) *
      lam ^ p * A₀ * Kinput ^ (s + ps.length))
    (fun t => orderedTransferAction (fun v F c => fderiv ℝ F c v) ps (f t) param)
    hpass.1 (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      have hq := (hpoint t ht).2.2 Kinput nu A₀ Dprofile hLK hKlam hnu hnu1 hdata
      refine ⟨hq.1, ?_⟩
      simpa only [Complement.vectorFourierSobolevScale_gradeNorm s hq.1] using hq.2)
  refine ⟨hmem, ?_⟩
  change Complement.vectorFourierSobolevScale.gradeNorm s
    (orderedTransferAction (fun v F c => fderiv ℝ F c v) ps
      (fun c => ∫ t in Icc 0 Δ, f t c) param) ≤ _
  rw [Complement.vectorFourierSobolevScale_gradeNorm s hmem, hpass.2]
  simpa only [mul_assoc] using hbProfile.2

end JanetCartan.ResponseTransfer.DirectEvolution.IntegratedEnvelope.Parameter
