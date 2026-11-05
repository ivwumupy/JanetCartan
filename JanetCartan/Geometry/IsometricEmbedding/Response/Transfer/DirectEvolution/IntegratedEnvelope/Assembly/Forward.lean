module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.IntegratedEnvelope.Parameter
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.IntegratedEnvelope.Tails
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.IntegratedEnvelope.Assembly.Words
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Envelope

/-!
# The full elapsed envelope from the original primitive data

The near and complementary producers are instantiated for the same phase,
amplitude, masks, beta, source and fixed interval. Their exact difference
identity identifies the original uncut operator, and the parameter-word bridge
preserves all parameter derivatives. The arbitrary-precision tail is used at
precision `-order`, retaining the original order-zero or order-minus-one gain.
The regular sector and compatible response still supply the displayed original
geometry and symbol profiles; no estimate for a modified or integrated operator
is a hypothesis. Consumer: `HasEnvelopeProfile` for fixed-factor transfer and
finite chains in `app:ch_response:eq:response-graded-reduced`.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option cleanup.letToHave false
open Set Filter MeasureTheory LineDeriv
open scoped ContDiff Topology Matrix.Norms.Frobenius SchwartzMap
namespace JanetCartan.ResponseTransfer.DirectEvolution.IntegratedEnvelope.Assembly
open Pseudodifferential FourierIntegral FourierIntegral.FullLowBounds FourierIntegral.LowBounds
open FourierIntegral.SourceExpansion NormalComparison FrequencyCutoff AmplitudeBound
open FullAmplitudePrimitiveBudget.Local CompactTransfer BranchAmplitudes ModifiedLow
open RegularSector.Characteristic.EvolutionIntegral SymbolBudgets KernelIdentification
open AnnularComplement AnnularSobolev Parameter
open JanetCartan.ResponseTransfer.Complement JanetCartan.ResponseTransfer.Complement.ParameterDerivatives
variable {p d r : ℕ} {I ι : Type} [Fintype ι]
local notation "Par" => Euclidean p
local notation "E" => Euclidean (d + 1)
local notation "Fv" => EuclideanSpace ℂ (Fin r)
local notation "F" => EuclideanSpace ℂ (Fin r)
local notation "H" => SpacetimeL2 d r
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ
local instance fullEnvelopeMatrixTopology : TopologicalSpace Mat :=
  (Matrix.frobeniusNormedAddCommGroup (m := Fin r) (n := Fin r)
    (α := ℂ)).toUniformSpace.toTopologicalSpace
attribute [local irreducible] normalizedTermAmplitude elapsedCarrierPhase
  averagedPhaseHessian modifiedAmplitude fullGraphOperator

/-- Full uncut forward elapsed-envelope profile, including actual parameter
words, from the original geometry and datum profiles on one interval. The two
scales retain `1 ≤ L ≤ K ≤ lam^(1-ν)`, and the amplitude retains `lam^order`.
Constants are uniform over the family index (which may include frequency,
coefficients and the datum). Sources: `app:ch_response:eq:direct-envelope-profile`
and `app:ch_response:eq:fixed-factor-transfer`. -/
theorem fullElapsedEnvelope_hasEnvelopeProfile_of_primitive_jets
    {V : Set Par} (hV : IsOpen V) {X₀ S : Set E}
    (hX₀ : IsCompact X₀) [CompactSpace X₀] (hS : IsCompact S)
    {U X : Set E} (hU : IsOpen U) (hX : IsOpen X) (hSU : S ⊆ U) (hXX : X₀ ⊆ X)
    {Δ ν : ℝ} (hΔ : 0 ≤ Δ) (hν : 0 < ν) (hν1 : ν < 1)
    {a₀ B₀ m M : ℝ} (ha₀ : 0 < a₀) (hB₀ : 0 < B₀)
    (hm : 0 < m) (hm1 : m ≤ 1) (hM1 : 1 ≤ M)
    (Pφ PΨ BΨ Bφ O T B : ℕ → ℝ) (C : ℕ → ℕ → ℝ) (Mβ : ℝ)
    (hPφ : ∀ k, 0 ≤ Pφ k) (hPΨ : ∀ k, 0 ≤ PΨ k)
    (hBΨ : ∀ k, 0 ≤ BΨ k) (hBφ : ∀ k, 0 ≤ Bφ k)
    (hO : ∀ k, 0 ≤ O k) (hT : ∀ k, 0 ≤ T k) (hB : ∀ k, 0 ≤ B k) (hMβ : 0 ≤ Mβ)
    (lam L K A₀ : I → ℝ)
    (hlam : ∀ i, 1 ≤ lam i) (hL : ∀ i, 1 ≤ L i) (hLK : ∀ i, L i ≤ K i)
    (hscale : ∀ i, K i ≤ lam i ^ (1 - ν))
    (hA₀ : ∀ i, 0 ≤ A₀ i)
    (Ψ : I → TwoTimePhase d) (b : I → TwoTimeAmplitude d r)
    (χout χsource β : I → E → ℂ) (φ : I → Par → E → ℝ) (a : I → Par → E → F)
    (ha : ∀ i, ContDiffOn ℝ ∞ (Function.uncurry (a i)) (V ×ˢ univ))
    (has : ∀ i c, c ∈ V → tsupport (a i c) ⊆ S)
    (hmask : ∀ i, tsupport (χout i) ∪ tsupport (χsource i) ⊆ X₀)
    (ho : ∀ i, ContDiff ℝ ∞ (χout i)) (hs : ∀ i, ContDiff ℝ ∞ (χsource i))
    (hβsmooth : ∀ i, ContDiff ℝ ∞ (β i))
    (hβ : ∀ i ξ, ‖β i ξ‖ ≤ Mβ)
    (OΨ Ob : I → Set (TwoTimePoint d))
    (hOΨ : ∀ i, IsOpen (OΨ i)) (hOb : ∀ i, IsOpen (Ob i))
    (hΨ : ∀ i, ContDiffOn ℝ ∞ (jointPhase (Ψ i)) (OΨ i))
    (hb : ∀ i, ContDiff ℝ ∞ (jointAmplitude (b i)))
    (hmapΨ : ∀ i t, t ∈ Icc 0 Δ → ∀ ξ, β i ξ ≠ 0 → ∀ y ∈ U ∪ X,
      elapsedPoint t ((y, 0), ξ) ∈ OΨ i)
    (hmapb : ∀ i t, t ∈ Icc 0 Δ → ∀ ξ, β i ξ ≠ 0 → ∀ y ∈ U ∪ X,
      elapsedPoint t ((y, 0), ξ) ∈ Ob i)
    (hφ : ∀ i, ContDiffOn ℝ ∞ (Function.uncurry (φ i)) (V ×ˢ (U ∪ X)))
    (hΨb : ∀ i t, t ∈ Icc 0 Δ → ∀ ξ, β i ξ ≠ 0 → ∀ k y, y ∈ S ∪ X₀ →
      ‖iteratedFDeriv ℝ k (jointPhase (Ψ i)) (elapsedPoint t ((y, 0), ξ))‖ ≤
        BΨ k * (1 + ‖ξ‖) * L i ^ k)
    (hφb : ∀ i k c, c ∈ V → ∀ y ∈ S ∪ X₀,
      ‖iteratedFDeriv ℝ k (Function.uncurry (φ i)) (c, y)‖ ≤ Bφ k * L i ^ k)
    (hbb : ∀ i t, t ∈ Icc 0 Δ → ∀ ξ, β i ξ ≠ 0 → ∀ k y, y ∈ S ∪ X₀ →
      ‖iteratedFDeriv ℝ k (jointAmplitude (b i)) (elapsedPoint t ((y, 0), ξ))‖ ≤
        B k * L i ^ k)
    (hout : ∀ i k y, y ∈ S ∪ X₀ → ‖iteratedFDeriv ℝ k (χout i) y‖ ≤ O k)
    (hsource : ∀ i k y, y ∈ S ∪ X₀ → ‖iteratedFDeriv ℝ k (χsource i) y‖ ≤ T k)
    (hmem : ∀ i (c : Par) (hc : c ∈ V) l (w : Fin l → Par),
      (∀ j, ‖w j‖ ≤ 1) → ∀ s : ℕ, MemVectorFourierSobolev (s : ℝ)
        ((parameterSource_memLp hS hV (ha i) (has i) l w hc).toLp
          (fun y => iteratedFDeriv ℝ l (fun q => a i q y) c w)))
    (hsob : ∀ i (c : Par) (hc : c ∈ V) l (w : Fin l → Par),
      (∀ j, ‖w j‖ ≤ 1) → ∀ s : ℕ, vectorFourierSobolevNorm (s : ℝ)
        ((parameterSource_memLp hS hV (ha i) (has i) l w hc).toLp
          (fun y => iteratedFDeriv ℝ l (fun q => a i q y) c w)) ≤
            C l s * A₀ i * K i ^ (s + l))
    (hgradient : ∀ i c, c ∈ V → ∀ z ∈ U,
      a₀ ≤ ‖fderiv ℝ (φ i c) z‖ ∧ ‖fderiv ℝ (φ i c) z‖ ≤ B₀)
    (hradial : ∀ i t, t ∈ Icc 0 Δ → ∀ ξ, β i ξ ≠ 0 → ∀ z ∈ U,
      m * ‖ξ‖ ≤ ‖fderiv ℝ (fun y => elapsedPhase (Ψ i) t y ξ) z‖ ∧
        ‖fderiv ℝ (fun y => elapsedPhase (Ψ i) t y ξ) z‖ ≤ M * ‖ξ‖)
    (hsourceφ : ∀ i c, c ∈ V → ∀ z ∈ S, ∀ k, 1 ≤ k →
      ‖iteratedFDeriv ℝ (k + 1) (φ i c) z‖ ≤ Pφ k * L i ^ k)
    (hsourceΨ : ∀ i t, t ∈ Icc 0 Δ → ∀ ξ, β i ξ ≠ 0 → ∀ z ∈ S, ∀ k, 1 ≤ k →
      ‖iteratedFDeriv ℝ (k + 1) (jointPhase (Ψ i)) (elapsedPoint t ((z, 0), ξ))‖ ≤
        PΨ k * (1 + ‖ξ‖) * L i ^ k)
    (D Ω : I → ℝ → Set (E × E))
    (hD : ∀ i t, t ∈ Icc 0 Δ → IsClosed (D i t))
    (hΩ : ∀ i t, t ∈ Icc 0 Δ → IsOpen (Ω i t))
    (hDΩ : ∀ i t, t ∈ Icc 0 Δ → D i t ⊆ Ω i t)
    (hphaseMap : ∀ i t, t ∈ Icc 0 Δ → ∀ q, q ∈ Ω i t → elapsedPoint t ((q.1, 0), q.2) ∈ OΨ i)
    (hsD : ∀ i t, t ∈ Icc 0 Δ → ∀ x z ξ, elapsedAmplitude (b i) (χout i) (χsource i) (β i) t x z ξ ≠ 0 →
      (x, ξ) ∈ D i t)
    (hΨtime : ∀ i t, t ∈ Icc 0 Δ → ∀ x ∈ tsupport (χout i), ∀ ξ ∈ tsupport (β i),
      ContinuousAt (fun q : (ℝ × ℝ) × (Euclidean d × Euclidean d) =>
        Ψ i q.1.1 q.1.2 q.2.1 q.2.2)
        ((x 0, x 0 - t), (spatialPart x, spatialPart ξ)))
    (χ : I → ℕ → E → ℂ) (hχ : ∀ i j, ContDiff ℝ ∞ (χ i j))
    (hχcs : ∀ i j, HasCompactSupport (χ i j))
    (Treg : I → ℕ → ℝ → H →L[ℂ] H)
    (hreal : ∀ i j t, t ∈ Icc 0 Δ → ∀ u : graphTestSpace (d + 1) r,
      Treg i j t (graphTestToLp u) =ᵐ[volume] graphTestOutput (elapsedPhase (Ψ i) t)
        (frequencyCutFullAmplitude (χ i j)
          (elapsedAmplitude (b i) (χout i) (χsource i) (β i) t)) u)
    (hrealAdj : ∀ i j t, t ∈ Icc 0 Δ → ∀ u : graphTestSpace (d + 1) r,
      (Treg i j t).adjoint (graphTestToLp u) =ᵐ[volume] fun z => WithLp.toLp 2
        (reverseGraphOperator (elapsedPhase (Ψ i) t)
          (frequencyCutFullAmplitude (fun ξ => star (χ i j ξ))
            (fun x z ξ => (elapsedAmplitude (b i) (χout i) (χsource i) (β i) t x z ξ).conjTranspose))
          (fun x => (u.val x).ofLp) z))
    (hcut : ∀ i j t, t ∈ Icc 0 Δ →
      frequencyCutFullAmplitude (χ i j) (elapsedAmplitude (b i) (χout i) (χsource i) (β i) t) =
        frequencyCutFullAmplitude (complexPhysicalCutoff j)
          (elapsedAmplitude (b i) (χout i) (χsource i) (β i) t))
    (hlim : ∀ i t, t ∈ Icc 0 Δ → ∀ w, Tendsto (fun j => Treg i j t w) atTop
      (𝓝 (elapsedGraph (Ψ i) (b i) (χout i) (χsource i) (β i) t w)))
    (hlimAdj : ∀ i t, t ∈ Icc 0 Δ → ∀ w, Tendsto (fun j => (Treg i j t).adjoint w) atTop
      (𝓝 ((elapsedGraph (Ψ i) (b i) (χout i) (χsource i) (β i) t).adjoint w)))
    (Creg : I → ℝ)
    (hregBound : ∀ i j t, t ∈ Icc 0 Δ → ‖Treg i j t‖ ≤ Creg i)
    (Rcell ℓ Mgraph Ggraph cgraph : ℝ) (hℓ : 0 < ℓ)
    (hRcell : Rcell / ℓ < 1 / 2) {δ growth : ℝ}
    (hδ : 0 < δ) (hgrowth0 : 0 ≤ growth) (hcgraph : 1 ≤ cgraph)
    (basis : OrthonormalBasis ι ℝ (CarrierVariables (d + 1)))
    (Aphase Aamp Dprofile : ℕ → ℝ)
    (hphase : ∀ j, 0 ≤ Aphase j) (hamp : ∀ j, 0 ≤ Aamp j)
    (hprofile : ∀ j, 0 ≤ Dprofile j)
    {InvBound radius : ℝ} (hInvBound : 0 ≤ InvBound) (hradius : 0 ≤ radius)
    (hbox : ∀ y ∈ X₀, ∀ j : Fin (d + 1), |y j| ≤ Rcell)
    (F₀ : I → Set E) (hFclosed : ∀ i, IsClosed (F₀ i)) (hFzero : ∀ i, (0 : E) ∉ F₀ i)
    (hSPhase : ∀ i t, t ∈ Icc 0 Δ → ContDiff ℝ ∞ (Function.uncurry (elapsedPhase (Ψ i) t)))
    (Xn Dn : I → ℝ → Set E)
    (η : I → ℝ → E → E → E → E)
    (J : I → ℝ → E → E → E → E →L[ℝ] E)
    (Wn Kn : I → ℝ → Set (NormalVariables (d + 1)))
    (chart : ∀ i t, t ∈ Icc 0 Δ → AveragedGradientChart (elapsedPhase (Ψ i) t)
      (Xn i t) (Dn i t) (η i t) (J i t) δ)
    (hopen : ∀ i t, t ∈ Icc 0 Δ → IsOpen (bufferedNormalDomain (Xn i t) (Dn i t) (elapsedPhase (Ψ i) t)))
    (hηinput : ∀ i t, t ∈ Icc 0 Δ → ContDiffOn ℝ ∞ (normalInverseCoordinates (η i t))
      (bufferedNormalDomain (Xn i t) (Dn i t) (elapsedPhase (Ψ i) t)))
    (hmapinput : ∀ i t, t ∈ Icc 0 Δ → MapsTo (normalInverseCoordinates (η i t))
      (bufferedNormalDomain (Xn i t) (Dn i t) (elapsedPhase (Ψ i) t)) (Wn i t))
    (hJinput : ∀ i t, t ∈ Icc 0 Δ → ContDiffOn ℝ ∞
      (fun q : NormalVariables (d + 1) => J i t q.1 q.2.1 q.2.2) (Wn i t))
    (hgapinput : ∀ i t, t ∈ Icc 0 Δ → ∀ q ∈ Wn i t, (J i t q.1 q.2.1 q.2.2).det ≠ 0)
    (hrightInverse : ∀ i t, t ∈ Icc 0 Δ → ∀ q ∈ bufferedNormalDomain (Xn i t) (Dn i t) (elapsedPhase (Ψ i) t),
      normalForwardCoordinates (elapsedPhase (Ψ i) t) (normalInverseCoordinates (η i t) q) = q)
    (hcarrier : ∀ i t, t ∈ Icc 0 Δ → ∀ q ∈ Wn i t,
      q.1 ∈ X₀ → q.2.1 ∈ X₀ → q.2.2 ∈ F₀ i → q ∈ Kn i t)
    (hclosed : ∀ i t, t ∈ Icc 0 Δ → IsClosed (normalForwardCoordinates (elapsedPhase (Ψ i) t) '' Kn i t))
    (hbuffer : ∀ i t, t ∈ Icc 0 Δ → normalForwardCoordinates (elapsedPhase (Ψ i) t) '' Kn i t ⊆
      bufferedNormalDomain (Xn i t) (Dn i t) (elapsedPhase (Ψ i) t))
    (hR : ∀ i t, t ∈ Icc 0 Δ → ∀ x ∈ Xn i t, ‖x‖ ≤ Rcell)
    (hgrowth : ∀ i t, t ∈ Icc 0 Δ → ∀ x ∈ Xn i t, ∀ y ∈ Xn i t, ∀ u ∈ Dn i t,
      ‖averagedGradient (elapsedPhase (Ψ i) t) x y u‖ ≤ growth * (1 + ‖u‖))
    (Vn : I → ℝ → ℕ → Set (NormalVariables (d + 1)))
    (hUopen : ∀ i t, t ∈ Icc 0 Δ → ∀ l, IsOpen (normalDyadicShell
      (bufferedNormalDomain (Xn i t) (Dn i t) (elapsedPhase (Ψ i) t)) l))
    (hVopen : ∀ i t, t ∈ Icc 0 Δ → ∀ l, IsOpen (Vn i t l))
    (hη : ∀ i t, t ∈ Icc 0 Δ → ∀ l, ContDiffOn ℝ ∞
      (normalInverseCoordinates (normalizedNormalInverse ((2 : ℝ)^l) (η i t)))
      (normalDyadicShell (bufferedNormalDomain (Xn i t) (Dn i t) (elapsedPhase (Ψ i) t)) l))
    (hmap : ∀ i t, t ∈ Icc 0 Δ → ∀ l, MapsTo
      (normalInverseCoordinates (normalizedNormalInverse ((2 : ℝ)^l) (η i t)))
      (normalDyadicShell (bufferedNormalDomain (Xn i t) (Dn i t) (elapsedPhase (Ψ i) t)) l) (Vn i t l))
    (hJ : ∀ i t, t ∈ Icc 0 Δ → ∀ l, ContDiffOn ℝ ∞
      (fun q : NormalVariables (d + 1) => normalizedNormalJacobian ((2 : ℝ)^l) (J i t) q.1 q.2.1 q.2.2) (Vn i t l))
    (hgap : ∀ i t, t ∈ Icc 0 Δ → ∀ l q, q ∈ Vn i t l → δ ≤
      |(normalizedNormalJacobian ((2 : ℝ)^l) (J i t) q.1 q.2.1 q.2.2).det|)
    (hJjet : ∀ i t, t ∈ Icc 0 Δ → ∀ l q, q ∈ Vn i t l → ∀ j ≤ primitiveNormalReserve (d + 1),
      ‖iteratedFDeriv ℝ j (fun q : NormalVariables (d + 1) =>
        normalizedNormalJacobian ((2 : ℝ)^l) (J i t) q.1 q.2.1 q.2.2) q‖ ≤ Mgraph)
    (hηjet : ∀ i t, t ∈ Icc 0 Δ → ∀ l q,
      q ∈ normalDyadicShell (bufferedNormalDomain (Xn i t) (Dn i t) (elapsedPhase (Ψ i) t)) l →
      ∀ j, 1 ≤ j → j ≤ primitiveNormalReserve (d + 1) →
        ‖iteratedFDeriv ℝ j (normalInverseCoordinates (normalizedNormalInverse ((2 : ℝ)^l) (η i t))) q‖ ≤ Ggraph)
    (hscaleN : ∀ i t, t ∈ Icc 0 Δ → ∀ l q, q ∈ Vn i t l →
      (2 : ℝ)^l ≤ cgraph * (1 + ‖(2 : ℝ)^l • q.2.2‖))
    (hXn : ∀ i t, t ∈ Icc 0 Δ → X₀ ⊆ Xn i t)
    (hFn : ∀ i t, t ∈ Icc 0 Δ → F₀ i ⊆ Dn i t)
    (Rstar : ℕ) (hRstar : fullLowReserve (d + 1) + 2 < Rstar) (order : ℤ)
    (w₀ : I → ℝ → E × Par → CarrierVariables (d + 1))
    (Ucrit : I → ℝ → Set (E × Par)) (Dcrit : I → ℝ → Set (CarrierVariables (d + 1)))
    (hUc : ∀ i t, t ∈ Icc 0 Δ → IsOpen (Ucrit i t))
    (hDc : ∀ i t, t ∈ Icc 0 Δ → IsOpen (Dcrit i t))
    (hcD : ∀ i t, t ∈ Icc 0 Δ → Convex ℝ (Dcrit i t))
    (hfc : ∀ i t, t ∈ Icc 0 Δ → ContDiffOn ℝ ∞
      (Function.uncurry (elapsedCarrierPhase (Ψ i) t (fun x c => φ i c x))) ((Ucrit i t) ×ˢ (Dcrit i t)))
    (hw₀ : ∀ i t, t ∈ Icc 0 Δ → ContDiffOn ℝ ∞ (w₀ i t) (Ucrit i t))
    (h₀ : ∀ i t, t ∈ Icc 0 Δ → MapsTo (w₀ i t) (Ucrit i t) (Dcrit i t))
    (hcrit : ∀ i t, t ∈ Icc 0 Δ → ∀ q ∈ Ucrit i t,
      gradient (elapsedCarrierPhase (Ψ i) t (fun x c => φ i c x) q) (w₀ i t q) = 0)
    (hvalue : ∀ i t, t ∈ Icc 0 Δ → ∀ q ∈ Ucrit i t,
      elapsedCarrierPhase (Ψ i) t (fun x c => φ i c x) q (w₀ i t q) = 0)
    (hu : ∀ i t, t ∈ Icc 0 Δ → ∀ q ∈ Ucrit i t, ∀ w ∈ Dcrit i t,
      IsUnit (averagedPhaseHessian (elapsedCarrierPhase (Ψ i) t (fun x c => φ i c x)) (w₀ i t) q w))
    (hi : ∀ i t, t ∈ Icc 0 Δ → ∀ q ∈ Ucrit i t, ∀ w ∈ Dcrit i t,
      ‖Ring.inverse (averagedPhaseHessian (elapsedCarrierPhase (Ψ i) t (fun x c => φ i c x)) (w₀ i t) q w)‖ ≤ InvBound)
    (hp : ∀ i t, t ∈ Icc 0 Δ → ∀ j q, q ∈ (Ucrit i t) ×ˢ (Dcrit i t) →
      ‖iteratedFDeriv ℝ j (Function.uncurry (elapsedCarrierPhase (Ψ i) t (fun x c => φ i c x))) q‖ ≤
        Aphase j * L i ^ (j - Rstar))
    (Kcrit : I → ℝ → Set (CarrierVariables (d + 1)))
    (hKcrit : ∀ i t, t ∈ Icc 0 Δ → IsCompact (Kcrit i t))
    (hKD : ∀ i t, t ∈ Icc 0 Δ → Kcrit i t ⊆ Dcrit i t)
    (hXU : ∀ i t, t ∈ Icc 0 Δ → X₀ ×ˢ V ⊆ Ucrit i t)
    (hcφ : ∀ i c, Continuous (φ i c))
    (hφsource : ∀ i c, c ∈ V → ContDiffOn ℝ ∞ (φ i c) U)
    (hΨcont : ∀ i, Continuous (fun q : (ℝ × ℝ) × (Euclidean d × Euclidean d) =>
      Ψ i q.1.1 q.1.2 q.2.1 q.2.2))
    (haJoint : ∀ i, ContDiff ℝ ∞ (fun q : E × Par => a i q.2 q.1))
    (haGlobal : ∀ i (q : E × Par), q.1 ∉ S → a i q.2 q.1 = 0)
    (hDatum : ∀ i c, c ∈ V → ∀ j,
      ∃ hm : MemLp (fun x : E => iteratedFDeriv ℝ j (fun q : E × Par => a i q.2 q.1) (x,c)) 2 volume,
        ‖hm.toLp (fun x : E => iteratedFDeriv ℝ j (fun q : E × Par => a i q.2 q.1) (x,c))‖ ≤
          A₀ i * Dprofile j * K i ^ j)
    (hΘ : ∀ i t, t ∈ Icc 0 Δ → ∀ x ∈ X₀, ∀ θ, lam i • θ ∈ F₀ i →
      elapsedPhase (Ψ i) t x (lam i • θ) = lam i * elapsedPhase (Ψ i) t x θ) :
    let π : E → ℂ := fun θ =>
      annularSelector (a₀ / (2 * M)) (2 * B₀ / m) (by positivity) (by positivity) θ
    let α := fun i t => normalizedAnnularElapsedAmplitude (P := Par)
      (b i) (χout i) (χsource i) (β i) π t (lam i) order
    (∀ i t, t ∈ Icc 0 Δ → ContDiffOn ℝ ∞ (Function.uncurry (α i t)) ((Ucrit i t) ×ˢ (Dcrit i t))) →
    (∀ i t, t ∈ Icc 0 Δ → ∀ j q, q ∈ (Ucrit i t) ×ˢ (Dcrit i t) →
      ‖iteratedFDeriv ℝ j (Function.uncurry (α i t)) q‖ ≤ Aamp j * L i ^ (j + 2 - Rstar)) →
    (∀ i t, t ∈ Icc 0 Δ → ∀ q ∈ Ucrit i t, Function.support (α i t q) ⊆ Kcrit i t) →
    (∀ i t, t ∈ Icc 0 Δ → ∀ q ∈ tsupport (Function.uncurry (α i t)), q.1.1 ∈ X₀) →
    (∀ i t, t ∈ Icc 0 Δ → ∀ c ∈ V, ∀ q, normalizedSlice c q ∈ tsupport (Function.uncurry (α i t)) →
      normalizedSlice c q ∈ (Ucrit i t) ×ˢ (Dcrit i t)) →
    (∀ i t, t ∈ Icc 0 Δ → ∀ c ∈ V, ∀ q, normalizedSlice c q ∈ tsupport (Function.uncurry (α i t)) → ‖q.2‖ ≤ radius) →
    (∀ i t, t ∈ Icc 0 Δ → ∀ c ∈ V, ∀ q, normalizedSlice c q ∈ tsupport (Function.uncurry (α i t)) →
      q.1.1 ∈ X₀ ∧ q.1.2 ∈ X₀ ∧ lam i • q.2 ∈ F₀ i) →
    ∀ ps : List Par, (∀ v ∈ ps, ‖v‖ ≤ 1) →
    HasEnvelopeProfile (vectorFourierSobolevScale (d := d + 1) (I := Fin r))
      (fun z : I × V => orderedTransferAction (fun v g c => fderiv ℝ g c v) ps
        (fun c => carrierMultiplication (-(lam z.1)) (φ z.1 c) (hcφ z.1 c)
          (elapsedGraphIntegral Δ (Ψ z.1) (b z.1) (χout z.1) (χsource z.1) (β z.1)
            (carrierMultiplication (lam z.1) (φ z.1 c) (hcφ z.1 c)
              (graphTestToLp (vectorOriginalDatumTest (fun q : E × Par => a z.1 q.2 q.1)
                (haJoint z.1) hS (haGlobal z.1) [] c))))) z.2)
      (fun z => lam z.1 ^ order * A₀ z.1 * K z.1 ^ ps.length) (fun z => K z.1) := by
  dsimp only
  intro hα hαjet hsupportCrit houtput hslice hsfreq hsupport ps hps
  let π : E → ℂ := fun θ =>
    annularSelector (a₀ / (2 * M)) (2 * B₀ / m) (by positivity) (by positivity) θ
  let datum (i : I) (c : Par) : H := graphTestToLp
    (vectorOriginalDatumTest (fun q : E × Par => a i q.2 q.1) (haJoint i) hS (haGlobal i) [] c)
  let f : I → ℝ → Par → H := fun i t c => annularEnvelopeOperator
    (Ψ i) (b i) (χout i) (χsource i) (β i) π t (lam i) (φ i c) (hcφ i c) (datum i c)
  let rem : I → Par → H := fun i c => ∫ t in Icc 0 Δ,
    elapsedAnnularRemainder hX₀ false true (Ψ i) (b i) (χout i) (χsource i) (β i)
      π (φ i) t (lam i) (a i) c
  have ht := Tails.originalAnnularComplement_elapsed_sobolev
    hV hX₀ hS hU hX hSU hXX hΔ hν hν1 ha₀ hB₀ hm hm1 hM1
    Pφ PΨ BΨ Bφ O T B C Mβ hPφ hPΨ hBΨ hBφ hO hT hB hMβ
    lam L K A₀ hlam hL hLK hscale hA₀ Ψ b χout χsource β φ a ha has hmask
    ho hs hβsmooth hβ OΨ Ob hOΨ hOb hΨ hb hmapΨ hmapb hφ hΨb hφb hbb
    hout hsource hmem hsob hgradient hradial hsourceφ hsourceΨ D Ω hD hΩ
    hDΩ hphaseMap hsD hΨtime χ hχ hχcs Treg hreal hrealAdj hcut hlim hlimAdj Creg hregBound false
  have hremSmooth : ∀ i, ContDiffOn ℝ ∞ (rem i) V := (ht.2.2 true).2.2.2.1
  have hbcont (i : I) : Continuous
      (fun q : (ℝ × ℝ) × (Euclidean d × Euclidean d) => b i q.1.1 q.1.2 q.2.1 q.2.2) :=
    (hb i).continuous.comp (show Continuous (fun q : (ℝ × ℝ) × (Euclidean d × Euclidean d) =>
      ((q.1.1, q.1.2, q.2.1), q.2.2)) from by fun_prop)
  have hocs (i : I) : HasCompactSupport (χout i) :=
    hX₀.of_isClosed_subset (isClosed_tsupport _) (fun _ h => hmask i (Or.inl h))
  have hscs (i : I) : HasCompactSupport (χsource i) :=
    hX₀.of_isClosed_subset (isClosed_tsupport _) (fun _ h => hmask i (Or.inr h))
  have hπ : ContDiff ℝ ∞ π := Complex.ofRealCLM.contDiff.comp (contDiff_annularSelector _ _ _ _)
  have hπcs : HasCompactSupport π := (hasCompactSupport_annularSelector _ _ _ _).comp_left (g := Complex.ofReal) rfl
  have hmeas (i : I) (c : Par) (_hc : c ∈ V) :
      AEStronglyMeasurable (fun t => f i t c) (volume.restrict (Icc 0 Δ)) :=
    (aestronglyMeasurable_annularEnvelope_and_adjoint (Ψ i) (b i) (χout i) (χsource i) (β i) π
      (zero_lt_one.trans_le (hlam i)).ne' (hΨcont i) (hbcont i) (ho i).continuous
      (hs i).continuous (hβsmooth i).continuous hπ.continuous (hocs i) (hscs i) hπcs
      (φ i c) (hcφ i c) (volume.restrict (Icc 0 Δ)) (datum i c)).1
  have hregular (i : I) (t : ℝ) (ht : t ∈ Icc 0 Δ) : ContDiffOn ℝ ∞ (f i t) V :=
    contDiffOn_annularEnvelope_originalDatum basis (Ψ i) (b i) (χout i) (χsource i) (β i) π t
      (hSPhase i t ht) (zero_lt_one.trans_le (hlam i)) order (fun x c => φ i c x) (w₀ i t)
      (hUc i t ht) (hDc i t ht) (hcD i t ht) (hKcrit i t ht) (hKD i t ht)
      (hfc i t ht) (hα i t ht) (hsupportCrit i t ht) (hw₀ i t ht) (h₀ i t ht) (hu i t ht)
      hX₀ (houtput i t ht) hV (hXU i t ht) (hcφ i) (hslice i t ht) (hsupport i t ht)
      (hΘ i t ht) hS hU hSU (hφsource i) (fun q : E × Par => a i q.2 q.1) (haJoint i) (haGlobal i)
  have hlocal (i : I) := exists_annularEnvelope_local_word_bounds_of_primitive_jets
    Rcell ℓ Mgraph Ggraph cgraph hℓ hRcell hδ hgrowth0 hcgraph basis ps.length
    Aphase Aamp hphase hamp hInvBound hradius S U hS hU hSU
    X₀ X₀ (F₀ i) hX₀ hbox (hFclosed i) (hFzero i) (Ψ i) Δ hΔ (hSPhase i)
    (chart i) (hopen i) (hηinput i) (hmapinput i) (hJinput i) (hgapinput i)
    (hrightInverse i) (hcarrier i) (hclosed i) (hbuffer i) (hR i) (hgrowth i)
    (Vn i) (hUopen i) (hVopen i) (hη i) (hmap i) (hJ i) (hgap i) (hJjet i) (hηjet i)
    (hscaleN i) (hXn i) (hFn i) Rstar hRstar (L i) (lam i) (hL i) (hlam i) order
    (fun x c => φ i c x) (w₀ i) (b i) (χout i) (χsource i) (β i) π
    (Ucrit i) (Dcrit i) (hUc i) (hDc i) (hcD i) (hfc i) (hw₀ i) (h₀ i) (hcrit i)
    (hvalue i) (hu i) (hi i) (fun t ht j _ => hp i t ht j) (hα i)
    (fun t ht j _ => hαjet i t ht j) (Kcrit i) (hKcrit i) (hKD i)
    (hsupportCrit i) (houtput i) V hV (hXU i) (hcφ i) (hslice i) (hsfreq i) (hsupport i)
    (hΘ i) (hφsource i) (fun q : E × Par => a i q.2 q.1) (haJoint i) (haGlobal i)
  have hdatum (i : I) (c : Par) : datum i c =ᵐ[volume] a i c := by
    exact vectorOriginalDatumTest_toLp_ae (fun q : E × Par => a i q.2 q.1)
      (haJoint i) hS (haGlobal i) [] c
  have heq (i : I) (c : Par) (hc : c ∈ V) :
      carrierMultiplication (-(lam i)) (φ i c) (hcφ i c)
        (elapsedGraphIntegral Δ (Ψ i) (b i) (χout i) (χsource i) (β i)
          (carrierMultiplication (lam i) (φ i c) (hcφ i c) (datum i c))) =
      (∫ t in Icc 0 Δ, f i t c) + rem i c := by
    obtain ⟨w, _, _, _, _, _, hdemod⟩ := ht.1 i c hc
    obtain ⟨u, hu, hcu, he, _⟩ := hdemod (hcφ i c)
    have heu : u = datum i c := Lp.ext (hu.trans (hdatum i c).symm)
    subst u
    rw [← hcu] at he
    change rem i c = _ - (∫ t in Icc 0 Δ, f i t c) at he
    exact (eq_add_of_sub_eq he.symm).trans (add_comm _ _)
  intro s
  obtain ⟨Cn, hCn, hn⟩ := exists_annularEnvelopeIntegral_joint_envelope_of_primitive_jets
    (r := r) (P := Par) Rcell ℓ Mgraph Ggraph cgraph hℓ hRcell hδ hgrowth0 hcgraph basis s ps hps
    Aphase Aamp hphase hamp hInvBound hradius S U hS hU hSU
  obtain ⟨Ct, hCt, htail⟩ := (ht.2.2 true).2.2.2.2.2.2 (s : ℝ) ps.length (-(order : ℝ))
  let Cn' := (Δ * Cn) * ∑ j ∈ Finset.range (s + ps.length + 1), Dprofile j
  refine ⟨Cn' + Δ * Ct, add_nonneg (mul_nonneg (mul_nonneg hΔ hCn)
    (Finset.sum_nonneg (fun j _ => hprofile j))) (mul_nonneg hΔ hCt), ?_⟩
  rintro ⟨i, c, hc⟩
  have hn' := hn X₀ X₀ (F₀ i) hX₀ hbox (hFclosed i) (hFzero i) (Ψ i) Δ hΔ (hSPhase i)
    (chart i) (hopen i) (hηinput i) (hmapinput i) (hJinput i) (hgapinput i)
    (hrightInverse i) (hcarrier i) (hclosed i) (hbuffer i) (hR i) (hgrowth i)
    (Vn i) (hUopen i) (hVopen i) (hη i) (hmap i) (hJ i) (hgap i) (hJjet i) (hηjet i)
    (hscaleN i) (hXn i) (hFn i) Rstar hRstar (L i) (lam i) (hL i) (hlam i) order
    (fun x c => φ i c x) (w₀ i) (b i) (χout i) (χsource i) (β i) π
    (Ucrit i) (Dcrit i) (hUc i) (hDc i) (hcD i) (hfc i) (hw₀ i) (h₀ i) (hcrit i)
    (hvalue i) (hu i) (hi i) (fun t ht j _ => hp i t ht j) (hα i)
    (fun t ht j _ => hαjet i t ht j) (Kcrit i) (hKcrit i) (hKD i)
    (hsupportCrit i) (houtput i) V hV (hXU i) (hcφ i) (hslice i) (hsfreq i) (hsupport i)
    (hΘ i) (hφsource i) (hΨcont i) (hbcont i) (ho i).continuous (hs i).continuous
    (hβsmooth i).continuous hπ.continuous (hocs i) (hscs i) hπcs
    (fun q : E × Par => a i q.2 q.1) (haJoint i) (haGlobal i)
    c hc (fun j => A₀ i * Dprofile j * K i ^ j)
    (fun j => mul_nonneg (mul_nonneg (hA₀ i) (hprofile j))
      (pow_nonneg (zero_le_one.trans ((hL i).trans (hLK i))) j))
    (fun j _ => hDatum i c hc j)
  have hnProfile := hn'.2.2.2.2 (K i) ν (A₀ i) Dprofile (hLK i) (hscale i) hν hν1 (fun _ _ => le_rfl)
  have htProfile := htail i c hc ps.get (fun j => hps _ (List.get_mem ..))
  have heword : orderedTransferAction (fun v g c => fderiv ℝ g c v) ps
      (fun c => carrierMultiplication (-(lam i)) (φ i c) (hcφ i c)
        (elapsedGraphIntegral Δ (Ψ i) (b i) (χout i) (χsource i) (β i)
          (carrierMultiplication (lam i) (φ i c) (hcφ i c) (datum i c)))) c =
      orderedTransferAction (fun v g c => fderiv ℝ g c v) ps
        (fun c => ∫ t in Icc 0 Δ, f i t c) c +
      iteratedFDeriv ℝ ps.length (rem i) c ps.get := by
    rw [orderedParameterWord_congr_nhds
      (Filter.eventuallyEq_of_mem (hV.mem_nhds hc) (fun a ha => heq i a ha)) ps]
    exact ordered_elapsedIntegral_add hV (hmeas i) (hregular i) ps.length (hlocal i)
      (hremSmooth i) ps le_rfl hc
  let full : I → Par → H := fun i c => carrierMultiplication (-(lam i)) (φ i c) (hcφ i c)
    (elapsedGraphIntegral Δ (Ψ i) (b i) (χout i) (χsource i) (β i)
      (carrierMultiplication (lam i) (φ i c) (hcφ i c) (datum i c)))
  let G := vectorFourierSobolevScale (d := d + 1) (I := Fin r)
  change orderedTransferAction (fun v g c => fderiv ℝ g c v) ps (full i) c = _ at heword
  change orderedTransferAction (fun v g c => fderiv ℝ g c v) ps (full i) c ∈ G.level s ∧
    G.gradeNorm s (orderedTransferAction (fun v g c => fderiv ℝ g c v) ps (full i) c) ≤
      (Cn' + Δ * Ct) * (lam i ^ order * A₀ i * K i ^ ps.length) * K i ^ s
  rw [heword]
  have hmTail : iteratedFDeriv ℝ ps.length (rem i) c ps.get ∈ G.level s := htProfile.1
  refine ⟨(G.level s).add_mem hnProfile.1 hmTail, ?_⟩
  apply (gradeNorm_add_le G hnProfile.1 hmTail).trans
  have htBound : G.gradeNorm s (iteratedFDeriv ℝ ps.length (rem i) c ps.get) ≤
      (Δ * Ct) * (lam i ^ order * A₀ i) * K i ^ (s + ps.length) := by
    rw [vectorFourierSobolevScale_gradeNorm s hmTail]
    have htB := htProfile.2
    rw [neg_neg, Real.rpow_intCast] at htB
    apply htB.trans
    calc
      (Δ * Ct) * A₀ i * lam i ^ order = (Δ * Ct) * (lam i ^ order * A₀ i) := by ring
      _ ≤ _ := le_mul_of_one_le_right (mul_nonneg (mul_nonneg hΔ hCt)
        (mul_nonneg (zpow_nonneg (zero_le_one.trans (hlam i)) order) (hA₀ i)))
        (one_le_pow₀ ((hL i).trans (hLK i)))
  calc
    _ ≤ Cn' * lam i ^ order * A₀ i * K i ^ (s + ps.length) +
        (Δ * Ct) * (lam i ^ order * A₀ i) * K i ^ (s + ps.length) :=
      add_le_add hnProfile.2 htBound
    _ = (Cn' + Δ * Ct) * (lam i ^ order * A₀ i * K i ^ ps.length) * K i ^ s := by
      rw [pow_add]
      ring

end JanetCartan.ResponseTransfer.DirectEvolution.IntegratedEnvelope.Assembly
