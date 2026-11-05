module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.IntegratedEnvelope.Tails.Integration
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.IntegratedEnvelope.Tails.Realization
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.IntegratedEnvelope.Tails.Identification

/-!
# Uniform primitive complementary estimates after elapsed integration

The same fixed-time endpoint is applied with family index `I × Icc 0 Δ`.
Neither the physical graph nor the carrier parameter changes in time integration.
The original regularization test actions and strong limits are exactly the
outputs of `EvolutionIntegral.exists_elapsedGraphFamily_of_primitive_phase`;
actual sector instantiation of that constructor belongs to the parent.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.DirectEvolution.IntegratedEnvelope.Tails
open FourierIntegral FourierIntegral.FullLowBounds
open RegularSector.Characteristic.EvolutionIntegral SymbolBudgets KernelIdentification
open AnnularComplement JanetCartan.Pseudodifferential
open JanetCartan.ResponseTransfer.Complement
open JanetCartan.ResponseTransfer.Complement.ParameterDerivatives
open FourierIntegral.LowBounds.FrequencyCutoff
variable {p d r : ℕ} {I : Type}
local notation "P" => Euclidean p
local notation "E" => Euclidean (d + 1)
local notation "F" => EuclideanSpace ℂ (Fin r)
local notation "H" => SpacetimeL2 d r

/-- The actual elapsed complementary remainder is smooth in the carrier
parameter, Bochner integrable in time at every parameter order, and arbitrarily
small in every real physical or demodulated Sobolev order after integration.
The fixed losses and separate `L,K` window are those of
`originalAnnularComplement_sobolev`. No integrated estimate, time measurability,
or derivative-interchange premise is assumed. The original graph realization
inputs below have the precise producer `exists_elapsedGraphFamily_of_primitive_phase`.
The supported continuity input `hΨtime` is derived from that producer's original
open phase chart, exactly as in `EvolutionIntegral.PrimitiveRetarded`. The
regularization bound is used only to establish integrability of the separate
uncut and annular orbits; none of the tail constants depends on that bound.
The final four bounded action identities are the outputs of `StrongIntegral`
and `IntegratedEnvelope.Construction`, and are used only for identification.
Source: `app:ch_response:lem:energy-carrier-jets`; consumer:
`app:ch_response:eq:direct-envelope-profile`, for both orders `0` and `-1`. -/
theorem originalAnnularComplement_elapsed_sobolev
    {V : Set P} (hV : IsOpen V) {X₀ S : Set E}
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
    (χout χsource β : I → E → ℂ) (φ : I → P → E → ℝ) (a : I → P → E → F)
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
    (hmem : ∀ i (c : P) (hc : c ∈ V) l (w : Fin l → P),
      (∀ j, ‖w j‖ ≤ 1) → ∀ s : ℕ, MemVectorFourierSobolev (s : ℝ)
        ((parameterSource_memLp hS hV (ha i) (has i) l w hc).toLp
          (fun y => iteratedFDeriv ℝ l (fun q => a i q y) c w)))
    (hsob : ∀ i (c : P) (hc : c ∈ V) l (w : Fin l → P),
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
    (adj : Bool) :
    let π : E → ℂ := fun η =>
      annularSelector (a₀ / (2 * M)) (2 * B₀ / m) (by positivity) (by positivity) η
    let R := fun dm i t => elapsedAnnularRemainder hX₀ adj dm (Ψ i) (b i)
      (χout i) (χsource i) (β i) π (φ i) t (lam i) (a i)
    (∀ i c, c ∈ V → ∃ w : H,
      w =ᵐ[volume] (fun x => carrier (lam i) (φ i c) x • a i c x) ∧
      (∀ t ∈ Icc 0 Δ, R false i t c =
        annularGraphOrientation adj (elapsedGraph (Ψ i) (b i) (χout i) (χsource i) (β i) t) w -
        annularGraphOrientation adj (elapsedGraph (Ψ i) (b i) (χout i) (χsource i)
          (fun ξ => π ((lam i)⁻¹ • ξ) * β i ξ) t) w) ∧
      IntegrableOn (fun t => annularGraphOrientation adj
        (elapsedGraph (Ψ i) (b i) (χout i) (χsource i) (β i) t) w) (Icc 0 Δ) ∧
      IntegrableOn (fun t => annularGraphOrientation adj
        (elapsedGraph (Ψ i) (b i) (χout i) (χsource i)
          (fun ξ => π ((lam i)⁻¹ • ξ) * β i ξ) t) w) (Icc 0 Δ) ∧
      (∫ t in Icc 0 Δ, R false i t c) =
        (∫ t in Icc 0 Δ, annularGraphOrientation adj
          (elapsedGraph (Ψ i) (b i) (χout i) (χsource i) (β i) t) w) -
        (∫ t in Icc 0 Δ, annularGraphOrientation adj
          (elapsedGraph (Ψ i) (b i) (χout i) (χsource i)
            (fun ξ => π ((lam i)⁻¹ • ξ) * β i ξ) t) w) ∧
      ∀ hcφ : Continuous (φ i c), ∃ u : H,
        u =ᵐ[volume] a i c ∧ carrierMultiplication (lam i) (φ i c) hcφ u = w ∧
        (∫ t in Icc 0 Δ, R true i t c) =
          carrierMultiplication (-(lam i)) (φ i c) hcφ
            (∫ t in Icc 0 Δ, annularGraphOrientation adj
              (elapsedGraph (Ψ i) (b i) (χout i) (χsource i) (β i) t) w) -
          (if adj then annularEnvelopeAdjointIntegral Δ (Ψ i) (b i) (χout i) (χsource i)
            (β i) π (lam i) (φ i c) hcφ u
           else annularEnvelopeIntegral Δ (Ψ i) (b i) (χout i) (χsource i)
            (β i) π (lam i) (φ i c) hcφ u) ∧
        ∀ Tfull Tannular : H →L[ℂ] H,
          (∀ v, Tfull v = elapsedGraphIntegral Δ (Ψ i) (b i) (χout i) (χsource i) (β i) v) →
          (∀ v, Tfull.adjoint v = ∫ t in Icc 0 Δ,
            (elapsedGraph (Ψ i) (b i) (χout i) (χsource i) (β i) t).adjoint v) →
          (∀ v, Tannular v = annularEnvelopeIntegral Δ (Ψ i) (b i) (χout i) (χsource i)
            (β i) π (lam i) (φ i c) hcφ v) →
          (∀ v, Tannular.adjoint v = annularEnvelopeAdjointIntegral Δ (Ψ i) (b i)
            (χout i) (χsource i) (β i) π (lam i) (φ i c) hcφ v) →
          (∫ t in Icc 0 Δ, R true i t c) = annularGraphOrientation adj
            (AnnularSobolev.demodulatedL2Operator (lam i) (φ i c) hcφ Tfull - Tannular) u) ∧
    (∀ i c, c ∈ V → ∀ hcφ : Continuous (φ i c),
      (∫ t in Icc 0 Δ, R true i t c) = carrierMultiplication (-(lam i)) (φ i c) hcφ
        (∫ t in Icc 0 Δ, R false i t c)) ∧
    ∀ dm,
      (∀ i c, c ∈ V → AEStronglyMeasurable (fun t => R dm i t c)
        (volume.restrict (Icc 0 Δ))) ∧
      (∀ i c, c ∈ V → IntegrableOn (fun t => R dm i t c) (Icc 0 Δ)) ∧
      (∀ i k c, c ∈ V → IntegrableOn
        (fun t => iteratedFDeriv ℝ k (R dm i t) c) (Icc 0 Δ)) ∧
      (∀ i, ContDiffOn ℝ ∞ (fun c => ∫ t in Icc 0 Δ, R dm i t c) V) ∧
      (∀ i k c, c ∈ V → iteratedFDeriv ℝ k
        (fun a => ∫ t in Icc 0 Δ, R dm i t a) c =
          ∫ t in Icc 0 Δ, iteratedFDeriv ℝ k (R dm i t) c) ∧
      (∀ i k (v : Fin k → P) c, c ∈ V → iteratedFDeriv ℝ k
        (fun a => ∫ t in Icc 0 Δ, R dm i t a) c v =
          ∫ t in Icc 0 Δ, iteratedFDeriv ℝ k (R dm i t) c v) ∧
      ∀ (s : ℝ) (k : ℕ) (Q : ℝ), ∃ Csob : ℝ, 0 ≤ Csob ∧
        ∀ i c, c ∈ V → ∀ v : Fin k → P, (∀ j, ‖v j‖ ≤ 1) →
          MemVectorFourierSobolev s
            (iteratedFDeriv ℝ k (fun a => ∫ t in Icc 0 Δ, R dm i t a) c v) ∧
          vectorFourierSobolevNorm s
            (iteratedFDeriv ℝ k (fun a => ∫ t in Icc 0 Δ, R dm i t a) c v) ≤
              (Δ * Csob) * A₀ i * lam i ^ (-Q) := by
  dsimp only
  let π : E → ℂ := fun η =>
    annularSelector (a₀ / (2 * M)) (2 * B₀ / m) (by positivity) (by positivity) η
  let R := fun dm i t => elapsedAnnularRemainder hX₀ adj dm (Ψ i) (b i)
    (χout i) (χsource i) (β i) π (φ i) t (lam i) (a i)
  have hp (dm : Bool) := originalAnnularComplement_sobolev (I := I × Icc (0 : ℝ) Δ)
    hV hX₀ hS hU hX hSU hXX hΔ hν hν1 ha₀ hB₀ hm hm1 hM1
    Pφ PΨ BΨ Bφ O T B C Mβ hPφ hPΨ hBΨ hBφ hO hT hB hMβ
    (fun j => lam j.1) (fun j => L j.1) (fun j => K j.1) (fun j => j.2.val)
    (fun j => A₀ j.1) (fun j => hlam j.1) (fun j => hL j.1) (fun j => hLK j.1)
    (fun j => hscale j.1) (fun j => j.2.property) (fun j => hA₀ j.1)
    (fun j => Ψ j.1) (fun j => b j.1) (fun j => χout j.1) (fun j => χsource j.1)
    (fun j => β j.1) (fun j => φ j.1) (fun j => a j.1)
    (fun j => ha j.1) (fun j => has j.1) (fun j => hmask j.1)
    (fun j => ho j.1) (fun j => hs j.1) (fun j => hβsmooth j.1) (fun j => hβ j.1)
    (fun j => OΨ j.1) (fun j => Ob j.1) (fun j => hOΨ j.1) (fun j => hOb j.1)
    (fun j => hΨ j.1) (fun j => hb j.1)
    (fun j => hmapΨ j.1 j.2 j.2.property) (fun j => hmapb j.1 j.2 j.2.property)
    (fun j => hφ j.1) (fun j => hΨb j.1 j.2 j.2.property) (fun j => hφb j.1)
    (fun j => hbb j.1 j.2 j.2.property) (fun j => hout j.1) (fun j => hsource j.1)
    (fun j => hmem j.1) (fun j => hsob j.1) (fun j => hgradient j.1)
    (fun j => hradial j.1 j.2 j.2.property) (fun j => hsourceφ j.1)
    (fun j => hsourceΨ j.1 j.2 j.2.property)
    (fun j => D j.1 j.2) (fun j => Ω j.1 j.2)
    (fun j => hD j.1 j.2 j.2.property) (fun j => hΩ j.1 j.2 j.2.property)
    (fun j => hDΩ j.1 j.2 j.2.property) (fun j => hphaseMap j.1 j.2 j.2.property)
    (fun j => hsD j.1 j.2 j.2.property) adj dm
  have horient (i : I) (t : ℝ) (ht : t ∈ Icc 0 Δ) (w : H) :
      Tendsto (fun j => annularGraphOrientation adj (Treg i j t) w) atTop
        (𝓝 (annularGraphOrientation adj
          (elapsedGraph (Ψ i) (b i) (χout i) (χsource i) (β i) t) w)) := by
    cases adj
    · exact hlim i t ht w
    · exact hlimAdj i t ht w
  have hstrong (j : I × Icc (0 : ℝ) Δ) :=
    annularGraphOrientation_strongLimit_of_testRealizations adj (elapsedPhase (Ψ j.1) j.2)
      (elapsedAmplitude (b j.1) (χout j.1) (χsource j.1) (β j.1) j.2)
      (χ j.1) (fun k => Treg j.1 k j.2)
      (fun k => hreal j.1 k j.2 j.2.property)
      (fun k => hcut j.1 k j.2 j.2.property)
      (horient j.1 j.2 j.2.property)
  have hid := (hp false).2.2.2.2.1 (fun _ => complexPhysicalCutoff)
    (fun _ => complexPhysicalCutoff_contDiff) (fun _ => complexPhysicalCutoff_hasCompactSupport)
    (fun _ => complexPhysicalCutoff_norm_le) (fun _ => complexPhysicalCutoff_tendsto) hstrong
  have hsame : ∀ i c, c ∈ V → ∃ w : H,
      w =ᵐ[volume] (fun x => carrier (lam i) (φ i c) x • a i c x) ∧
      ∀ t ∈ Icc 0 Δ, R false i t c =
        annularGraphOrientation adj (elapsedGraph (Ψ i) (b i) (χout i) (χsource i) (β i) t) w -
        annularGraphOrientation adj (elapsedGraph (Ψ i) (b i) (χout i) (χsource i)
          (fun ξ => π ((lam i)⁻¹ • ξ) * β i ξ) t) w := by
    intro i c hc
    obtain ⟨w, hw, _⟩ := hid (i, ⟨0, ⟨le_rfl, hΔ⟩⟩) c hc
    refine ⟨w, hw, fun t ht => ?_⟩
    obtain ⟨w', hw', he⟩ := hid (i, ⟨t, ht⟩) c hc
    have hww : w' = w := Lp.ext (hw'.trans hw.symm)
    subst w'
    have hAe : frequencyCutFullAmplitude (fun ξ => π ((lam i)⁻¹ • ξ))
        (elapsedAmplitude (b i) (χout i) (χsource i) (β i) t) =
        elapsedAmplitude (b i) (χout i) (χsource i)
          (fun ξ => π ((lam i)⁻¹ • ξ) * β i ξ) t :=
      annularElapsedAmplitude_eq_elapsedAmplitude (b i) (χout i) (χsource i)
        (β i) π t (lam i)
    apply Lp.ext
    change R false i t c =ᵐ[volume] fun x => (1 : ℂ) •
      ((annularGraphOrientation adj (elapsedGraph (Ψ i) (b i)
        (χout i) (χsource i) (β i) t) w -
        annularGraphOrientation adj (fullGraphOperator (elapsedPhase (Ψ i) t)
          (frequencyCutFullAmplitude (fun ξ => π ((lam i)⁻¹ • ξ))
            (elapsedAmplitude (b i) (χout i) (χsource i) (β i) t))) w) x) at he
    simpa only [one_smul, elapsedGraph, hAe] using he
  have hbtime (i : I) (t : ℝ) (x ξ : E) :
      ContinuousAt (fun q : (ℝ × ℝ) × (Euclidean d × Euclidean d) =>
        b i q.1.1 q.1.2 q.2.1 q.2.2)
        ((x 0, x 0 - t), (spatialPart x, spatialPart ξ)) := by
    exact (hb i).continuous.continuousAt.comp
      (f := fun q : (ℝ × ℝ) × (Euclidean d × Euclidean d) =>
        ((q.1.1, q.1.2, q.2.1), q.2.2)) (by fun_prop)
  have hocs (i : I) : HasCompactSupport (χout i) :=
    hX₀.of_isClosed_subset (isClosed_tsupport _) (fun _ h => hmask i (Or.inl h))
  have hscs (i : I) : HasCompactSupport (χsource i) :=
    hX₀.of_isClosed_subset (isClosed_tsupport _) (fun _ h => hmask i (Or.inr h))
  have hmfull (i : I) (w : H) : AEStronglyMeasurable
      (fun t => annularGraphOrientation adj
        (elapsedGraph (Ψ i) (b i) (χout i) (χsource i) (β i) t) w)
      (volume.restrict (Icc 0 Δ)) := by
    have hmr (j : ℕ) := aestronglyMeasurable_supported_elapsed_regularizations
      (Ψ i) (b i) (χout i) (χsource i) (β i) Δ hΔ (hΨtime i)
      (fun t _ x _ ξ _ => hbtime i t x ξ) (ho i).continuous (hs i).continuous
      (hβsmooth i).continuous (hocs i) (hscs i) (χ i) (fun k => (hχ i k).continuous)
      (hχcs i) (Treg i) (hreal i) (hrealAdj i) j w
    apply aestronglyMeasurable_of_tendsto_ae atTop (f := fun j t =>
      annularGraphOrientation adj (Treg i j t) w)
    · intro j
      cases adj
      · exact (hmr j).1
      · exact (hmr j).2
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact horient i t ht w
  have hmcut (i : I) (w : H) : AEStronglyMeasurable
      (fun t => annularGraphOrientation adj (elapsedGraph (Ψ i) (b i) (χout i) (χsource i)
        (fun ξ => π ((lam i)⁻¹ • ξ) * β i ξ) t) w) (volume.restrict (Icc 0 Δ)) := by
    have hmc := aestronglyMeasurable_supported_frequencyCut_and_adjoint
      (Ψ i) (b i) (χout i) (χsource i) (β i) (fun ξ => π ((lam i)⁻¹ • ξ))
      Δ hΔ (hΨtime i) (fun t _ x _ ξ _ => hbtime i t x ξ)
      (ho i).continuous (hs i).continuous (hβsmooth i).continuous
      (contDiff_physicalAnnularSelector _ _ _ _ (lam i)).continuous
      (hocs i) (hscs i) (hasCompactSupport_physicalAnnularSelector _ _ _ _
        (zero_lt_one.trans_le (hlam i))) w
    cases adj
    · simpa only [annularGraphOrientation, Bool.false_eq_true, ↓reduceIte,
        elapsedGraph, ← annularElapsedAmplitude_eq_elapsedAmplitude,
        AnnularSobolev.annularElapsedAmplitude] using hmc.1
    · simpa only [annularGraphOrientation, ↓reduceIte,
        elapsedGraph, ← annularElapsedAmplitude_eq_elapsedAmplitude,
        AnnularSobolev.annularElapsedAmplitude] using hmc.2
  have hmR (dm : Bool) (i : I) (c : P) (hc : c ∈ V) :
      AEStronglyMeasurable (fun t => R dm i t c) (volume.restrict (Icc 0 Δ)) := by
    obtain ⟨w, _, hw⟩ := hsame i c hc
    have hphys : AEStronglyMeasurable (fun t => R false i t c)
        (volume.restrict (Icc 0 Δ)) := by
      apply ((hmfull i w).sub (hmcut i w)).congr
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact (hw t ht).symm
    cases dm
    · exact hphys
    · have hr (t : ℝ) (ht : t ∈ Icc 0 Δ) := annularRemainder_support_and_demodulation
        adj (Ψ i) (b i) (χout i) (χsource i) (β i) π (φ i c) (lam i) t (a i c)
        (hmask i) (fun dm => R dm i t c)
        (fun dm => (hp dm).2.2.1 (i, ⟨t, ht⟩) c hc)
      apply aestronglyMeasurable_supported_demodulation hX₀.isClosed (φ i c) _
        (fun t => R false i t c) (fun t => R true i t c) hphys
        (fun t ht => (hr t ht).1) (fun t ht => (hr t ht).2)
      exact ((hφ i).continuousOn.comp (continuousOn_const.prodMk continuousOn_id)
        (fun x hx => ⟨hc, Or.inr (hXX hx)⟩))
  have hSob (dm : Bool) (s : ℝ) (k : ℕ) (Q : ℝ) := (hp dm).2.2.2.2.2 s k Q
  have hInt (dm : Bool) := elapsedIntegral_complementary_sobolev
    hΔ hV (R dm) lam A₀ hA₀ (hmR dm)
    (fun i t ht => (hp dm).2.1 (i, ⟨t, ht⟩)) (by
      intro s k Q
      obtain ⟨Csob, hCsob, hbound⟩ := hSob dm s k Q
      exact ⟨Csob, hCsob, fun i t ht c hc v hv => hbound (i, ⟨t, ht⟩) c hc v hv⟩)
  have hFullInt (i : I) (w : H) : IntegrableOn
      (fun t => annularGraphOrientation adj
        (elapsedGraph (Ψ i) (b i) (χout i) (χsource i) (β i) t) w) (Icc 0 Δ) := by
    apply (integrable_const (Creg i * ‖w‖)).mono' (hmfull i w)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    apply le_of_tendsto (horient i t ht w).norm
    apply Eventually.of_forall
    intro j
    have hn : ‖annularGraphOrientation adj (Treg i j t)‖ ≤ Creg i := by
      cases adj
      · exact hregBound i j t ht
      · simpa only [annularGraphOrientation, ↓reduceIte, ContinuousLinearMap.adjoint.norm_map]
          using hregBound i j t ht
    exact ((annularGraphOrientation adj (Treg i j t)).le_opNorm w).trans
      (mul_le_mul_of_nonneg_right hn (norm_nonneg w))
  have hDemod (i : I) (c : P) (hc : c ∈ V) (hcφ : Continuous (φ i c)) :
      (∫ t in Icc 0 Δ, R true i t c) = carrierMultiplication (-(lam i)) (φ i c) hcφ
        (∫ t in Icc 0 Δ, R false i t c) := by
    have he : ∀ᵐ t ∂volume.restrict (Icc 0 Δ), R true i t c =
        carrierMultiplication (-(lam i)) (φ i c) hcφ (R false i t c) := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      have hr := annularRemainder_support_and_demodulation
        adj (Ψ i) (b i) (χout i) (χsource i) (β i) π (φ i c) (lam i) t (a i c)
        (hmask i) (fun dm => R dm i t c)
        (fun dm => (hp dm).2.2.1 (i, ⟨t, ht⟩) c hc)
      exact Lp.ext (hr.2.trans
        (carrierMultiplication_ae (-(lam i)) (φ i c) hcφ (R false i t c)).symm)
    rw [integral_congr_ae he]
    exact (carrierMultiplication (-(lam i)) (φ i c) hcφ).integral_comp_comm
      ((hInt false).1 i c hc)
  refine ⟨?_, hDemod, fun dm => ⟨hmR dm, hInt dm⟩⟩
  · intro i c hc
    obtain ⟨w, hw, he⟩ := hsame i c hc
    have hRI := (hInt false).1 i c hc
    have hFI := hFullInt i w
    have hCI : IntegrableOn (fun t => annularGraphOrientation adj
        (elapsedGraph (Ψ i) (b i) (χout i) (χsource i)
          (fun ξ => π ((lam i)⁻¹ • ξ) * β i ξ) t) w) (Icc 0 Δ) := by
      apply (hFI.sub hRI).congr
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      dsimp only [Pi.sub_apply]
      rw [he t ht, sub_sub_cancel]
    have hRIeq : (∫ t in Icc 0 Δ, R false i t c) =
        (∫ t in Icc 0 Δ, annularGraphOrientation adj
          (elapsedGraph (Ψ i) (b i) (χout i) (χsource i) (β i) t) w) -
        (∫ t in Icc 0 Δ, annularGraphOrientation adj
          (elapsedGraph (Ψ i) (b i) (χout i) (χsource i)
            (fun ξ => π ((lam i)⁻¹ • ξ) * β i ξ) t) w) := by
      rw [← integral_sub hFI hCI]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact he t ht
    refine ⟨w, hw, he, hFI, hCI, hRIeq, fun hcφ => ?_⟩
    let u := carrierMultiplication (-(lam i)) (φ i c) hcφ w
    have hcu : carrierMultiplication (lam i) (φ i c) hcφ u = w := by
      simpa only [neg_neg] using carrierMultiplication_neg_cancel (-(lam i)) (φ i c) hcφ w
    refine ⟨u, ?_, hcu, ?_, ?_⟩
    · change carrierMultiplication (-(lam i)) (φ i c) hcφ w =ᵐ[volume] a i c
      filter_upwards [carrierMultiplication_ae (-(lam i)) (φ i c) hcφ w, hw] with x hx hwx
      rw [hx, hwx, smul_smul, carrier_neg_mul, one_smul]
    · rw [hDemod i c hc hcφ, hRIeq]
      simpa only [hcu] using demodulatedElapsedDifference_eq_annularDifference
        adj Δ (Ψ i) (b i) (χout i) (χsource i) (β i) π (lam i) (φ i c) hcφ u
    · intro Tfull Tannular hfull hfullAdj hnear hnearAdj
      rw [hDemod i c hc hcφ, hRIeq]
      simpa only [hcu] using demodulatedElapsedDifference_eq_boundedDifference
        adj Δ (Ψ i) (b i) (χout i) (χsource i) (β i) π (lam i) (φ i c) hcφ
        Tfull Tannular hfull hfullAdj hnear hnearAdj u

end JanetCartan.ResponseTransfer.DirectEvolution.IntegratedEnvelope.Tails
