module

public import JanetCartan.Geometry.IsometricEmbedding.Response.FullSourceEnvelopes.Assembly
public import JanetCartan.Geometry.IsometricEmbedding.Response.RetainedCharacteristicEnvelopes.PhysicalAnnularCarrier
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.IncidenceCriticalSlice
public import JanetCartan.Geometry.IsometricEmbedding.Response.FullSourceEnvelopes.StationarySlice
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EndpointPdoBounds.Masks

/-!
# Full-source envelopes with the original physical frequency cutoff

This is the physical-cutoff, original-incidence specialization of the existing
full-source assembly. It keeps the permutation inside `2*threshold`, the actual
open incidence set and its stationary segments. It creates no new analytic
interface. The retained family application must still instantiate the phase,
amplitude and graph inputs from their concrete producers.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius SchwartzMap
namespace JanetCartan.ResponseTransfer.RetainedCharacteristicEnvelopes
open FullSourceEnvelopes RegularSector.Characteristic.ResidualCoordinates
open ActualCarriers ActualCarriers.CurrentFullPhase HamiltonPhase FrozenMenu CompatibleResponse
open RegularSector.Characteristic ConicPhase EvolutionIntegral AmplitudeBounds SymbolBudgets
open Pseudodifferential FourierIntegral FullLowBounds LowBounds SourceExpansion
open NormalComparison FrequencyCutoff AmplitudeBound FullAmplitudePrimitiveBudget.Local
open DirectEvolution CompactTransfer BranchAmplitudes ModifiedLow AnnularComplement AnnularSobolev
open JanetCartan.ResponseTransfer.Complement UniformEvolution IntegratedEnvelope RegularSector.FiniteMasks RetainedFactors WholeImageGeometry FullSourceStationary
variable {d r : ℕ} {I ι : Type} [Fintype ι]
variable {P : Patch (d + 1)} {Uref : Set (Euclidean (d + 1))} {hUref : IsOpen Uref}
  (T : PatchQuantitativeFamily P Uref hUref)
local notation "E" => Euclidean (d + 1)
local notation "Par" => Euclidean 3 × Euclidean d
local notation "CW" => CarrierVariables (d + 1)
local notation "F" => EuclideanSpace ℂ (Fin r)
local notation "TC" => RegularSector.Characteristic.TwoTimePoint (Euclidean d)

/-- Apply the full-source envelope machinery to the literal doubled physical
multiplier on the supplied original incidence domain. Both `W₀+W₁` and full
`PW₁`, both physical masks, every ordered full-source parameter word and the
entire elapsed interval are unchanged. The original segment certificates
transfer the stationary phases to their representatives. Closed-support
nesting proves the annular carrier and radial identity for the physical cutoff.

This deduction still requires the original raw profile and graph inputs;
its final instantiation on the selected finite family remains unfinished.
Consumers: the retained characteristic envelope and the complete normalized
response (`app:ch_response:eq:fixed-factor-transfer`,
`app:ch_response:eq:direct-envelope-profile`). -/
theorem fullSource_physical_incidence_solver_residual_envelopes (i₀ : Fin (d + 1))
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : RootState (Euclidean d))
    {ε aperture g Rad τ src δ : ℝ} (hε : 0 < ε) (hAp : 0 < aperture) (hg : 0 < g)
    (hτ : 0 < τ) (hτε : τ ≤ ε) (hsrc : 0 ≤ src) (hsrcτ : src ≤ τ)
    (hδ : 0 < δ) (hδg : δ ≤ g / (1 + ‖ℓ‖)) (hδhalf : δ ≤ 1 / 2)
    {ν a₀ B₀ m M Rcell graphGap growth : ℝ}
    (hν : 0 < ν) (hν1 : ν < 1) (ha₀ : 0 < a₀) (hB₀ : 0 < B₀)
    (hm : 0 < m) (hm1 : m ≤ 1) (hM : 1 ≤ M) (hRcell : 0 < Rcell)
    (hgraphGap : 0 < graphGap) (hgrowth : 0 ≤ growth)
    (Mgraph Ggraph cgraph : ℝ) (hcgraph : 1 ≤ cgraph)
    (basis : OrthonormalBasis ι ℝ CW) (Rstar : ℕ)
    (hRstar : fullLowReserve (d + 1) + 2 < Rstar)
    {V : Set Par} (hV : IsOpen V) (hVc : IsCompact (closure V)) {S : Set E} (hS : IsCompact S)
    (χout χsource : E → ℂ) (ho : ContDiff ℝ ∞ χout) (hs : ContDiff ℝ ∞ χsource)
    (hco : HasCompactSupport χout) (hcs : HasCompactSupport χsource)
    (κtime : ℝ → ℝ) (hplateau : ∀ x, χout x ≠ 0 → κtime =ᶠ[𝓝 (x 0)] (fun _ ↦ 1))
    (mask : E → ℝ) (hmask : ContDiff ℝ ∞ mask) (hmaskRange : ∀ ξ, mask ξ ∈ Icc 0 1)
    (hmaskCarrier : tsupport (mask ∘ physicalCoordinates i₀) ∩ sphere (0 : E) 1 ⊆ fullAngularCone ℓ z.2.2 (ε / 4) (aperture / 2))
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (χg : TC → ℝ) (heg : ∀ p ∈ closedBall (z.1, z) (4 * ε), χg =ᶠ[𝓝 p] (fun _ ↦ 1))
    (χp : E × Par → ℝ)
    (Bphase Bprimary Bamp Aphase Aamp : ℕ → ℝ) (C : ℕ → ℕ → ℝ)
    (hBphase : ∀ j, 0 ≤ Bphase j) (hBprimary : ∀ j, 0 ≤ Bprimary j)
    (hBamp : ∀ j, 0 ≤ Bamp j) (hAphase : ∀ j, 0 ≤ Aphase j) (hAamp : ∀ j, 0 ≤ Aamp j)
    (InvBound : ℝ) (hInv : 0 ≤ InvBound) (bandLo bandHi : ℝ)
    (Q : I → {Q : E → Fin (d + 1) → MetricTensor (d + 1) // ContDiffOn ℝ ∞ Q Uref ∧
      cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress (d + 1)) < T.family.threshold})
    (chart : I → OpenPartialHomeomorph TC TC) (G : I → TC → ℝ)
    (matrix : I → Fin 3 → TC → Matrix (Fin r) (Fin r) ℂ)
    (hGsolver : ∀ i p, p ∈ tsupport (matrix i 0) ∪ tsupport (matrix i 1) →
      G i =ᶠ[𝓝 p] phase ℓ (chart i))
    (hGres : ∀ i p, κtime =ᶠ[𝓝 p.1] (fun _ ↦ 1) → matrix i 2 p ≠ 0 →
      G i =ᶠ[𝓝 p] phase ℓ (chart i))
    (κ : I → Bool → (ℝ × (E × Par)) → CW)
    (η : I → ℝ → E → E → E → E) (J : I → ℝ → E → E → E → E →L[ℝ] E)
    (lam L K A₀ : I → ℝ) (hlam : ∀ i, 1 ≤ lam i) (hL : ∀ i, 1 ≤ L i)
    (hLK : ∀ i, L i ≤ K i) (hscale : ∀ i, K i ≤ lam i ^ (1 - ν)) (hA₀ : ∀ i, 0 ≤ A₀ i)
    (a : I → Par → E → F) (haJoint : ∀ i, ContDiff ℝ ∞ (fun p : E × Par ↦ a i p.2 p.1))
    (haGlobal : ∀ i (p : E × Par), p.1 ∉ S → a i p.2 p.1 = 0)
    (ha : ∀ i, ContDiffOn ℝ ∞ (Function.uncurry (a i)) (V ×ˢ univ))
    (has : ∀ i c, c ∈ V → tsupport (a i c) ⊆ S) (o : Fin 2) (Creg : I → ℝ) :
    let U := elapsedPhysicalBox z (ε / 2)
    let X₀ := tsupport χout ∪ tsupport χsource
    let β : E → ℂ := fun ξ ↦ (dilatedConicMask mask (2 * threshold) (physicalCoordinates i₀ ξ) : ℂ)
    let Dn := retainedFrequencyDomain ℓ z ε aperture (1 / 2)
    let O := retainedOpenAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture g Rad
    let D := retainedOpenIntegrationDomain z ε O
    let Uc := U ×ˢ V
    let Z := Ioo (-2 * τ) (2 * τ) ×ˢ Uc
    let KP := closure (elapsedPhysicalBox z ε) ×ˢ closure V
    let Ksigned := fullSourceSignedCarrier z ε (closure V) O
    let aSel := a₀ / (2 * M)
    let bSel := 2 * B₀ / m
    let π : E → ℂ := fun θ ↦ annularSelector aSel bSel (div_pos ha₀ (by positivity))
      (div_pos (by positivity) hm) θ
    let Ψ := fun i ↦ SmoothRepresentative.curriedRepresentative ℓ δ hδ χg (twoTimePhase (chart i))
    let Ψactual : I → TwoTimePhase d := fun i t s y ξ ↦ G i (t, (s, (y, ξ)))
    let Wraw := fun (k : Fin 3) i ↦ curryCharacteristicMatrix (matrix i k)
    let W := fullElapsedPhysicalFactor (Wraw 0) (Wraw 1) (Wraw 2) o
    let φ₀ := fun i ↦ T.fullSourcePhaseInCoordinates i₀ (Q i)
    let φ := fun i c y ↦ χp (y, c) * φ₀ i y c
    let raw := fun i rev ↦ fullSourceJointPhase rev (curriedPhase ℓ (chart i)) (φ₀ i)
    IsOpen O → Convex ℝ O → IsCompact (closure O) →
    (retainedAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture
      (retainedSelectorGap z.2.2 (ε / 2) aperture aSel) (2 * bSel) ⊆ O) →
    (S ⊆ U) → (X₀ ⊆ U) → (tsupport β ⊆ Dn) → (∀ x ∈ U, ‖x‖ ≤ Rcell) →
    (∀ p ∈ KP, χp =ᶠ[𝓝 p] (fun _ ↦ 1)) →
    ∀ hprimary : ∀ i, ContDiff ℝ ∞ (fun p : E × Par ↦ φ i p.2 p.1),
    (∀ i j p, p ∈ KP →
      ‖iteratedFDeriv ℝ j (Function.uncurry (φ i)) p.swap‖ ≤ Bprimary j * L i ^ (j - Rstar) ∧
      ‖iteratedFDeriv ℝ j (φ i p.2) p.1‖ ≤ Bprimary j * L i ^ (j - Rstar)) →
    (∀ i, ContDiff ℝ ∞ (jointPhase (Ψ i))) →
    (∀ i, ContDiff ℝ ∞ (jointAmplitude (W i))) →
    (∀ i t, t ∈ Icc 0 (3 * src / 4) → ∀ ξ ∈ tsupport β, ∀ j y, y ∈ U →
      ‖iteratedFDeriv ℝ j (jointPhase (Ψ i)) (elapsedPoint t ((y, 0), ξ))‖ ≤
        Bphase j * (1 + ‖ξ‖) * L i ^ (j - 1)) →
    (∀ i t, t ∈ Icc 0 (3 * src / 4) → ∀ ξ ∈ tsupport β, ∀ j y, y ∈ U →
      ‖iteratedFDeriv ℝ j (jointAmplitude (W i)) (elapsedPoint t ((y, 0), ξ))‖ ≤ Bamp j * L i ^ j) →
    (∀ i c, c ∈ V → ∀ y ∈ U,
      a₀ ≤ ‖fderiv ℝ (fun x ↦ φ₀ i x c) y‖ ∧ ‖fderiv ℝ (fun x ↦ φ₀ i x c) y‖ ≤ B₀) →
    (∀ i t, t ∈ Icc 0 (3 * src / 4) → ∀ ξ ∈ tsupport β, ∀ y ∈ U,
      m * ‖ξ‖ ≤ ‖fderiv ℝ (fun x ↦ elapsedPhase (Ψ i) t x ξ) y‖ ∧
        ‖fderiv ℝ (fun x ↦ elapsedPhase (Ψ i) t x ξ) y‖ ≤ M * ‖ξ‖) →
    (∀ i, CappedGraphRealizations (3 * src / 4) (Ψ i) (W i) χout χsource β (Creg i)) →
    (∀ i t, t ∈ Icc 0 (3 * src / 4) →
      let phase := elapsedPhase (Ψ i) t
      let domain := bufferedNormalDomain U Dn phase
      let Wn := U ×ˢ (U ×ˢ Dn)
      AveragedGradientChart phase U Dn (η i t) (J i t) graphGap ∧
      IsOpen domain ∧ ContDiffOn ℝ ∞ (normalInverseCoordinates (η i t)) domain ∧
      MapsTo (normalInverseCoordinates (η i t)) domain Wn ∧
      ContDiffOn ℝ ∞ (fun q : NormalVariables (d + 1) ↦ J i t q.1 q.2.1 q.2.2) Wn ∧
      (∀ q ∈ Wn, graphGap ≤ |(J i t q.1 q.2.1 q.2.2).det|) ∧
      (∀ q ∈ domain, normalForwardCoordinates phase (normalInverseCoordinates (η i t) q) = q) ∧
      (∀ x ∈ U, ∀ y ∈ U, ∀ ξ ∈ Dn, ‖averagedGradient phase x y ξ‖ ≤ growth * (1 + ‖ξ‖)) ∧
      (∀ Kn : Set (NormalVariables (d + 1)), IsClosed Kn → Kn ⊆ Wn →
        IsClosed (normalForwardCoordinates phase '' Kn) ∧
          normalForwardCoordinates phase '' Kn ⊆ domain) ∧
      ∀ l : ℕ,
        let Vn := U ×ˢ (U ×ˢ normalizedSourceBand Dn ((2 : ℝ)^l) bandLo bandHi)
        let Un := normalDyadicShell domain l
        IsOpen Un ∧ IsOpen Vn ∧
        ContDiffOn ℝ ∞ (normalInverseCoordinates (normalizedNormalInverse ((2 : ℝ)^l) (η i t))) Un ∧
        MapsTo (normalInverseCoordinates (normalizedNormalInverse ((2 : ℝ)^l) (η i t))) Un Vn ∧
        ContDiffOn ℝ ∞ (fun q : NormalVariables (d + 1) ↦
          normalizedNormalJacobian ((2 : ℝ)^l) (J i t) q.1 q.2.1 q.2.2) Vn ∧
        (∀ q ∈ Vn, graphGap ≤ |(normalizedNormalJacobian ((2 : ℝ)^l) (J i t) q.1 q.2.1 q.2.2).det|) ∧
        (∀ q ∈ Vn, ∀ j ≤ primitiveNormalReserve (d + 1),
          ‖iteratedFDeriv ℝ j (fun q : NormalVariables (d + 1) ↦
            normalizedNormalJacobian ((2 : ℝ)^l) (J i t) q.1 q.2.1 q.2.2) q‖ ≤ Mgraph) ∧
        (∀ q ∈ Un, ∀ j, 1 ≤ j → j ≤ primitiveNormalReserve (d + 1) →
          ‖iteratedFDeriv ℝ j (normalInverseCoordinates (normalizedNormalInverse ((2 : ℝ)^l) (η i t))) q‖ ≤ Ggraph) ∧
        ∀ q ∈ Vn, (2 : ℝ)^l ≤ cgraph * (1 + ‖(2 : ℝ)^l • q.2.2‖)) →
    (∀ i rev, ContDiffOn ℝ ∞ (raw i rev) (Z ×ˢ D)) →
    (∀ i rev, ContDiffOn ℝ ∞ (κ i rev) Z) →
    (∀ i rev p, p ∈ Z → κ i rev p ∈ D ∧
      gradient (fun w ↦ raw i rev (p, w)) (κ i rev p) = 0 ∧ raw i rev (p, κ i rev p) = 0) →
    (∀ i rev p, p ∈ Z → ∀ w ∈ closure D,
      let f := fun q w ↦ raw i rev ((p.1, q), w)
      IsUnit (averagedPhaseHessian f (fun q ↦ κ i rev (p.1, q)) p.2 w) ∧
        ‖Ring.inverse (averagedPhaseHessian f (fun q ↦ κ i rev (p.1, q)) p.2 w)‖ ≤ InvBound) →
    (∀ i rev p, p ∈ Z → ∀ w ∈ closure D,
      ∀ u ∈ uIcc (0 : ℝ) p.1, ∀ a ∈ Icc (0 : ℝ) 1,
        ((u, p.2), κ i rev p + a • (w - κ i rev p)) ∈ Ksigned) →
    (∀ i rev j t (v : (E × Par) × CW), ((t, v.1), v.2) ∈ Ksigned →
      ‖iteratedFDeriv ℝ j (fun b : (E × Par) × CW ↦ raw i rev ((t, b.1), b.2)) v‖ ≤
        Aphase j * L i ^ (j - Rstar)) →
    (∀ i rev t, t ∈ Icc 0 (3 * src / 4) → ∀ j v,
      v ∈ (closure (elapsedPhysicalBox z ε) ×ˢ closure V) ×ˢ closure D →
      ‖iteratedFDeriv ℝ j (Function.uncurry (orientedAnnularAmplitude Par rev
        (W i) χout χsource β π t (lam i) (-(o.val : ℤ)))) v‖ ≤ Aamp j * L i ^ (j + 2 - Rstar)) →
    (∀ i c (hc : c ∈ V) l (w : Fin l → Par), (∀ j, ‖w j‖ ≤ 1) → ∀ s : ℕ,
      MemVectorFourierSobolev (s : ℝ)
        ((fullSource_parameterJet_memLp hS hV (ha i) (has i) l w hc).toLp
          (fun y ↦ iteratedFDeriv ℝ l (fun q ↦ a i q y) c w))) →
    (∀ i c (hc : c ∈ V) l (w : Fin l → Par), (∀ j, ‖w j‖ ≤ 1) → ∀ s : ℕ,
      vectorFourierSobolevNorm (s : ℝ)
        ((fullSource_parameterJet_memLp hS hV (ha i) (has i) l w hc).toLp
          (fun y ↦ iteratedFDeriv ℝ l (fun q ↦ a i q y) c w)) ≤ C l s * A₀ i * K i ^ (s + l)) →
    ∀ adj : Bool, ∀ ps : List Par, (∀ v ∈ ps, ‖v‖ ≤ 1) →
    HasEnvelopeProfile (vectorFourierSobolevScale (d := d + 1) (I := Fin r))
      (fun z : I × V ↦ orderedTransferAction (fun v g c ↦ fderiv ℝ g c v) ps
        (fun c ↦ carrierMultiplication (-(lam z.1)) (φ z.1 c) ((hprimary z.1).continuous.comp (continuous_id.prodMk continuous_const))
          ((if adj then fun u ↦ ∫ t in Icc 0 (3 * src / 4), (elapsedGraph (Ψactual z.1) (W z.1) χout χsource β t).adjoint u
            else elapsedGraphIntegral (3 * src / 4) (Ψactual z.1) (W z.1) χout χsource β)
            (carrierMultiplication (lam z.1) (φ z.1 c) ((hprimary z.1).continuous.comp (continuous_id.prodMk continuous_const))
              (graphTestToLp (vectorOriginalDatumTest (fun q : E × Par ↦ a z.1 q.2 q.1)
                (haJoint z.1) hS (haGlobal z.1) [] c))))) z.2)
      (fun z ↦ lam z.1 ^ (-(o.val : ℤ)) * A₀ z.1 * K z.1 ^ ps.length) (fun z ↦ K z.1) := by
  intro U X₀ β Dn O D Uc Z KP Ksigned aSel bSel π Ψ Ψactual Wraw W φ₀ φ raw
    hO hcO hKO hsel hSU hXU hβD hbox heP hprimary hpjet hΨ hW hphase hamp hgrad hrad hgraphs hwhole
    hraw hκ hstat hHess hsegments hjoint hann hmem hsob
  have hX : IsOpen U := isOpen_elapsedPhysicalBox _ _
  have hX₀ : IsCompact X₀ := hco.union hcs
  have hUc : IsOpen Uc := hX.prod hV
  have hP {p : E × Par} (hp : p ∈ Uc) : p ∈ KP :=
    ⟨subset_closure (UniformEvolution.closure_elapsedPhysicalBox_half_subset hε (subset_closure hp.1)),
      subset_closure hp.2⟩
  have hPc {x : E} {c : Par} (hx : x ∈ U) (hc : c ∈ V) : (x, c) ∈ Uc := ⟨hx, hc⟩
  have hφ i : ContDiff ℝ ∞ (Function.uncurry (φ i)) := (hprimary i).comp (contDiff_snd.prodMk contDiff_fst)
  have hgrad' i c (hc : c ∈ V) y (hy : y ∈ U) :
      a₀ ≤ ‖fderiv ℝ (φ i c) y‖ ∧ ‖fderiv ℝ (φ i c) y‖ ≤ B₀ := by
    have he : φ i c =ᶠ[𝓝 y] fun x ↦ φ₀ i x c := by
      filter_upwards [(heP (y, c) (hP (hPc hy hc))).comp_tendsto
        (continuous_id.prodMk continuous_const).continuousAt] with b hb
      change χp (b, c) = 1 at hb
      exact (congrArg (· * φ₀ i b c) hb).trans (one_mul _)
    rw [he.fderiv_eq]
    exact hgrad i c hc y hy
  have hpjet' i j c (hc : c ∈ V) y (hy : y ∈ U) :=
    hpjet i j (y, c) (hP (hPc hy hc))
  have hjScale i j : Bprimary j * L i ^ (j - Rstar) ≤ Bprimary j * L i ^ (j - 1) :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (hL i) (by omega)) (hBprimary j)
  have hsA : 0 < aSel := div_pos ha₀ (by positivity)
  have hsB : 0 < bSel := div_pos (by positivity) hm
  have hπ : ContDiff ℝ ∞ π := Complex.ofRealCLM.contDiff.comp (contDiff_annularSelector ..)
  have hβraw := EndpointPdoBounds.complex_dilatedConicMask_pdo_bounds mask hmask hmaskRange (2 * threshold)
  have hβs : ContDiff ℝ ∞ β := hβraw.1.comp (physicalCoordinates i₀).contDiff
  have hβbound : ∀ ξ, ‖β ξ‖ ≤ 1 := fun ξ ↦ hβraw.2 (physicalCoordinates i₀ ξ)
  have hxo : tsupport χout ⊆ U := subset_union_left.trans hXU
  have hxs : tsupport χsource ⊆ U := subset_union_right.trans hXU
  obtain ⟨Kcrit, hKcrit, hKD, hgeometry⟩ := exists_physical_capped_annular_integration_carrier
    (p := 3) i₀ ℓ z hε hAp hsA hsB hδ hδg hsel χout χsource hco hcs hxo hxs
  let F₀ := fun i ↦ SmoothRepresentative.retainedFrequencyCarrier δ (2 * bSel) (lam i) β
  have hgeo i := hgeometry mask hmaskCarrier threshold hthreshold (lam i) (hlam i)
  obtain ⟨hD, hcD, _, _⟩ := retainedOpenIntegrationDomain_geometry z ε hO hcO hKO
  have hElapsed : Icc (0 : ℝ) (3 * src / 4) ⊆ Ioo (-2 * τ) (2 * τ) := by
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hcrit i rev := full_source_incidence_critical_slice_of_stationary_segments T i₀
    ℓ z hε hAp hg hO hcO hKO hδ hδg heg (chart i) V hV hVc (Q i) χp
    (fun p hp ↦ (heP p hp).eq_of_nhds) hElapsed (κ i rev) rev InvBound (L i) Rstar
    Aphase (hraw i rev) (hκ i rev) (hstat i rev) (hHess i rev) (hsegments i rev) (hjoint i rev)
  have haMap i rev t := fullSource_annularAmplitude_jets_support rev (W i) χout χsource β π
    (hW i) ho hs hβs hπ t (zero_lt_one.trans_le (hlam i)).ne' o.val
  have hphaseEq i t (ht : t ∈ Icc 0 (3 * src / 4)) x y ξ
      (hA : elapsedAmplitude (W i) χout χsource β t x y ξ ≠ 0) :
      elapsedPhase (Ψactual i) t x ξ = elapsedPhase (Ψ i) t x ξ := by
    by_cases h : o = 0
    · apply capped_solver_phase_eq_representative_on_amplitude ℓ z hε (hsrcτ.trans hτε)
        (chart i) hδ hδhalf heg (matrix i 0) (matrix i 1) (G i) (hGsolver i) χout χsource β hxo hβD ht x y ξ
      simpa only [W, fullElapsedPhysicalFactor, ite_eq_left h, Wraw] using hA
    · apply capped_residual_phase_eq_representative_on_amplitude ℓ z hε (hsrcτ.trans hτε)
        (chart i) hδ hδhalf heg (matrix i 2) (G i) κtime (hGres i) χout χsource β hxo hplateau hβD ht x y ξ
      simpa only [W, fullElapsedPhysicalFactor, ite_eq_right h, Wraw] using hA
  refine fullSource_fullElapsed_envelopes_of_supported_phase (Wraw 0) (Wraw 1) (Wraw 2) o
    hV hX₀ hS hX hSU hXU hsrc hν hν1 ha₀ hB₀ hm hm1 hM hRcell hgraphGap hgrowth Mgraph Ggraph
    cgraph hcgraph hbox basis Rstar hRstar lam L K A₀ hlam hL hLK hscale hA₀ Ψ χout χsource β
    ho hs hβs (Subset.refl X₀) 1 zero_le_one hβbound φ hΨ hW hφ Bphase Bprimary Bamp Aphase Aamp
    hBphase hBprimary hBamp hAphase hAamp hphase
    (fun i j c hc y hy ↦ ⟨(hpjet' i j c hc y hy).1.trans (hjScale i j),
      (hpjet' i j c hc y hy).2.trans (hjScale i j)⟩)
    hamp hgrad' hrad Creg hgraphs Dn hβD η J bandLo bandHi hwhole Uc D Kcrit hUc hD hcD hKcrit hKD
    (fun _ h ↦ hPc (hXU h.1) h.2) InvBound (2 * bSel) hInv (by positivity) (fun i rev t q ↦ κ i rev (t, q))
    hcrit F₀ (fun i ↦ ⟨(hgeo i).1, (hgeo i).2.1, (hgeo i).2.2.1⟩)
    (fun i t _ x _ θ hθ ↦ (hgeo i).2.2.2.1 χg (twoTimePhase (chart i)) t x θ hθ)
    a haJoint haGlobal ha has C hmem hsob ?_ ?_ Ψactual hphaseEq
  · intro i rev t ht j v hv
    have hp := hP hv.1
    exact hann i rev t ht j v ⟨hp, subset_closure hv.2⟩
  · intro i rev t _
    have hsupp := (hgeo i).2.2.2.2 r (W i) t (-(o.val : ℤ)) rev
    refine ⟨?_, ?_⟩
    · intro v hv
      exact hsupp.1 ((v.1.1, v.1.2.1), v.2) (((haMap i rev t).2.1).le hv)
    · intro q
      exact ((haMap i rev t).2.2 q).le.trans (hsupp.2 (q.1, q.2.1))

end JanetCartan.ResponseTransfer.RetainedCharacteristicEnvelopes
