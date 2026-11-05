module

public import JanetCartan.Geometry.IsometricEmbedding.Response.FullSourceEnvelopes.SourceJets
public import JanetCartan.Geometry.IsometricEmbedding.Response.FullSourceEnvelopes.Coordinates
public import JanetCartan.Geometry.IsometricEmbedding.Response.FullSourceEnvelopes.AnnularInput
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.IntegratedEnvelopes
public import JanetCartan.Analysis.Microlocal.FullSourceStationary.Geometry

/-!
# Complete elapsed envelopes with an independent source covector

Apply the Euclidean integrated-envelope primitives to the Cartesian split of
the external parameters. The low graph certificates, physical cutoffs,
frequency, integration variables, critical points and averaged Hessians are
the original ones. Only parameter directions change. The label and covector
are independently variable in the final ordered word.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4800000
set_option maxRecDepth 4096
open Set Metric Filter MeasureTheory LineDeriv
open scoped ContDiff Topology Matrix.Norms.Frobenius SchwartzMap
namespace JanetCartan.ResponseTransfer.FullSourceEnvelopes
open RetainedFactors
open Pseudodifferential FourierIntegral FullLowBounds LowBounds SourceExpansion
open NormalComparison FrequencyCutoff AmplitudeBound FullAmplitudePrimitiveBudget.Local
open RegularSector.Characteristic EvolutionIntegral SymbolBudgets KernelIdentification
open DirectEvolution CompactTransfer BranchAmplitudes ModifiedLow AnnularComplement AnnularSobolev
open IntegratedEnvelope IntegratedEnvelope.Parameter
open JanetCartan.ResponseTransfer.Complement JanetCartan.ResponseTransfer.Complement.ParameterDerivatives
open WholeImageGeometry
variable {d r : ℕ} {I ι : Type} [Fintype ι]
local notation "Par" => Euclidean 3 × Euclidean d
local notation "Pc" => Euclidean (3 + d)
local notation "E" => Euclidean (d + 1)
local notation "CW" => CarrierVariables (d + 1)
local notation "F" => EuclideanSpace ℂ (Fin r)
local notation "H" => SpacetimeL2 d r


/-- Physical factor of order `-o`: the complete solver sum for `o=0` and
the supplied full residual for `o=1` (`app:ch_response:eq:fixed-factor-transfer`). -/
abbrev fullElapsedPhysicalFactor (W₀ W₁ PW₁ : I → TwoTimeAmplitude d r) (o : Fin 2)
    (j : I) : TwoTimeAmplitude d r := if o = 0 then W₀ j + W₁ j else PW₁ j

/-- From the original source Sobolev profiles, the full solver sum or the entire
residual satisfies the elapsed envelope in both literal orientations.
`FullSourceStationary` supplies the same critical branch and phase jets;
the retained capped construction supplies the complete amplitude jets, graph
realizations and masks. Supported agreement is produced for both complete
factors by `capped_solver_phase_eq_representative_on_amplitude` and
`capped_residual_phase_eq_representative_on_amplitude`. Taking the very same
phase gives the controlled-representative estimate by reflexivity. The family
index may include all varying histories.
Only the fixed word constant absorbs the inverse coordinate norm
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem fullSource_fullElapsed_envelopes_of_supported_phase
    (W₀ W₁ PW₁ : I → TwoTimeAmplitude d r) (o : Fin 2)
    {V : Set Par} (hV : IsOpen V) {X₀ S U : Set E}
    (hX₀ : IsCompact X₀) (hS : IsCompact S) (hU : IsOpen U)
    (hSU : S ⊆ U) (hXU : X₀ ⊆ U)
    {src ν a₀ B₀ m M Rcell graphGap growth : ℝ}
    (hsrc : 0 ≤ src) (hν : 0 < ν) (hν1 : ν < 1)
    (ha₀ : 0 < a₀) (hB₀ : 0 < B₀) (hm : 0 < m) (hm1 : m ≤ 1) (hM : 1 ≤ M)
    (hRcell : 0 < Rcell) (hgraphGap : 0 < graphGap) (hgrowth : 0 ≤ growth)
    (Mgraph Ggraph cgraph : ℝ) (hcgraph : 1 ≤ cgraph)
    (hR : ∀ x ∈ U, ‖x‖ ≤ Rcell)
    (basis : OrthonormalBasis ι ℝ CW)
    (Rstar : ℕ) (hRstar : fullLowReserve (d + 1) + 2 < Rstar)
    (lam L K A₀ : I → ℝ)
    (hlam : ∀ i, 1 ≤ lam i) (hL : ∀ i, 1 ≤ L i) (hLK : ∀ i, L i ≤ K i)
    (hscale : ∀ i, K i ≤ lam i ^ (1 - ν)) (hA₀ : ∀ i, 0 ≤ A₀ i)
    (Ψ : I → TwoTimePhase d)
    (χout χsource β : E → ℂ)
    (ho : ContDiff ℝ ∞ χout) (hs : ContDiff ℝ ∞ χsource) (hβ : ContDiff ℝ ∞ β)
    (hmask : tsupport χout ∪ tsupport χsource ⊆ X₀)
    (Mβ : ℝ) (hMβ : 0 ≤ Mβ) (hβbound : ∀ ξ, ‖β ξ‖ ≤ Mβ)
    (φ : I → Par → E → ℝ)
    (hΨ : ∀ i, ContDiff ℝ ∞ (jointPhase (Ψ i)))
    (hW : ∀ i, ContDiff ℝ ∞ (jointAmplitude (fullElapsedPhysicalFactor W₀ W₁ PW₁ o i)))
    (hφ : ∀ i, ContDiff ℝ ∞ (Function.uncurry (φ i)))
    (Bphase Bprimary Bamp Aphase Aamp : ℕ → ℝ)
    (hBphase : ∀ j, 0 ≤ Bphase j) (hBprimary : ∀ j, 0 ≤ Bprimary j)
    (hBamp : ∀ j, 0 ≤ Bamp j) (hAphase : ∀ j, 0 ≤ Aphase j)
    (hAamp : ∀ j, 0 ≤ Aamp j)
    (hphaseJets : ∀ i t, t ∈ Icc 0 (3 * src / 4) → ∀ ξ ∈ tsupport β, ∀ j y, y ∈ U →
      ‖iteratedFDeriv ℝ j (jointPhase (Ψ i)) (elapsedPoint t ((y, 0), ξ))‖ ≤
        Bphase j * (1 + ‖ξ‖) * L i ^ (j - 1))
    (hprimaryJets : ∀ i j c, c ∈ V → ∀ y ∈ U,
      ‖iteratedFDeriv ℝ j (Function.uncurry (φ i)) (c,y)‖ ≤ Bprimary j * L i ^ (j - 1) ∧
      ‖iteratedFDeriv ℝ j (φ i c) y‖ ≤ Bprimary j * L i ^ (j - 1))
    (hamplitudeJets : ∀ i t, t ∈ Icc 0 (3 * src / 4) → ∀ ξ ∈ tsupport β, ∀ j y, y ∈ U →
      ‖iteratedFDeriv ℝ j (jointAmplitude (fullElapsedPhysicalFactor W₀ W₁ PW₁ o i)) (elapsedPoint t ((y, 0), ξ))‖ ≤ Bamp j * L i ^ j)
    (hgradient : ∀ i c, c ∈ V → ∀ y ∈ U,
      a₀ ≤ ‖fderiv ℝ (φ i c) y‖ ∧ ‖fderiv ℝ (φ i c) y‖ ≤ B₀)
    (hradial : ∀ i t, t ∈ Icc 0 (3 * src / 4) → ∀ ξ ∈ tsupport β, ∀ y ∈ U,
      m * ‖ξ‖ ≤ ‖fderiv ℝ (fun x ↦ elapsedPhase (Ψ i) t x ξ) y‖ ∧
        ‖fderiv ℝ (fun x ↦ elapsedPhase (Ψ i) t x ξ) y‖ ≤ M * ‖ξ‖)
    (Creg : I → ℝ)
    (hgraphs : ∀ i, CappedGraphRealizations (3 * src / 4) (Ψ i) (fullElapsedPhysicalFactor W₀ W₁ PW₁ o i) χout χsource β (Creg i))
    (Dn : Set E) (hβDn : tsupport β ⊆ Dn)
    (η : I → ℝ → E → E → E → E)
    (J : I → ℝ → E → E → E → E →L[ℝ] E)
    (bandLo bandHi : ℝ)
    (hwhole : ∀ i t, t ∈ Icc 0 (3 * src / 4) →
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
        ∀ q ∈ Vn, (2 : ℝ)^l ≤ cgraph * (1 + ‖(2 : ℝ)^l • q.2.2‖))
    (Ucrit : Set (E × Par)) (Dcrit Kcrit : Set CW)
    (hUc : IsOpen Ucrit) (hDc : IsOpen Dcrit) (hcD : Convex ℝ Dcrit)
    (hKcrit : IsCompact Kcrit) (hKD : Kcrit ⊆ Dcrit) (hXUc : X₀ ×ˢ V ⊆ Ucrit)
    (InvBound radius : ℝ) (hInvBound : 0 ≤ InvBound) (hradius : 0 ≤ radius)
    (w₀ : I → Bool → ℝ → E × Par → CW)
    (hcritical : ∀ i adj t, t ∈ Icc 0 (3 * src / 4) →
      let f := fun q w ↦ FullSourceStationary.fullSourceJointPhase adj (Ψ i) (fun x c ↦ φ i c x) ((t,q),w)
      ContDiffOn ℝ ∞ (Function.uncurry f) (Ucrit ×ˢ Dcrit) ∧
      ContDiffOn ℝ ∞ (w₀ i adj t) Ucrit ∧ MapsTo (w₀ i adj t) Ucrit Dcrit ∧
      (∀ q ∈ Ucrit, gradient (f q) (w₀ i adj t q) = 0 ∧ f q (w₀ i adj t q) = 0) ∧
      (∀ q ∈ Ucrit, ∀ w ∈ Dcrit, IsUnit (averagedPhaseHessian f (w₀ i adj t) q w) ∧
        ‖Ring.inverse (averagedPhaseHessian f (w₀ i adj t) q w)‖ ≤ InvBound) ∧
      ∀ j q, q ∈ Ucrit ×ˢ Dcrit →
        ‖iteratedFDeriv ℝ j (Function.uncurry f) q‖ ≤ Aphase j * L i ^ (j - Rstar))
    (F₀ : I → Set E) (hF : ∀ i, IsCompact (F₀ i) ∧ (0 : E) ∉ F₀ i ∧ F₀ i ⊆ tsupport β)
    (hΘ : ∀ i t, t ∈ Icc 0 (3 * src / 4) → ∀ x ∈ X₀, ∀ θ, lam i • θ ∈ F₀ i →
      elapsedPhase (Ψ i) t x (lam i • θ) = lam i * elapsedPhase (Ψ i) t x θ)
    (a : I → Par → E → F)
    (haJoint : ∀ i, ContDiff ℝ ∞ (fun q : E × Par ↦ a i q.2 q.1))
    (haGlobal : ∀ i (q : E × Par), q.1 ∉ S → a i q.2 q.1 = 0)
    (ha : ∀ i, ContDiffOn ℝ ∞ (Function.uncurry (a i)) (V ×ˢ univ))
    (has : ∀ i c, c ∈ V → tsupport (a i c) ⊆ S)
    (C : ℕ → ℕ → ℝ)
    (hmem : ∀ i c (hc : c ∈ V) l (w : Fin l → Par), (∀ j, ‖w j‖ ≤ 1) → ∀ s : ℕ,
      MemVectorFourierSobolev (s : ℝ)
        ((fullSource_parameterJet_memLp hS hV (ha i) (has i) l w hc).toLp
          (fun y ↦ iteratedFDeriv ℝ l (fun q ↦ a i q y) c w)))
    (hsob : ∀ i c (hc : c ∈ V) l (w : Fin l → Par), (∀ j, ‖w j‖ ≤ 1) → ∀ s : ℕ,
      vectorFourierSobolevNorm (s : ℝ)
        ((fullSource_parameterJet_memLp hS hV (ha i) (has i) l w hc).toLp
          (fun y ↦ iteratedFDeriv ℝ l (fun q ↦ a i q y) c w)) ≤ C l s * A₀ i * K i ^ (s + l)) :
    let W := fullElapsedPhysicalFactor W₀ W₁ PW₁ o
    let π : E → ℂ := fun θ ↦ annularSelector (a₀ / (2 * M)) (2 * B₀ / m) (by positivity) (by positivity) θ
    let α := fun i (adj : Bool) t ↦ if adj then normalizedAdjointAnnularElapsedAmplitude (P := Par)
      (W i) χout χsource β π t (lam i) (-(o.val : ℤ)) else
        normalizedAnnularElapsedAmplitude (P := Par) (W i) χout χsource β π t (lam i) (-(o.val : ℤ))
    (∀ i adj t, t ∈ Icc 0 (3 * src / 4) → ∀ j q, q ∈ Ucrit ×ˢ Dcrit →
      ‖iteratedFDeriv ℝ j (Function.uncurry (α i adj t)) q‖ ≤ Aamp j * L i ^ (j + 2 - Rstar)) →
    (∀ i adj t, t ∈ Icc 0 (3 * src / 4) →
      (∀ v ∈ tsupport (Function.uncurry (α i adj t)),
        v.1.1 ∈ X₀ ∧ v.2 ∈ Kcrit ∧ v.2.fst ∈ X₀ ∧ ‖v.2.snd‖ ≤ radius ∧ lam i • v.2.snd ∈ F₀ i) ∧
      ∀ q : E × Par, Function.support (α i adj t q) ⊆ Kcrit) →
    ∀ Ψactual : I → TwoTimePhase d,
    (∀ i t, t ∈ Icc 0 (3 * src / 4) → ∀ x y ξ, elapsedAmplitude (W i) χout χsource β t x y ξ ≠ 0 →
      elapsedPhase (Ψactual i) t x ξ = elapsedPhase (Ψ i) t x ξ) →
    ∀ adj : Bool, ∀ ps : List Par, (∀ v ∈ ps, ‖v‖ ≤ 1) →
    HasEnvelopeProfile (vectorFourierSobolevScale (d := d + 1) (I := Fin r))
      (fun z : I × V ↦ orderedTransferAction (fun v g c ↦ fderiv ℝ g c v) ps
        (fun c ↦ carrierMultiplication (-(lam z.1)) (φ z.1 c) ((hφ z.1).continuous.comp (continuous_const.prodMk continuous_id))
          ((if adj then fun u ↦ ∫ t in Icc 0 (3 * src / 4), (elapsedGraph (Ψactual z.1) (W z.1) χout χsource β t).adjoint u
            else elapsedGraphIntegral (3 * src / 4) (Ψactual z.1) (W z.1) χout χsource β)
            (carrierMultiplication (lam z.1) (φ z.1 c) ((hφ z.1).continuous.comp (continuous_const.prodMk continuous_id))
              (graphTestToLp (vectorOriginalDatumTest (fun q : E × Par ↦ a z.1 q.2 q.1)
                (haJoint z.1) hS (haGlobal z.1) [] c))))) z.2)
      (fun z ↦ lam z.1 ^ (-(o.val : ℤ)) * A₀ z.1 * K z.1 ^ ps.length) (fun z ↦ K z.1) := by
  classical
  intro W π α hαjet hsupport Ψactual hphaseEq adj ps hps
  let e : Pc ≃L[ℝ] Par := EuclideanSpace.finAddEquivProd
  let ep := (ContinuousLinearEquiv.refl ℝ E).prodCongr e
  let pe := e.prodCongr (ContinuousLinearEquiv.refl ℝ E)
  let ec := ep.prodCongr (ContinuousLinearEquiv.refl ℝ CW)
  let Vc := e ⁻¹' V
  let Uc := ep ⁻¹' Ucrit
  have hVc : IsOpen Vc := hV.preimage e.continuous
  have hUC : IsOpen Uc := hUc.preimage ep.continuous
  have hep (q : E × Pc) : ‖ep q‖ ≤ ‖q‖ :=
    max_le_max le_rfl (fullSource_coordinate_norm_bounds.1 q.2)
  have hpe (q : Pc × E) : ‖pe q‖ ≤ ‖q‖ :=
    max_le_max (fullSource_coordinate_norm_bounds.1 q.1) le_rfl
  have hec (q : (E × Pc) × CW) : ‖ec q‖ ≤ ‖q‖ := max_le_max (hep q.1) le_rfl
  let ac := fun i (c : Pc) ↦ a i (e c)
  let φc := fun i (c : Pc) ↦ φ i (e c)
  have hacJoint i : ContDiff ℝ ∞ (fun q : E × Pc ↦ ac i q.2 q.1) := (haJoint i).comp ep.contDiff
  have hacGlobal i (q : E × Pc) (hq : q.1 ∉ S) : ac i q.2 q.1 = 0 := haGlobal i (ep q) hq
  have hac i : ContDiffOn ℝ ∞ (Function.uncurry (ac i)) (Vc ×ˢ univ) :=
    (ha i).comp pe.contDiff.contDiffOn (fun _ h ↦ ⟨h.1, h.2⟩)
  have hasc i c (hc : c ∈ Vc) : tsupport (ac i c) ⊆ S := has i (e c) hc
  have hφc i : ContDiff ℝ ∞ (Function.uncurry (φc i)) := (hφ i).comp pe.contDiff
  have hclass i c (hc : c ∈ Vc) l (w : Fin l → Pc) :
      (parameterSource_memLp hS hVc (hac i) (hasc i) l w hc).toLp
        (fun y ↦ iteratedFDeriv ℝ l (fun q ↦ ac i q y) c w) =
      (fullSource_parameterJet_memLp hS hV (ha i) (has i) l (e ∘ w) hc).toLp
        (fun y ↦ iteratedFDeriv ℝ l (fun q ↦ a i q y) (e c) (e ∘ w)) := by
    apply MemLp.toLp_congr
    apply Filter.Eventually.of_forall
    intro y
    exact congrArg (fun D : Pc [×l]→L[ℝ] F ↦ D w) (externalCoordinate_jet e (fun q ↦ a i q y) c l)
  have hunit {l : ℕ} {w : Fin l → Pc} (hw : ∀ j, ‖w j‖ ≤ 1) (j : Fin l) :
      ‖(e ∘ w) j‖ ≤ 1 := (fullSource_coordinate_norm_bounds.1 (w j)).trans (hw j)
  obtain ⟨Dprofile, hDprofile, hmixed⟩ := exists_fullSource_mixedL2_profile (d + 1) d r C
  have hDatum := hmixed I V S hS hV a A₀ K ha has haJoint haGlobal hA₀
    (fun i ↦ (hL i).trans (hLK i)) hmem hsob
  have hDatumC i c (hc : c ∈ Vc) j :
      ∃ hm : MemLp (fun x : E ↦ iteratedFDeriv ℝ j (fun q : E × Pc ↦ ac i q.2 q.1) (x,c)) 2 volume,
        ‖hm.toLp (fun x : E ↦ iteratedFDeriv ℝ j (fun q : E × Pc ↦ ac i q.2 q.1) (x,c))‖ ≤
          A₀ i * Dprofile j * K i ^ j := by
    obtain ⟨hm, hb⟩ := hDatum i (e c) hc j
    have hle (x : E) := norm_externalCoordinate_jet_le ep hep (fun q : E × Par ↦ a i q.2 q.1) (x,c) j
    have hcont : Continuous (fun x : E ↦ iteratedFDeriv ℝ j (fun q : E × Pc ↦ ac i q.2 q.1) (x,c)) :=
      ((hacJoint i).continuous_iteratedFDeriv (by simp)).comp (continuous_id.prodMk continuous_const)
    let : SecondCountableTopologyEither E ((E × Pc) [×j]→L[ℝ] F) := ⟨Or.inl inferInstance⟩
    have hm' := hm.mono hcont.aestronglyMeasurable (Filter.Eventually.of_forall hle)
    refine ⟨hm', le_trans ?_ hb⟩
    rw [Lp.norm_toLp, Lp.norm_toLp]
    exact ENNReal.toReal_mono hm.eLpNorm_ne_top (eLpNorm_mono hm'.aestronglyMeasurable hle)
  let : CompactSpace X₀ := isCompact_iff_compactSpace.mp hX₀
  have hΔ : 0 ≤ 3 * src / 4 := by positivity
  have hSX : S ∪ X₀ ⊆ U := union_subset hSU hXU
  let Omask : ℕ → ℝ := fun j ↦ cNorm (S ∪ X₀) j χout
  let Tmask : ℕ → ℝ := fun j ↦ cNorm (S ∪ X₀) j χsource
  have hO j : 0 ≤ Omask j := cNorm_nonneg ..
  have hT j : 0 ≤ Tmask j := cNorm_nonneg ..
  have hout j y (hy : y ∈ S ∪ X₀) : ‖iteratedFDeriv ℝ j χout y‖ ≤ Omask j :=
    norm_iteratedFDeriv_le_cNorm (hS.union hX₀) (ho.of_le (by simp)) hy le_rfl
  have hsource j y (hy : y ∈ S ∪ X₀) : ‖iteratedFDeriv ℝ j χsource y‖ ≤ Tmask j :=
    norm_iteratedFDeriv_le_cNorm (hS.union hX₀) (hs.of_le (by simp)) hy le_rfl
  have hBΨ i t ht ξ hξ j y hy := (hphaseJets i t ht ξ (subset_tsupport _ hξ) j y (hSX hy)).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (hL i) (Nat.sub_le j 1))
      (mul_nonneg (hBphase j) (by positivity : 0 ≤ 1 + ‖ξ‖)))
  have hBφ i j c (hc : c ∈ Vc) y hy := (norm_externalCoordinate_jet_le pe hpe
    (Function.uncurry (φ i)) (c,y) j).trans <| (hprimaryJets i j (e c) hc y (hSX hy)).1.trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (hL i) (Nat.sub_le j 1)) (hBprimary j))
  have hPφ i c (hc : c ∈ V) y (hy : y ∈ S) (k : ℕ) (_hk : 1 ≤ k) :
      ‖iteratedFDeriv ℝ (k + 1) (φ i c) y‖ ≤ Bprimary (k + 1) * L i ^ k := by
    simpa only [Nat.add_sub_cancel] using (hprimaryJets i (k + 1) c hc y (hSU hy)).2
  have hPΨ i t (ht : t ∈ Icc 0 (3 * src / 4)) ξ (hξ : β ξ ≠ 0) y (hy : y ∈ S) (k : ℕ) (_hk : 1 ≤ k) :
      ‖iteratedFDeriv ℝ (k + 1) (jointPhase (Ψ i)) (elapsedPoint t ((y, 0), ξ))‖ ≤
        Bphase (k + 1) * (1 + ‖ξ‖) * L i ^ k := by
    simpa only [Nat.add_sub_cancel] using hphaseJets i t ht ξ (subset_tsupport _ hξ) (k + 1) y (hSU hy)
  choose χ hχ hχcs Treg hlow hreg hreal hrealAdj hcut hlim hlimAdj using hgraphs
  have hSPhase i t : ContDiff ℝ ∞ (Function.uncurry (elapsedPhase (Ψ i) t)) := by
    apply contDiff_iff_contDiffAt.mpr
    rintro ⟨x, ξ⟩
    apply contDiffAt_elapsedPhase
    apply contDiffAt_elapsedSpatialPhase
    exact ((hΨ i).comp ((contDiff_fst.fst.prodMk
      (contDiff_fst.snd.prodMk contDiff_snd.fst)).prodMk contDiff_snd.snd)).contDiffAt
  have hΨcont i : Continuous (fun q : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      Ψ i q.1.1 q.1.2 q.2.1 q.2.2) :=
    ((hΨ i).comp ((contDiff_fst.fst.prodMk
      (contDiff_fst.snd.prodMk contDiff_snd.fst)).prodMk contDiff_snd.snd)).continuous
  let Kn := fun i ↦ X₀ ×ˢ (X₀ ×ˢ F₀ i)
  have hKn i : IsClosed (Kn i) := hX₀.isClosed.prod (hX₀.isClosed.prod (hF i).1.isClosed)
  have hKnsub i : Kn i ⊆ U ×ˢ (U ×ˢ Dn) :=
    fun _ h ↦ ⟨hXU h.1, hXU h.2.1, hβDn ((hF i).2.2 h.2.2)⟩
  have hπ : ContDiff ℝ ∞ π := Complex.ofRealCLM.contDiff.comp (contDiff_annularSelector ..)
  let αc := fun i (rev : Bool) t ↦ if rev then normalizedAdjointAnnularElapsedAmplitude (P := Pc)
    (W i) χout χsource β π t (lam i) (-(o.val : ℤ)) else
      normalizedAnnularElapsedAmplitude (P := Pc) (W i) χout χsource β π t (lam i) (-(o.val : ℤ))
  have hαsmooth i rev t : ContDiff ℝ ∞ (Function.uncurry (αc i rev t)) :=
    contDiff_orientedAnnularAmplitude (3+d) rev (W i) χout χsource β π (hW i) ho hs hβ hπ t
      (zero_lt_one.trans_le (hlam i)).ne' o.val
  have hαeq i rev t : Function.uncurry (αc i rev t) = Function.uncurry (α i rev t) ∘ ec := by
    cases rev <;> rfl
  have hsup i rev t : tsupport (Function.uncurry (αc i rev t)) =
      ec ⁻¹' tsupport (Function.uncurry (α i rev t)) := by
    rw [hαeq]
    exact tsupport_comp_eq_preimage _ ec.toHomeomorph
  have hsC i rev t ht q (hq : q ∈ tsupport (Function.uncurry (αc i rev t))) :=
    (hsupport i rev t ht).1 (ec q) (by rw [hsup i rev t] at hq; exact hq)
  have hjC i rev t (ht : t ∈ Icc 0 (3 * src / 4)) j q (hq : q ∈ Uc ×ˢ Dcrit) :
      ‖iteratedFDeriv ℝ j (Function.uncurry (αc i rev t)) q‖ ≤ Aamp j * L i ^ (j+2-Rstar) := by
    rw [hαeq]
    exact (norm_externalCoordinate_jet_le ec hec _ q j).trans (hαjet i rev t ht j (ec q) hq)
  have hsKC i rev t (ht : t ∈ Icc 0 (3 * src / 4)) (q : E × Pc) : Function.support (αc i rev t q) ⊆ Kcrit := by
    cases rev
    · exact (hsupport i false t ht).2 (ep q)
    · exact (hsupport i true t ht).2 (ep q)
  have hslice i rev t (ht : t ∈ Icc 0 (3 * src / 4)) c (hc : c ∈ Vc) q
      (hq : normalizedSlice c q ∈ tsupport (Function.uncurry (αc i rev t))) :
      normalizedSlice c q ∈ Uc ×ˢ Dcrit :=
    ⟨hXUc ⟨(hsC i rev t ht _ hq).1,hc⟩, hKD (hsC i rev t ht _ hq).2.1⟩
  have hφsource i c : ContDiff ℝ ∞ (φ i c) := (hφ i).comp (contDiff_const.prodMk contDiff_id)
  have hbox y (hy : y ∈ X₀) j : |y j| ≤ Rcell :=
    by simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le y j).trans (hR y (hXU hy))
  have hnormal i t ht := (hwhole i t ht).2.2.2.2.2.2.2.2.1 (Kn i) (hKn i) (hKnsub i)
  have hsh i t ht l := (hwhole i t ht).2.2.2.2.2.2.2.2.2 l
  let fc := fun i rev t (q : E × Pc) w ↦ FullSourceStationary.fullSourceJointPhase rev
    (Ψ i) (fun y c ↦ φ i c y) ((t, ep q), w)
  let wc := fun i rev t ↦ w₀ i rev t ∘ ep
  have hcC i rev t (ht : t ∈ Icc 0 (3 * src / 4)) :=
    ((hcritical i rev t ht).1.comp ec.contDiff.contDiffOn
      (show MapsTo ec (Uc ×ˢ Dcrit) (Ucrit ×ˢ Dcrit) from fun _ h ↦ h))
  have hpC i rev t (ht : t ∈ Icc 0 (3 * src / 4)) j q (hq : q ∈ Uc ×ˢ Dcrit) :
      ‖iteratedFDeriv ℝ j (Function.uncurry (fc i rev t)) q‖ ≤ Aphase j * L i ^ (j - Rstar) :=
    (norm_externalCoordinate_jet_le ec hec _ q j).trans ((hcritical i rev t ht).2.2.2.2.2 j (ec q) hq)
  let qs := ps.map (fun v ↦ (2 : ℝ)⁻¹ • e.symm v)
  have hqs : ∀ u ∈ qs, ‖u‖ ≤ 1 := fullSource_coordinate_word_unit ps hps
  let action (phase : I → TwoTimePhase d) (i : I) (c : Par) : H :=
    carrierMultiplication (-(lam i)) (φ i c) (hφsource i c).continuous
      ((if adj then fun u ↦ ∫ t in Icc 0 (3 * src / 4), (elapsedGraph (phase i) (W i) χout χsource β t).adjoint u
        else elapsedGraphIntegral (3 * src / 4) (phase i) (W i) χout χsource β)
        (carrierMultiplication (lam i) (φ i c) (hφsource i c).continuous
          (graphTestToLp (vectorOriginalDatumTest (fun q : E × Par ↦ a i q.2 q.1)
            (haJoint i) hS (haGlobal i) [] c))))
  have hgraph i t (ht : t ∈ Icc 0 (3 * src / 4)) :
      elapsedGraph (Ψactual i) (W i) χout χsource β t = elapsedGraph (Ψ i) (W i) χout χsource β t :=
    fullGraphOperator_phase_congr _ _ _ (hphaseEq i t ht)
  have he : action Ψactual = action Ψ := by
    funext i c
    apply congrArg (carrierMultiplication (-(lam i)) (φ i c) (hφsource i c).continuous)
    cases adj <;> apply setIntegral_congr_fun measurableSet_Icc <;> intro t ht <;>
      dsimp only <;> rw [hgraph i t ht]
  change HasEnvelopeProfile _ (fun z : I × V ↦ orderedTransferAction
    (fun v g c ↦ fderiv ℝ g c v) ps (action Ψactual z.1) (z.2 : Par)) _ _
  rw [he]
  apply fullSource_profile_of_coordinate_word _ V (action Ψ)
    (fun i ↦ lam i ^ (-(o.val : ℤ)) * A₀ i * K i ^ ps.length) K ps
  have hlength : ps.length = qs.length := (List.length_map ..).symm
  rw [hlength]
  cases adj
  case' false =>
    have prim := Assembly.fullElapsedEnvelope_hasEnvelopeProfile_of_primitive_jets
      (r := r) (I := I) (ι := ι) hVc hX₀ hS hU hU hSU hXU hΔ hν hν1 ha₀ hB₀ hm hm1 hM
    let rev := false
  case' true =>
    have prim := Assembly.fullElapsedAdjointEnvelope_hasEnvelopeProfile_of_primitive_jets
      (r := r) (I := I) (ι := ι) hVc hX₀ hS hU hU hSU hXU hΔ hν hν1 ha₀ hB₀ hm hm1 hM
    let rev := true
  all_goals
    refine prim
      (fun k ↦ Bprimary (k + 1)) (fun k ↦ Bphase (k + 1)) Bphase Bprimary Omask Tmask Bamp C Mβ
      (fun k ↦ hBprimary (k + 1)) (fun k ↦ hBphase (k + 1)) hBphase hBprimary hO hT hBamp hMβ
      lam L K A₀ hlam hL hLK hscale hA₀ Ψ W (fun _ ↦ χout) (fun _ ↦ χsource) (fun _ ↦ β) φc ac
      hac hasc (fun _ ↦ hmask) (fun _ ↦ ho) (fun _ ↦ hs) (fun _ ↦ hβ) (fun _ ↦ hβbound)
      (fun _ ↦ univ) (fun _ ↦ univ) (fun _ ↦ isOpen_univ) (fun _ ↦ isOpen_univ)
      (fun i ↦ (hΨ i).contDiffOn) hW (by intros; trivial) (by intros; trivial)
      (fun i ↦ (hφc i).contDiffOn) hBΨ hBφ
      (fun i t ht ξ hξ j y hy ↦ hamplitudeJets i t ht ξ (subset_tsupport _ hξ) j y (hSX hy))
      (fun _ ↦ hout) (fun _ ↦ hsource) (fun i c hc l w hw s ↦ (hclass i c hc l w).symm ▸ hmem i (e c) hc l (e ∘ w) (hunit hw) s)
      (fun i c hc l w hw s ↦ (hclass i c hc l w).symm ▸ hsob i (e c) hc l (e ∘ w) (hunit hw) s)
      (fun i c hc ↦ hgradient i (e c) hc)
      (fun i t ht ξ hξ y hy ↦ hradial i t ht ξ (subset_tsupport _ hξ) y hy) (fun i c hc ↦ hPφ i (e c) hc) hPΨ
      (fun _ _ ↦ univ) (fun _ _ ↦ univ) (by intros; exact isClosed_univ)
      (by intros; exact isOpen_univ) (by intros; exact Subset.rfl) (by intros; trivial)
      (by intros; trivial) (fun i _ _ _ _ _ _ ↦ (hΨcont i).continuousAt)
      χ hχ hχcs Treg hreal hrealAdj (fun i j t _ ↦ hcut i j t) hlim hlimAdj Creg hreg
      Rcell (4 * Rcell) Mgraph Ggraph cgraph (by positivity)
      (by apply (div_lt_iff₀ (by positivity : 0 < 4 * Rcell)).mpr; linarith)
      hgraphGap hgrowth hcgraph basis Aphase Aamp Dprofile hAphase hAamp hDprofile hInvBound hradius hbox
      F₀ (fun i ↦ (hF i).1.isClosed) (fun i ↦ (hF i).2.1) (fun i t _ ↦ hSPhase i t)
      (fun _ _ ↦ U) (fun _ _ ↦ Dn) η J (fun _ _ ↦ U ×ˢ (U ×ˢ Dn)) (fun i _ ↦ Kn i)
      (fun i t ht ↦ (hwhole i t ht).1)
      (fun i t ht ↦ (hwhole i t ht).2.1)
      (fun i t ht ↦ (hwhole i t ht).2.2.1)
      (fun i t ht ↦ (hwhole i t ht).2.2.2.1)
      (fun i t ht ↦ (hwhole i t ht).2.2.2.2.1)
      (fun i t ht q hq ↦ abs_pos.mp (hgraphGap.trans_le ((hwhole i t ht).2.2.2.2.2.1 q hq)))
      (fun i t ht ↦ (hwhole i t ht).2.2.2.2.2.2.1)
      (fun _ _ _ _ _ hx hy hξ ↦ ⟨hx, hy, hξ⟩)
      (fun i t ht ↦ (hnormal i t ht).1) (fun i t ht ↦ (hnormal i t ht).2)
      (fun _ _ _ ↦ hR) (fun i t ht ↦ (hwhole i t ht).2.2.2.2.2.2.2.1)
      (fun _ _ l ↦ U ×ˢ (U ×ˢ normalizedSourceBand Dn ((2 : ℝ)^l) bandLo bandHi))
      (fun i t ht l ↦ (hsh i t ht l).1) (fun i t ht l ↦ (hsh i t ht l).2.1)
      (fun i t ht l ↦ (hsh i t ht l).2.2.1) (fun i t ht l ↦ (hsh i t ht l).2.2.2.1)
      (fun i t ht l ↦ (hsh i t ht l).2.2.2.2.1) (fun i t ht l ↦ (hsh i t ht l).2.2.2.2.2.1)
      (fun i t ht l ↦ (hsh i t ht l).2.2.2.2.2.2.1)
      (fun i t ht l ↦ (hsh i t ht l).2.2.2.2.2.2.2.1)
      (fun i t ht l ↦ (hsh i t ht l).2.2.2.2.2.2.2.2)
      (fun _ _ _ ↦ hXU) (fun i _ _ ↦ (hF i).2.2.trans hβDn)
      Rstar hRstar (-(o.val : ℤ)) (fun i ↦ wc i rev) (fun _ _ ↦ Uc) (fun _ _ ↦ Dcrit)
      (fun _ _ _ ↦ hUC) (fun _ _ _ ↦ hDc) (fun _ _ _ ↦ hcD)
      (fun i t ht ↦ hcC i rev t ht)
      (fun i t ht ↦ (hcritical i rev t ht).2.1.comp ep.contDiff.contDiffOn (fun _ h ↦ h))
      (fun i t ht _ hq ↦ (hcritical i rev t ht).2.2.1 hq)
      (fun i t ht q hq ↦ ((hcritical i rev t ht).2.2.2.1 (ep q) hq).1)
      (fun i t ht q hq ↦ ((hcritical i rev t ht).2.2.2.1 (ep q) hq).2)
      (fun i t ht q hq w hw ↦ ((hcritical i rev t ht).2.2.2.2.1 (ep q) hq w hw).1)
      (fun i t ht q hq w hw ↦ ((hcritical i rev t ht).2.2.2.2.1 (ep q) hq w hw).2)
      (fun i t ht ↦ hpC i rev t ht)
      (fun _ _ ↦ Kcrit) (fun _ _ _ ↦ hKcrit) (fun _ _ _ ↦ hKD) (fun _ _ _ _ h ↦ hXUc ⟨h.1,h.2⟩)
      (fun i c ↦ (hφsource i (e c)).continuous) (fun i c _ ↦ (hφsource i (e c)).contDiffOn)
      hΨcont hacJoint hacGlobal hDatumC hΘ
      (fun i t _ ↦ (hαsmooth i rev t).contDiffOn) (fun i t ht ↦ hjC i rev t ht)
      (fun i t ht q _ ↦ hsKC i rev t ht q)
      (fun i t ht v hv ↦ (hsC i rev t ht v hv).1)
      (fun i t ht ↦ hslice i rev t ht)
      (fun i t ht _ _ q hq ↦ (hsC i rev t ht _ hq).2.2.2.1)
      (fun i t ht _ _ q hq ↦ ⟨?_, ?_, (hsC i rev t ht _ hq).2.2.2.2⟩)
      qs hqs
    all_goals first | exact (hsC i rev t ht _ hq).1 | exact (hsC i rev t ht _ hq).2.2.1

end JanetCartan.ResponseTransfer.FullSourceEnvelopes
