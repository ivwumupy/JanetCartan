module
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ReservedRetardedNear.FiniteNear
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ReservedRetardedNear.SuppliedCriticalSlice
public import JanetCartan.Geometry.IsometricEmbedding.Response.RetainedCharacteristicEnvelopes.PhysicalAnnularCarrier

/-!
# Reserved annular retarded bounds on the original incidence carrier

The actual physical cutoff and source-incidence segments construct the annular
support and critical slices. The original source phase may have either sign;
no graph phase is negated or reselected. The finite near theorem then preserves
the source reserve over the complete original elapsed interval.
Consumer: the selected-history producer in `app:ch_response:eq:fixed-factor-transfer`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius SchwartzMap
namespace JanetCartan.FixedDomainInverse.ReservedRetardedNear
open ResponseTransfer RetainedCharacteristicEnvelopes FullSourceEnvelopes
open RegularSector.Characteristic.ResidualCoordinates
open ActualCarriers ActualCarriers.CurrentFullPhase HamiltonPhase FrozenMenu CompatibleResponse
open RegularSector.Characteristic ConicPhase EvolutionIntegral AmplitudeBounds SymbolBudgets
open Pseudodifferential FourierIntegral FullLowBounds LowBounds SourceExpansion
open NormalComparison FrequencyCutoff AmplitudeBound FullAmplitudePrimitiveBudget.Local
open DirectEvolution CompactTransfer BranchAmplitudes ModifiedLow AnnularComplement AnnularSobolev
open JanetCartan.ResponseTransfer.Complement
open UniformEvolution IntegratedEnvelope RegularSector.FiniteMasks RetainedFactors WholeImageGeometry FullSourceStationary
variable {d r : ℕ} {I ι : Type} [Fintype ι]
local notation "E" => Euclidean (d+1)
local notation "Par" => Euclidean 3 × Euclidean d
local notation "CW" => CarrierVariables (d+1)
local notation "Fibre" => EuclideanSpace ℂ (Fin r)
local notation "TC" => RegularSector.Characteristic.TwoTimePoint (Euclidean d)

/-- Original physical annular support and stationary segments supply the
finite reserved retarded estimate for the SAME complete solver sum/residual.
Both source signs use this theorem with their own original source phase;
the physical operator and full `3*src/4` interval are retained
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem physical_incidence_reserved_annular_envelopes
    (i₀ : Fin (d+1)) (ℓ : Euclidean d →L[ℝ] ℝ) (z : RootState (Euclidean d))
    {ε aperture g Rad τ src δ : ℝ} (hε : 0 < ε) (hAp : 0 < aperture) (hg : 0 < g)
    (hτ : 0 < τ) (hτε : τ ≤ ε) (hsrc : 0 ≤ src) (hsrcτ : src ≤ τ)
    (hδ : 0 < δ) (hδg : δ ≤ g/(1+‖ℓ‖)) (hδhalf : δ ≤ 1/2)
    {ν a₀ B₀ m M Rcell graphGap growth : ℝ}
    (hν : 0 < ν) (hν1 : ν < 1) (ha₀ : 0 < a₀) (hB₀ : 0 < B₀)
    (hm : 0 < m) (hRcell : 0 < Rcell) (hM : 1 ≤ M)
    (hgraphGap : 0 < graphGap) (hgrowth : 0 ≤ growth)
    (Mgraph Ggraph cgraph : ℝ) (hcgraph : 1 ≤ cgraph)
    (basis : OrthonormalBasis ι ℝ CW) (Rsource Rstar : ℕ)
    (hreserve : Rsource + fullLowReserve (d+1) + 4 ≤ Rstar)
    {V : Set Par} (hV : IsOpen V) (hVc : IsCompact (closure V)) {S : Set E} (hS : IsCompact S)
    (χout χsource : E → ℂ) (ho : ContDiff ℝ ∞ χout) (hs : ContDiff ℝ ∞ χsource)
    (hco : HasCompactSupport χout) (hcs : HasCompactSupport χsource)
    (κtime : ℝ → ℝ) (hplateau : ∀ x, χout x ≠ 0 → κtime =ᶠ[𝓝 (x 0)] (fun _ ↦ 1))
    (mask : E → ℝ) (hmask : ContDiff ℝ ∞ mask) (hmaskRange : ∀ ξ, mask ξ ∈ Icc 0 1)
    (hmaskCarrier : tsupport (mask ∘ physicalCoordinates i₀) ∩ sphere (0 : E) 1 ⊆
      fullAngularCone ℓ z.2.2 (ε/4) (aperture/2))
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (χg : TC → ℝ) (heg : ∀ p ∈ closedBall (z.1,z) (4*ε), χg =ᶠ[𝓝 p] (fun _ ↦ 1))
    (χp : E × Par → ℝ) (sourcePhase : I → E → Par → ℝ)
    (Aphase Aamp : ℕ → ℝ) (Csource : ℕ → ℕ → ℝ)
    (hAphase : ∀ j, 0 ≤ Aphase j) (hAamp : ∀ j, 0 ≤ Aamp j)
    (InvBound : ℝ) (hInv : 0 ≤ InvBound) (bandLo bandHi : ℝ)
    (chart : I → OpenPartialHomeomorph TC TC) (G : I → TC → ℝ)
    (matrix : I → Fin 3 → TC → Matrix (Fin r) (Fin r) ℂ)
    (hGsolver : ∀ i p, p ∈ tsupport (matrix i 0) ∪ tsupport (matrix i 1) →
      G i =ᶠ[𝓝 p] phase ℓ (chart i))
    (hGres : ∀ i p, κtime =ᶠ[𝓝 p.1] (fun _ ↦ 1) → matrix i 2 p ≠ 0 →
      G i =ᶠ[𝓝 p] phase ℓ (chart i))
    (κ : I → (ℝ × (E × Par)) → CW)
    (η : I → ℝ → E → E → E → E) (J : I → ℝ → E → E → E → E →L[ℝ] E)
    (lam L K A₀ : I → ℝ) (hlam : ∀ i, 1 ≤ lam i) (hL : ∀ i, 1 ≤ L i)
    (hLK : ∀ i, L i ≤ K i) (hscale : ∀ i, K i ≤ lam i ^ (1-ν)) (hA₀ : ∀ i, 0 ≤ A₀ i)
    (a : I → E × Par → Fibre) (ha : ∀ i, ContDiff ℝ ∞ (a i))
    (has : ∀ i q, q.1 ∉ S → a i q = 0) (o : Fin 2) :
    let U := elapsedPhysicalBox z (ε/2)
    let X₀ := tsupport χout ∪ tsupport χsource
    let β : E → ℂ := fun ξ ↦ (dilatedConicMask mask (2*threshold) (physicalCoordinates i₀ ξ) : ℂ)
    let Dn := retainedFrequencyDomain ℓ z ε aperture (1/2)
    let O := retainedOpenAnnularFrequencyCarrier ℓ z.2.2 (ε/2) aperture g Rad
    let D := retainedOpenIntegrationDomain z ε O
    let Uc := U ×ˢ V
    let Z := Ioo (-2*τ) (2*τ) ×ˢ Uc
    let KP := closure (elapsedPhysicalBox z ε) ×ˢ closure V
    let Ksigned := fullSourceSignedCarrier z ε (closure V) O
    let aSel := a₀/(2*M)
    let bSel := 2*B₀/m
    let π : E → ℂ := fun θ ↦ annularSelector aSel bSel (by positivity) (by positivity) θ
    let Ψ := fun i ↦ SmoothRepresentative.curriedRepresentative ℓ δ hδ χg (twoTimePhase (chart i))
    let Ψactual : I → TwoTimePhase d := fun i t s y ξ ↦ G i (t,(s,(y,ξ)))
    let Wraw := fun (k : Fin 3) i ↦ curryCharacteristicMatrix (matrix i k)
    let W := fullElapsedPhysicalFactor (Wraw 0) (Wraw 1) (Wraw 2) o
    let φ := fun i c y ↦ χp (y,c) * sourcePhase i y c
    let raw := fun i ↦ fullSourceJointPhase false (curriedPhase ℓ (chart i)) (sourcePhase i)
    IsOpen O → Convex ℝ O → IsCompact (closure O) →
    (retainedAnnularFrequencyCarrier ℓ z.2.2 (ε/2) aperture
      (retainedSelectorGap z.2.2 (ε/2) aperture aSel) (2*bSel) ⊆ O) →
    S ⊆ U → X₀ ⊆ U → tsupport β ⊆ Dn → (∀ x ∈ U, ‖x‖ ≤ Rcell) →
    (∀ p ∈ KP, χp =ᶠ[𝓝 p] (fun _ ↦ 1)) →
    ∀ hprimary : ∀ i, ContDiff ℝ ∞ (fun p : E × Par ↦ φ i p.2 p.1),
    (∀ i, ContDiff ℝ ∞ (jointPhase (Ψ i))) →
    (∀ i, ContDiff ℝ ∞ (jointAmplitude (W i))) →
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
    (∀ i, ContDiffOn ℝ ∞ (raw i) (Z ×ˢ D)) →
    (∀ i, ContDiffOn ℝ ∞ (κ i) Z) →
    (∀ i p, p ∈ Z → κ i p ∈ D ∧
      gradient (fun w ↦ raw i (p,w)) (κ i p) = 0 ∧ raw i (p,κ i p) = 0) →
    (∀ i p, p ∈ Z → ∀ w ∈ closure D,
      let f := fun q w ↦ raw i ((p.1,q),w)
      IsUnit (averagedPhaseHessian f (fun q ↦ κ i (p.1,q)) p.2 w) ∧
        ‖Ring.inverse (averagedPhaseHessian f (fun q ↦ κ i (p.1,q)) p.2 w)‖ ≤ InvBound) →
    (∀ i p, p ∈ Z → ∀ w ∈ closure D, ∀ u ∈ uIcc (0:ℝ) p.1, ∀ b ∈ Icc (0:ℝ) 1,
      ((u,p.2),κ i p+b • (w-κ i p)) ∈ Ksigned) →
    (∀ i j t (v : (E × Par) × CW), ((t,v.1),v.2) ∈ Ksigned →
      ‖iteratedFDeriv ℝ j (fun q : (E × Par) × CW ↦ raw i ((t,q.1),q.2)) v‖ ≤
        Aphase j * L i ^ (j-Rstar)) →
    (∀ i t, t ∈ Icc 0 (3*src/4) → ∀ j v, v ∈ KP ×ˢ closure D →
      ‖iteratedFDeriv ℝ j (Function.uncurry (orientedAnnularAmplitude Par false
        (W i) χout χsource β π t (lam i) (-(o.val:ℤ)))) v‖ ≤ Aamp j * L i ^ (j+2-Rstar)) →
    (∀ i c, c ∈ V → ∀ l (v : Fin l → Par), (∀ j, ‖v j‖ ≤ 1) → ∀ s : ℕ,
      let f := fun y ↦ iteratedFDeriv ℝ l (fun q ↦ a i (y,q)) c v
      ∃ hm : MemLp f 2 volume, MemVectorFourierSobolev (s:ℝ) (hm.toLp f) ∧
        vectorFourierSobolevNorm (s:ℝ) (hm.toLp f) ≤ Csource l s * A₀ i * K i ^ (s+l-Rsource)) →
    ∀ s : ℕ, ∀ ps : List Par, (∀ v ∈ ps, ‖v‖ ≤ 1) →
      ∃ C ≥ 0, ∀ i c, c ∈ V →
      let output := orderedTransferAction (fun v F c ↦ fderiv ℝ F c v) ps
        (fun c ↦ annularEnvelopeIntegral (3*src/4) (Ψactual i) (W i) χout χsource β π (lam i)
          (φ i c) ((hprimary i).continuous.comp (continuous_id.prodMk continuous_const))
          (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] c))) c
      MemVectorFourierSobolev (s:ℝ) output ∧
        vectorFourierSobolevNorm (s:ℝ) output ≤
          C * lam i ^ (-(o.val:ℤ)) * A₀ i * K i ^ (s+ps.length-Rsource) := by
  intro U X₀ β Dn O D Uc Z KP Ksigned aSel bSel π Ψ Ψactual Wraw W φ raw
    hO hcO hKO hsel hSU hXU hβD hbox heP hprimary hΨ hW hwhole
    hraw hκ hstat hHess hsegments hjoint hann hfourier
  have hX : IsOpen U := isOpen_elapsedPhysicalBox _ _
  have hX₀ : IsCompact X₀ := hco.union hcs
  have hUc : IsOpen Uc := hX.prod hV
  have hP {q : E × Par} (hq : q ∈ Uc) : q ∈ KP :=
    ⟨subset_closure (UniformEvolution.closure_elapsedPhysicalBox_half_subset hε (subset_closure hq.1)),
      subset_closure hq.2⟩
  have hφ i : ContDiff ℝ ∞ (Function.uncurry (φ i)) :=
    (hprimary i).comp (contDiff_snd.prodMk contDiff_fst)
  have hsA : 0 < aSel := div_pos ha₀ (by positivity)
  have hsB : 0 < bSel := div_pos (by positivity) hm
  have hπ : ContDiff ℝ ∞ π := Complex.ofRealCLM.contDiff.comp (contDiff_annularSelector ..)
  have hcπ : HasCompactSupport π :=
    (hasCompactSupport_annularSelector aSel bSel hsA hsB).comp_left Complex.ofReal_zero
  have hβraw := EndpointPdoBounds.complex_dilatedConicMask_pdo_bounds mask hmask hmaskRange (2*threshold)
  have hβs : ContDiff ℝ ∞ β := hβraw.1.comp (physicalCoordinates i₀).contDiff
  have hxo : tsupport χout ⊆ U := subset_union_left.trans hXU
  have hxs : tsupport χsource ⊆ U := subset_union_right.trans hXU
  obtain ⟨Kcrit,hKcrit,hKD,hgeometry⟩ := exists_physical_capped_annular_integration_carrier
    (p := 3) i₀ ℓ z hε hAp hsA hsB hδ hδg hsel χout χsource hco hcs hxo hxs
  let F₀ := fun i ↦ SmoothRepresentative.retainedFrequencyCarrier δ (2*bSel) (lam i) β
  have hgeo i := hgeometry mask hmaskCarrier threshold hthreshold (lam i) (hlam i)
  obtain ⟨hD,hcD,_,_⟩ := retainedOpenIntegrationDomain_geometry z ε hO hcO hKO
  have hElapsed : Icc (0:ℝ) (3*src/4) ⊆ Ioo (-2*τ) (2*τ) := by
    intro t ht
    exact ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have hcrit i := full_source_incidence_critical_slice_for_supplied_source
    ℓ z hε hAp hg hO hcO hKO hδ hδg heg (chart i) V hV hVc (sourcePhase i) χp
    (fun q hq ↦ (heP q hq).eq_of_nhds) hElapsed (κ i) false InvBound (L i) Rstar Aphase
    (hraw i) (hκ i) (hstat i) (hHess i) (hsegments i) (hjoint i)
  have haMap i t := fullSource_annularAmplitude_jets_support false (W i) χout χsource β π
    (hW i) ho hs hβs hπ t (zero_lt_one.trans_le (hlam i)).ne' o.val
  have hphaseEq i t (ht : t ∈ Icc 0 (3*src/4)) x y ξ
      (hA : elapsedAmplitude (W i) χout χsource β t x y ξ ≠ 0) :
      elapsedPhase (Ψactual i) t x ξ = elapsedPhase (Ψ i) t x ξ := by
    by_cases h : o=0
    · apply capped_solver_phase_eq_representative_on_amplitude ℓ z hε (hsrcτ.trans hτε)
        (chart i) hδ hδhalf heg (matrix i 0) (matrix i 1) (G i) (hGsolver i) χout χsource β hxo hβD ht x y ξ
      simpa only [W,fullElapsedPhysicalFactor,ite_eq_left h,Wraw] using hA
    · apply capped_residual_phase_eq_representative_on_amplitude ℓ z hε (hsrcτ.trans hτε)
        (chart i) hδ hδhalf heg (matrix i 2) (G i) κtime (hGres i) χout χsource β hxo hplateau hβD ht x y ξ
      simpa only [W,fullElapsedPhysicalFactor,ite_eq_right h,Wraw] using hA
  refine reserved_annularEnvelopeIntegral_of_retained_primitives
    hV hX₀ hS hX hSU hXU (by positivity : 0 ≤ 3*src/4) hν hν1 hRcell hgraphGap hgrowth
    Mgraph Ggraph cgraph hcgraph hbox basis Rsource Rstar hreserve
    lam L K A₀ hlam hL hLK hscale hA₀ Ψ Ψactual W o χout χsource β π ho hs hβs hπ hcπ
    (Subset.refl X₀) φ hΨ hW hφ Aphase Aamp hAphase hAamp Dn hβD η J bandLo bandHi hwhole
    Uc D Kcrit hUc hD hcD hKcrit hKD (fun _ h ↦ ⟨hXU h.1,h.2⟩)
    InvBound (2*bSel) hInv (by positivity) (fun i t q ↦ κ i (t,q)) hcrit F₀
    (fun i ↦ ⟨(hgeo i).1,(hgeo i).2.1,(hgeo i).2.2.1⟩)
    (fun i t _ x _ θ hθ ↦ (hgeo i).2.2.2.1 χg (twoTimePhase (chart i)) t x θ hθ)
    a ha has Csource hfourier hphaseEq ?_ ?_
  · intro i t ht j v hv
    exact hann i t ht j v ⟨hP hv.1,subset_closure hv.2⟩
  · intro i t _
    have hsupp := (hgeo i).2.2.2.2 r (W i) t (-(o.val:ℤ)) false
    refine ⟨?_,?_⟩
    · intro v hv
      exact hsupp.1 ((v.1.1,v.1.2.1),v.2) (((haMap i t).2.1).le hv)
    · intro q
      exact ((haMap i t).2.2 q).le.trans (hsupp.2 (q.1,q.2.1))

end JanetCartan.FixedDomainInverse.ReservedRetardedNear
