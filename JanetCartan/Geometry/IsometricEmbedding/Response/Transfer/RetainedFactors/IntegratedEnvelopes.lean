module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.CappedGraphFamily
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.AdjointAmplitudeJets
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.JointPhaseJets
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.SourceMixedJets
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.IntegratedEnvelope.Assembly

/-!
# Apply both integrated envelopes to retained primitive data

This is the application layer between `CappedConstruction` and the complete
fixed-response chains. Its inputs are the original retained phase and amplitude
jets, the constructed whole-image geometry, and the same graph regularizations.
Both orientations use the complete interval `[0,3*src/4]`. The mixed L2 jet
is derived by `SourceMixedJets` from the original parameter Fourier-Sobolev
profiles, with no extra source premise. No envelope or modified-operator
estimate is an input. Sources: `app:ch_response:eq:direct-envelope-profile` and
`app:ch_response:eq:fixed-factor-transfer`.

The supported-phase endpoint also applies these estimates to the original
cancellation extension. Only the controlled representative has quantitative
phase profiles. Equality on the nonzero full amplitude identifies the entire
physical operators and their literal adjoints, so no bounds on an arbitrary
off-support extension enter the envelope constants.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4800000
set_option maxRecDepth 4096
open Set Metric Filter MeasureTheory LineDeriv
open scoped ContDiff Topology Matrix.Norms.Frobenius SchwartzMap
namespace JanetCartan.ResponseTransfer.RetainedFactors
open Pseudodifferential FourierIntegral FullLowBounds LowBounds SourceExpansion
open NormalComparison FrequencyCutoff AmplitudeBound FullAmplitudePrimitiveBudget.Local
open RegularSector.Characteristic EvolutionIntegral SymbolBudgets KernelIdentification
open DirectEvolution CompactTransfer BranchAmplitudes ModifiedLow AnnularComplement AnnularSobolev
open IntegratedEnvelope IntegratedEnvelope.Parameter
open JanetCartan.ResponseTransfer.Complement JanetCartan.ResponseTransfer.Complement.ParameterDerivatives
open WholeImageGeometry
variable {d r : ℕ} {I ι : Type} [Fintype ι]
local notation "Par" => Euclidean 3
local notation "E" => Euclidean (d + 1)
local notation "CW" => CarrierVariables (d + 1)
local notation "F" => EuclideanSpace ℂ (Fin r)
local notation "H" => SpacetimeL2 d r

/-- Both full elapsed envelopes from the exact retained constructor outputs.
The full-frequency phase grade `L^(j-1)` supplies the tail derivative budgets;
the annular jets and critical data supply derivative transfer. The input
signatures match the exported `CappedConstruction` data. `CappedEnvelopes`
instantiates them on the original solver and complete residual history family;
the finite fixed inverse must still retain that family. `SourceMixedJets` discharges the
quantitative mixed L2 input from the original source profiles, for both literal
orientations (`app:ch_response:eq:fixed-factor-transfer`). -/
theorem retained_fullElapsed_envelopes_of_source_profiles
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
    (Rstar o : ℕ) (hRstar : fullLowReserve (d + 1) + 2 < Rstar)
    (lam L K A₀ : I → ℝ)
    (hlam : ∀ i, 1 ≤ lam i) (hL : ∀ i, 1 ≤ L i) (hLK : ∀ i, L i ≤ K i)
    (hscale : ∀ i, K i ≤ lam i ^ (1 - ν)) (hA₀ : ∀ i, 0 ≤ A₀ i)
    (Ψ : I → TwoTimePhase d) (W : I → TwoTimeAmplitude d r)
    (χout χsource β : E → ℂ)
    (ho : ContDiff ℝ ∞ χout) (hs : ContDiff ℝ ∞ χsource) (hβ : ContDiff ℝ ∞ β)
    (hmask : tsupport χout ∪ tsupport χsource ⊆ X₀)
    (Mβ : ℝ) (hMβ : 0 ≤ Mβ) (hβbound : ∀ ξ, ‖β ξ‖ ≤ Mβ)
    (φ : I → Par → E → ℝ)
    (hΨ : ∀ i, ContDiff ℝ ∞ (jointPhase (Ψ i)))
    (hW : ∀ i, ContDiff ℝ ∞ (jointAmplitude (W i)))
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
      ‖iteratedFDeriv ℝ j (jointAmplitude (W i)) (elapsedPoint t ((y, 0), ξ))‖ ≤ Bamp j * L i ^ j)
    (hgradient : ∀ i c, c ∈ V → ∀ y ∈ U,
      a₀ ≤ ‖fderiv ℝ (φ i c) y‖ ∧ ‖fderiv ℝ (φ i c) y‖ ≤ B₀)
    (hradial : ∀ i t, t ∈ Icc 0 (3 * src / 4) → ∀ ξ ∈ tsupport β, ∀ y ∈ U,
      m * ‖ξ‖ ≤ ‖fderiv ℝ (fun x ↦ elapsedPhase (Ψ i) t x ξ) y‖ ∧
        ‖fderiv ℝ (fun x ↦ elapsedPhase (Ψ i) t x ξ) y‖ ≤ M * ‖ξ‖)
    (Creg : I → ℝ)
    (hgraphs : ∀ i, CappedGraphRealizations (3 * src / 4) (Ψ i) (W i) χout χsource β (Creg i))
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
      let f := fun q w ↦ jointRetainedCarrierPhase adj (Ψ i) (fun x c ↦ φ i c x) ((t,q),w)
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
        ((parameterSource_memLp hS hV (ha i) (has i) l w hc).toLp
          (fun y ↦ iteratedFDeriv ℝ l (fun q ↦ a i q y) c w)))
    (hsob : ∀ i c (hc : c ∈ V) l (w : Fin l → Par), (∀ j, ‖w j‖ ≤ 1) → ∀ s : ℕ,
      vectorFourierSobolevNorm (s : ℝ)
        ((parameterSource_memLp hS hV (ha i) (has i) l w hc).toLp
          (fun y ↦ iteratedFDeriv ℝ l (fun q ↦ a i q y) c w)) ≤ C l s * A₀ i * K i ^ (s + l)) :
    let π : E → ℂ := fun θ ↦ annularSelector (a₀ / (2 * M)) (2 * B₀ / m) (by positivity) (by positivity) θ
    let α := fun i (adj : Bool) t ↦ if adj then normalizedAdjointAnnularElapsedAmplitude (P := Par)
      (W i) χout χsource β π t (lam i) (-(o : ℤ)) else
        normalizedAnnularElapsedAmplitude (P := Par) (W i) χout χsource β π t (lam i) (-(o : ℤ))
    (∀ i adj t, t ∈ Icc 0 (3 * src / 4) → ∀ j q, q ∈ Ucrit ×ˢ Dcrit →
      ‖iteratedFDeriv ℝ j (Function.uncurry (α i adj t)) q‖ ≤ Aamp j * L i ^ (j + 2 - Rstar)) →
    (∀ i adj t, t ∈ Icc 0 (3 * src / 4) →
      (∀ v ∈ tsupport (Function.uncurry (α i adj t)),
        v.1.1 ∈ X₀ ∧ v.2 ∈ Kcrit ∧ v.2.fst ∈ X₀ ∧ ‖v.2.snd‖ ≤ radius ∧ lam i • v.2.snd ∈ F₀ i) ∧
      ∀ q : E × Par, Function.support (α i adj t q) ⊆ Kcrit) →
    ∀ adj : Bool, ∀ ps : List Par, (∀ v ∈ ps, ‖v‖ ≤ 1) →
    HasEnvelopeProfile (vectorFourierSobolevScale (d := d + 1) (I := Fin r))
      (fun z : I × V ↦ orderedTransferAction (fun v g c ↦ fderiv ℝ g c v) ps
        (fun c ↦ carrierMultiplication (-(lam z.1)) (φ z.1 c) ((hφ z.1).continuous.comp (continuous_const.prodMk continuous_id))
          ((if adj then fun u ↦ ∫ t in Icc 0 (3 * src / 4), (elapsedGraph (Ψ z.1) (W z.1) χout χsource β t).adjoint u
            else elapsedGraphIntegral (3 * src / 4) (Ψ z.1) (W z.1) χout χsource β)
            (carrierMultiplication (lam z.1) (φ z.1 c) ((hφ z.1).continuous.comp (continuous_const.prodMk continuous_id))
              (graphTestToLp (vectorOriginalDatumTest (fun q : E × Par ↦ a z.1 q.2 q.1)
                (haJoint z.1) hS (haGlobal z.1) [] c))))) z.2)
      (fun z ↦ lam z.1 ^ (-(o : ℤ)) * A₀ z.1 * K z.1 ^ ps.length) (fun z ↦ K z.1) := by
  classical
  intro π α hαjet hsupport adj ps hps
  obtain ⟨Dprofile, hDprofile, hmixed⟩ :=
    SourceMixedJets.exists_sourceMixedJet_profile (d + 1) r C
  have hDatum := hmixed I V S hS hV a A₀ K ha has haJoint haGlobal hA₀
    (fun i ↦ (hL i).trans (hLK i)) hmem hsob
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
  have hBφ i j c hc y hy := (hprimaryJets i j c hc y (hSX hy)).1.trans
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
  have hαsmooth i adj t : ContDiff ℝ ∞ (Function.uncurry (α i adj t)) := by
    cases adj
    · exact contDiff_normalizedAnnularElapsedAmplitude (W i) χout χsource β π (hW i)
        ho hs hβ hπ t (zero_lt_one.trans_le (hlam i)).ne' o
    · let Jc : Matrix (Fin r) (Fin r) ℂ ≃ₗᵢ[ℝ] Matrix (Fin r) (Fin r) ℂ := {
        Matrix.conjTransposeLinearEquiv (Fin r) (Fin r) ℝ ℂ with
        norm_map' := Matrix.frobenius_norm_conjTranspose }
      have he : Function.uncurry (α i true t) =
          Jc ∘ (Function.uncurry (α i false t) ∘ annularCarrierSwap) := by
        funext w
        change _ = ((lam i ^ (-(o : ℤ)))⁻¹ •
          annularElapsedAmplitude (W i) χout χsource β π t (lam i)
            w.2.fst w.1.1 (lam i • w.2.snd)).conjTranspose
        simp only [α, ↓reduceIte, normalizedAdjointAnnularElapsedAmplitude, Function.uncurry,
          Matrix.conjTranspose_smul, star_trivial]
      rw [he]
      exact Jc.contDiff.comp ((contDiff_normalizedAnnularElapsedAmplitude
        (W i) χout χsource β π (hW i) ho hs hβ hπ t
        (zero_lt_one.trans_le (hlam i)).ne' o).comp annularCarrierSwap.contDiff)
  have hslice i adj t ht c hc q (hq : normalizedSlice c q ∈ tsupport (Function.uncurry (α i adj t))) :
      normalizedSlice c q ∈ Ucrit ×ˢ Dcrit :=
    ⟨hXUc ⟨((hsupport i adj t ht).1 _ hq).1, hc⟩,
      hKD ((hsupport i adj t ht).1 _ hq).2.1⟩
  have hφsource i c : ContDiff ℝ ∞ (φ i c) := (hφ i).comp (contDiff_const.prodMk contDiff_id)
  have hbox y (hy : y ∈ X₀) j : |y j| ≤ Rcell :=
    by simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le y j).trans (hR y (hXU hy))
  have hnormal i t ht := (hwhole i t ht).2.2.2.2.2.2.2.2.1 (Kn i) (hKn i) (hKnsub i)
  have hsh i t ht l := (hwhole i t ht).2.2.2.2.2.2.2.2.2 l
  cases adj
  · exact Assembly.fullElapsedEnvelope_hasEnvelopeProfile_of_primitive_jets
      hV hX₀ hS hU hU hSU hXU hΔ hν hν1 ha₀ hB₀ hm hm1 hM
      (fun k ↦ Bprimary (k + 1)) (fun k ↦ Bphase (k + 1)) Bphase Bprimary Omask Tmask Bamp C Mβ
      (fun k ↦ hBprimary (k + 1)) (fun k ↦ hBphase (k + 1)) hBphase hBprimary hO hT hBamp hMβ
      lam L K A₀ hlam hL hLK hscale hA₀ Ψ W (fun _ ↦ χout) (fun _ ↦ χsource) (fun _ ↦ β) φ a
      ha has (fun _ ↦ hmask) (fun _ ↦ ho) (fun _ ↦ hs) (fun _ ↦ hβ) (fun _ ↦ hβbound)
      (fun _ ↦ univ) (fun _ ↦ univ) (fun _ ↦ isOpen_univ) (fun _ ↦ isOpen_univ)
      (fun i ↦ (hΨ i).contDiffOn) hW (by intros; trivial) (by intros; trivial)
      (fun i ↦ (hφ i).contDiffOn) hBΨ hBφ
      (fun i t ht ξ hξ j y hy ↦ hamplitudeJets i t ht ξ (subset_tsupport _ hξ) j y (hSX hy))
      (fun _ ↦ hout) (fun _ ↦ hsource) hmem hsob hgradient
      (fun i t ht ξ hξ y hy ↦ hradial i t ht ξ (subset_tsupport _ hξ) y hy) hPφ hPΨ
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
      Rstar hRstar (-(o : ℤ)) (fun i ↦ w₀ i false) (fun _ _ ↦ Ucrit) (fun _ _ ↦ Dcrit)
      (fun _ _ _ ↦ hUc) (fun _ _ _ ↦ hDc) (fun _ _ _ ↦ hcD)
      (fun i t ht ↦ (hcritical i false t ht).1)
      (fun i t ht ↦ (hcritical i false t ht).2.1)
      (fun i t ht ↦ (hcritical i false t ht).2.2.1)
      (fun i t ht q hq ↦ ((hcritical i false t ht).2.2.2.1 q hq).1)
      (fun i t ht q hq ↦ ((hcritical i false t ht).2.2.2.1 q hq).2)
      (fun i t ht q hq w hw ↦ ((hcritical i false t ht).2.2.2.2.1 q hq w hw).1)
      (fun i t ht q hq w hw ↦ ((hcritical i false t ht).2.2.2.2.1 q hq w hw).2)
      (fun i t ht ↦ (hcritical i false t ht).2.2.2.2.2)
      (fun _ _ ↦ Kcrit) (fun _ _ _ ↦ hKcrit) (fun _ _ _ ↦ hKD) (fun _ _ _ ↦ hXUc)
      (fun i c ↦ (hφsource i c).continuous) (fun i c _ ↦ (hφsource i c).contDiffOn)
      hΨcont haJoint haGlobal hDatum hΘ
      (fun i t _ ↦ (hαsmooth i false t).contDiffOn) (fun i t ht ↦ hαjet i false t ht)
      (fun i t ht q _ ↦ (hsupport i false t ht).2 q)
      (fun i t ht v hv ↦ ((hsupport i false t ht).1 v hv).1)
      (fun i t ht ↦ hslice i false t ht)
      (fun i t ht _ _ q hq ↦ ((hsupport i false t ht).1 _ hq).2.2.2.1)
      (fun i t ht _ _ q hq ↦ ⟨((hsupport i false t ht).1 _ hq).1, ((hsupport i false t ht).1 _ hq).2.2.1, ((hsupport i false t ht).1 _ hq).2.2.2.2⟩)
      ps hps
  · exact Assembly.fullElapsedAdjointEnvelope_hasEnvelopeProfile_of_primitive_jets
      hV hX₀ hS hU hU hSU hXU hΔ hν hν1 ha₀ hB₀ hm hm1 hM
      (fun k ↦ Bprimary (k + 1)) (fun k ↦ Bphase (k + 1)) Bphase Bprimary Omask Tmask Bamp C Mβ
      (fun k ↦ hBprimary (k + 1)) (fun k ↦ hBphase (k + 1)) hBphase hBprimary hO hT hBamp hMβ
      lam L K A₀ hlam hL hLK hscale hA₀ Ψ W (fun _ ↦ χout) (fun _ ↦ χsource) (fun _ ↦ β) φ a
      ha has (fun _ ↦ hmask) (fun _ ↦ ho) (fun _ ↦ hs) (fun _ ↦ hβ) (fun _ ↦ hβbound)
      (fun _ ↦ univ) (fun _ ↦ univ) (fun _ ↦ isOpen_univ) (fun _ ↦ isOpen_univ)
      (fun i ↦ (hΨ i).contDiffOn) hW (by intros; trivial) (by intros; trivial)
      (fun i ↦ (hφ i).contDiffOn) hBΨ hBφ
      (fun i t ht ξ hξ j y hy ↦ hamplitudeJets i t ht ξ (subset_tsupport _ hξ) j y (hSX hy))
      (fun _ ↦ hout) (fun _ ↦ hsource) hmem hsob hgradient
      (fun i t ht ξ hξ y hy ↦ hradial i t ht ξ (subset_tsupport _ hξ) y hy) hPφ hPΨ
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
      Rstar hRstar (-(o : ℤ)) (fun i ↦ w₀ i true) (fun _ _ ↦ Ucrit) (fun _ _ ↦ Dcrit)
      (fun _ _ _ ↦ hUc) (fun _ _ _ ↦ hDc) (fun _ _ _ ↦ hcD)
      (fun i t ht ↦ (hcritical i true t ht).1)
      (fun i t ht ↦ (hcritical i true t ht).2.1)
      (fun i t ht ↦ (hcritical i true t ht).2.2.1)
      (fun i t ht q hq ↦ ((hcritical i true t ht).2.2.2.1 q hq).1)
      (fun i t ht q hq ↦ ((hcritical i true t ht).2.2.2.1 q hq).2)
      (fun i t ht q hq w hw ↦ ((hcritical i true t ht).2.2.2.2.1 q hq w hw).1)
      (fun i t ht q hq w hw ↦ ((hcritical i true t ht).2.2.2.2.1 q hq w hw).2)
      (fun i t ht ↦ (hcritical i true t ht).2.2.2.2.2)
      (fun _ _ ↦ Kcrit) (fun _ _ _ ↦ hKcrit) (fun _ _ _ ↦ hKD) (fun _ _ _ ↦ hXUc)
      (fun i c ↦ (hφsource i c).continuous) (fun i c _ ↦ (hφsource i c).contDiffOn)
      hΨcont haJoint haGlobal hDatum hΘ
      (fun i t _ ↦ (hαsmooth i true t).contDiffOn) (fun i t ht ↦ hαjet i true t ht)
      (fun i t ht q _ ↦ (hsupport i true t ht).2 q)
      (fun i t ht v hv ↦ ((hsupport i true t ht).1 v hv).1)
      (fun i t ht ↦ hslice i true t ht)
      (fun i t ht _ _ q hq ↦ ((hsupport i true t ht).1 _ hq).2.2.2.1)
      (fun i t ht _ _ q hq ↦ ⟨((hsupport i true t ht).1 _ hq).2.2.1, ((hsupport i true t ht).1 _ hq).1, ((hsupport i true t ht).1 _ hq).2.2.2.2⟩)
      ps hps

/-- Both envelopes for the ORIGINAL full elapsed operators whose supported
phase agrees with the controlled representative. Every phase derivative,
normal-image estimate and stationary-map bound is imposed only on `Ψ`.
The selected cancellation extension `Ψactual` needs no global jet profile.

`capped_solver_phase_eq_representative_on_amplitude` and
`capped_residual_phase_eq_representative_on_amplitude` prove `hphaseEq` from
the original supported cancellation germs and the once-capped geometry.
Exact equality of the full operators, their literal adjoints and the entire
parameter functions transports all derivative words with precisely the old
constants, `lam^(-o)` and `K^|ps|`. No envelope bound or operator identification
is taken as a hypothesis, and `[0,3*src/4]` is unchanged.
Sources: `app:ch_response:eq:fixed-factor-transfer` and
`paper-v2.tex`, `app:ch_response:lem:energy-carrier-jets`. -/
theorem retained_fullElapsed_envelopes_of_supported_phase
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
    (Rstar o : ℕ) (hRstar : fullLowReserve (d + 1) + 2 < Rstar)
    (lam L K A₀ : I → ℝ)
    (hlam : ∀ i, 1 ≤ lam i) (hL : ∀ i, 1 ≤ L i) (hLK : ∀ i, L i ≤ K i)
    (hscale : ∀ i, K i ≤ lam i ^ (1 - ν)) (hA₀ : ∀ i, 0 ≤ A₀ i)
    (Ψ Ψactual : I → TwoTimePhase d) (W : I → TwoTimeAmplitude d r)
    (χout χsource β : E → ℂ)
    (ho : ContDiff ℝ ∞ χout) (hs : ContDiff ℝ ∞ χsource) (hβ : ContDiff ℝ ∞ β)
    (hmask : tsupport χout ∪ tsupport χsource ⊆ X₀)
    (hphaseEq : ∀ i t, t ∈ Icc 0 (3 * src / 4) → ∀ x y ξ,
      elapsedAmplitude (W i) χout χsource β t x y ξ ≠ 0 →
      elapsedPhase (Ψactual i) t x ξ = elapsedPhase (Ψ i) t x ξ)
    (Mβ : ℝ) (hMβ : 0 ≤ Mβ) (hβbound : ∀ ξ, ‖β ξ‖ ≤ Mβ)
    (φ : I → Par → E → ℝ)
    (hΨ : ∀ i, ContDiff ℝ ∞ (jointPhase (Ψ i)))
    (hW : ∀ i, ContDiff ℝ ∞ (jointAmplitude (W i)))
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
      ‖iteratedFDeriv ℝ j (jointAmplitude (W i)) (elapsedPoint t ((y, 0), ξ))‖ ≤ Bamp j * L i ^ j)
    (hgradient : ∀ i c, c ∈ V → ∀ y ∈ U,
      a₀ ≤ ‖fderiv ℝ (φ i c) y‖ ∧ ‖fderiv ℝ (φ i c) y‖ ≤ B₀)
    (hradial : ∀ i t, t ∈ Icc 0 (3 * src / 4) → ∀ ξ ∈ tsupport β, ∀ y ∈ U,
      m * ‖ξ‖ ≤ ‖fderiv ℝ (fun x ↦ elapsedPhase (Ψ i) t x ξ) y‖ ∧
        ‖fderiv ℝ (fun x ↦ elapsedPhase (Ψ i) t x ξ) y‖ ≤ M * ‖ξ‖)
    (Creg : I → ℝ)
    (hgraphs : ∀ i, CappedGraphRealizations (3 * src / 4) (Ψ i) (W i) χout χsource β (Creg i))
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
      let f := fun q w ↦ jointRetainedCarrierPhase adj (Ψ i) (fun x c ↦ φ i c x) ((t,q),w)
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
        ((parameterSource_memLp hS hV (ha i) (has i) l w hc).toLp
          (fun y ↦ iteratedFDeriv ℝ l (fun q ↦ a i q y) c w)))
    (hsob : ∀ i c (hc : c ∈ V) l (w : Fin l → Par), (∀ j, ‖w j‖ ≤ 1) → ∀ s : ℕ,
      vectorFourierSobolevNorm (s : ℝ)
        ((parameterSource_memLp hS hV (ha i) (has i) l w hc).toLp
          (fun y ↦ iteratedFDeriv ℝ l (fun q ↦ a i q y) c w)) ≤ C l s * A₀ i * K i ^ (s + l)) :
    let π : E → ℂ := fun θ ↦ annularSelector (a₀ / (2 * M)) (2 * B₀ / m) (by positivity) (by positivity) θ
    let α := fun i (adj : Bool) t ↦ if adj then normalizedAdjointAnnularElapsedAmplitude (P := Par)
      (W i) χout χsource β π t (lam i) (-(o : ℤ)) else
        normalizedAnnularElapsedAmplitude (P := Par) (W i) χout χsource β π t (lam i) (-(o : ℤ))
    (∀ i adj t, t ∈ Icc 0 (3 * src / 4) → ∀ j q, q ∈ Ucrit ×ˢ Dcrit →
      ‖iteratedFDeriv ℝ j (Function.uncurry (α i adj t)) q‖ ≤ Aamp j * L i ^ (j + 2 - Rstar)) →
    (∀ i adj t, t ∈ Icc 0 (3 * src / 4) →
      (∀ v ∈ tsupport (Function.uncurry (α i adj t)),
        v.1.1 ∈ X₀ ∧ v.2 ∈ Kcrit ∧ v.2.fst ∈ X₀ ∧ ‖v.2.snd‖ ≤ radius ∧ lam i • v.2.snd ∈ F₀ i) ∧
      ∀ q : E × Par, Function.support (α i adj t q) ⊆ Kcrit) →
    ∀ adj : Bool, ∀ ps : List Par, (∀ v ∈ ps, ‖v‖ ≤ 1) →
    HasEnvelopeProfile (vectorFourierSobolevScale (d := d + 1) (I := Fin r))
      (fun z : I × V ↦ orderedTransferAction (fun v g c ↦ fderiv ℝ g c v) ps
        (fun c ↦ carrierMultiplication (-(lam z.1)) (φ z.1 c) ((hφ z.1).continuous.comp (continuous_const.prodMk continuous_id))
          ((if adj then fun u ↦ ∫ t in Icc 0 (3 * src / 4), (elapsedGraph (Ψactual z.1) (W z.1) χout χsource β t).adjoint u
            else elapsedGraphIntegral (3 * src / 4) (Ψactual z.1) (W z.1) χout χsource β)
            (carrierMultiplication (lam z.1) (φ z.1 c) ((hφ z.1).continuous.comp (continuous_const.prodMk continuous_id))
              (graphTestToLp (vectorOriginalDatumTest (fun q : E × Par ↦ a z.1 q.2 q.1)
                (haJoint z.1) hS (haGlobal z.1) [] c))))) z.2)
      (fun z ↦ lam z.1 ^ (-(o : ℤ)) * A₀ z.1 * K z.1 ^ ps.length) (fun z ↦ K z.1) := by
  intro π α hαjet hsupport adj ps hps
  have hprofile := retained_fullElapsed_envelopes_of_source_profiles
    hV hX₀ hS hU hSU hXU hsrc hν hν1 ha₀ hB₀ hm hm1 hM hRcell hgraphGap hgrowth
    Mgraph Ggraph cgraph hcgraph hR basis Rstar o hRstar lam L K A₀ hlam hL hLK hscale hA₀
    Ψ W χout χsource β ho hs hβ hmask Mβ hMβ hβbound φ hΨ hW hφ
    Bphase Bprimary Bamp Aphase Aamp hBphase hBprimary hBamp hAphase hAamp
    hphaseJets hprimaryJets hamplitudeJets hgradient hradial Creg hgraphs Dn hβDn
    η J bandLo bandHi hwhole Ucrit Dcrit Kcrit hUc hDc hcD hKcrit hKD hXUc
    InvBound radius hInvBound hradius w₀ hcritical F₀ hF hΘ a haJoint haGlobal ha has
    C hmem hsob hαjet hsupport adj ps hps
  have hgraph i t (ht : t ∈ Icc 0 (3 * src / 4)) :
      elapsedGraph (Ψactual i) (W i) χout χsource β t =
        elapsedGraph (Ψ i) (W i) χout χsource β t :=
    fullGraphOperator_phase_congr _ _ _ (hphaseEq i t ht)
  have haction i (u : H) :
      (if adj then fun u ↦ ∫ t in Icc 0 (3 * src / 4),
          (elapsedGraph (Ψactual i) (W i) χout χsource β t).adjoint u
        else elapsedGraphIntegral (3 * src / 4) (Ψactual i) (W i) χout χsource β) u =
      (if adj then fun u ↦ ∫ t in Icc 0 (3 * src / 4),
          (elapsedGraph (Ψ i) (W i) χout χsource β t).adjoint u
        else elapsedGraphIntegral (3 * src / 4) (Ψ i) (W i) χout χsource β) u := by
    cases adj <;> apply setIntegral_congr_fun measurableSet_Icc <;>
      intro t ht <;> dsimp only <;> rw [hgraph i t ht]
  apply (hasEnvelopeProfile_congr ?_).2 hprofile
  intro z
  apply congrArg (fun g : Par → H ↦
    orderedTransferAction (fun v g c ↦ fderiv ℝ g c v) ps g z.2)
  funext c
  apply congrArg (carrierMultiplication (-(lam z.1)) (φ z.1 c)
    ((hφ z.1).continuous.comp (continuous_const.prodMk continuous_id)))
  exact haction z.1 _

end JanetCartan.ResponseTransfer.RetainedFactors
