module

public import JanetCartan.Geometry.IsometricEmbedding.Response.FullSourceEnvelopes.Assembly
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ReserveCompression
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.FiniteResidualEnvelopes.ReservedMixedJets

/-!
# The finite reserved retarded annular estimate

Apply the actual full-interval annular integral theorem at the single total
order `s + ps.length`. Only the finitely many source, phase and amplitude jets
used at that order are compressed. The original phase, physical amplitude,
cutoffs, source class and elapsed interval are unchanged.

Consumer: the selected-history reserved retarded letters in
`app:ch_response:eq:fixed-factor-transfer` and
`app:ch_response:eq:response-graded-reduced`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius SchwartzMap
namespace JanetCartan.FixedDomainInverse.ReservedRetardedNear
open ResponseTransfer ResponseTransfer.FullSourceEnvelopes ResponseTransfer.RetainedFactors
open Pseudodifferential FourierIntegral FullLowBounds LowBounds SourceExpansion
open NormalComparison FrequencyCutoff AmplitudeBound FullAmplitudePrimitiveBudget.Local
open RegularSector.Characteristic EvolutionIntegral SymbolBudgets KernelIdentification
open DirectEvolution CompactTransfer BranchAmplitudes ModifiedLow AnnularComplement AnnularSobolev
open IntegratedEnvelope IntegratedEnvelope.Parameter WholeImageGeometry FullSourceStationary
open JanetCartan.ResponseTransfer.Complement
open FiniteResidualEnvelopes
variable {d r : ℕ} {I ι : Type} [Fintype ι]
local notation "Par" => Euclidean 3 × Euclidean d
local notation "E" => Euclidean (d+1)
local notation "CW" => CarrierVariables (d+1)
local notation "Fibre" => EuclideanSpace ℂ (Fin r)
local notation "H" => SpacetimeL2 d r

/-- Actual finite-jet annular transfer preserves the original source reserve.
The retained whole-image, stationary, amplitude and support primitives are the
outputs of the selected-history producers; no near-envelope bound is a
premise. The literal phase may be replaced only by its proved supported
representative, with the SAME complete amplitude and interval.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem reserved_annularEnvelopeIntegral_of_retained_primitives
    {V : Set Par} (hV : IsOpen V) {X₀ S U : Set E}
    (hX₀ : IsCompact X₀) (hS : IsCompact S) (hU : IsOpen U)
    (hSU : S ⊆ U) (hXU : X₀ ⊆ U)
    {Δ ν Rcell graphGap growth : ℝ} (hΔ : 0 ≤ Δ)
    (hν : 0 < ν) (hν1 : ν < 1) (hRcell : 0 < Rcell)
    (hgraphGap : 0 < graphGap) (hgrowth : 0 ≤ growth)
    (Mgraph Ggraph cgraph : ℝ) (hcgraph : 1 ≤ cgraph)
    (hR : ∀ x ∈ U, ‖x‖ ≤ Rcell)
    (basis : OrthonormalBasis ι ℝ CW)
    (Rsource Rstar : ℕ) (hreserve : Rsource + fullLowReserve (d+1) + 4 ≤ Rstar)
    (lam L K A₀ : I → ℝ)
    (hlam : ∀ i, 1 ≤ lam i) (hL : ∀ i, 1 ≤ L i) (hLK : ∀ i, L i ≤ K i)
    (hscale : ∀ i, K i ≤ lam i ^ (1-ν)) (hA₀ : ∀ i, 0 ≤ A₀ i)
    (Ψ Ψactual : I → TwoTimePhase d)
    (amp : I → TwoTimeAmplitude d r) (o : Fin 2)
    (χout χsource β π : E → ℂ)
    (ho : ContDiff ℝ ∞ χout) (hs : ContDiff ℝ ∞ χsource)
    (hβ : ContDiff ℝ ∞ β) (hπ : ContDiff ℝ ∞ π) (hcπ : HasCompactSupport π)
    (hmask : tsupport χout ∪ tsupport χsource ⊆ X₀)
    (φ : I → Par → E → ℝ)
    (hΨ : ∀ i, ContDiff ℝ ∞ (jointPhase (Ψ i)))
    (hamp : ∀ i, ContDiff ℝ ∞ (jointAmplitude (amp i)))
    (hφ : ∀ i, ContDiff ℝ ∞ (Function.uncurry (φ i)))
    (Aphase Aamp : ℕ → ℝ) (hAphase : ∀ j, 0 ≤ Aphase j) (hAamp : ∀ j, 0 ≤ Aamp j)
    (Dn : Set E) (hβDn : tsupport β ⊆ Dn)
    (η : I → ℝ → E → E → E → E)
    (J : I → ℝ → E → E → E → E →L[ℝ] E)
    (bandLo bandHi : ℝ)
    (hwhole : ∀ i t, t ∈ Icc 0 Δ →
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
    (w₀ : I → ℝ → E × Par → CW)
    (hcritical : ∀ i t, t ∈ Icc 0 Δ →
      let f := elapsedCarrierPhase (Ψ i) t (fun y c ↦ φ i c y)
      ContDiffOn ℝ ∞ (Function.uncurry f) (Ucrit ×ˢ Dcrit) ∧
      ContDiffOn ℝ ∞ (w₀ i t) Ucrit ∧ MapsTo (w₀ i t) Ucrit Dcrit ∧
      (∀ q ∈ Ucrit, gradient (f q) (w₀ i t q) = 0 ∧ f q (w₀ i t q) = 0) ∧
      (∀ q ∈ Ucrit, ∀ w ∈ Dcrit, IsUnit (averagedPhaseHessian f (w₀ i t) q w) ∧
        ‖Ring.inverse (averagedPhaseHessian f (w₀ i t) q w)‖ ≤ InvBound) ∧
      ∀ j q, q ∈ Ucrit ×ˢ Dcrit →
        ‖iteratedFDeriv ℝ j (Function.uncurry f) q‖ ≤ Aphase j * L i ^ (j-Rstar))
    (F₀ : I → Set E) (hF : ∀ i, IsCompact (F₀ i) ∧ (0 : E) ∉ F₀ i ∧ F₀ i ⊆ tsupport β)
    (hΘ : ∀ i t, t ∈ Icc 0 Δ → ∀ x ∈ X₀, ∀ θ, lam i • θ ∈ F₀ i →
      elapsedPhase (Ψ i) t x (lam i • θ) = lam i * elapsedPhase (Ψ i) t x θ)
    (a : I → E × Par → Fibre) (ha : ∀ i, ContDiff ℝ ∞ (a i))
    (has : ∀ i q, q.1 ∉ S → a i q = 0) (Csource : ℕ → ℕ → ℝ)
    (hfourier : ∀ i c, c ∈ V → ∀ l (v : Fin l → Par), (∀ j, ‖v j‖ ≤ 1) → ∀ s : ℕ,
      let f := fun y ↦ iteratedFDeriv ℝ l (fun q ↦ a i (y,q)) c v
      ∃ hm : MemLp f 2 volume, MemVectorFourierSobolev (s : ℝ) (hm.toLp f) ∧
        vectorFourierSobolevNorm (s : ℝ) (hm.toLp f) ≤ Csource l s * A₀ i * K i ^ (s+l-Rsource))
    (hphaseEq : ∀ i t, t ∈ Icc 0 Δ → ∀ x y ξ,
      elapsedAmplitude (amp i) χout χsource β t x y ξ ≠ 0 →
        elapsedPhase (Ψactual i) t x ξ = elapsedPhase (Ψ i) t x ξ) :
    let α := fun i t ↦ normalizedAnnularElapsedAmplitude (P := Par)
      (amp i) χout χsource β π t (lam i) (-(o.val : ℤ))
    (∀ i t, t ∈ Icc 0 Δ → ∀ j q, q ∈ Ucrit ×ˢ Dcrit →
      ‖iteratedFDeriv ℝ j (Function.uncurry (α i t)) q‖ ≤ Aamp j * L i ^ (j+2-Rstar)) →
    (∀ i t, t ∈ Icc 0 Δ →
      (∀ v ∈ tsupport (Function.uncurry (α i t)),
        v.1.1 ∈ X₀ ∧ v.2 ∈ Kcrit ∧ v.2.fst ∈ X₀ ∧ ‖v.2.snd‖ ≤ radius ∧ lam i • v.2.snd ∈ F₀ i) ∧
      ∀ q : E × Par, Function.support (α i t q) ⊆ Kcrit) →
    ∀ s : ℕ, ∀ ps : List Par, (∀ v ∈ ps, ‖v‖ ≤ 1) →
      ∃ C ≥ 0, ∀ i c, c ∈ V →
      let output := orderedTransferAction (fun v F c ↦ fderiv ℝ F c v) ps
        (fun c ↦ annularEnvelopeIntegral Δ (Ψactual i) (amp i) χout χsource β π (lam i)
          (φ i c) ((hφ i).continuous.comp (continuous_const.prodMk continuous_id))
          (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] c))) c
      MemVectorFourierSobolev (s : ℝ) output ∧
        vectorFourierSobolevNorm (s : ℝ) output ≤
          C * lam i ^ (-(o.val : ℤ)) * A₀ i * K i ^ (s+ps.length-Rsource) := by
  intro α hαjet hsupport s ps hps
  have hK i : 1 ≤ K i := (hL i).trans (hLK i)
  let Knear := fun i ↦ reservedEnvelopeScale (K i) (s+ps.length) Rsource
  have hKnear i : 1 ≤ Knear i := one_le_reservedEnvelopeScale (hK i) (s+ps.length) Rsource
  have hKnearScale i : Knear i ≤ lam i ^ (1-ν) :=
    (reservedEnvelopeScale_le (hK i) (s+ps.length) Rsource).trans (hscale i)
  have hphaseScale i j (hj : j ≤ fullLowReserve (d+1)+(s+ps.length)+2) :
      L i ^ (j-Rstar) ≤ Knear i ^ (j-(fullLowReserve (d+1)+3)) := by
    apply (pow_le_pow_left₀ (zero_le_one.trans (hL i)) (hLK i) _).trans
    exact reserved_phase_power_le_reservedEnvelopeScale (hK i) hj hreserve
  have hampScale i j (hj : j ≤ fullLowReserve (d+1)+(s+ps.length)) :
      L i ^ (j+2-Rstar) ≤ Knear i ^ (j+2-(fullLowReserve (d+1)+3)) := by
    apply (pow_le_pow_left₀ (zero_le_one.trans (hL i)) (hLK i) _).trans
    exact reserved_symbol_power_le_reservedEnvelopeScale (hK i) (by omega) hreserve
  let a' := fun i c y ↦ a i (y,c)
  have ha' i : ContDiffOn ℝ ∞ (Function.uncurry (a' i)) (V ×ˢ univ) :=
    ((ha i).comp (contDiff_snd.prodMk contDiff_fst)).contDiffOn
  have has' i c (_hc : c ∈ V) : tsupport (a' i c) ⊆ S := by
    apply closure_minimal _ hS.isClosed
    intro y hy
    by_contra h
    exact hy (has i (y,c) h)
  obtain ⟨Dprofile,hDprofile,hmixed⟩ := exists_fullSource_reserved_mixedL2_profile
    (d+1) d r Csource Rsource
  have hdatum := hmixed I V S hS hV a' A₀ K ha' has' ha has hA₀ hK
    (by
      intro i c hc l v hv j
      obtain ⟨hm,hmem,hbound⟩ := hfourier i c hc l v hv j
      exact hmem)
    (by
      intro i c hc l v hv j
      obtain ⟨hm,hmem,hbound⟩ := hfourier i c hc l v hv j
      exact hbound)
  have hcompressed i c (hc : c ∈ V) j (hj : j ≤ s+ps.length) :
      ∃ hm : MemLp (fun y : E ↦ iteratedFDeriv ℝ j (a i) (y,c)) 2 volume,
        ‖hm.toLp (fun y : E ↦ iteratedFDeriv ℝ j (a i) (y,c))‖ ≤
          A₀ i * Dprofile j * Knear i ^ j := by
    obtain ⟨hm,hb⟩ := hdatum i c hc j
    exact ⟨hm,hb.trans (mul_le_mul_of_nonneg_left
      (reserved_power_le_reservedEnvelopeScale (hK i) hj Rsource)
      (mul_nonneg (hA₀ i) (hDprofile j)))⟩
  obtain ⟨C,hC,hnear⟩ := exists_annularEnvelopeIntegral_joint_envelope_of_primitive_jets
    (r := r) (P := Par) Rcell (4*Rcell) Mgraph Ggraph cgraph (by positivity)
    (by apply (div_lt_iff₀ (by positivity : 0 < 4*Rcell)).mpr; linarith)
    hgraphGap hgrowth hcgraph basis s ps hps Aphase Aamp hAphase hAamp hInvBound hradius
    S U hS hU hSU
  refine ⟨(Δ*C) * ∑ j ∈ Finset.range (s+ps.length+1), Dprofile j,
    mul_nonneg (mul_nonneg hΔ hC) (Finset.sum_nonneg (fun j _ ↦ hDprofile j)),?_⟩
  intro i c hc
  let Kn := X₀ ×ˢ (X₀ ×ˢ F₀ i)
  have hKn : IsClosed Kn := hX₀.isClosed.prod (hX₀.isClosed.prod (hF i).1.isClosed)
  have hKnsub : Kn ⊆ U ×ˢ (U ×ˢ Dn) :=
    fun _ h ↦ ⟨hXU h.1,hXU h.2.1,hβDn ((hF i).2.2 h.2.2)⟩
  have hnormal t ht := (hwhole i t ht).2.2.2.2.2.2.2.2.1 Kn hKn hKnsub
  have hsh t ht l := (hwhole i t ht).2.2.2.2.2.2.2.2.2 l
  have hSPhase t : ContDiff ℝ ∞ (Function.uncurry (elapsedPhase (Ψ i) t)) := by
    apply contDiff_iff_contDiffAt.mpr
    rintro ⟨x,ξ⟩
    apply contDiffAt_elapsedPhase
    apply contDiffAt_elapsedSpatialPhase
    exact ((hΨ i).comp ((contDiff_fst.fst.prodMk
      (contDiff_fst.snd.prodMk contDiff_snd.fst)).prodMk contDiff_snd.snd)).contDiffAt
  have hΨcont : Continuous (fun q : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      Ψ i q.1.1 q.1.2 q.2.1 q.2.2) :=
    ((hΨ i).comp ((contDiff_fst.fst.prodMk
      (contDiff_fst.snd.prodMk contDiff_snd.fst)).prodMk contDiff_snd.snd)).continuous
  have hampcont : Continuous (fun q : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      amp i q.1.1 q.1.2 q.2.1 q.2.2) :=
    ((hamp i).comp ((contDiff_fst.fst.prodMk
      (contDiff_fst.snd.prodMk contDiff_snd.fst)).prodMk contDiff_snd.snd)).continuous
  have hαsmooth t : ContDiff ℝ ∞ (Function.uncurry (α i t)) := by
    let e : Euclidean (3+d) ≃L[ℝ] Par := EuclideanSpace.finAddEquivProd
    let ec := ((ContinuousLinearEquiv.refl ℝ E).prodCongr e).prodCongr
      (ContinuousLinearEquiv.refl ℝ CW)
    have h := (contDiff_orientedAnnularAmplitude (3+d) false (amp i) χout χsource β π
      (hamp i) ho hs hβ hπ t (zero_lt_one.trans_le (hlam i)).ne' o.val).comp ec.symm.contDiff
    convert h using 1
    funext q
    rfl
  have hbox y (hy : y ∈ X₀) j : |y j| ≤ Rcell :=
    by simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le y j).trans (hR y (hXU hy))
  have hsC t ht q (hq : q ∈ tsupport (Function.uncurry (α i t))) :=
    (hsupport i t ht).1 q hq
  have hslice t (ht : t ∈ Icc 0 Δ) c (hc : c ∈ V) q
      (hq : normalizedSlice c q ∈ tsupport (Function.uncurry (α i t))) :
      normalizedSlice c q ∈ Ucrit ×ˢ Dcrit :=
    ⟨hXUc ⟨(hsC t ht _ hq).1,hc⟩,hKD (hsC t ht _ hq).2.1⟩
  have hφsource c : ContDiff ℝ ∞ (φ i c) := (hφ i).comp (contDiff_const.prodMk contDiff_id)
  have hocs : HasCompactSupport χout := hX₀.of_isClosed_subset (isClosed_tsupport _)
    (subset_union_left.trans hmask)
  have hscs : HasCompactSupport χsource := hX₀.of_isClosed_subset (isClosed_tsupport _)
    (subset_union_right.trans hmask)
  have hb := hnear X₀ X₀ (F₀ i) hX₀ hbox (hF i).1.isClosed (hF i).2.1 (Ψ i) Δ hΔ
    (fun t _ ↦ hSPhase t)
    (K := fun _ ↦ Kn)
    (fun t ht ↦ (hwhole i t ht).1)
    (fun t ht ↦ (hwhole i t ht).2.1)
    (fun t ht ↦ (hwhole i t ht).2.2.1)
    (fun t ht ↦ (hwhole i t ht).2.2.2.1)
    (fun t ht ↦ (hwhole i t ht).2.2.2.2.1)
    (fun t ht q hq ↦ abs_pos.mp (hgraphGap.trans_le ((hwhole i t ht).2.2.2.2.2.1 q hq)))
    (fun t ht ↦ (hwhole i t ht).2.2.2.2.2.2.1)
    (fun _ _ _ _ hx hy hξ ↦ ⟨hx,hy,hξ⟩)
    (fun t ht ↦ (hnormal t ht).1) (fun t ht ↦ (hnormal t ht).2)
    (fun _ _ ↦ hR) (fun t ht ↦ (hwhole i t ht).2.2.2.2.2.2.2.1)
    (fun _ l ↦ U ×ˢ (U ×ˢ normalizedSourceBand Dn ((2:ℝ)^l) bandLo bandHi))
    (fun t ht l ↦ (hsh t ht l).1) (fun t ht l ↦ (hsh t ht l).2.1)
    (fun t ht l ↦ (hsh t ht l).2.2.1) (fun t ht l ↦ (hsh t ht l).2.2.2.1)
    (fun t ht l ↦ (hsh t ht l).2.2.2.2.1) (fun t ht l ↦ (hsh t ht l).2.2.2.2.2.1)
    (fun t ht l ↦ (hsh t ht l).2.2.2.2.2.2.1)
    (fun t ht l ↦ (hsh t ht l).2.2.2.2.2.2.2.1)
    (fun t ht l ↦ (hsh t ht l).2.2.2.2.2.2.2.2)
    (fun _ _ ↦ hXU) (fun _ _ ↦ (hF i).2.2.trans hβDn)
    (fullLowReserve (d+1)+3) (by omega) (Knear i) (lam i) (hKnear i) (hlam i) (-(o.val : ℤ))
    (fun y c ↦ φ i c y) (w₀ i) (amp i) χout χsource β π
    (fun _ ↦ Ucrit) (fun _ ↦ Dcrit) (fun _ _ ↦ hUc) (fun _ _ ↦ hDc) (fun _ _ ↦ hcD)
    (fun t ht ↦ (hcritical i t ht).1)
    (fun t ht ↦ (hcritical i t ht).2.1)
    (fun t ht ↦ (hcritical i t ht).2.2.1)
    (fun t ht q hq ↦ ((hcritical i t ht).2.2.2.1 q hq).1)
    (fun t ht q hq ↦ ((hcritical i t ht).2.2.2.1 q hq).2)
    (fun t ht q hq w hw ↦ ((hcritical i t ht).2.2.2.2.1 q hq w hw).1)
    (fun t ht q hq w hw ↦ ((hcritical i t ht).2.2.2.2.1 q hq w hw).2)
    (fun t ht j hj q hq ↦ ((hcritical i t ht).2.2.2.2.2 j q hq).trans
      (mul_le_mul_of_nonneg_left (hphaseScale i j hj) (hAphase j)))
    (fun t _ ↦ (hαsmooth t).contDiffOn)
    (fun t ht j hj q hq ↦ (hαjet i t ht j q hq).trans
      (mul_le_mul_of_nonneg_left (hampScale i j hj) (hAamp j)))
    (fun _ ↦ Kcrit) (fun _ _ ↦ hKcrit) (fun _ _ ↦ hKD)
    (fun t ht q _ ↦ (hsupport i t ht).2 q)
    (fun t ht q hq ↦ (hsC t ht q hq).1) V hV (fun _ _ ↦ hXUc)
    (fun c ↦ (hφsource c).continuous) hslice
    (fun t ht c _ q hq ↦ (hsC t ht _ hq).2.2.2.1)
    (fun t ht c _ q hq ↦ ⟨(hsC t ht _ hq).1,(hsC t ht _ hq).2.2.1,(hsC t ht _ hq).2.2.2.2⟩)
    (hΘ i) (fun c _ ↦ (hφsource c).contDiffOn)
    hΨcont hampcont ho.continuous hs.continuous hβ.continuous hπ.continuous hocs hscs hcπ
    (a i) (ha i) (has i) c hc
    (fun j ↦ A₀ i * Dprofile j * Knear i ^ j)
    (fun j ↦ mul_nonneg (mul_nonneg (hA₀ i) (hDprofile j)) (pow_nonneg (zero_le_one.trans (hKnear i)) _))
    (hcompressed i c hc)
  have hp := hb.2.2.2.2 (Knear i) ν (A₀ i) Dprofile le_rfl (hKnearScale i) hν hν1
    (fun _ _ ↦ le_rfl)
  have hnorm := hp.2
  rw [vectorFourierSobolevScale_gradeNorm s hp.1,
    reservedEnvelopeScale_pow_top (hK i) (s+ps.length) Rsource] at hnorm
  have heq : (fun c ↦ annularEnvelopeIntegral Δ (Ψactual i) (amp i) χout χsource β π (lam i)
      (φ i c) ((hφ i).continuous.comp (continuous_const.prodMk continuous_id))
      (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] c))) =
      fun c ↦ annularEnvelopeIntegral Δ (Ψ i) (amp i) χout χsource β π (lam i)
        (φ i c) ((hφ i).continuous.comp (continuous_const.prodMk continuous_id))
        (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] c)) := by
    funext c
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    have hg : fullGraphOperator (elapsedPhase (Ψactual i) t)
        (annularElapsedAmplitude (amp i) χout χsource β π t (lam i)) =
        fullGraphOperator (elapsedPhase (Ψ i) t)
          (annularElapsedAmplitude (amp i) χout χsource β π t (lam i)) := by
      apply fullGraphOperator_phase_congr
      intro x y ξ hne
      apply hphaseEq i t ht x y ξ
      intro hz
      exact hne (by simp only [annularElapsedAmplitude,frequencyCutFullAmplitude,hz,smul_zero])
    simp only [annularEnvelopeOperator,hg]
  dsimp only
  rw [heq]
  exact ⟨hp.1,hnorm⟩

end JanetCartan.FixedDomainInverse.ReservedRetardedNear
