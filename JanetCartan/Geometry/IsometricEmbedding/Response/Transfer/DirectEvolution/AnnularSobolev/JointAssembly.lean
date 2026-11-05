module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.UniformBranches
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.WeakTransfer.Envelope
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.Estimates.JointExpansion
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.DatumBridge

/-!
# Primitive joint Sobolev estimate for the actual annular envelope

The weak expansion and every branch norm are instantiated for the SAME
elapsed graph and the literal normalized annular amplitude. Parameter
variation fixes that graph, its frequency and all masks. Only original
phase/amplitude jets, critical geometry and original datum jets are inputs.
Source: `app:ch_response:eq:direct-envelope-profile`,
`app:ch_response:lem:energy-carrier-jets` and `new:eq:carrier-ibp`.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option cleanup.letToHave false
open Set MeasureTheory Filter LineDeriv
open scoped ContDiff Topology Matrix.Norms.Frobenius SchwartzMap
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularSobolev
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
local instance jointAnnularComplexMatrixTopology : TopologicalSpace Mat :=
  (Matrix.frobeniusNormedAddCommGroup (m := Fin r) (n := Fin r)
    (α := ℂ)).toUniformSpace.toTopologicalSpace

attribute [local irreducible] normalizedTermAmplitude elapsedCarrierPhase
  averagedPhaseHessian modifiedAmplitude fullGraphOperator

/-- Joint Sobolev membership and the exact weighted estimate for the actual
annular envelope, from primitive original jets and local critical geometry.
Every low-calculus bound and weak identity is discharged. The physical graph,
frequency and masks stay fixed under parameter differentiation; the datum
profile consists of actual original mixed Fréchet jets. This covers both
`p = 0` and `p = -1` without changing the low reserve. Source:
`app:ch_response:eq:direct-envelope-profile` and `new:eq:carrier-ibp`. -/
theorem exists_annularEnvelope_joint_sobolev_of_primitive_jets
    (R ℓ M G c : ℝ) (hℓ : 0 < ℓ) (hRcell : R / ℓ < 1 / 2)
    {δ F : ℝ} (hδ : 0 < δ) (hF : 0 ≤ F) (hc : 1 ≤ c)
    (basis : OrthonormalBasis ι ℝ (CarrierVariables (d + 1)))
    (s : ℕ) (ps : List P) (hps : ∀ v ∈ ps, ‖v‖ ≤ 1)
    (Aphase Aamp : ℕ → ℝ) (hphase : ∀ j, 0 ≤ Aphase j) (hamp : ∀ j, 0 ≤ Aamp j)
    {B radius : ℝ} (hB : 0 ≤ B) (hradius : 0 ≤ radius) :
    ∃ C ≥ 0, ∀ (X₀ Y₀ F₀ : Set E), IsCompact X₀ →
      (∀ y ∈ Y₀, ∀ i : Fin (d + 1), |y i| ≤ R) → IsClosed F₀ → (0 : E) ∉ F₀ →
    ∀ (Ψ : TwoTimePhase d) (t : ℝ)
    (_hS : ContDiff ℝ ∞ (Function.uncurry (elapsedPhase Ψ t)))
    {X D : Set E} {η : E → E → E → E} {J : E → E → E → E →L[ℝ] E}
    {W K : Set (NormalVariables (d + 1))}
    (_chart : AveragedGradientChart (elapsedPhase Ψ t) X D η J δ)
    (_hopen : IsOpen (bufferedNormalDomain X D (elapsedPhase Ψ t)))
    (_hηinput : ContDiffOn ℝ ∞ (normalInverseCoordinates η) (bufferedNormalDomain X D (elapsedPhase Ψ t)))
    (_hmapinput : MapsTo (normalInverseCoordinates η) (bufferedNormalDomain X D (elapsedPhase Ψ t)) W)
    (_hJinput : ContDiffOn ℝ ∞ (fun q : NormalVariables (d + 1) ↦ J q.1 q.2.1 q.2.2) W)
    (_hgapinput : ∀ q ∈ W, (J q.1 q.2.1 q.2.2).det ≠ 0)
    (_hrightInverse : ∀ q ∈ bufferedNormalDomain X D (elapsedPhase Ψ t),
      normalForwardCoordinates (elapsedPhase Ψ t) (normalInverseCoordinates η q) = q)
    (_hcarrier : ∀ q ∈ W, q.1 ∈ X₀ → q.2.1 ∈ X₀ → q.2.2 ∈ F₀ → q ∈ K)
    (_hclosed : IsClosed (normalForwardCoordinates (elapsedPhase Ψ t) '' K))
    (_hbuffer : normalForwardCoordinates (elapsedPhase Ψ t) '' K ⊆ bufferedNormalDomain X D (elapsedPhase Ψ t))
    (_hR : ∀ x ∈ X, ‖x‖ ≤ R)
    (_hgrowth : ∀ x ∈ X, ∀ y ∈ X, ∀ u ∈ D,
      ‖averagedGradient (elapsedPhase Ψ t) x y u‖ ≤ F * (1 + ‖u‖))
    (V : ℕ → Set (NormalVariables (d + 1)))
    (_hUopen : ∀ l, IsOpen (normalDyadicShell (bufferedNormalDomain X D (elapsedPhase Ψ t)) l))
    (_hVopen : ∀ l, IsOpen (V l))
    (_hη : ∀ l, ContDiffOn ℝ ∞
      (normalInverseCoordinates (normalizedNormalInverse ((2 : ℝ)^l) η))
      (normalDyadicShell (bufferedNormalDomain X D (elapsedPhase Ψ t)) l))
    (_hmap : ∀ l, MapsTo
      (normalInverseCoordinates (normalizedNormalInverse ((2 : ℝ)^l) η))
      (normalDyadicShell (bufferedNormalDomain X D (elapsedPhase Ψ t)) l) (V l))
    (_hJ : ∀ l, ContDiffOn ℝ ∞
      (fun q : NormalVariables (d + 1) ↦
        normalizedNormalJacobian ((2 : ℝ)^l) J q.1 q.2.1 q.2.2) (V l))
    (_hgap : ∀ l z, z ∈ V l → δ ≤ |(normalizedNormalJacobian
      ((2 : ℝ)^l) J z.1 z.2.1 z.2.2).det|)
    (_hJjet : ∀ l z, z ∈ V l → ∀ i ≤ primitiveNormalReserve (d + 1),
      ‖iteratedFDeriv ℝ i (fun q : NormalVariables (d + 1) ↦
        normalizedNormalJacobian ((2 : ℝ)^l) J q.1 q.2.1 q.2.2) z‖ ≤ M)
    (_hηjet : ∀ l z, z ∈ normalDyadicShell (bufferedNormalDomain X D (elapsedPhase Ψ t)) l →
      ∀ i, 1 ≤ i → i ≤ primitiveNormalReserve (d + 1) →
      ‖iteratedFDeriv ℝ i (normalInverseCoordinates
        (normalizedNormalInverse ((2 : ℝ)^l) η)) z‖ ≤ G)
    (_hscale : ∀ l z, z ∈ V l →
      (2 : ℝ)^l ≤ c * (1 + ‖(2 : ℝ)^l • z.2.2‖))
    (_hX₀ : X₀ ⊆ X) (_hF₀ : F₀ ⊆ D),
    ∀ (Rstar : ℕ), fullLowReserve (d + 1) + 2 < Rstar →
    ∀ (L lam : ℝ), 1 ≤ L → 1 ≤ lam → ∀ (p : ℤ)
    (φ : E → P → ℝ) (w₀ : E × P → CarrierVariables (d + 1))
    (A : TwoTimeAmplitude d r) (χout χsource β π : E → ℂ),
    let α := normalizedAnnularElapsedAmplitude (P := P) A χout χsource β π t lam p
    ∀ (U : Set (E × P)) (Dcrit : Set (CarrierVariables (d + 1))),
    IsOpen U → IsOpen Dcrit → Convex ℝ Dcrit →
    ContDiffOn ℝ ∞ (Function.uncurry (elapsedCarrierPhase Ψ t φ)) (U ×ˢ Dcrit) →
    ContDiffOn ℝ ∞ w₀ U → MapsTo w₀ U Dcrit →
    (∀ q ∈ U, gradient (elapsedCarrierPhase Ψ t φ q) (w₀ q) = 0) →
    (∀ q ∈ U, elapsedCarrierPhase Ψ t φ q (w₀ q) = 0) →
    (∀ q ∈ U, ∀ w ∈ Dcrit, IsUnit (averagedPhaseHessian (elapsedCarrierPhase Ψ t φ) w₀ q w)) →
    (∀ q ∈ U, ∀ w ∈ Dcrit,
      ‖Ring.inverse (averagedPhaseHessian (elapsedCarrierPhase Ψ t φ) w₀ q w)‖ ≤ B) →
    (∀ j ≤ fullLowReserve (d + 1) + (s + ps.length) + 2,
      ∀ q ∈ U ×ˢ Dcrit,
        ‖iteratedFDeriv ℝ j (Function.uncurry (elapsedCarrierPhase Ψ t φ)) q‖ ≤
          Aphase j * L ^ (j - Rstar)) →
    ContDiffOn ℝ ∞ (Function.uncurry α) (U ×ˢ Dcrit) →
    (∀ j ≤ fullLowReserve (d + 1) + (s + ps.length),
      ∀ q ∈ U ×ˢ Dcrit,
        ‖iteratedFDeriv ℝ j (Function.uncurry α) q‖ ≤ Aamp j * L ^ (j + 2 - Rstar)) →
    ∀ (Kcrit : Set (CarrierVariables (d + 1))), IsCompact Kcrit → Kcrit ⊆ Dcrit →
    (∀ q ∈ U, Function.support (α q) ⊆ Kcrit) →
    (∀ q ∈ tsupport (Function.uncurry α), q.1.1 ∈ X₀) →
    ∀ (Cpar : Set P), IsOpen Cpar → X₀ ×ˢ Cpar ⊆ U →
    ∀ (hcφ : ∀ param, Continuous (fun x => φ x param)),
    (∀ param ∈ Cpar, ∀ q, normalizedSlice param q ∈ tsupport (Function.uncurry α) →
      normalizedSlice param q ∈ U ×ˢ Dcrit) →
    (∀ param ∈ Cpar, ∀ q, normalizedSlice param q ∈ tsupport (Function.uncurry α) → ‖q.2‖ ≤ radius) →
    (∀ param ∈ Cpar, ∀ q, normalizedSlice param q ∈ tsupport (Function.uncurry α) →
      q.1.1 ∈ X₀ ∧ q.1.2 ∈ Y₀ ∧ lam • q.2 ∈ F₀) →
    (∀ x ∈ X₀, ∀ θ, lam • θ ∈ F₀ →
      elapsedPhase Ψ t x (lam • θ) = lam * elapsedPhase Ψ t x θ) →
    ∀ (Ksource Ssource : Set E) (hKsource : IsCompact Ksource), IsOpen Ssource →
    Ksource ⊆ Ssource → (∀ param ∈ Cpar, ContDiffOn ℝ ∞ (fun x => φ x param) Ssource) →
    ∀ (a : E × P → Vf) (ha : ContDiff ℝ ∞ a)
      (has : ∀ q, q.1 ∉ Ksource → a q = 0),
    ∀ param ∈ Cpar, ∀ (Ddata : ℕ → ℝ), (∀ j, 0 ≤ Ddata j) →
    (∀ j, j ≤ s + ps.length →
      ∃ hm : MemLp (fun x : E => iteratedFDeriv ℝ j a (x, param)) 2 volume,
        ‖hm.toLp (fun x : E => iteratedFDeriv ℝ j a (x, param))‖ ≤ Ddata j) →
    let output := orderedTransferAction (fun v F c => fderiv ℝ F c v) ps
      (fun c => annularEnvelopeOperator Ψ A χout χsource β π t lam
        (fun x => φ x c) (hcφ c)
        (graphTestToLp (vectorOriginalDatumTest a ha hKsource has [] c))) param
    MemVectorFourierSobolev (s : ℝ) output ∧
      vectorFourierSobolevNorm (s : ℝ) output ≤ C * lam ^ p *
        (∑ j ∈ Finset.range (s + ps.length + 1), L ^ (s + ps.length - j) * Ddata j) := by
  obtain ⟨Cb, hCb, hbuild⟩ := exists_annularBranchFamily_of_primitive_jets
    (r := r) R ℓ M G c hℓ hRcell hδ hF hc basis s
    (ps.map fun v => ((0 : E), v)) Aphase Aamp hphase hamp hB hradius
  let Cs : ℝ := (((r : ℝ) * (d + 1 + 1 : ℝ) ^ s) *
    (((Fintype.card ι + 2 : ℕ) : ℝ) ^ (s + ps.length) * Cb))
  refine ⟨Cs, by dsimp [Cs]; positivity, ?_⟩
  intro X₀ Y₀ F₀ hXcompact hYbox hFclosed hFzero
    Ψ t hS X D η J Wnormal Knormal chart hopen hηinput hmapinput hJinput hgapinput
    hrightInverse hcarrier hclosed hbuffer hR hgrowth V hUopen hVopen hη hmap hJ
    hgap hJjet hηjet hscale hX₀ hF₀ Rstar hRstar L lam hL hlam p φ w₀ A χout χsource β π
  dsimp only
  let α := normalizedAnnularElapsedAmplitude (P := P) A χout χsource β π t lam p
  intro U Dcrit hU hDcrit hcD hf hw₀ h₀ hcrit hvalue hu hi hp hα hαjet
    Kcrit hKcrit hKD hsupportCrit houtput Cpar hCpar hXU hcφ hs hsfreq hsupport
    hΘ Ksource Ssource hKsource hSsource hKS hφ a ha has param hparam Ddata hDdata hj
  have hlampos : 0 < lam := zero_lt_one.trans_le hlam
  have hfamily (c : P) (hc : c ∈ Cpar) := hbuild X₀ Y₀ F₀ hXcompact hYbox hFclosed hFzero
    Ψ t hS chart hopen hηinput hmapinput hJinput hgapinput
    hrightInverse hcarrier hclosed hbuffer hR hgrowth V hUopen hVopen hη hmap hJ
    hgap hJjet hηjet hscale hX₀ hF₀ Rstar hRstar L lam hL hlam p φ w₀ α
    U Dcrit hU hDcrit hcD hf hw₀ h₀ hcrit hu hi
    (by simpa only [List.length_map] using hp) hα
    (by simpa only [List.length_map] using hαjet) c (hs c hc) (hsfreq c hc) (hsupport c hc)
  have hhom (c : P) (hc : c ∈ Cpar) (es : List (E × P))
      (branch : JointTransferTerm (d + 1) P Mat ι) (hb : branch ∈ jointTransferTerms basis es)
      (x z θ : E)
      (hn : modifiedAmplitude lam p (normalizedTermAmplitude basis
        (elapsedCarrierPhase Ψ t φ) w₀ α branch c) x z (lam • θ) ≠ 0) :
      elapsedPhase Ψ t x (lam • θ) = lam * elapsedPhase Ψ t x θ := by
    have hn' : normalizedTermAmplitude basis (elapsedCarrierPhase Ψ t φ) w₀ α branch c
        ((x, z), θ) ≠ 0 := by
      intro hz
      apply hn
      simp [modifiedAmplitude, NearCarrierSymbol.physicalAmplitudeOfNormalized,
        smul_smul, inv_mul_cancel₀ hlampos.ne', hz]
    have hsup := hsupport c hc ((x, z), θ)
      (tsupport_normalizedTermAmplitude_subset basis (elapsedCarrierPhase Ψ t φ) w₀ α es
        branch hb c (subset_tsupport _ hn'))
    exact hΘ x hsup.1 θ hsup.2.2
  let aPi := fun q => (a q).ofLp
  have haPi : ContDiff ℝ ∞ aPi :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin r => ℂ)).contDiff.comp ha
  have hasPi : ∀ q, q.1 ∉ Ksource → aPi q = 0 :=
    fun q hq => congrArg WithLp.ofLp (has q hq)
  let T := fun branch => annularBranchOperator basis Ψ t lam p φ w₀ α branch param (hcφ param)
  let da := fun ds => graphTestToLp (vectorOriginalDatumTest a ha hKsource has ds param)
  let output := orderedTransferAction (fun v F c => fderiv ℝ F c v) ps
    (fun c => annularEnvelopeOperator Ψ A χout χsource β π t lam
      (fun x => φ x c) (hcφ c)
      (graphTestToLp (vectorOriginalDatumTest a ha hKsource has [] c))) param
  have hweak (is : List (Fin (d + 1))) (his : is.length ≤ s) :
      orderedTransferAction (fun i => lineDerivOp (EuclideanSpace.single i (1 : ℝ))) is
        (output : 𝓢'(E, Vf)) =
      ((jointTransferTerms basis ((is.map fun i => (EuclideanSpace.single i (1 : ℝ), (0 : P))) ++
        ps.map (fun v => ((0 : E), v)))).map
          fun branch => (T branch (da branch.datumWord) : 𝓢'(E, Vf))).sum := by
    have h := WeakTransfer.annularEnvelope_joint_derivative_expansion basis Ψ A χout χsource β π
      t hlampos p φ w₀ hU hDcrit hcD hKcrit hKD hf hα haPi hsupportCrit hw₀ hcrit hvalue h₀ hu
      hKsource hSsource hKS hasPi ps is hXcompact houtput hCpar hXU hcφ hφ
      (fun c hc ds hd branch hb => (hfamily c hc).2 ds
        (by simpa only [List.length_map] using (show ds.length ≤ s + ps.length by omega)) branch hb)
      (fun c hc ds _ branch hb => hhom c hc ds branch hb) param hparam
    simpa only [T, da, output, vectorOriginalDatumTest] using h
  obtain ⟨w, heq, hw, hnorm⟩ := annular_joint_sobolev_of_expansion s Cb hCb basis ps hps T
    L lam p hL hlampos a ha param da
    (fun ds _ _ => vectorOriginalDatumTest_toLp_ae a ha hKsource has ds param)
    Ddata hDdata hj (output : 𝓢'(E, Vf)) hweak
    (fun is his branch hb => by
      simpa only [List.length_map] using ((hfamily param hparam).1 is his branch hb (hcφ param)))
  have he : w = output := (LinearMap.ker_eq_bot.mp
    (Lp.ker_toTemperedDistributionCLM_eq_bot (F := Vf) (μ := (volume : Measure E)) (p := 2))) heq
  rw [he] at hw hnorm
  exact ⟨hw, by simpa only [Cs, Nat.cast_add, Nat.cast_one] using hnorm⟩

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularSobolev
