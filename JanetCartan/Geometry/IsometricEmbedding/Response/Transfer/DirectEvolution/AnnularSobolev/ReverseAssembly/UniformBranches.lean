module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.ReverseAssembly.Realization
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.Operators
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.Estimates.Counting
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.ModifiedLow

/-!
# Uniform primitive bounds and uncut identities for reverse annular branches

The constants are selected before the coefficient scale, frequency and varying
fields. Every uncut reverse test realization follows from the primitive forward
identity and a cutoff equal to one on the actual normalized support; the common bound covers the coordinate words with a fixed
parameter suffix. Consumer: the Sobolev assembly of
`app:ch_response:eq:direct-envelope-profile`, using `new:eq:carrier-ibp`.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 1600000
set_option cleanup.letToHave false
set_option maxSynthPendingDepth 4
open Set MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularSobolev
open FourierIntegral FourierIntegral.FullLowBounds FourierIntegral.LowBounds
open FourierIntegral.SourceExpansion NormalComparison FrequencyCutoff AmplitudeBound
open FullAmplitudePrimitiveBudget.Local CompactTransfer BranchAmplitudes ModifiedLow
open RegularSector.Characteristic.EvolutionIntegral
variable {d r : ℕ} {P ι : Type}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] [Fintype ι]
local notation "E" => Euclidean (d + 1)
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)
local instance uniformReverseAnnularComplexMatrixTopology : TopologicalSpace Mat :=
  (Matrix.frobeniusNormedAddCommGroup (m := Fin r) (n := Fin r)
    (α := ℂ)).toUniformSpace.toTopologicalSpace

attribute [local irreducible] normalizedTermAmplitude adjointCarrierPhase
  averagedPhaseHessian modifiedAmplitude fullGraphOperator

/-- Simultaneous primitive realization for the exact finite output/parameter
branch family. The constant precedes scales and all varying fields, and the
low reserve is independent of the total order. All physical test identities
needed by weak transfer are constructed, including for intermediate words.
Source: `new:eq:carrier-ibp`, `app:ch_response:eq:direct-envelope-profile`. -/
theorem exists_reverseAnnularBranchFamily_of_primitive_jets
    (R ℓ M G c : ℝ) (hℓ : 0 < ℓ) (hRcell : R / ℓ < 1 / 2)
    {δ F : ℝ} (hδ : 0 < δ) (hF : 0 ≤ F) (hc : 1 ≤ c)
    (basis : OrthonormalBasis ι ℝ (CarrierVariables (d + 1)))
    (s : ℕ) (suffix : List (E × P))
    (Aphase Aamp : ℕ → ℝ) (hphase : ∀ j, 0 ≤ Aphase j) (hamp : ∀ j, 0 ≤ Aamp j)
    {B radius : ℝ} (hB : 0 ≤ B) (hradius : 0 ≤ radius) :
    ∃ C ≥ 0, ∀ (X₀ Y₀ F₀ : Set E), IsCompact X₀ → IsCompact Y₀ →
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
    (α : (E × P) → CarrierVariables (d + 1) → Mat)
    (U : Set (E × P)) (Dcrit : Set (CarrierVariables (d + 1))),
    IsOpen U → IsOpen Dcrit → Convex ℝ Dcrit →
    ContDiffOn ℝ ∞ (Function.uncurry (adjointCarrierPhase (elapsedPhase Ψ t) φ)) (U ×ˢ Dcrit) →
    ContDiffOn ℝ ∞ w₀ U → MapsTo w₀ U Dcrit →
    (∀ q ∈ U, gradient (adjointCarrierPhase (elapsedPhase Ψ t) φ q) (w₀ q) = 0) →
    (∀ q ∈ U, ∀ w ∈ Dcrit, IsUnit (averagedPhaseHessian (adjointCarrierPhase (elapsedPhase Ψ t) φ) w₀ q w)) →
    (∀ q ∈ U, ∀ w ∈ Dcrit,
      ‖Ring.inverse (averagedPhaseHessian (adjointCarrierPhase (elapsedPhase Ψ t) φ) w₀ q w)‖ ≤ B) →
    (∀ j ≤ fullLowReserve (d + 1) + (s + suffix.length) + 2,
      ∀ q ∈ U ×ˢ Dcrit,
        ‖iteratedFDeriv ℝ j (Function.uncurry (adjointCarrierPhase (elapsedPhase Ψ t) φ)) q‖ ≤
          Aphase j * L ^ (j - Rstar)) →
    ContDiffOn ℝ ∞ (Function.uncurry α) (U ×ˢ Dcrit) →
    (∀ j ≤ fullLowReserve (d + 1) + (s + suffix.length),
      ∀ q ∈ U ×ˢ Dcrit,
        ‖iteratedFDeriv ℝ j (Function.uncurry α) q‖ ≤ Aamp j * L ^ (j + 2 - Rstar)) →
    ∀ param : P,
    (∀ q, normalizedSlice param q ∈ tsupport (Function.uncurry α) →
      normalizedSlice param q ∈ U ×ˢ Dcrit) →
    (∀ q, normalizedSlice param q ∈ tsupport (Function.uncurry α) → ‖q.2‖ ≤ radius) →
    (∀ q, normalizedSlice param q ∈ tsupport (Function.uncurry α) →
      q.1.2 ∈ X₀ ∧ q.1.1 ∈ Y₀ ∧ lam • q.2 ∈ F₀) →
    (∀ is : List (Fin (d + 1)), is.length ≤ s →
      ∀ branch ∈ jointTransferTerms basis
        ((is.map fun i => (EuclideanSpace.single i (1 : ℝ), (0 : P))) ++ suffix),
      ∀ hφ : Continuous (fun x => φ x param),
        ‖reverseAnnularBranchOperator basis Ψ t lam p φ w₀ α branch param hφ‖ ≤
          C * lam ^ p * L ^ (is.length + suffix.length - branch.datumWord.length)) ∧
    (∀ es : List (E × P), es.length ≤ s + suffix.length →
      ∀ branch ∈ jointTransferTerms basis es,
      ∀ u : graphTestSpace (d + 1) r,
        (fullGraphOperator (elapsedPhase Ψ t) (fun x z ξ =>
          (modifiedAmplitude lam p (normalizedTermAmplitude basis
            (adjointCarrierPhase (elapsedPhase Ψ t) φ) w₀ α branch param) z x ξ).conjTranspose)).adjoint
          (graphTestToLp u) =ᵐ[volume] fun x => WithLp.toLp 2
        (reverseGraphOperator (elapsedPhase Ψ t) (fun y z ξ =>
          modifiedAmplitude lam p (normalizedTermAmplitude basis
            (adjointCarrierPhase (elapsedPhase Ψ t) φ) w₀ α branch param) z y ξ)
          (fun y => (u.val y).ofLp) x)) := by
  classical
  let Cbranch (es : List (E × P)) (branch : JointTransferTerm (d + 1) P Mat ι) : ℝ :=
    if hb : branch ∈ jointTransferTerms basis es then
      (exists_reverseAnnularBranchElapsedGraph_of_primitive_jets R ℓ M G c hℓ hRcell hδ hF hc
        basis es branch hb Aphase Aamp hphase hamp hB hradius).choose
    else 0
  let es := fun is : List (Fin (d + 1)) =>
    (is.map fun i => (EuclideanSpace.single i (1 : ℝ), (0 : P))) ++ suffix
  let W : Set (List (Fin (d + 1))) := ⋃ k ∈ Set.Iic s,
    Set.range (fun v : Fin k → Fin (d + 1) => List.ofFn v)
  have hW : W.Finite := (Set.finite_Iic s).biUnion
    (fun k _ => Set.finite_range (fun v : Fin k → Fin (d + 1) => List.ofFn v))
  let Bset : Set ℝ := ⋃ is ∈ W,
    (Cbranch (es is)) '' {branch | branch ∈ jointTransferTerms (M := Mat) basis (es is)}
  have hBset : Bset.Finite := hW.biUnion (fun is _ =>
    (jointTransferTerms (M := Mat) basis (es is)).finite_toSet.image (Cbranch (es is)))
  obtain ⟨Cmax, hmax⟩ := hBset.exists_le
  have hbound (is : List (Fin (d + 1))) (hi : is.length ≤ s)
      (branch : JointTransferTerm (d + 1) P Mat ι)
      (hb : branch ∈ jointTransferTerms basis (es is)) :
      Cbranch (es is) branch ≤ max 0 Cmax := by
    have his : is ∈ W := Set.mem_iUnion.mpr ⟨is.length,
      Set.mem_iUnion.mpr ⟨hi, ⟨is.get, List.ofFn_get is⟩⟩⟩
    exact (hmax _ (Set.mem_iUnion.mpr ⟨is,
      Set.mem_iUnion.mpr ⟨his, ⟨branch, hb, rfl⟩⟩⟩)).trans (le_max_right _ _)
  refine ⟨max 0 Cmax, le_max_left _ _, ?_⟩
  intro X₀ Y₀ F₀ hXcompact hYcompact hYbox hFclosed hFzero
    Ψ t hS X D η J Wnormal Knormal chart hopen hηinput hmapinput hJinput hgapinput
    hrightInverse hcarrier hclosed hbuffer hR hgrowth V hUopen hVopen hη hmap hJ
    hgap hJjet hηjet hscale hX₀ hF₀ Rstar hRstar L lam hL hlam p φ w₀ α
    U Dcrit hU hDcrit hcD hf hw₀ h₀ hcrit hu hi hp hα hαjet param hs hsfreq hsupport
  have hbranchResult (ds : List (E × P)) (hd : ds.length ≤ s + suffix.length)
      (branch : JointTransferTerm (d + 1) P Mat ι)
      (hb : branch ∈ jointTransferTerms basis ds) :
      ‖(fullGraphOperator (elapsedPhase Ψ t) (fun x z ξ =>
        (modifiedAmplitude lam p (normalizedTermAmplitude basis
          (adjointCarrierPhase (elapsedPhase Ψ t) φ) w₀ α branch param) z x ξ).conjTranspose)).adjoint‖ ≤
        Cbranch ds branch * lam ^ p * L ^ (ds.length - branch.datumWord.length) ∧
      ∀ u : graphTestSpace (d + 1) r,
        (fullGraphOperator (elapsedPhase Ψ t) (fun x z ξ =>
          (modifiedAmplitude lam p (normalizedTermAmplitude basis
            (adjointCarrierPhase (elapsedPhase Ψ t) φ) w₀ α branch param) z x ξ).conjTranspose)).adjoint
          (graphTestToLp u) =ᵐ[volume] fun x => WithLp.toLp 2
        (reverseGraphOperator (elapsedPhase Ψ t) (fun y z ξ =>
          modifiedAmplitude lam p (normalizedTermAmplitude basis
            (adjointCarrierPhase (elapsedPhase Ψ t) φ) w₀ α branch param) z y ξ)
          (fun y => (u.val y).ofLp) x) := by
    have hbuild := (exists_reverseAnnularBranchElapsedGraph_of_primitive_jets
      R ℓ M G c hℓ hRcell hδ hF hc basis ds branch hb Aphase Aamp hphase hamp hB hradius).choose_spec.2
    obtain ⟨χ, _, _, _, _, hfamily⟩ := hbuild X₀ Y₀ F₀ hXcompact hYbox hFclosed hFzero
    have hresult := hfamily Ψ t hS chart hopen hηinput hmapinput hJinput hgapinput
      hrightInverse hcarrier hclosed hbuffer hR hgrowth V hUopen hVopen hη hmap hJ
      hgap hJjet hηjet hscale hX₀ hF₀ Rstar hRstar L lam hL hlam p φ w₀ α
      U Dcrit hU hDcrit hcD hf hw₀ h₀ hcrit hu hi
      (fun j hj q hq => hp j (by omega) q hq) hα
      (fun j hj q hq => hαjet j (by omega) q hq) param hs hsfreq hsupport
    obtain ⟨Treg, hT⟩ := hresult
    refine ⟨by simpa only [Cbranch, dite_eq_left hb] using hT.2.1, ?_⟩
    have hsm := contDiff_normalizedTermAmplitude basis hU hDcrit hα
      (contDiffOn_transferCoefficient hU hDcrit hcD hf hw₀ h₀ hu) ds branch hb param hs
    exact modifiedAmplitude_adjoint_ae_of_normalized_support (elapsedPhase Ψ t) hS
      hsm (zero_lt_one.trans_le hlam) hradius p hXcompact hYcompact
      (fun q hq => (hsupport q (tsupport_normalizedTermAmplitude_subset basis
        (adjointCarrierPhase (elapsedPhase Ψ t) φ) w₀ α ds branch hb param hq)).imp_right And.left)
      (fun q hq => hsfreq q (tsupport_normalizedTermAmplitude_subset basis
        (adjointCarrierPhase (elapsedPhase Ψ t) φ) w₀ α ds branch hb param hq))
      _ hT.2.2.2.2.2.2.2.1
  refine ⟨?_, fun ds hd branch hb => (hbranchResult ds hd branch hb).2⟩
  intro is hi branch hb hφ
  have hlen : (es is).length = is.length + suffix.length := by simp [es]
  have hn : (es is).length ≤ s + suffix.length := by omega
  apply (norm_demodulatedL2Operator_le lam (fun x => φ x param) hφ _).trans
  apply (hbranchResult (es is) hn branch hb).1.trans
  rw [hlen]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hbound is hi branch hb) (zpow_nonneg (by linarith) p))
    (pow_nonneg (by linarith) _)

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularSobolev
