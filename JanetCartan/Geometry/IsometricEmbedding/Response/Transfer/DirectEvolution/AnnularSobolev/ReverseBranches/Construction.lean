module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.ReverseBranches.SymbolBudget
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.ReverseBranches.Initial
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.ReverseBranches.Realization
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.ModifiedLow

/-!
# Primitive construction of the literal reversed annular branch

Apply the original elapsed graph constructor to the exchanged conjugate
transpose of the complete restored reversed branch. The chart, inverse and
Jacobian are those of the original phase. Only the original support and
primitive reversed critical geometry and phase/amplitude jets are inputs.
The consumer is the weak-transfer and Sobolev assembly of
`app:ch_response:eq:direct-envelope-profile`, via `new:eq:carrier-ibp`.
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
local instance reverseAnnularComplexMatrixTopology : TopologicalSpace Mat :=
  (Matrix.frobeniusNormedAddCommGroup (m := Fin r) (n := Fin r)
    (α := ℂ)).toUniformSpace.toTopologicalSpace

attribute [local irreducible] normalizedTermAmplitude adjointCarrierPhase
  averagedPhaseHessian modifiedAmplitude fullGraphOperator

/-- Construct the literal reversed branch from primitive jets with bound
`C * lam^p * L^(q-j)`. The frequency cutoffs, test identities, strong limits
and distributional realizations all belong to the SAME original graph and
its literal Hilbert adjoint. Carrier conjugation gives the published
`reverseAnnularBranchOperator` with the same bound and strong limits.
The constant precedes the scales and varying fields, and
`fullLowReserve (d+1)` is independent of derivative and parameter orders.
Source: `new:eq:carrier-ibp`, `app:ch_response:eq:direct-envelope-profile`. -/
theorem exists_reverseAnnularBranchElapsedGraph_of_primitive_jets
    (R ℓ M G c : ℝ) (hℓ : 0 < ℓ) (hRcell : R / ℓ < 1 / 2)
    {δ F : ℝ} (hδ : 0 < δ) (hF : 0 ≤ F) (hc : 1 ≤ c)
    (basis : OrthonormalBasis ι ℝ (CarrierVariables (d + 1)))
    (es : List (E × P)) (branch : JointTransferTerm (d + 1) P Mat ι)
    (hbranch : branch ∈ jointTransferTerms basis es)
    (Aphase Aamp : ℕ → ℝ) (hphase : ∀ j, 0 ≤ Aphase j) (hamp : ∀ j, 0 ≤ Aamp j)
    {B radius : ℝ} (hB : 0 ≤ B) (hradius : 0 ≤ radius) :
    ∃ C ≥ 0, ∀ (X₀ Y₀ F₀ : Set E), IsCompact X₀ →
      (∀ y ∈ Y₀, ∀ i : Fin (d + 1), |y i| ≤ R) → IsClosed F₀ → (0 : E) ∉ F₀ →
    ∃ χ : ℕ → E → ℂ,
      (∀ j, ContDiff ℝ ∞ (χ j)) ∧ (∀ j, HasCompactSupport (χ j)) ∧
      (∀ j, (0 : E) ∉ tsupport (χ j)) ∧
      (∀ (A : FullAmplitude (d + 1) r), (∀ x y ξ, ξ ∉ F₀ → A x y ξ = 0) →
        ∀ j, frequencyCutFullAmplitude (χ j) A =
          frequencyCutFullAmplitude (complexPhysicalCutoff j) A) ∧
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
    (∀ j ≤ fullLowReserve (d + 1) + (es.length - branch.datumWord.length) + 2,
      ∀ q ∈ U ×ˢ Dcrit,
        ‖iteratedFDeriv ℝ j (Function.uncurry (adjointCarrierPhase (elapsedPhase Ψ t) φ)) q‖ ≤
          Aphase j * L ^ (j - Rstar)) →
    ContDiffOn ℝ ∞ (Function.uncurry α) (U ×ˢ Dcrit) →
    (∀ j ≤ fullLowReserve (d + 1) + (es.length - branch.datumWord.length),
      ∀ q ∈ U ×ˢ Dcrit,
        ‖iteratedFDeriv ℝ j (Function.uncurry α) q‖ ≤ Aamp j * L ^ (j + 2 - Rstar)) →
    ∀ param : P,
    (∀ q, normalizedSlice param q ∈ tsupport (Function.uncurry α) →
      normalizedSlice param q ∈ U ×ˢ Dcrit) →
    (∀ q, normalizedSlice param q ∈ tsupport (Function.uncurry α) → ‖q.2‖ ≤ radius) →
    (∀ q, normalizedSlice param q ∈ tsupport (Function.uncurry α) →
      q.1.2 ∈ X₀ ∧ q.1.1 ∈ Y₀ ∧ lam • q.2 ∈ F₀) →
    let Arev := modifiedAmplitude lam p
      (normalizedTermAmplitude basis (adjointCarrierPhase (elapsedPhase Ψ t) φ) w₀ α branch param)
    let A : FullAmplitude (d + 1) r := fun x z ξ => (Arev z x ξ).conjTranspose
        ∃ Treg : ℕ → H →L[ℂ] H,
          ‖fullGraphOperator (elapsedPhase Ψ t) A‖ ≤ C * lam ^ p * L ^ (es.length - branch.datumWord.length) ∧ ‖(fullGraphOperator (elapsedPhase Ψ t) A).adjoint‖ ≤ C * lam ^ p * L ^ (es.length - branch.datumWord.length) ∧
          (∀ j, ‖Treg j‖ ≤ C * lam ^ p * L ^ (es.length - branch.datumWord.length)) ∧
          (∀ j u, Treg j (graphTestToLp u) =ᵐ[volume]
            graphTestOutput (elapsedPhase Ψ t) (frequencyCutFullAmplitude (χ j) A) u) ∧
          (∀ j (u : graphTestSpace (d + 1) r), (Treg j).adjoint (graphTestToLp u) =ᵐ[volume]
            fun y ↦ WithLp.toLp 2 (reverseGraphOperator (elapsedPhase Ψ t)
              (frequencyCutFullAmplitude (fun η ↦ star (χ j η))
                (fun x y η ↦ (A x y η).conjTranspose)) (fun x ↦ (u.val x).ofLp) y)) ∧
          (∀ u, Tendsto (fun j ↦ Treg j u) atTop (𝓝 (fullGraphOperator (elapsedPhase Ψ t) A u))) ∧
          (∀ u, Tendsto (fun j ↦ (Treg j).adjoint u) atTop
            (𝓝 ((fullGraphOperator (elapsedPhase Ψ t) A).adjoint u))) ∧
          (∀ u, fullGraphOperator (elapsedPhase Ψ t) A (graphTestToLp u) =ᵐ[volume] graphTestOutput (elapsedPhase Ψ t) A u) ∧
          GraphDistributionalRealization (graphOperator (elapsedPhase Ψ t)) χ A (fullGraphOperator (elapsedPhase Ψ t) A) ∧
          GraphDistributionalRealization (reverseGraphOperator (elapsedPhase Ψ t)) (fun j η ↦ star (χ j η))
            (fun x y η ↦ (A x y η).conjTranspose) (fullGraphOperator (elapsedPhase Ψ t) A).adjoint ∧
          (∀ U : H →L[ℂ] H,
            (∀ u, U (graphTestToLp u) =ᵐ[volume] graphTestOutput (elapsedPhase Ψ t) A u) →
            U = fullGraphOperator (elapsedPhase Ψ t) A) ∧
          ∀ hφ : Continuous (fun x => φ x param),
            ‖reverseAnnularBranchOperator basis Ψ t lam p φ w₀ α branch param hφ‖ ≤
              C * lam ^ p * L ^ (es.length - branch.datumWord.length) ∧
            (∀ j, ‖demodulatedL2Operator lam (fun x => φ x param) hφ (Treg j).adjoint‖ ≤
              C * lam ^ p * L ^ (es.length - branch.datumWord.length)) ∧
            (∀ u, Tendsto (fun j =>
              demodulatedL2Operator lam (fun x => φ x param) hφ (Treg j).adjoint u)
              atTop (𝓝 (reverseAnnularBranchOperator basis Ψ t lam p φ w₀ α branch param hφ u))) ∧
            (ContDiff ℝ ∞ (fun x => φ x param) →
              (∀ j (u : graphTestSpace (d + 1) r),
                demodulatedL2Operator lam (fun x => φ x param) hφ (Treg j).adjoint
                    (graphTestToLp u) =ᵐ[volume]
                  fun x => WithLp.toLp 2
                    (reverseAnnularKernel (elapsedPhase Ψ t) (fun y => φ y param) lam
                      (frequencyCutFullAmplitude (fun ξ => star (χ j ξ)) Arev)
                      (fun z => (u.val z).ofLp) x)) ∧
              GraphDistributionalRealization
                (reverseAnnularKernel (elapsedPhase Ψ t) (fun x => φ x param) lam)
                (fun j ξ => star (χ j ξ)) Arev
                (reverseAnnularBranchOperator basis Ψ t lam p φ w₀ α branch param hφ)) := by
  have hconstructor := exists_fullGraphFamily_of_primitive_inputs
    (n := d + 1) (r := r) (Nat.zero_lt_succ d) R ℓ M G c hℓ hRcell hδ hF hc
  let C₀ := hconstructor.choose
  have hC₀ := hconstructor.choose_spec.1
  have hbuild := hconstructor.choose_spec.2
  have hsymbolConstructor := exists_reverseJointTransferTerm_symbol_constant
    (n := d + 1) (r := r) (P := P) (ι := ι)
    basis es branch hbranch (fullLowReserve (d + 1)) Aphase Aamp hphase hamp hB hradius
  let Cbranch := hsymbolConstructor.choose
  have hCbranch := hsymbolConstructor.choose_spec.1
  have hsymbol := hsymbolConstructor.choose_spec.2
  refine ⟨C₀ * Cbranch, mul_nonneg hC₀.le hCbranch, ?_⟩
  intro X₀ Y₀ F₀ hXcompact hYbox hFclosed hFzero
  have hcutoffs := hbuild X₀ Y₀ F₀ hXcompact hYbox hFclosed hFzero
  let χ := hcutoffs.choose
  have hχ := hcutoffs.choose_spec
  have hfamily := hχ.2.2.2.2
  refine ⟨χ, hχ.1, hχ.2.1, hχ.2.2.1, hχ.2.2.2.1, ?_⟩
  intro Ψ t hS X D η J W K chart hopen hηinput hmapinput hJinput hgapinput
    hrightInverse hcarrier hclosed hbuffer hR hgrowth V hUopen hVopen hη hmap hJ
    hgap hJjet hηjet hscale hX₀ hF₀ Rstar hRstar L lam hL hlam p φ w₀ α
    U Dcrit hU hDcrit hcD hf hw₀ h₀ hcrit hu hi hp hα hαjet param hs hsfreq hsupport
  have hbranchSymbol := hsymbol Rstar hRstar L lam hL hlam p
    (adjointCarrierPhase (elapsedPhase Ψ t) φ) w₀ α U Dcrit hU hDcrit hcD hf hw₀ h₀ hcrit hu hi
    hp hα hαjet param hs hsfreq
  have hsm := hbranchSymbol.1
  have hsym := hbranchSymbol.2
  let Arev := modifiedAmplitude lam p
    (normalizedTermAmplitude basis (adjointCarrierPhase (elapsedPhase Ψ t) φ) w₀ α branch param)
  let A : FullAmplitude (d + 1) r := fun x z ξ => (Arev z x ξ).conjTranspose
  have hA : ForwardAmplitudeAdmissible X₀ Y₀ F₀ A :=
    forwardAmplitudeAdmissible_exchange_conjTranspose
      (admissible_modifiedAmplitude (zero_lt_one.trans_le hlam).ne' p hsm
        (fun q hq => by
          have h := hsupport q (tsupport_normalizedTermAmplitude_subset basis
            (adjointCarrierPhase (elapsedPhase Ψ t) φ) w₀ α es branch hbranch param hq)
          exact ⟨h.2.1, h.1, h.2.2⟩))
  have hgeometry := hfamily (elapsedPhase Ψ t) hS chart hopen hηinput hmapinput hJinput hgapinput
    hrightInverse hcarrier hclosed hbuffer hR hgrowth V hUopen hVopen hη hmap hJ
    hgap hJjet hηjet hscale hX₀ hF₀
  have hoperator :=
    hgeometry.1 A hA (Cbranch * lam ^ p * L ^ (es.length - branch.datumWord.length)) hsym
  let Treg := hoperator.choose
  have hT := hoperator.choose_spec
  refine ⟨Treg, ?_, ?_, ?_, hT.2.2.2.1, hT.2.2.2.2.1,
    hT.2.2.2.2.2.1, hT.2.2.2.2.2.2.1, hT.2.2.2.2.2.2.2.1,
    hT.2.2.2.2.2.2.2.2.1, hT.2.2.2.2.2.2.2.2.2, ?_, ?_⟩
  · simpa only [mul_assoc] using hT.1
  · simpa only [mul_assoc] using hT.2.1
  · simpa only [mul_assoc] using hT.2.2.1
  · intro T hT
    exact (fullGraphOperator_eq_of_realizes (elapsedPhase Ψ t) A T hT).symm

  · intro hφ
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact (norm_demodulatedL2Operator_le lam (fun x => φ x param) hφ _).trans
        (by simpa only [mul_assoc] using hT.2.1)
    · intro j
      apply (norm_demodulatedL2Operator_le lam (fun x => φ x param) hφ _).trans
      calc
        ‖(Treg j).adjoint‖ = ‖Treg j‖ := ContinuousLinearMap.adjoint.norm_map _
        _ ≤ C₀ * (Cbranch * lam ^ p * L ^ (es.length - branch.datumWord.length)) := hT.2.2.1 j
        _ = _ := by ring
    · exact demodulatedL2Operator_strongLimit lam (fun x => φ x param) hφ
        (fun j => (Treg j).adjoint) _ hT.2.2.2.2.2.2.1

    · intro hφsmooth
      have hreverse (j : ℕ) (u : graphTestSpace (d + 1) r) :
          (Treg j).adjoint (graphTestToLp u) =ᵐ[volume]
            fun y => WithLp.toLp 2 (reverseGraphOperator (elapsedPhase Ψ t)
              (frequencyCutFullAmplitude (fun ξ => star (χ j ξ))
                (fun x y ξ => Arev y x ξ)) (fun x => (u.val x).ofLp) y) := by
        simpa only [A, Matrix.conjTranspose_conjTranspose] using hT.2.2.2.2.1 j u
      refine ⟨?_, ?_⟩
      · intro j u
        exact demodulated_reverseGraph_test_ae (elapsedPhase Ψ t) (fun x => φ x param)
          lam hφsmooth (frequencyCutFullAmplitude (fun ξ => star (χ j ξ)) Arev)
          (Treg j).adjoint (hreverse j) u
      · exact reverseAnnularKernel_distributional_of_strong_limit (elapsedPhase Ψ t)
          (fun x => φ x param) lam hφsmooth (fun j ξ => star (χ j ξ)) Arev
          (fullGraphOperator (elapsedPhase Ψ t) A).adjoint (fun j => (Treg j).adjoint)
          hreverse hT.2.2.2.2.2.2.1

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularSobolev
