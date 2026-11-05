module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.PrimitiveIntegrated
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.OperatorUniqueness
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.LocalizerReality
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.PhysicalLeakage

/-!
# Supported-collar leakage for the literal direct residual

Apply the primitive integrated estimate on its supported collar domains, identify
its operators with the supplied literal realizations, and pass to complex and real
physical pairings. No chart leakage estimate is an input.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.RegularSector.Realization
namespace JanetCartan.ArbitraryAccuracy.ResidualLocalization.UniformSupported
open FourierIntegral CharacteristicTransport.CompleteResidual
open FiniteChain.Graph KernelEstimates PhysicalShells CartesianJets KernelLimits
open PhysicalShells.Noncomparable
open FiniteChain.Retarded.KernelDecay FiniteChain.Retarded.HalfSpace JanetCartan.Localization
open RegularSector.Characteristic RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Realization RegularSector.Characteristic.RetardedLocalization LocalSobolev
open EvolutionLocalization.SobolevRealization Pseudodifferential EvolutionIntegratedLocalization
open LowBounds LowBounds.FrequencyCutoff FiniteChain.Retarded.KernelSobolev
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "V" => ℝ × JointVariables E
local notation "Mat" => Matrix (Fin q) (Fin q) ℂ
local notation "Hspace" => SpacetimeL2 d q
attribute [local instance] KernelLimits.matrixContinuousENorm KernelLimits.matrixPseudoMetrizableSpace
set_option synthInstance.maxSize 256
set_option maxHeartbeats 20000000
set_option backward.isDefEq.respectTransparency false

/-- The supported elapsed residual estimate with its common constants chosen
before the varying even masks. The primitive collar proof, actual conic graph
regularizations, strong limits, literal adjoints and physical pairing are
unchanged. Consumer: uniform complete residual leakage on the same selected
family (`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_supported_directResidual_integral_fourier_bound_of_uniform_masks
    {ι κ ιu ιz : Type*} [Fintype ι] [Fintype κ] [Fintype ιu] [Fintype ιz]
    (eT : Module.Basis ι ℝ (JointVariables E)) (eI : Module.Basis κ ℝ V)
    (eu : OrthonormalBasis ιu ℝ E) (ez : OrthonormalBasis ιz ℝ E)
    (J : (ℝ × (Fin d → ℝ)) ≃L[ℝ] E)
    (hJ : MeasurePreserving (graphInputCoordinates J) volume volume)
    (s Δ : ℝ) (hΔ : 0 ≤ Δ) (m bo offset bt bs bg bb bi : ℕ)
    (c C b₀ : ℝ) (hc : 0 < c) {a₀ Ci : ℝ} (ha₀ : 0 < a₀) (hCi : 0 ≤ Ci)
    (χout χsource β : E → ℂ)
    (hχout : ContDiff ℝ ∞ χout) (hχsource : ContDiff ℝ ∞ χsource)
    (hβsmooth : ContDiff ℝ ∞ β)
    (hout : HasCompactSupport χout) (hsource : HasCompactSupport χsource)
    {Bβ Cβ : ℝ} (hBβ : 0 ≤ Bβ) (hCβ : 0 ≤ Cβ)
    (hβ : ∀ ξ, ‖β ξ‖ ≤ Bβ)
    (hcone : ∀ ξ ∈ tsupport β, |ξ 0| ≤ Cβ * ‖spatialPart ξ‖)
    (Pbase Bbase Ophysical : ℕ → ℝ)
    (hPbase : ∀ k, 0 ≤ Pbase k) (hBbase : ∀ k, 0 ≤ Bbase k)
    (hOphysical : ∀ k, 0 ≤ Ophysical k)
    {K : Set V} (hK : IsCompact K)
    (δT δI GT GI : ℝ) (hδT : 0 < δT) (hδI : 0 < δI)
    (P₀ H W O Qt Qs Qg Qb Qi : ℕ → ℝ)
    (hP₀ : ∀ j, 0 ≤ P₀ j)
    (hQt : ∀ j, 0 ≤ Qt j) (hQs : ∀ j, 0 ≤ Qs j) (hQg : ∀ j, 0 ≤ Qg j)
    (hQb : ∀ j, 0 ≤ Qb j) (hQi : ∀ j, 0 ≤ Qi j)
    (hH : ∀ j, 0 ≤ H j) (hW : ∀ j, 0 ≤ W j)
    (hO : ∀ j, 0 ≤ O j)
    (Y : Set E) (hY : IsCompact Y)
    (ψ : E → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hsψ : HasCompactSupport ψ)
    (hψb : ∀ x, ‖ψ x‖ ≤ 1)
    (θ : ℝ → ℂ) (hθ : ContDiff ℝ ∞ θ) (hsθ : HasCompactSupport θ)
    (hθone : ∀ r ∈ Icc 0 Δ, θ r = 1)
    (Dglobal : AmplitudeProfiles) {Kglobal : Set (JointVariables E)} (hKglobal : IsCompact Kglobal) :
    ∃ (bFixed : ℕ) (Cq Cpair Creal : ℕ → ℝ),
      (∀ N, 0 ≤ Cq N) ∧ (∀ N, 0 ≤ Cpair N) ∧ (∀ N, 0 ≤ Creal N) ∧
    ∀ (mi mo : LocalizerSymbol (d + 1)),
    ContDiff ℝ ∞ mi → ContDiff ℝ ∞ mo → (∀ p, mo p ∈ Icc (0 : ℝ) 1) →
    HasCompactSupport mi → HasCompactSupport mo →
    (∀ y, tsupport (fun η ↦ mi (y, η)) ⊆ frequencyAnnulus a₀ b₀) →
    (∀ y η, ‖mi (y, η)‖ ≤ Ci) →
    ∀ (Ψoriginal : TwoTimePhase d),
    ∀ (ρ L : ℝ) (hρ : 1 ≤ ρ) (hL : 1 ≤ L)
      (Ac : E → Fin (d + 1) → Mat) (Bc : E → Mat)
      (W₀ W₁ : TwoTimeAmplitude d q) (branch : Bool)
      (Ψ : TwoTimePhase d) (_hauxPhase : ContDiff ℝ ∞ (SymbolBudgets.jointPhase Ψ))
      (Aoriginal : E → Fin (d + 1) → Mat) (Boriginal : E → Mat)
      (W₀original W₁original : TwoTimeAmplitude d q),
    let b := directRetardedAmplitudes Ac Bc W₀ W₁ branch
    ContDiff ℝ ∞ (SymbolBudgets.jointAmplitude b) →
    (∀ r ∈ Icc 0 Δ, elapsedAmplitude b χout χsource β r =
      elapsedAmplitude (directRetardedAmplitudes Aoriginal Boriginal W₀original W₁original branch)
        χout χsource β r) →
    ∀ (Up Ua : Set (SymbolBudgets.TwoTimePoint d)),
    IsOpen Up → ContDiffOn ℝ ∞ (SymbolBudgets.jointPhase Ψ) Up →
    (∀ η v, (v, η) ∈ Up → ∀ k, 1 ≤ k →
      ‖iteratedFDeriv ℝ (k + 1)
        (fun w : ℝ × ℝ × Euclidean d ↦ Ψ w.1 w.2.1 w.2.2 η) v‖ ≤
          ‖η‖ * Pbase k * L ^ k) →
    (∀ p ∈ Ua, ∀ k, ‖iteratedFDeriv ℝ k (SymbolBudgets.jointAmplitude b) p‖ ≤
      (1 + ‖p.2‖) ^ s * Bbase k * L ^ (k + offset)) →
    (∀ r ∈ Icc 0 Δ, ∀ low j, ∀ ξ ∈ normalizedGraphCarrier ρ low j,
      ∀ z ∈ tsupport χout ×ˢ tsupport χsource,
        β (ρ • ξ) ≠ 0 → SymbolBudgets.elapsedPoint r (z, ρ • ξ) ∈ Ua) →
    ∀ (hoBound : ∀ x ζ k, ‖iteratedFDeriv ℝ k (fun t ↦ mo (t, ζ)) x‖ ≤
      Ophysical k * L ^ (k + bo))
    (hψmask : ∀ (backward : Bool) x,
      x ∈ (if backward then tsupport χsource else tsupport χout) → ψ x = 1)
    (hψmo : ∀ x ∈ Prod.fst '' tsupport mo, ψ x = 1)
    (hinputSupport : Prod.fst '' tsupport mi ⊆ Y)
    (_hphaseAgree : ∀ r ∈ Icc 0 Δ, ∀ x z ξ,
      elapsedAmplitude b χout χsource β r x z ξ ≠ 0 →
        elapsedPhase Ψ r x ξ = elapsedPhase Ψoriginal r x ξ)
    (hs : ∀ backward y, y ∈ Prod.fst '' tsupport mi → ∀ low j k,
      IsComparablePair c C a₀ b₀ ρ low j k →
      tsupport (fun p : V ↦ θ p.1 • jointElapsedAmplitude backward ρ b χout χsource β
        mi (fun _ ↦ 0) (graphBranchCutoff low j) (outputCutoff k) 0 y p) ⊆ K)
    (a T : ℝ) (hb : ∀ t t' u η, t' ≤ a → b t t' u η = 0)
    (hslabOut : ∀ u, T < u 0 → χout u = 0) (hslab : T - a ≤ Δ)
    (χcollar : Bool → E → E → V → ℂ) (UT UI : Bool → E → E → Set V)
    (ε : ℝ) (hε : 0 < ε)
    (hχ : ∀ backward, ∀ x ∈ tsupport ψ, ∀ y ∈ Prod.fst '' tsupport mi,
      ContDiff ℝ ∞ (χcollar backward x y))
    (hUT : ∀ backward, ∀ x ∈ tsupport ψ, ∀ y ∈ Prod.fst '' tsupport mi, IsOpen (UT backward x y))
    (hUI : ∀ backward, ∀ x ∈ tsupport ψ, ∀ y ∈ Prod.fst '' tsupport mi, IsOpen (UI backward x y))
    (hχone : ∀ backward, ∀ x ∈ tsupport ψ, ∀ y ∈ Prod.fst '' tsupport mi,
      ∀ p, |p.1| < ε → χcollar backward x y p = 1)
    (hχT : ∀ backward, ∀ x ∈ tsupport ψ, ∀ y ∈ Prod.fst '' tsupport mi,
      elapsedOutputJetCarrier K mi mo x y ∩ tsupport (χcollar backward x y) ⊆ UT backward x y)
    (hχI : ∀ backward, ∀ x ∈ tsupport ψ, ∀ y ∈ Prod.fst '' tsupport mi,
      (elapsedOutputJetCarrier K mi mo x y ∩ tsupport (1 - χcollar backward x y)) ∩
        {p | 0 < p.1} ⊆ UI backward x y)
    (hgapT : ∀ backward, ∀ x ∈ tsupport ψ, ∀ y ∈ Prod.fst '' tsupport mi,
      ∀ r, 0 ≤ r → ∀ p, (r, p) ∈ UT backward x y →
      δT ≤ phaseGradientSquare eT (fun w ↦ jointElapsedPhase backward
        (SymbolBudgets.normalizedTwoTimePhase ρ Ψ) x y (r, w)) p)
    (hupperT : ∀ backward, ∀ x ∈ tsupport ψ, ∀ y ∈ Prod.fst '' tsupport mi,
      ∀ r, 0 ≤ r → ∀ p, (r, p) ∈ UT backward x y →
      ‖fderiv ℝ (jointElapsedPhase backward
        (SymbolBudgets.normalizedTwoTimePhase ρ Ψ) x y) (r, p)‖ ≤ GT)
    (hgapI : ∀ backward, ∀ x ∈ tsupport ψ, ∀ y ∈ Prod.fst '' tsupport mi,
      ∀ p ∈ UI backward x y ∩ {p | 0 < p.1},
      δI ≤ phaseGradientSquare eI (jointElapsedPhase backward
        (SymbolBudgets.normalizedTwoTimePhase ρ Ψ) x y) p)
    (hupperI : ∀ backward, ∀ x ∈ tsupport ψ, ∀ y ∈ Prod.fst '' tsupport mi,
      ∀ p ∈ UI backward x y ∩ {p | 0 < p.1},
      ‖fderiv ℝ (jointElapsedPhase backward
        (SymbolBudgets.normalizedTwoTimePhase ρ Ψ) x y) p‖ ≤ GI)
    (hprimitivePhase : ∀ x ∈ tsupport ψ, ∀ y ∈ Prod.fst '' tsupport mi,
      ∀ p ∈ elapsedOutputJetCarrier K mi mo x y, ∀ j,
      ‖iteratedFDeriv ℝ j (fderiv ℝ (SymbolBudgets.jointPhase
        (SymbolBudgets.normalizedTwoTimePhase ρ Ψ))) (elapsedJointCoordinates p)‖ ≤
          P₀ j * L ^ j)
    (hχbound : ∀ backward, ∀ x ∈ tsupport ψ, ∀ y ∈ Prod.fst '' tsupport mi,
      ∀ p ∈ elapsedOutputJetCarrier K mi mo x y, ∀ j,
      ‖iteratedFDeriv ℝ j (χcollar backward x y) p‖ ≤ H j)
    (hw : ∀ x ∈ tsupport ψ, ∀ y ∈ Prod.fst '' tsupport mi,
      ∀ p ∈ elapsedOutputJetCarrier K mi mo x y, ∀ j,
      ‖iteratedFDeriv ℝ j outputJointWave (0, p.2.2.2.2)‖ ≤ W j)
    (hmo : ∀ x ∈ tsupport ψ, ∀ y ∈ Prod.fst '' tsupport mi,
      ∀ p ∈ elapsedOutputJetCarrier K mi mo x y, ∀ j,
      ‖iteratedFDeriv ℝ j mo (x, p.2.2.2.2)‖ ≤ O j * L ^ (j + bo))
    (hprimitiveMasks : ∀ x ∈ tsupport ψ, ∀ y ∈ Prod.fst '' tsupport mi,
      ∀ p ∈ elapsedOutputJetCarrier K mi mo x y, ∀ l,
      ‖iteratedFDeriv ℝ l (fun w : V ↦ χout w.2.1.1) p‖ ≤ Qt l * L ^ (l + bt) ∧
      ‖iteratedFDeriv ℝ l (fun w : V ↦ χsource w.2.1.2) p‖ ≤ Qs l * L ^ (l + bs) ∧
      ‖iteratedFDeriv ℝ l (fun w : V ↦ β (ρ • w.2.2.1)) p‖ ≤ Qg l * L ^ (l + bg) ∧
      ‖iteratedFDeriv ℝ l (normalizedElapsedSymbol ρ b) p‖ ≤ ρ ^ s * Qb l * L ^ (l + bb) ∧
      ‖iteratedFDeriv ℝ l (fun w : V ↦ (mi (y, w.2.2.2.1) : ℂ)) p‖ ≤ Qi l * L ^ (l + bi))
    (Vphase : ℝ → Set (E × E)) (Kphase : ℝ → Bool → ℕ → Set (E × E))
    (g : ℝ → E → E → E)
    (hVphase : ∀ r ∈ Icc 0 Δ, IsOpen (Vphase r))
    (hKphase : ∀ r ∈ Icc 0 Δ, ∀ low j, IsCompact (Kphase r low j))
    (hKV : ∀ r ∈ Icc 0 Δ, ∀ low j, Kphase r low j ⊆ Vphase r)
    (hSphase : ∀ r ∈ Icc 0 Δ,
      ContDiffOn ℝ ∞ (Function.uncurry (elapsedPhase Ψ r)) (Vphase r))
    (hcarrier : ∀ r ∈ Icc 0 Δ, ∀ low j, ∀ ξ ∈ normalizedGraphCarrier ρ low j,
      ∀ z ∈ tsupport (fun z : E × E ↦ elapsedAmplitude b χout χsource β r z.1 z.2 (ρ • ξ)),
        (z.1, ρ • ξ) ∈ Kphase r low j ∧ SymbolBudgets.elapsedPoint r (z, ρ • ξ) ∈ Up)
    (hg : ∀ r ∈ Icc 0 Δ, ∀ u ξ, (u, ξ) ∈ Vphase r →
      fderiv ℝ (fun t ↦ elapsedPhase Ψ r t ξ) u = innerSL ℝ (g r u ξ))
    (hcomp : ∀ r ∈ Icc 0 Δ, ∀ u ξ, (u, ξ) ∈ Vphase r →
      c * ‖ξ‖ ≤ ‖g r u ξ‖ ∧ ‖g r u ξ‖ ≤ C * ‖ξ‖)
    (hglobalGrades : ∀ backward low j k, IsComparablePair c C a₀ b₀ ρ low j k →
      ∀ r ∈ Icc 0 Δ, ∀ y, HasAmplitudeGrades Dglobal ρ (ρ ^ s) L
        (orientedElapsedAmplitude backward b χout χsource β r) mi (fun _ ↦ 0)
        (graphBranchCutoff low j) (outputCutoff k) 0 y Kglobal)
    (hglobalSupport : ∀ backward low j k, IsComparablePair c C a₀ b₀ ρ low j k →
      ∀ r ∈ Icc 0 Δ, ∀ y, tsupport (jointAmplitude ρ
        (orientedElapsedAmplitude backward b χout χsource β r) mi (fun _ ↦ 0)
        (graphBranchCutoff low j) (outputCutoff k) 0 y) ⊆ Kglobal)
    (F : Set E) (hF : IsClosed F) (hzero : (0 : E) ∉ F) (hβF : tsupport β ⊆ F)
    (χ : ℕ → E → ℂ)
    (hχeq : ∀ (A : FullAmplitude (d + 1) q), (∀ x y ξ, ξ ∉ F → A x y ξ = 0) →
      ∀ j, frequencyCutFullAmplitude (χ j) A =
        frequencyCutFullAmplitude (complexPhysicalCutoff j) A)
    (Treg : ℕ → ℝ → Hspace →L[ℂ] Hspace)
    (hreal : ∀ j r, r ∈ Icc 0 Δ → ∀ u : graphTestSpace (d + 1) q,
      Treg j r (graphTestToLp u) =ᵐ[volume] graphTestOutput (elapsedPhase Ψoriginal r)
        (frequencyCutFullAmplitude (χ j) (elapsedAmplitude (directRetardedAmplitudes Aoriginal Boriginal W₀original W₁original branch) χout χsource β r)) u)
    (hrealAdj : ∀ j r, r ∈ Icc 0 Δ → ∀ u : graphTestSpace (d + 1) q,
      (Treg j r).adjoint (graphTestToLp u) =ᵐ[volume] fun z ↦ WithLp.toLp 2
        (reverseGraphOperator (elapsedPhase Ψoriginal r)
          (frequencyCutFullAmplitude (fun ξ ↦ star (χ j ξ))
            (fun x z ξ ↦ (elapsedAmplitude (directRetardedAmplitudes Aoriginal Boriginal W₀original W₁original branch) χout χsource β r x z ξ).conjTranspose))
          (fun x ↦ (u.val x).ofLp) z))
    (hm : ∀ j u, AEStronglyMeasurable (fun r ↦ Treg j r u) (volume.restrict (Icc 0 Δ)))
    (hmAdj : ∀ j u, AEStronglyMeasurable (fun r ↦ (Treg j r).adjoint u)
      (volume.restrict (Icc 0 Δ)))
    {LOW : ℝ} (hbound : ∀ j r, r ∈ Icc 0 Δ → ‖Treg j r‖ ≤ LOW)
    (hlim : ∀ r ∈ Icc 0 Δ, ∀ u, Tendsto (fun j ↦ Treg j r u) atTop
      (𝓝 (elapsedGraph Ψoriginal (directRetardedAmplitudes Aoriginal Boriginal W₀original W₁original branch) χout χsource β r u)))
    (hlimAdj : ∀ r ∈ Icc 0 Δ, ∀ u, Tendsto (fun j ↦ (Treg j r).adjoint u) atTop
      (𝓝 ((elapsedGraph Ψoriginal (directRetardedAmplitudes Aoriginal Boriginal W₀original W₁original branch) χout χsource β r).adjoint u))),
    ∀ Mi Mo Q : Hspace →L[ℂ] Hspace,
      (∀ u : Hspace, Mi u =ᵐ[volume] fun x ↦ WithLp.toLp 2
        (rightLocalizer ρ mi (fun y ↦ (u y).ofLp) x)) →
      (∀ u : Hspace, (∀ i, Integrable (fun y ↦ u y i)) → Mo u =ᵐ[volume]
        fun x ↦ WithLp.toLp 2 (leftLocalizer ρ mo (fun y ↦ (u y).ofLp) x)) →
      (∀ u, Q u = elapsedGraphIntegral Δ Ψoriginal
        (directRetardedAmplitudes Aoriginal Boriginal W₀original W₁original branch)
        χout χsource β u) →
      ‖Q‖ ≤ Δ * LOW ∧ (∀ u, Q u = elapsedGraphIntegral Δ Ψoriginal
        (directRetardedAmplitudes Aoriginal Boriginal W₀original W₁original branch)
        χout χsource β u) ∧
      (∀ u, Q.adjoint u = ∫ r in Icc 0 Δ, (elapsedGraph Ψoriginal
          (directRetardedAmplitudes Aoriginal Boriginal W₀original W₁original branch)
          χout χsource β r).adjoint u) ∧
      (∀ N (backward : Bool) u,
        MemVectorFourierSobolev (m : ℝ) ((1 - Mo) ((if backward then Q.adjoint else Q) (Mi u))) ∧
        vectorFourierSobolevNorm (m : ℝ) ((1 - Mo) ((if backward then Q.adjoint else Q) (Mi u))) ≤
          Cq N * ρ ^ ((m : ℝ) + (max 0 s + (3 * (d + 1) : ℕ))) *
            L ^ bFixed * (L / ρ) ^ N * ‖u‖) ∧
      ∀ (_hieven : ∀ y ξ, mi (y, -ξ) = mi (y, ξ))
        (_hoeven : ∀ y ξ, mo (y, -ξ) = mo (y, ξ))
        (N : ℕ) (backward : Bool) (U : Set E) (hU : MeasurableSet U),
        let T := if backward then Q.adjoint else Q
        (∀ u : Hspace, restrictL2 U ((1 - Mo) ((T + boundedConjugate T) (Mi u))) ∈
          (restrictionSobolevScale U (EuclideanSpace ℂ (Fin q)) hU).level m ∧
        (restrictionSobolevScale U (EuclideanSpace ℂ (Fin q)) hU).gradeNorm m
          (restrictL2 U ((1 - Mo) ((T + boundedConjugate T) (Mi u)))) ≤
          Cpair N * ρ ^ ((m : ℝ) + (max 0 s + (3 * (d + 1) : ℕ))) *
            L ^ bFixed * (L / ρ) ^ N * ‖u‖) ∧
        ∀ u : Lp (EuclideanSpace ℝ (Fin q)) 2 (volume : Measure E),
          let v := l2RealPart (volume.restrict U)
            (restrictL2 U ((1 - Mo) ((T + boundedConjugate T) (Mi (l2ComplexInclusion volume u)))))
          v ∈ (restrictionSobolevScale U (EuclideanSpace ℝ (Fin q)) hU).level m ∧
          (restrictionSobolevScale U (EuclideanSpace ℝ (Fin q)) hU).gradeNorm m v ≤
            Creal N * ρ ^ ((m : ℝ) + (max 0 s + (3 * (d + 1) : ℕ))) *
              L ^ bFixed * (L / ρ) ^ N * ‖u‖ := by
  classical
  obtain ⟨bFixed, Cq, hCq, hbound⟩ :=
    exists_directResidual_integral_fourier_bound_of_primitive_grades
      eT eI eu ez J hJ s Δ hΔ m bo offset bt bs bg bb bi c C b₀ hc ha₀ hCi
      χout χsource β hχout hχsource hβsmooth hout hsource hBβ hCβ hβ hcone
      Pbase Bbase Ophysical hPbase hBbase hOphysical hK δT δI GT GI hδT hδI
      P₀ H W O Qt Qs Qg Qb Qi hP₀ hQt hQs hQg hQb hQi hH hW hO
      Y hY ψ hψ hsψ hψb θ hθ hsθ hθone Dglobal hKglobal
  obtain ⟨Kpair, hKpair, hpair⟩ := exists_physicalPair_fourier_restriction_comparison d q m
  obtain ⟨Kreal, hKreal, hrealPair⟩ := exists_realPhysicalPair_fourier_restriction_comparison d q m
  refine ⟨bFixed, Cq, fun N ↦ Kpair * Cq N, fun N ↦ Kreal * Cq N, hCq,
    fun N ↦ mul_nonneg hKpair.le (hCq N), fun N ↦ mul_nonneg hKreal.le (hCq N), ?_⟩
  intro mi mo hi ho horange his hos hiAnn hiBound Ψoriginal ρ L hρ hL Ac Bc W₀ W₁ branch Ψ hauxPhase Aoriginal Boriginal W₀original W₁original b
    haux heqOriginal Up Ua hUp hΨ hpbase haGrade haMap hoBound
    hψmask hψmo hinputSupport hphaseAgree hs a T hb hslabOut hslab
    χcollar UT UI ε hε hχ hUT hUI hχone hχT hχI hgapT hupperT hgapI hupperI
    hprimitivePhase hχbound hw hmo hprimitiveMasks
    Vphase Kphase g hVphase hKphase hKV hSphase hcarrier hg hcomp
    hglobalGrades hglobalSupport F hF hzero hβF χreg hχeq Treg hreal hrealAdj
    hm hmAdj LOW hLOW hlim hlimAdj Mi Mo Q hMi hMo hQid
  have hSc := contDiff_elapsedPhase_joint_of_twoTimePhase Ψ hauxPhase
  have hgraph r (hr : r ∈ Icc 0 Δ) :
      elapsedGraph Ψ (directRetardedAmplitudes Aoriginal Boriginal W₀original W₁original branch)
        χout χsource β r =
      elapsedGraph Ψoriginal (directRetardedAmplitudes Aoriginal Boriginal W₀original W₁original branch)
        χout χsource β r := by
    apply FullLowBounds.fullGraphOperator_phase_congr
    intro x z ξ hne
    apply hphaseAgree r hr x z ξ
    simpa only [heqOriginal r hr] using hne
  have hgraphAux r (hr : r ∈ Icc 0 Δ) :
      elapsedGraph Ψ b χout χsource β r =
      elapsedGraph Ψoriginal
        (directRetardedAmplitudes Aoriginal Boriginal W₀original W₁original branch)
        χout χsource β r := by
    rw [← hgraph r hr]
    unfold elapsedGraph
    rw [heqOriginal r hr]
  have hforward j r (hr : r ∈ Icc 0 Δ) :
      graphTestOutput (elapsedPhase Ψ r)
          (frequencyCutFullAmplitude (χreg j) (elapsedAmplitude b χout χsource β r)) =
        graphTestOutput (elapsedPhase Ψoriginal r)
          (frequencyCutFullAmplitude (χreg j) (elapsedAmplitude
            (directRetardedAmplitudes Aoriginal Boriginal W₀original W₁original branch)
            χout χsource β r)) := by
    rw [← heqOriginal r hr]
    apply graphTestOutput_phase_congr
    intro x z ξ hne
    exact hphaseAgree r hr x z ξ (fun hz ↦ hne (by
      simp only [frequencyCutFullAmplitude, hz, smul_zero]))
  have hreverse j r (hr : r ∈ Icc 0 Δ) (v : E → Fin q → ℂ) :
      reverseGraphOperator (elapsedPhase Ψ r)
          (frequencyCutFullAmplitude (fun ξ ↦ star (χreg j ξ))
            (fun x z ξ ↦ (elapsedAmplitude b χout χsource β r x z ξ).conjTranspose)) v =
        reverseGraphOperator (elapsedPhase Ψoriginal r)
          (frequencyCutFullAmplitude (fun ξ ↦ star (χreg j ξ))
            (fun x z ξ ↦ (elapsedAmplitude
              (directRetardedAmplitudes Aoriginal Boriginal W₀original W₁original branch)
              χout χsource β r x z ξ).conjTranspose)) v := by
    rw [← heqOriginal r hr]
    apply FourierIntegral.reverseGraphOperator_phase_congr
    intro x z ξ hne
    exact hphaseAgree r hr x z ξ (fun hz ↦ hne (by
      simp only [frequencyCutFullAmplitude, hz, Matrix.conjTranspose_zero, smul_zero]))
  obtain ⟨Mi', Mo', Q', hMi', hMo', hQ', hQeq', hQadj', hleak⟩ := hbound
    ρ L hρ hL Ac Bc W₀ W₁ branch Ψ Aoriginal Boriginal W₀original W₁original
    haux heqOriginal Up Ua hUp hΨ hpbase haGrade haMap mi mo hi ho horange his hos
    hiAnn hiBound hoBound hψmask hψmo hinputSupport hSc.continuous
    (fun r _ u ξ _ ↦ (hSc.comp (contDiff_const.prodMk contDiff_id)).contDiffAt)
    (Jphase := Set.univ) (Wphase := Set.univ) isClosed_univ isOpen_univ (Subset.refl _)
    hauxPhase.contDiffOn (fun _ _ _ _ _ _ ↦ Set.mem_univ _) (fun _ _ _ _ _ _ ↦ Set.mem_univ _) hs a T hb hslabOut hslab
    χcollar UT UI ε hε hχ hUT hUI hχone hχT hχI hgapT hupperT hgapI hupperI
    hprimitivePhase hχbound
    hw hmo hprimitiveMasks Vphase Kphase g hVphase hKphase hKV hSphase hcarrier hg hcomp
    hglobalGrades hglobalSupport F hF hzero hβF χreg hχeq Treg
    (fun j r hr u ↦ by rw [hforward j r hr]; exact hreal j r hr u)
    (fun j r hr u ↦ (hrealAdj j r hr u).trans (Filter.Eventually.of_forall
      (fun z ↦ congrArg (fun v : E → Fin q → ℂ ↦ WithLp.toLp 2 (v z))
        (hreverse j r hr (fun x ↦ (u.val x).ofLp)).symm)))
    hm hmAdj hLOW
    (fun r hr u ↦ by rw [hgraphAux r hr]; exact hlim r hr u)
    (fun r hr u ↦ by rw [hgraphAux r hr]; exact hlimAdj r hr u)
  have hei : Mi' = Mi := eq_of_rightLocalizer_representatives ρ mi Mi' Mi hMi' hMi
  have heo : Mo' = Mo := eq_of_leftLocalizer_representatives ρ mo Mo' Mo hMo' hMo
  have hQoriginal u : Q' u = elapsedGraphIntegral Δ Ψoriginal
      (directRetardedAmplitudes Aoriginal Boriginal W₀original W₁original branch)
      χout χsource β u := by
    rw [hQeq' u]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    rw [hgraph r hr]
  have hQadjOriginal u : Q'.adjoint u = ∫ r in Icc 0 Δ,
      (elapsedGraph Ψoriginal (directRetardedAmplitudes Aoriginal Boriginal W₀original W₁original branch)
        χout χsource β r).adjoint u := by
    rw [hQadj' u]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    rw [hgraph r hr]
  have heq : Q' = Q := ContinuousLinearMap.ext (fun u ↦ (hQoriginal u).trans (hQid u).symm)
  subst Mi'
  subst Mo'
  subst Q'
  refine ⟨hQ', hQoriginal, hQadjOriginal, hleak, ?_⟩
  intro hieven hoeven N backward U hU T
  have hisReal := boundedRightLocalizer_star_of_even ρ mi hieven Mi hMi
  have hosReal := boundedLeftLocalizer_star_of_even
    (ne_of_gt (zero_lt_one.trans_le hρ)) mo ho.continuous hos hoeven Mo hMo
  constructor
  · intro u
    obtain ⟨hm, hn⟩ := hpair U hU T Mi Mo hisReal hosReal
      (Cq N * ρ ^ ((m : ℝ) + (max 0 s + (3 * (d + 1) : ℕ))) *
        L ^ bFixed * (L / ρ) ^ N) (hleak N backward) u
    exact ⟨hm, by simpa only [mul_assoc] using hn⟩
  · intro u
    have hnonneg : 0 ≤ Cq N * ρ ^ ((m : ℝ) + (max 0 s + (3 * (d + 1) : ℕ))) *
        L ^ bFixed * (L / ρ) ^ N := by
      have := hCq N
      have : 0 ≤ ρ := (zero_le_one.trans hρ)
      have : 0 ≤ L := (zero_le_one.trans hL)
      positivity
    obtain ⟨hm, hn⟩ := hrealPair U hU T Mi Mo hisReal hosReal
      (Cq N * ρ ^ ((m : ℝ) + (max 0 s + (3 * (d + 1) : ℕ))) *
        L ^ bFixed * (L / ρ) ^ N) hnonneg (hleak N backward) u
    exact ⟨hm, by simpa only [mul_assoc] using hn⟩


end JanetCartan.ArbitraryAccuracy.ResidualLocalization.UniformSupported
