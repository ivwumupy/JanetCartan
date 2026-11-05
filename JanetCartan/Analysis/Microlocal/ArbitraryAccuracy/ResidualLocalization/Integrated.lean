module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.Noncomparable
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.BufferedCollar
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.UniformEstimate

/-!
# Integrated leakage for the literal direct residual amplitudes

Source: `app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`, and
`app:ch_regular_base:eq:energy-complete-residual`.

This deduction instantiates the integrated localization producer for either
literal `directRetardedAmplitudes` branch. Both orientations use the SAME
identified elapsed integral and physical localizers at every accuracy.
Noncomparable differentiated kernels, global shell majorants, summability,
Fourier membership and strong identification are conclusions, not premises.

The remaining joint phase/amplitude grades are the exact interfaces of
`EvolutionIntegratedLocalization.PhaseGrades` and `AmplitudeGrades`.
The collar data below are the output of
`ResidualLocalization.exists_buffered_supportedPhase_collar_data`; their
finite-family instantiation remains explicit. Finite realizations, LOW and
strong limits come from the `EvolutionIntegral` primitive graph producer.
The supported auxiliary masked identity is supplied by
`ResidualCoordinates.Assembly.completeResidual_of_selected_physical_chart`.
No fixed-time zero-energy graph separation is used.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.ResidualLocalization
open FourierIntegral CharacteristicTransport.CompleteResidual
open FiniteChain.Graph KernelEstimates PhysicalShells CartesianJets KernelLimits
open PhysicalShells.Noncomparable
open FiniteChain.Retarded.KernelDecay FiniteChain.Retarded.HalfSpace JanetCartan.Localization
open RegularSector.Characteristic.EvolutionIntegral
open EvolutionLocalization.SobolevRealization Pseudodifferential EvolutionIntegratedLocalization
open LowBounds LowBounds.FrequencyCutoff FiniteChain.Retarded.KernelSobolev
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "V" => ℝ × JointVariables E
local notation "Mat" => Matrix (Fin q) (Fin q) ℂ
local notation "Hspace" => SpacetimeL2 d q
attribute [local instance] KernelLimits.matrixContinuousENorm KernelLimits.matrixPseudoMetrizableSpace
set_option synthInstance.maxSize 256
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

/-- The two direct complete-residual amplitudes, and their literal adjoints,
have the physical `L² → Hᵐ` chain-tail bound, conditional on primitive joint
grades, their buffered collar data and exact realization outputs. The fixed
loss and accuracy profile precede frequency, coefficient scale and the
coefficient family. Neither a per-time kernel estimate nor an integrated
majorant is assumed. Negative orders, the full two-position amplitude and
both physical masks remain literal. Consumer: the retarded-factor `hleak`
input of `finiteChain_observation_rapidDecayAt`
(`app:ch_regular:eq:chain-tail`, `app:ch_regular_base:eq:energy-complete-residual`). -/
theorem exists_directResidual_integral_fourier_bound_of_joint_grades
    {ι κ ιu ιz : Type*} [Fintype ι] [Fintype κ] [Fintype ιu] [Fintype ιz]
    (eT : ι → JointVariables E) (eI : κ → V)
    (eu : OrthonormalBasis ιu ℝ E) (ez : OrthonormalBasis ιz ℝ E)
    (J : (ℝ × (Fin d → ℝ)) ≃L[ℝ] E)
    (hJ : MeasurePreserving (graphInputCoordinates J) volume volume)
    (s Δ : ℝ) (hΔ : 0 ≤ Δ) (m bo ba offset : ℕ)
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
    (P H W O A : ℕ → ℝ)
    (hH : ∀ j, 0 ≤ H j) (hW : ∀ j, 0 ≤ W j)
    (hO : ∀ j, 0 ≤ O j) (hA : ∀ j, 0 ≤ A j)
    (Y : Set E) (hY : IsCompact Y)
    (ψ : E → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hsψ : HasCompactSupport ψ)
    (hψb : ∀ x, ‖ψ x‖ ≤ 1)
    (θ : ℝ → ℂ) (hθ : ContDiff ℝ ∞ θ) (hsθ : HasCompactSupport θ)
    (hθone : ∀ r ∈ Icc 0 Δ, θ r = 1)
    (Dglobal : AmplitudeProfiles) {Kglobal : Set (JointVariables E)} (hKglobal : IsCompact Kglobal) :
    ∃ (bFixed : ℕ) (Cq : ℕ → ℝ), (∀ N, 0 ≤ Cq N) ∧
    ∀ (ρ L : ℝ) (hρ : 1 ≤ ρ) (hL : 1 ≤ L)
      (Ac : E → Fin (d + 1) → Mat) (Bc : E → Mat)
      (W₀ W₁ : TwoTimeAmplitude d q) (branch : Bool)
      (Ψ : TwoTimePhase d) (aux : TwoTimeAmplitude d q),
    let b := directRetardedAmplitudes Ac Bc W₀ W₁ branch
    ContDiff ℝ ∞ (SymbolBudgets.jointAmplitude aux) →
    (∀ r ∈ Icc 0 Δ, elapsedAmplitude aux χout χsource β r =
      elapsedAmplitude b χout χsource β r) →
    ∀ (Up Ua : Set (SymbolBudgets.TwoTimePoint d)),
    IsOpen Up → ContDiffOn ℝ ∞ (SymbolBudgets.jointPhase Ψ) Up →
    (∀ η v, (v, η) ∈ Up → ∀ k, 1 ≤ k →
      ‖iteratedFDeriv ℝ (k + 1)
        (fun w : ℝ × ℝ × Euclidean d ↦ Ψ w.1 w.2.1 w.2.2 η) v‖ ≤
          ‖η‖ * Pbase k * L ^ k) →
    (∀ p ∈ Ua, ∀ k, ‖iteratedFDeriv ℝ k (SymbolBudgets.jointAmplitude aux) p‖ ≤
      (1 + ‖p.2‖) ^ s * Bbase k * L ^ (k + offset)) →
    (∀ r ∈ Icc 0 Δ, ∀ low j, ∀ ξ ∈ normalizedGraphCarrier ρ low j,
      ∀ z ∈ tsupport χout ×ˢ tsupport χsource,
        β (ρ • ξ) ≠ 0 → SymbolBudgets.elapsedPoint r (z, ρ • ξ) ∈ Ua) →
    ∀ (mi mo : LocalizerSymbol (d + 1))
    (hi : ContDiff ℝ ∞ mi) (ho : ContDiff ℝ ∞ mo)
    (horange : ∀ p, mo p ∈ Icc (0 : ℝ) 1)
    (his : HasCompactSupport mi) (hos : HasCompactSupport mo)
    (hiAnn : ∀ y, tsupport (fun η ↦ mi (y, η)) ⊆ frequencyAnnulus a₀ b₀)
    (hiBound : ∀ y η, ‖mi (y, η)‖ ≤ Ci)
    (hoBound : ∀ x ζ k, ‖iteratedFDeriv ℝ k (fun t ↦ mo (t, ζ)) x‖ ≤
      Ophysical k * L ^ (k + bo))
    (hψmask : ∀ (backward : Bool) x,
      x ∈ (if backward then tsupport χsource else tsupport χout) → ψ x = 1)
    (hψmo : ∀ x ∈ Prod.fst '' tsupport mo, ψ x = 1)
    (hinputSupport : Prod.fst '' tsupport mi ⊆ Y)
    (hSc : Continuous (fun p : ℝ × (E × E) ↦ elapsedPhase Ψ p.1 p.2.1 p.2.2))
    (hS : ∀ r ∈ Icc 0 Δ, ∀ u ξ, ξ ≠ 0 →
      ContDiffAt ℝ ∞ (Function.uncurry (elapsedPhase Ψ r)) (u, ξ))
    (hAmp : ∀ backward, ContDiff ℝ ∞ (fun p : ℝ × ((E × E) × E) ↦
      orientedElapsedAmplitude backward b χout χsource β p.1 p.2.1.1 p.2.1.2 p.2.2))
    {Jphase Wphase : Set (SymbolBudgets.TwoTimePoint d)}
    (hJphase : IsClosed Jphase) (hWphase : IsOpen Wphase) (hJW : Jphase ⊆ Wphase)
    (hPhase : ContDiffOn ℝ ∞ (SymbolBudgets.jointPhase Ψ) Wphase)
    (hPhaseSupport : ∀ r ∈ Icc 0 Δ, ∀ u z ξ,
      elapsedAmplitude b χout χsource β r u z ξ ≠ 0 →
        ((u 0, u 0 - r, spatialPart u), spatialPart ξ) ∈ Jphase)
    (hmap : ∀ x ∈ tsupport ψ, ∀ y ∈ Prod.fst '' tsupport mi,
      ∀ p ∈ elapsedOutputJetCarrier K mi mo x y,
        ((elapsedJointCoordinates p).1, ρ • (elapsedJointCoordinates p).2) ∈ Jphase)
    (hs : ∀ backward y, y ∈ Prod.fst '' tsupport mi → ∀ low j k,
      IsComparablePair c C a₀ b₀ ρ low j k →
      tsupport (fun p : V ↦ θ p.1 • jointElapsedAmplitude backward ρ b χout χsource β
        mi (fun _ ↦ 0) (graphBranchCutoff low j) (outputCutoff k) 0 y p) ⊆ K)
    (a T : ℝ) (hb : ∀ t t' u η, t' ≤ a → b t t' u η = 0)
    (hslabOut : ∀ u, T < u 0 → χout u = 0) (hslab : T - a ≤ Δ)
    (χ : Bool → E → E → V → ℂ) (UT UI : Bool → E → E → Set V)
    (ε : ℝ) (hε : 0 < ε)
    (hχ : ∀ backward, ∀ x ∈ tsupport ψ, ∀ y ∈ Prod.fst '' tsupport mi,
      ContDiff ℝ ∞ (χ backward x y))
    (hUT : ∀ backward, ∀ x ∈ tsupport ψ, ∀ y ∈ Prod.fst '' tsupport mi, IsOpen (UT backward x y))
    (hUI : ∀ backward, ∀ x ∈ tsupport ψ, ∀ y ∈ Prod.fst '' tsupport mi, IsOpen (UI backward x y))
    (hχone : ∀ backward, ∀ x ∈ tsupport ψ, ∀ y ∈ Prod.fst '' tsupport mi,
      ∀ p, |p.1| < ε → χ backward x y p = 1)
    (hχT : ∀ backward, ∀ x ∈ tsupport ψ, ∀ y ∈ Prod.fst '' tsupport mi,
      elapsedOutputJetCarrier K mi mo x y ∩ tsupport (χ backward x y) ⊆ UT backward x y)
    (hχI : ∀ backward, ∀ x ∈ tsupport ψ, ∀ y ∈ Prod.fst '' tsupport mi,
      (elapsedOutputJetCarrier K mi mo x y ∩ tsupport (1 - χ backward x y)) ∩
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
    (hp : ∀ backward, ∀ x ∈ tsupport ψ, ∀ y ∈ Prod.fst '' tsupport mi,
      ∀ p ∈ elapsedOutputJetCarrier K mi mo x y, ∀ j,
      ‖iteratedFDeriv ℝ j (fderiv ℝ (jointElapsedPhase backward
        (SymbolBudgets.normalizedTwoTimePhase ρ Ψ) x y)) p‖ ≤ P j * L ^ j)
    (hχbound : ∀ backward, ∀ x ∈ tsupport ψ, ∀ y ∈ Prod.fst '' tsupport mi,
      ∀ p ∈ elapsedOutputJetCarrier K mi mo x y, ∀ j,
      ‖iteratedFDeriv ℝ j (χ backward x y) p‖ ≤ H j)
    (hw : ∀ x ∈ tsupport ψ, ∀ y ∈ Prod.fst '' tsupport mi,
      ∀ p ∈ elapsedOutputJetCarrier K mi mo x y, ∀ j,
      ‖iteratedFDeriv ℝ j outputJointWave (0, p.2.2.2.2)‖ ≤ W j)
    (hmo : ∀ x ∈ tsupport ψ, ∀ y ∈ Prod.fst '' tsupport mi,
      ∀ p ∈ elapsedOutputJetCarrier K mi mo x y, ∀ j,
      ‖iteratedFDeriv ℝ j mo (x, p.2.2.2.2)‖ ≤ O j * L ^ (j + bo))
    (hab : ∀ backward low j k, IsComparablePair c C a₀ b₀ ρ low j k →
      ∀ x ∈ tsupport ψ, ∀ y ∈ Prod.fst '' tsupport mi,
      ∀ p ∈ elapsedOutputJetCarrier K mi mo x y, ∀ l,
      ‖iteratedFDeriv ℝ l (fun w : V ↦ θ w.1 • jointElapsedAmplitude backward ρ b
        χout χsource β mi (fun _ ↦ 0) (graphBranchCutoff low j) (outputCutoff k) 0 y w) p‖ ≤
        ρ ^ s * A l * L ^ (l + ba))
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
      Treg j r (graphTestToLp u) =ᵐ[volume] graphTestOutput (elapsedPhase Ψ r)
        (frequencyCutFullAmplitude (χ j) (elapsedAmplitude b χout χsource β r)) u)
    (hrealAdj : ∀ j r, r ∈ Icc 0 Δ → ∀ u : graphTestSpace (d + 1) q,
      (Treg j r).adjoint (graphTestToLp u) =ᵐ[volume] fun z ↦ WithLp.toLp 2
        (reverseGraphOperator (elapsedPhase Ψ r)
          (frequencyCutFullAmplitude (fun ξ ↦ star (χ j ξ))
            (fun x z ξ ↦ (elapsedAmplitude b χout χsource β r x z ξ).conjTranspose))
          (fun x ↦ (u.val x).ofLp) z))
    (hm : ∀ j u, AEStronglyMeasurable (fun r ↦ Treg j r u) (volume.restrict (Icc 0 Δ)))
    (hmAdj : ∀ j u, AEStronglyMeasurable (fun r ↦ (Treg j r).adjoint u)
      (volume.restrict (Icc 0 Δ)))
    {LOW : ℝ} (hbound : ∀ j r, r ∈ Icc 0 Δ → ‖Treg j r‖ ≤ LOW)
    (hlim : ∀ r ∈ Icc 0 Δ, ∀ u, Tendsto (fun j ↦ Treg j r u) atTop
      (𝓝 (elapsedGraph Ψ b χout χsource β r u)))
    (hlimAdj : ∀ r ∈ Icc 0 Δ, ∀ u, Tendsto (fun j ↦ (Treg j r).adjoint u) atTop
      (𝓝 ((elapsedGraph Ψ b χout χsource β r).adjoint u))),
    ∃ Mi Mo Q : Hspace →L[ℂ] Hspace,
      (∀ u : Hspace, Mi u =ᵐ[volume] fun x ↦ WithLp.toLp 2
        (rightLocalizer ρ mi (fun y ↦ (u y).ofLp) x)) ∧
      (∀ u : Hspace, (∀ i, Integrable (fun y ↦ u y i)) → Mo u =ᵐ[volume]
        fun x ↦ WithLp.toLp 2 (leftLocalizer ρ mo (fun y ↦ (u y).ofLp) x)) ∧
      ‖Q‖ ≤ Δ * LOW ∧ (∀ u, Q u = elapsedGraphIntegral Δ Ψ b χout χsource β u) ∧
      (∀ u, Q.adjoint u = ∫ r in Icc 0 Δ, (elapsedGraph Ψ b χout χsource β r).adjoint u) ∧
      ∀ N (backward : Bool) u,
        MemVectorFourierSobolev (m : ℝ) ((1 - Mo) ((if backward then Q.adjoint else Q) (Mi u))) ∧
        vectorFourierSobolevNorm (m : ℝ) ((1 - Mo) ((if backward then Q.adjoint else Q) (Mi u))) ≤
          Cq N * ρ ^ ((m : ℝ) + (max 0 s + (3 * (d + 1) : ℕ))) *
            L ^ bFixed * (L / ρ) ^ N * ‖u‖ := by
  classical
  have hnoncomp (l : ℕ) := exists_directResidual_noncomparable_kernel_bounds
    (q := q) (C := C) (b₀ := b₀) eu ez hc hCi ha₀ χout χsource β
      hχout hχsource hβsmooth hout hsource hBβ hCβ hβ hcone
      Pbase Bbase Ophysical hPbase hBbase hOphysical s Δ offset bo l
  choose bLoss D hD hnoncomp using hnoncomp
  obtain ⟨Cq, hCq, hbound⟩ :=
    exists_uniform_elapsedGraphIntegral_fourier_bound_of_joint_grades
      (q := q) eT eI J hJ s Δ hΔ m bo ba bLoss c C b₀ ha₀ hK
      δT δI GT GI hδT hδI P H W O A D hH hW hO hA hD
      Y hY ψ hψ hsψ hψb θ hθ hsθ hθone Dglobal hKglobal
  refine ⟨max ((m + bo) + ba) ((Finset.range (m + 1)).sup bLoss), Cq, hCq, ?_⟩
  intro ρ L hρ hL Ac Bc W₀ W₁ branch Ψ aux b haux heq Up Ua hUp hΨ hpbase
    haGrade haMap mi mo hi ho horange his hos hiAnn hiBound hoBound hψmask hψmo
    hinputSupport hSc hS hAmp Jphase Wphase hJphase hWphase hJW hPhase hPhaseSupport
    hmap hs a T hb hslabOut hslab χ UT UI ε hε hχ hUT hUI hχone hχT hχI
    hgapT hupperT hgapI hupperI hp hχbound hw hmo hab
    Vphase Kphase g hVphase hKphase hKV hSphase hcarrier hg hcomp
    hglobalGrades hglobalSupport F hF hzero hβF χreg hχeq Treg hreal hrealAdj
    hm hmAdj LOW hLOW hlim hlimAdj
  have hper (l : ℕ) (backward : Bool) (low : Bool) (j k : ℕ)
      (hsep : SeparatedRanges c C (a₀ * ρ) (b₀ * ρ)
        (graphLower low j) (graphUpper low j) (outputLower k) (outputUpper k))
      (r : ℝ) (hr : r ∈ Icc 0 Δ) (N : ℕ) (x y : E) (v : Fin l → E)
      (hv : ∀ i, ‖v i‖ ≤ 1) :=
    hnoncomp l ρ L hρ hL Ac Bc W₀ W₁ branch Ψ aux haux heq Up Ua hUp hΨ
      hpbase haGrade haMap mi mo hi ho his hiAnn hiBound hoBound
      r hr backward low j k (Vphase r) (Kphase r low j) (g r)
      (hVphase r hr) (hKphase r hr low j) (hKV r hr low j) (hSphase r hr)
      (hcarrier r hr low j) (hg r hr) (hcomp r hr) hsep N x y v hv
  apply hbound ρ L hρ hL Ψ b χout χsource β mi mo hi ho horange his hos hout hsource
    hψmask hψmo hinputSupport hSc hS hAmp hJphase hWphase hJW hPhase hPhaseSupport
    hmap hs a T hb hslabOut hslab χ UT UI ε hε hχ hUT hUI hχone hχT hχI
    hgapT hupperT hgapI hupperI hp hχbound hw hmo hab
    (fun backward l _ N low j k hsep r hr x _ y _ v hv ↦
      hper l backward low j k hsep r hr N x y v hv)
    hglobalGrades hglobalSupport (D 0 0) (hD 0 0) ?_
    F hF hzero hβF χreg hχeq Treg hreal hrealAdj hm hmAdj hLOW hlim hlimAdj
  intro backward low j k hsep r hr x y
  simpa only [iteratedFDeriv_zero_apply, pow_zero, mul_one] using
    hper 0 backward low j k hsep r hr 0 x y (fun i ↦ Fin.elim0 i) (fun i ↦ Fin.elim0 i)

end JanetCartan.ArbitraryAccuracy.ResidualLocalization
