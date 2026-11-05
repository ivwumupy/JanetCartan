module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.Integrated
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.JointGrades

/-!
# Integrated residual leakage from primitive joint grades

This closes the differentiated joint phase/amplitude premises of `Integrated`.
The auxiliary smooth direct branch is exactly the one constructed by
`ResidualCoordinates.Assembly.completeResidual_of_selected_physical_chart`;
its supported masked identity identifies the resulting integral and literal
adjoint with the original conic branch. No smoothness at zero of the original
conic amplitude is imposed. The original supported phase is retained by its
proved smooth extension and germ identities. The collar inputs are supplied
by `FiniteFamilyCollar` after the normalized supported chart is instantiated.
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
set_option maxHeartbeats 6400000
set_option backward.isDefEq.respectTransparency false

private theorem direct_joint_amplitude_smoothness
    (ρ : ℝ) (b : TwoTimeAmplitude d q)
    (χout χsource β : E → ℂ)
    (haux : ContDiff ℝ ∞ (SymbolBudgets.jointAmplitude b))
    (hχout : ContDiff ℝ ∞ χout) (hχsource : ContDiff ℝ ∞ χsource)
    (hβsmooth : ContDiff ℝ ∞ β) :
    ContDiff ℝ ∞ (normalizedElapsedSymbol ρ b) ∧
    ∀ backward, ContDiff ℝ ∞ (fun p : ℝ × ((E × E) × E) ↦
      orientedElapsedAmplitude backward b χout χsource β p.1 p.2.1.1 p.2.1.2 p.2.2) := by
  have hnorm : ContDiff ℝ ∞ (normalizedElapsedSymbol ρ b) :=
    haux.comp (show ContDiff ℝ ∞ (fun p : V ↦
      ((p.2.1.1 0, p.2.1.1 0 - p.1, spatialPart p.2.1.1), spatialPart (ρ • p.2.2.1)))
        from by fun_prop)
  have hAmp : ∀ backward, ContDiff ℝ ∞ (fun p : ℝ × ((E × E) × E) ↦
      orientedElapsedAmplitude backward b χout χsource β p.1 p.2.1.1 p.2.1.2 p.2.2) := by
    have hb' : ContDiff ℝ ∞ (fun p : ℝ × ((E × E) × E) ↦
        b (p.2.1.1 0) (p.2.1.1 0 - p.1) (spatialPart p.2.1.1) (spatialPart p.2.2)) :=
      haux.comp (show ContDiff ℝ ∞ (fun p : ℝ × ((E × E) × E) ↦
        ((p.2.1.1 0, p.2.1.1 0 - p.1, spatialPart p.2.1.1), spatialPart p.2.2))
          from by fun_prop)
    have hmasks : ContDiff ℝ ∞ (fun p : ℝ × ((E × E) × E) ↦
        χout p.2.1.1 * χsource p.2.1.2 * β p.2.2) := by fun_prop
    intro backward
    cases backward
    · exact hmasks.smul hb'
    · let Jc : Mat ≃ₗᵢ[ℝ] Mat := {
        Matrix.conjTransposeLinearEquiv (Fin q) (Fin q) ℝ ℂ with
        norm_map' := Matrix.frobenius_norm_conjTranspose }
      exact Jc.contDiff.comp (hmasks.smul hb')
  exact ⟨hnorm, hAmp⟩

/-- Derive joint phase and amplitude grades, all noncomparable kernels and
integrated shell majorants for the original direct complete-residual branch.
The only derivative bounds below are for the primitive normalized two-time
phase, auxiliary symbol and individual masks. Their producers are
`EvolutionIntegral.SymbolBudgets`, `ResidualCoordinates.Assembly` and the
protected-mask construction; finite realization and strong limits are the
`EvolutionIntegral` outputs. The same identified operators and proof localizers
work at every accuracy, with fixed frequency and coefficient losses.
Consumer: the retarded `hleak` in `finiteChain_observation_rapidDecayAt`
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`,
`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem exists_directResidual_integral_fourier_bound_of_primitive_grades
    {ι κ ιu ιz : Type*} [Fintype ι] [Fintype κ] [Fintype ιu] [Fintype ιz]
    (eT : ι → JointVariables E) (eI : κ → V)
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
    ∃ (bFixed : ℕ) (Cq : ℕ → ℝ), (∀ N, 0 ≤ Cq N) ∧
    ∀ (ρ L : ℝ) (hρ : 1 ≤ ρ) (hL : 1 ≤ L)
      (Ac : E → Fin (d + 1) → Mat) (Bc : E → Mat)
      (W₀ W₁ : TwoTimeAmplitude d q) (branch : Bool)
      (Ψ : TwoTimePhase d)
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
    (hprimitivePhase : ∀ x ∈ tsupport ψ, ∀ y ∈ Prod.fst '' tsupport mi,
      ∀ p ∈ elapsedOutputJetCarrier K mi mo x y, ∀ j,
      ‖iteratedFDeriv ℝ j (fderiv ℝ (SymbolBudgets.jointPhase
        (SymbolBudgets.normalizedTwoTimePhase ρ Ψ))) (elapsedJointCoordinates p)‖ ≤
          P₀ j * L ^ j)
    (hχbound : ∀ backward, ∀ x ∈ tsupport ψ, ∀ y ∈ Prod.fst '' tsupport mi,
      ∀ p ∈ elapsedOutputJetCarrier K mi mo x y, ∀ j,
      ‖iteratedFDeriv ℝ j (χ backward x y) p‖ ≤ H j)
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
      ‖Q‖ ≤ Δ * LOW ∧ (∀ u, Q u = elapsedGraphIntegral Δ Ψ
        (directRetardedAmplitudes Aoriginal Boriginal W₀original W₁original branch)
        χout χsource β u) ∧
      (∀ u, Q.adjoint u = ∫ r in Icc 0 Δ, (elapsedGraph Ψ
          (directRetardedAmplitudes Aoriginal Boriginal W₀original W₁original branch)
          χout χsource β r).adjoint u) ∧
      ∀ N (backward : Bool) u,
        MemVectorFourierSobolev (m : ℝ) ((1 - Mo) ((if backward then Q.adjoint else Q) (Mi u))) ∧
        vectorFourierSobolevNorm (m : ℝ) ((1 - Mo) ((if backward then Q.adjoint else Q) (Mi u))) ≤
          Cq N * ρ ^ ((m : ℝ) + (max 0 s + (3 * (d + 1) : ℕ))) *
            L ^ bFixed * (L / ρ) ^ N * ‖u‖ := by
  classical
  obtain ⟨P, _hP, hphaseGrade⟩ := exists_residual_joint_phase_profile hsψ hY hK P₀ hP₀
  let Z := fun j ↦ cNorm (Prod.fst '' K) j θ
  have hZ (j : ℕ) : 0 ≤ Z j := cNorm_nonneg _ _ _
  obtain ⟨ba, A, hA, _hba, hampGrade⟩ := exists_directResidual_joint_amplitude_profile
    (d := d) (q := q) c C a₀ b₀ s ha₀ Qt Qs Qg Qb Qi Z hQt hQs hQg hQb hQi hZ bt bs bg bb bi
  obtain ⟨bFixed, Cq, hCq, hbound⟩ := exists_directResidual_integral_fourier_bound_of_joint_grades
    eT eI eu ez J hJ s Δ hΔ m bo ba offset c C b₀ hc ha₀ hCi χout χsource β
    hχout hχsource hβsmooth hout hsource hBβ hCβ hβ hcone
    Pbase Bbase Ophysical hPbase hBbase hOphysical hK δT δI GT GI hδT hδI
    P H W O A hH hW hO hA Y hY ψ hψ hsψ hψb θ hθ hsθ hθone Dglobal hKglobal
  refine ⟨bFixed, Cq, hCq, ?_⟩
  intro ρ L hρ hL Ac Bc W₀ W₁ branch Ψ Aoriginal Boriginal W₀original W₁original b
    haux heqOriginal Up Ua hUp hΨ hpbase haGrade haMap mi mo hi ho horange his hos
    hiAnn hiBound hoBound hψmask hψmo hinputSupport hSc hS
    Jphase Wphase hJphase hWphase hJW hPhase hPhaseSupport hmap hs a T hb hslabOut hslab
    χ UT UI ε hε hχ hUT hUI hχone hχT hχI hgapT hupperT hgapI hupperI
    hprimitivePhase hχbound hw hmo hprimitiveMasks
    Vphase Kphase g hVphase hKphase hKV hSphase hcarrier hg hcomp
    hglobalGrades hglobalSupport F hF hzero hβF χreg hχeq Treg hreal hrealAdj
    hm hmAdj LOW hLOW hlim hlimAdj
  change E × E → ℝ at mi mo
  obtain ⟨hnorm, hAmp⟩ := direct_joint_amplitude_smoothness ρ b χout χsource β
    haux hχout hχsource hβsmooth
  obtain ⟨Ψ', hsm, hgerm, _hF, _hphysical, _hshell⟩ :=
    exists_supported_elapsedPhysicalShellKernel_phase Δ Ψ b χout χsource β
      hJphase hWphase hJW hPhase hPhaseSupport
  have hp backward x (hx : x ∈ tsupport ψ) y (hy : y ∈ Prod.fst '' tsupport mi)
      p (hp : p ∈ elapsedOutputJetCarrier K mi mo x y) j :
      ‖iteratedFDeriv ℝ j (fderiv ℝ (jointElapsedPhase backward
        (SymbolBudgets.normalizedTwoTimePhase ρ Ψ) x y)) p‖ ≤ P j * L ^ j := by
    have he := normalizedTwoTimePhase_eventuallyEq_of_germ ρ Ψ Ψ' (elapsedJointCoordinates p)
      (hgerm _ (hmap x hx y hy p hp))
    have heJoint := jointElapsedPhase_eventuallyEq_of_twoTimePhase backward _ _ x y p he
    rw [← ((heJoint.fderiv (𝕜 := ℝ)).iteratedFDeriv ℝ j).eq_of_nhds]
    apply hphaseGrade L hL (SymbolBudgets.normalizedTwoTimePhase ρ Ψ')
      (contDiff_normalizedTwoTimePhase_joint ρ Ψ' hsm) backward x hx y (hinputSupport hy) p hp.1
    intro l
    rw [((he.fderiv (𝕜 := ℝ)).iteratedFDeriv ℝ l).eq_of_nhds]
    exact hprimitivePhase x hx y hy p hp l
  have hab backward low j k (hpair : IsComparablePair c C a₀ b₀ ρ low j k)
      x (hx : x ∈ tsupport ψ) y (hy : y ∈ Prod.fst '' tsupport mi)
      p (hp : p ∈ elapsedOutputJetCarrier K mi mo x y) l :=
    hampGrade ρ L hρ hL Ac Bc W₀ W₁ branch backward χout χsource β mi θ hnorm
      hχout hχsource hβsmooth hi hθ low j k hpair y p
      (fun l ↦ (hprimitiveMasks x hx y hy p hp l).1)
      (fun l ↦ (hprimitiveMasks x hx y hy p hp l).2.1)
      (fun l ↦ (hprimitiveMasks x hx y hy p hp l).2.2.1)
      (fun l ↦ (hprimitiveMasks x hx y hy p hp l).2.2.2.1)
      (fun l ↦ (hprimitiveMasks x hx y hy p hp l).2.2.2.2)
      (fun l ↦ norm_iteratedFDeriv_le_cNorm (hK.image continuous_fst)
        (hθ.of_le (by simp)) ⟨p, hp.1, rfl⟩ le_rfl) l
  obtain ⟨Mi, Mo, Q, hMi, hMo, hQ, hQeq, hQadj, hleak⟩ :=
    hbound ρ L hρ hL Ac Bc W₀ W₁ branch Ψ b haux (fun _ _ ↦ rfl)
      Up Ua hUp hΨ hpbase haGrade haMap mi mo hi ho horange his hos hiAnn hiBound hoBound
      hψmask hψmo hinputSupport hSc hS hAmp hJphase hWphase hJW hPhase hPhaseSupport
      hmap hs a T hb hslabOut hslab χ UT UI ε hε hχ hUT hUI hχone hχT hχI
      hgapT hupperT hgapI hupperI hp hχbound hw hmo hab
      Vphase Kphase g hVphase hKphase hKV hSphase hcarrier hg hcomp
      hglobalGrades hglobalSupport F hF hzero hβF χreg hχeq Treg hreal hrealAdj
      hm hmAdj hLOW hlim hlimAdj
  have hgraph r (hr : r ∈ Icc 0 Δ) : elapsedGraph Ψ b χout χsource β r =
      elapsedGraph Ψ (directRetardedAmplitudes Aoriginal Boriginal W₀original W₁original branch)
        χout χsource β r := by
    unfold elapsedGraph
    rw [heqOriginal r hr]
  refine ⟨Mi, Mo, Q, hMi, hMo, hQ, ?_, ?_, hleak⟩
  · intro u
    rw [hQeq u]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    rw [hgraph r hr]
  · intro u
    rw [hQadj u]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    rw [hgraph r hr]

end JanetCartan.ArbitraryAccuracy.ResidualLocalization
