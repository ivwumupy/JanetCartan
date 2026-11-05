module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.PrimitiveIntegrated
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.ConicCollar
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.OperatorUniqueness
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.LocalizerReality
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.PhysicalLeakage

/-!
# Actual elapsed leakage from buffered conic chart geometry

Apply the finite-family collar producer to the actual jet carrier, then the
primitive integrated estimate. Both literal orientations share the collar
and the accuracy profile. A globally smooth supported auxiliary is used only
inside the analytic producer: normalized germ equality transfers the geometric
gaps, and supported phase equality identifies the original conic integral.
This removes the gradient-gap premises from the retarded part of `app:ch_regular:eq:chain-tail`. The fixed operators are
identified by their literal integral and localizer actions.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.RegularSector.Realization
namespace JanetCartan.ArbitraryAccuracy.ResidualLocalization
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

/-- Apply buffered conic chart geometry and primitive grades to both literal
retarded branches of the complete residual. `ConicCollar` produces the gaps
on the exact carrier; `PrimitiveIntegrated` produces the differentiated
kernels, shell majorants and Sobolev bound. No localization estimate or
gradient gap is assumed. The actual chart differentials and supported germs
come from `ResidualCoordinates.Assembly`; plateaus and whole-domain buffers
come from `ProtectedMasks`. `SupportedPhase.exists_supported_twoTimePhase_extension`
produces the globally smooth analytic phase and its supported germs; the
normalized germs and supported equality below are exact phase-identification
inputs, not localized estimates. In particular the original conic phase is
not assumed smooth at a zero spatial covector. Primitive grades and finite
realizations remain the named `EvolutionIntegral` inputs. Constants are common to the supplied
finite charts and both orientations and precede frequency and accuracy.
The integral and localizer identities retain the SAME bounded operators.
For even real physical proof masks, the physical plus pairing is also bounded
in the actual restriction scale by `PhysicalLeakage`; `LocalizerReality`
derives the requisite commutation from the literal quantizations. The paired
adjoint remains the plus pairing of the literal adjoint (`boundedConjugate_adjoint`).
Consumer: retarded `hleak` in `finiteChain_observation_rapidDecayAt`
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_conic_directResidual_integral_fourier_bound
    {α ι κ ιu ιz : Type*} [Finite α] [TopologicalSpace α] [DiscreteTopology α] [Fintype ι] [Fintype κ] [Fintype ιu] [Fintype ιz]
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
    (P₀ W O Qt Qs Qg Qb Qi : ℕ → ℝ)
    (hP₀ : ∀ j, 0 ≤ P₀ j)
    (hQt : ∀ j, 0 ≤ Qt j) (hQs : ∀ j, 0 ≤ Qs j) (hQg : ∀ j, 0 ≤ Qg j)
    (hQb : ∀ j, 0 ≤ Qb j) (hQi : ∀ j, 0 ≤ Qi j)
    (hW : ∀ j, 0 ≤ W j)
    (hO : ∀ j, 0 ≤ O j)
    (Y : Set E) (hY : IsCompact Y)
    (ψ : E → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hsψ : HasCompactSupport ψ)
    (hψb : ∀ x, ‖ψ x‖ ≤ 1)
    (θ : ℝ → ℂ) (hθ : ContDiff ℝ ∞ θ) (hsθ : HasCompactSupport θ)
    (hθone : ∀ r ∈ Icc 0 Δ, θ r = 1)
    (mi mo : LocalizerSymbol (d + 1))
    (hi : ContDiff ℝ ∞ mi) (ho : ContDiff ℝ ∞ mo)
    (horange : ∀ p, mo p ∈ Icc (0 : ℝ) 1)
    (his : HasCompactSupport mi) (hos : HasCompactSupport mo)
    (hiAnn : ∀ y, tsupport (fun η ↦ mi (y, η)) ⊆ frequencyAnnulus a₀ b₀)
    (hiBound : ∀ y η, ‖mi (y, η)‖ ≤ Ci)
    (Dglobal : AmplitudeProfiles) {Kglobal : Set (JointVariables E)} (hKglobal : IsCompact Kglobal)
    (h : α → RootState (Euclidean d) → ℝ)
    (Φ : α → RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (Cchart : α → OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (Ψsupport : α → TwoTimePhase d)
    (R : α → Set (E × E))
    (ℓ : α → Euclidean d →L[ℝ] ℝ)
    (Fchart : α → TwoTimePoint (Euclidean d) → ℝ) :
    let KG := elapsedFiniteFamilyCarrier (fun _ : α ↦ tsupport ψ ×ˢ (Prod.fst '' tsupport mi))
      (fun _ ↦ K) (fun _ ↦ mi) (fun _ ↦ mo)
    ∀ (_hΨ : ∀ t, ContDiff ℝ ∞ (SymbolBudgets.jointPhase (Ψsupport t)))
    (_hC : ∀ t, (Cchart t : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) =
      twoTimeProjection (Φ t))
    (_hdiag : tsupport mi ⊆ interior {p | mo p = 1})
    (_hflow : ∀ backward, ∀ t ∈ KG, 0 < t.2.1 → ∀ a ∈ tsupport mi, ∀ b ∈ R t.1.1,
      zeroEnergyFlowRelation backward (h t.1.1) (Φ t.1.1) t.2.1 a b →
        b ∈ interior {p | mo p = 1})
    (_hR : ∀ t ∈ KG, (t.1.2.1, t.2.2.2.2.2) ∈ R t.1.1)
    (_hqB : ∀ t ∈ KG, elapsedChartPoint 0 t.2.2.1.1 t.2.2.2.1 ∈ (Cchart t.1.1).target)
    (_hi : ∀ t ∈ KG,
      Φ t.1.1 (((Cchart t.1.1).symm (elapsedChartPoint 0 t.2.2.1.1 t.2.2.2.1)).2, 0) =
        ((Cchart t.1.1).symm (elapsedChartPoint 0 t.2.2.1.1 t.2.2.2.1)).2)
    (_hphaseB : ∀ t ∈ KG, HasFDerivAt (twoTimePhase (Cchart t.1.1))
      (twoTimePhaseDifferential (h t.1.1) (Φ t.1.1) (Cchart t.1.1)
        (elapsedChartPoint 0 t.2.2.1.1 t.2.2.2.1))
      (elapsedChartPoint 0 t.2.2.1.1 t.2.2.2.1))
    (_hqI : ∀ t ∈ KG, 0 < t.2.1 →
      elapsedChartPoint t.2.1 t.2.2.1.1 t.2.2.2.1 ∈ (Cchart t.1.1).target)
    (_hclock : ∀ t ∈ KG, 0 < t.2.1 →
      (twoTimeState (Φ t.1.1) ((Cchart t.1.1).symm
        (elapsedChartPoint t.2.1 t.2.2.1.1 t.2.2.2.1))).1 = t.2.2.1.1 0)
    (_hphaseI : ∀ t ∈ KG, 0 < t.2.1 → HasFDerivAt (twoTimePhase (Cchart t.1.1))
      (twoTimePhaseDifferential (h t.1.1) (Φ t.1.1) (Cchart t.1.1)
        (elapsedChartPoint t.2.1 t.2.2.1.1 t.2.2.2.1))
      (elapsedChartPoint t.2.1 t.2.2.1.1 t.2.2.2.1))
    (_hGermB : ∀ t ∈ KG, SymbolBudgets.jointPhase (Ψsupport t.1.1) =ᶠ[𝓝
      (elapsedJointCoordinates (0, t.2.2))] SymbolBudgets.jointPhase (chartPhase (Cchart t.1.1)))
    (_hGermI : ∀ t ∈ KG, 0 < t.2.1 → SymbolBudgets.jointPhase (Ψsupport t.1.1) =ᶠ[𝓝
      (elapsedJointCoordinates t.2)] SymbolBudgets.jointPhase (chartPhase (Cchart t.1.1)))
    (_hsupported : ∀ t ∈ KG, 0 ≤ t.2.1 →
      SymbolBudgets.jointPhase (Ψsupport t.1.1) =ᶠ[𝓝 (elapsedJointCoordinates t.2)]
        SymbolBudgets.jointPhase (ConicPhase.curriedExtend (ℓ t.1.1) (Fchart t.1.1))),
    ∃ (bFixed : ℕ) (Cq Cpair Creal : ℕ → ℝ),
      (∀ N, 0 ≤ Cq N) ∧ (∀ N, 0 ≤ Cpair N) ∧ (∀ N, 0 ≤ Creal N) ∧
    ∀ sector : α,
    let Ψoriginal := ConicPhase.curriedExtend (ℓ sector) (Fchart sector)
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
    (_hphaseGerm : ∀ x ∈ tsupport ψ, ∀ y ∈ Prod.fst '' tsupport mi,
      ∀ p ∈ elapsedOutputJetCarrier K mi mo x y, 0 ≤ p.1 →
        SymbolBudgets.jointPhase (SymbolBudgets.normalizedTwoTimePhase ρ Ψ) =ᶠ[𝓝
          (elapsedJointCoordinates p)] SymbolBudgets.jointPhase Ψoriginal)
    (_hphaseAgree : ∀ r ∈ Icc 0 Δ, ∀ x z ξ,
      elapsedAmplitude b χout χsource β r x z ξ ≠ 0 →
        elapsedPhase Ψ r x ξ = elapsedPhase Ψoriginal r x ξ)
    (hs : ∀ backward y, y ∈ Prod.fst '' tsupport mi → ∀ low j k,
      IsComparablePair c C a₀ b₀ ρ low j k →
      tsupport (fun p : V ↦ θ p.1 • jointElapsedAmplitude backward ρ b χout χsource β
        mi (fun _ ↦ 0) (graphBranchCutoff low j) (outputCutoff k) 0 y p) ⊆ K)
    (a T : ℝ) (hb : ∀ t t' u η, t' ≤ a → b t t' u η = 0)
    (hslabOut : ∀ u, T < u 0 → χout u = 0) (hslab : T - a ≤ Δ)
    (hprimitivePhase : ∀ x ∈ tsupport ψ, ∀ y ∈ Prod.fst '' tsupport mi,
      ∀ p ∈ elapsedOutputJetCarrier K mi mo x y, ∀ j,
      ‖iteratedFDeriv ℝ j (fderiv ℝ (SymbolBudgets.jointPhase
        (SymbolBudgets.normalizedTwoTimePhase ρ Ψ))) (elapsedJointCoordinates p)‖ ≤
          P₀ j * L ^ j)
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
  intro KG hΨsupport hC hdiag hflow hR hqB hinit hphaseB hqI hclock hphaseI
    hGermB hGermI hsupported
  obtain ⟨χcollar, UT, UI, ε, δT, δI, G, H, hε, hδT, hδI, hH, hcollar⟩ :=
    exists_finiteFamily_conic_residual_collar eT eI
      (fun _ : α ↦ tsupport ψ ×ˢ (Prod.fst '' tsupport mi))
      (fun _ ↦ K) (fun _ ↦ mi) (fun _ ↦ mo)
      (fun _ ↦ hsψ.isCompact.prod (his.isCompact.image continuous_fst)) (fun _ ↦ hK)
      h Φ Cchart Ψsupport R ℓ Fchart hΨsupport hC (fun _ ↦ hdiag)
      hflow hR hqB hinit hphaseB hqI hclock hphaseI hGermB hGermI hsupported
  obtain ⟨bFixed, Cq, hCq, hbound⟩ :=
    exists_directResidual_integral_fourier_bound_of_primitive_grades
      eT eI eu ez J hJ s Δ hΔ m bo offset bt bs bg bb bi c C b₀ hc ha₀ hCi
      χout χsource β hχout hχsource hβsmooth hout hsource hBβ hCβ hβ hcone
      Pbase Bbase Ophysical hPbase hBbase hOphysical hK δT δI G G hδT hδI
      P₀ H W O Qt Qs Qg Qb Qi hP₀ hQt hQs hQg hQb hQi hH hW hO
      Y hY ψ hψ hsψ hψb θ hθ hsθ hθone Dglobal hKglobal
  obtain ⟨Kpair, hKpair, hpair⟩ := exists_physicalPair_fourier_restriction_comparison d q m
  obtain ⟨Kreal, hKreal, hrealPair⟩ := exists_realPhysicalPair_fourier_restriction_comparison d q m
  refine ⟨bFixed, Cq, fun N ↦ Kpair * Cq N, fun N ↦ Kreal * Cq N, hCq,
    fun N ↦ mul_nonneg hKpair.le (hCq N), fun N ↦ mul_nonneg hKreal.le (hCq N), ?_⟩
  intro sector Ψoriginal ρ L hρ hL Ac Bc W₀ W₁ branch Ψ hauxPhase Aoriginal Boriginal W₀original W₁original b
    haux heqOriginal Up Ua hUp hΨ hpbase haGrade haMap hoBound
    hψmask hψmo hinputSupport hphaseGerm hphaseAgree hs a T hb hslabOut hslab hprimitivePhase hw hmo hprimitiveMasks
    Vphase Kphase g hVphase hKphase hKV hSphase hcarrier hg hcomp
    hglobalGrades hglobalSupport F hF hzero hβF χreg hχeq Treg hreal hrealAdj
    hm hmAdj LOW hLOW hlim hlimAdj Mi Mo Q hMi hMo hQid
  have hcdata := hcollar ρ (zero_lt_one.trans_le hρ)
  have hbases x (hx : x ∈ tsupport ψ) y (hy : y ∈ Prod.fst '' tsupport mi) :
      (x, y) ∈ tsupport ψ ×ˢ (Prod.fst '' tsupport mi) := ⟨hx, hy⟩
  let Ω (x y : E) : Set V := {p |
    SymbolBudgets.jointPhase (SymbolBudgets.normalizedTwoTimePhase ρ Ψ) =ᶠ[𝓝
      (elapsedJointCoordinates p)] SymbolBudgets.jointPhase Ψoriginal}
  have hΩ x y : IsOpen (Ω x y) :=
    isOpen_setOfPred_eventually_nhds.preimage elapsedJointCoordinates.continuous
  let U (backward : Bool) (x y : E) := UT backward (sector, x, y) ∩
    (Ω x y ∪ {p : V | p.1 < 0})
  let W (backward : Bool) (x y : E) := UI backward (sector, x, y) ∩ Ω x y
  have hmem x hx y hy p hp hr : p ∈ Ω x y := hphaseGerm x hx y hy p hp hr
  have he backward x y p (hp : p ∈ Ω x y) :=
    jointElapsedPhase_eventuallyEq_of_twoTimePhase backward _ _ x y p hp
  have hnormalized := ConicPhase.normalizedTwoTimePhase_curriedExtend
    (ℓ sector) (Fchart sector) (zero_lt_one.trans_le hρ)
  have hχT backward x (hx : x ∈ tsupport ψ) y (hy : y ∈ Prod.fst '' tsupport mi) :
      elapsedOutputJetCarrier K mi mo x y ∩ tsupport (χcollar backward) ⊆ U backward x y := by
    intro p hp
    refine ⟨(hcdata backward).2.2.2.2.1 sector x y (hbases x hx y hy) hp, ?_⟩
    by_cases hr : 0 ≤ p.1
    · exact Or.inl (hmem x hx y hy p hp.1 hr)
    · exact Or.inr (lt_of_not_ge hr)
  have hχI backward x (hx : x ∈ tsupport ψ) y (hy : y ∈ Prod.fst '' tsupport mi) :
      (elapsedOutputJetCarrier K mi mo x y ∩ tsupport (1 - χcollar backward)) ∩
        {p | 0 < p.1} ⊆ W backward x y := by
    intro p hp
    exact ⟨(hcdata backward).2.2.2.2.2.1 sector x y (hbases x hx y hy) hp,
      hmem x hx y hy p hp.1.1 hp.2.le⟩
  have hgapT backward x y r (hr : 0 ≤ r) p (hp : (r, p) ∈ U backward x y) :
      δT ≤ phaseGradientSquare eT (fun w ↦ jointElapsedPhase backward
        (SymbolBudgets.normalizedTwoTimePhase ρ Ψ) x y (r, w)) p := by
    have hg := (hcdata backward).2.2.2.2.2.2.1 (sector, x, y) r hr p hp.1
    rw [hnormalized] at hg
    have he' := fderiv_jointElapsedPhase_slice_eq_of_twoTimePhase_germ backward Ψoriginal
      (SymbolBudgets.normalizedTwoTimePhase ρ Ψ) x y r p
      (hp.2.resolve_right (not_lt_of_ge hr))
    unfold phaseGradientSquare
    rw [he']
    exact hg
  have hupperT backward x y r (hr : 0 ≤ r) p (hp : (r, p) ∈ U backward x y) :
      ‖fderiv ℝ (jointElapsedPhase backward (SymbolBudgets.normalizedTwoTimePhase ρ Ψ) x y)
        (r, p)‖ ≤ G := by
    have hg := (hcdata backward).2.2.2.2.2.2.2.1 (sector, x, y) r hr p hp.1
    rw [hnormalized] at hg
    rw [(he backward x y (r, p) (hp.2.resolve_right (not_lt_of_ge hr))).fderiv_eq]
    exact hg
  have hgapI backward x y p (hp : p ∈ W backward x y ∩ {p | 0 < p.1}) :
      δI ≤ phaseGradientSquare eI (jointElapsedPhase backward
        (SymbolBudgets.normalizedTwoTimePhase ρ Ψ) x y) p := by
    have hg := (hcdata backward).2.2.2.2.2.2.2.2.1 (sector, x, y) p ⟨hp.1.1, hp.2⟩
    rw [hnormalized] at hg
    simpa only [phaseGradientSquare, (he backward x y p hp.1.2).fderiv_eq] using hg
  have hupperI backward x y p (hp : p ∈ W backward x y ∩ {p | 0 < p.1}) :
      ‖fderiv ℝ (jointElapsedPhase backward (SymbolBudgets.normalizedTwoTimePhase ρ Ψ) x y) p‖ ≤ G := by
    have hg := (hcdata backward).2.2.2.2.2.2.2.2.2.1 (sector, x, y) p ⟨hp.1.1, hp.2⟩
    rw [hnormalized] at hg
    rw [(he backward x y p hp.1.2).fderiv_eq]
    exact hg
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
  obtain ⟨Mi', Mo', Q', hMi', hMo', hQ', hQeq', hQadj', hleak⟩ := hbound
    ρ L hρ hL Ac Bc W₀ W₁ branch Ψ Aoriginal Boriginal W₀original W₁original
    haux heqOriginal Up Ua hUp hΨ hpbase haGrade haMap mi mo hi ho horange his hos
    hiAnn hiBound hoBound hψmask hψmo hinputSupport hSc.continuous
    (fun r _ u ξ _ ↦ (hSc.comp (contDiff_const.prodMk contDiff_id)).contDiffAt)
    (Jphase := Set.univ) (Wphase := Set.univ) isClosed_univ isOpen_univ (Subset.refl _)
    hauxPhase.contDiffOn (fun _ _ _ _ _ _ ↦ Set.mem_univ _) (fun _ _ _ _ _ _ ↦ Set.mem_univ _) hs a T hb hslabOut hslab
    (fun backward _ _ ↦ χcollar backward)
    U W ε hε
    (fun backward _ _ _ _ ↦ (hcdata backward).1)
    (fun backward x _ y _ ↦ ((hcdata backward).2.1 (sector, x, y)).inter
      ((hΩ x y).union (isOpen_lt continuous_fst continuous_const)))
    (fun backward x _ y _ ↦ ((hcdata backward).2.2.1 (sector, x, y)).inter (hΩ x y))
    (fun backward _ _ _ _ ↦ (hcdata backward).2.2.2.1)
    hχT hχI
    (fun backward x _ y _ ↦ hgapT backward x y)
    (fun backward x _ y _ ↦ hupperT backward x y)
    (fun backward x _ y _ ↦ hgapI backward x y)
    (fun backward x _ y _ ↦ hupperI backward x y)
    hprimitivePhase
    (fun backward x hx y hy ↦ (hcdata backward).2.2.2.2.2.2.2.2.2.2 sector x y (hbases x hx y hy))
    hw hmo hprimitiveMasks Vphase Kphase g hVphase hKphase hKV hSphase hcarrier hg hcomp
    hglobalGrades hglobalSupport F hF hzero hβF χreg hχeq Treg hreal hrealAdj
    hm hmAdj hLOW hlim hlimAdj
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

end JanetCartan.ArbitraryAccuracy.ResidualLocalization
