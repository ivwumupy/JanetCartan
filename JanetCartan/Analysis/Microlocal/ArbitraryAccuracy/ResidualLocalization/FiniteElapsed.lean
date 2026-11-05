module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.GeometricIntegrated
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.PolynomialCosts.Adjoints
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.ConicCollar
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.OperatorUniqueness
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.LocalizerReality
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.PhysicalLeakage

/-!
# The finite physical elapsed correction

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

/-- Sum the actual conic elapsed branches after applying the buffered geometric
and primitive-grade producer to each member. The original common physical masks,
phase germs, all finite realizations, and both adjoints are retained. Constants
precede accuracy, frequency and the primitive current coefficients. Consumer:
the elapsed part of the complete residual in `app:ch_regular:eq:chain-tail`. -/
theorem exists_finiteConic_directResidual_restriction_bound
    {α ι κ ιu ιz : Type*} [Fintype α] [TopologicalSpace α] [DiscreteTopology α] [Fintype ι] [Fintype κ] [Fintype ιu] [Fintype ιz]
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
    ∃ (bFixed : ℕ) (Cpair : ℕ → ℝ), (∀ N, 0 ≤ Cpair N) ∧
    ∀ (ρ L : ℝ) (hρ : 1 ≤ ρ) (hL : 1 ≤ L),
    let Ψoriginal := fun sector ↦ ConicPhase.curriedExtend (ℓ sector) (Fchart sector)
    ∀ (Ac : α → E → Fin (d + 1) → Mat),
    ∀ (Bc : α → E → Mat),
    ∀ (W₀ W₁ : α → TwoTimeAmplitude d q),
    ∀ (branch : α → Bool),
    ∀ (Ψ : α → TwoTimePhase d),
    ∀ (_hauxPhase : ∀ sector : α, ContDiff ℝ ∞ (SymbolBudgets.jointPhase (Ψ sector))),
    ∀ (Aoriginal : α → E → Fin (d + 1) → Mat),
    ∀ (Boriginal : α → E → Mat),
    ∀ (W₀original W₁original : α → TwoTimeAmplitude d q),
    let b := fun sector ↦ directRetardedAmplitudes (Ac sector) (Bc sector) (W₀ sector) (W₁ sector) (branch sector)
    ∀ (hsmoothAuxAmplitude : ∀ sector : α, ContDiff ℝ ∞ (SymbolBudgets.jointAmplitude (b sector))),
    ∀ (hmaskedAuxAmplitude : ∀ sector : α, ∀ r ∈ Icc 0 Δ, elapsedAmplitude (b sector) χout χsource β r =
      elapsedAmplitude (directRetardedAmplitudes (Aoriginal sector) (Boriginal sector) (W₀original sector) (W₁original sector) (branch sector))
        χout χsource β r),
    ∀ (Up Ua : α → Set (SymbolBudgets.TwoTimePoint d)),
    ∀ (hUp : ∀ sector : α, IsOpen (Up sector)),
    ∀ (hauxSmoothOn : ∀ sector : α, ContDiffOn ℝ ∞ (SymbolBudgets.jointPhase (Ψ sector)) (Up sector)),
    ∀ (hauxPhaseGrades : ∀ sector : α, ∀ η v, (v, η) ∈ (Up sector) → ∀ k, 1 ≤ k →
      ‖iteratedFDeriv ℝ (k + 1)
        (fun w : ℝ × ℝ × Euclidean d ↦ (Ψ sector) w.1 w.2.1 w.2.2 η) v‖ ≤
          ‖η‖ * Pbase k * L ^ k),
    ∀ (hauxAmplitudeGrades : ∀ sector : α, ∀ p ∈ (Ua sector), ∀ k, ‖iteratedFDeriv ℝ k (SymbolBudgets.jointAmplitude (b sector)) p‖ ≤
      (1 + ‖p.2‖) ^ s * Bbase k * L ^ (k + offset)),
    ∀ (hauxAmplitudeCarrier : ∀ sector : α, ∀ r ∈ Icc 0 Δ, ∀ low j, ∀ ξ ∈ normalizedGraphCarrier ρ low j,
      ∀ z ∈ tsupport χout ×ˢ tsupport χsource,
        β (ρ • ξ) ≠ 0 → SymbolBudgets.elapsedPoint r (z, ρ • ξ) ∈ (Ua sector)),
    ∀ (hoBound : ∀ _sector : α, ∀ x ζ k, ‖iteratedFDeriv ℝ k (fun t ↦ mo (t, ζ)) x‖ ≤
      Ophysical k * L ^ (k + bo)),
    ∀ (hψmask : ∀ _sector : α, ∀ (backward : Bool) x,
      x ∈ (if backward then tsupport χsource else tsupport χout) → ψ x = 1),
    ∀ (hψmo : ∀ _sector : α, ∀ x ∈ Prod.fst '' tsupport mo, ψ x = 1),
    ∀ (hinputSupport : ∀ _sector : α, Prod.fst '' tsupport mi ⊆ Y),
    ∀ (_hphaseGerm : ∀ sector : α, ∀ x ∈ tsupport ψ, ∀ y ∈ Prod.fst '' tsupport mi,
      ∀ p ∈ elapsedOutputJetCarrier K mi mo x y, 0 ≤ p.1 →
        SymbolBudgets.jointPhase (SymbolBudgets.normalizedTwoTimePhase ρ (Ψ sector)) =ᶠ[𝓝
          (elapsedJointCoordinates p)] SymbolBudgets.jointPhase (Ψoriginal sector)),
    ∀ (_hphaseAgree : ∀ sector : α, ∀ r ∈ Icc 0 Δ, ∀ x z ξ,
      elapsedAmplitude (b sector) χout χsource β r x z ξ ≠ 0 →
        elapsedPhase (Ψ sector) r x ξ = elapsedPhase (Ψoriginal sector) r x ξ),
    ∀ (hs : ∀ sector : α, ∀ backward y, y ∈ Prod.fst '' tsupport mi → ∀ low j k,
      IsComparablePair c C a₀ b₀ ρ low j k →
      tsupport (fun p : V ↦ θ p.1 • jointElapsedAmplitude backward ρ (b sector) χout χsource β
        mi (fun _ ↦ 0) (graphBranchCutoff low j) (outputCutoff k) 0 y p) ⊆ K),
    ∀ (a T : α → ℝ),
    ∀ (hb : ∀ sector : α, ∀ t t' u η, t' ≤ (a sector) → (b sector) t t' u η = 0),
    ∀ (hslabOut : ∀ sector : α, ∀ u, (T sector) < u 0 → χout u = 0),
    ∀ (hslab : ∀ sector : α, (T sector) - (a sector) ≤ Δ),
    ∀ (hprimitivePhase : ∀ sector : α, ∀ x ∈ tsupport ψ, ∀ y ∈ Prod.fst '' tsupport mi,
      ∀ p ∈ elapsedOutputJetCarrier K mi mo x y, ∀ j,
      ‖iteratedFDeriv ℝ j (fderiv ℝ (SymbolBudgets.jointPhase
        (SymbolBudgets.normalizedTwoTimePhase ρ (Ψ sector)))) (elapsedJointCoordinates p)‖ ≤
          P₀ j * L ^ j),
    ∀ (hw : ∀ _sector : α, ∀ x ∈ tsupport ψ, ∀ y ∈ Prod.fst '' tsupport mi,
      ∀ p ∈ elapsedOutputJetCarrier K mi mo x y, ∀ j,
      ‖iteratedFDeriv ℝ j outputJointWave (0, p.2.2.2.2)‖ ≤ W j),
    ∀ (hmo : ∀ _sector : α, ∀ x ∈ tsupport ψ, ∀ y ∈ Prod.fst '' tsupport mi,
      ∀ p ∈ elapsedOutputJetCarrier K mi mo x y, ∀ j,
      ‖iteratedFDeriv ℝ j mo (x, p.2.2.2.2)‖ ≤ O j * L ^ (j + bo)),
    ∀ (hprimitiveMasks : ∀ sector : α, ∀ x ∈ tsupport ψ, ∀ y ∈ Prod.fst '' tsupport mi,
      ∀ p ∈ elapsedOutputJetCarrier K mi mo x y, ∀ l,
      ‖iteratedFDeriv ℝ l (fun w : V ↦ χout w.2.1.1) p‖ ≤ Qt l * L ^ (l + bt) ∧
      ‖iteratedFDeriv ℝ l (fun w : V ↦ χsource w.2.1.2) p‖ ≤ Qs l * L ^ (l + bs) ∧
      ‖iteratedFDeriv ℝ l (fun w : V ↦ β (ρ • w.2.2.1)) p‖ ≤ Qg l * L ^ (l + bg) ∧
      ‖iteratedFDeriv ℝ l (normalizedElapsedSymbol ρ (b sector)) p‖ ≤ ρ ^ s * Qb l * L ^ (l + bb) ∧
      ‖iteratedFDeriv ℝ l (fun w : V ↦ (mi (y, w.2.2.2.1) : ℂ)) p‖ ≤ Qi l * L ^ (l + bi)),
    ∀ (Vphase : α → ℝ → Set (E × E)),
    ∀ (Kphase : α → ℝ → Bool → ℕ → Set (E × E)),
    ∀ (g : α → ℝ → E → E → E),
    ∀ (hVphase : ∀ sector : α, ∀ r ∈ Icc 0 Δ, IsOpen ((Vphase sector) r)),
    ∀ (hKphase : ∀ sector : α, ∀ r ∈ Icc 0 Δ, ∀ low j, IsCompact ((Kphase sector) r low j)),
    ∀ (hKV : ∀ sector : α, ∀ r ∈ Icc 0 Δ, ∀ low j, (Kphase sector) r low j ⊆ (Vphase sector) r),
    ∀ (hSphase : ∀ sector : α, ∀ r ∈ Icc 0 Δ,
      ContDiffOn ℝ ∞ (Function.uncurry (elapsedPhase (Ψ sector) r)) ((Vphase sector) r)),
    ∀ (hcarrier : ∀ sector : α, ∀ r ∈ Icc 0 Δ, ∀ low j, ∀ ξ ∈ normalizedGraphCarrier ρ low j,
      ∀ z ∈ tsupport (fun z : E × E ↦ elapsedAmplitude (b sector) χout χsource β r z.1 z.2 (ρ • ξ)),
        (z.1, ρ • ξ) ∈ (Kphase sector) r low j ∧ SymbolBudgets.elapsedPoint r (z, ρ • ξ) ∈ (Up sector)),
    ∀ (hg : ∀ sector : α, ∀ r ∈ Icc 0 Δ, ∀ u ξ, (u, ξ) ∈ (Vphase sector) r →
      fderiv ℝ (fun t ↦ elapsedPhase (Ψ sector) r t ξ) u = innerSL ℝ ((g sector) r u ξ)),
    ∀ (hcomp : ∀ sector : α, ∀ r ∈ Icc 0 Δ, ∀ u ξ, (u, ξ) ∈ (Vphase sector) r →
      c * ‖ξ‖ ≤ ‖(g sector) r u ξ‖ ∧ ‖(g sector) r u ξ‖ ≤ C * ‖ξ‖),
    ∀ (hglobalGrades : ∀ sector : α, ∀ backward low j k, IsComparablePair c C a₀ b₀ ρ low j k →
      ∀ r ∈ Icc 0 Δ, ∀ y, HasAmplitudeGrades Dglobal ρ (ρ ^ s) L
        (orientedElapsedAmplitude backward (b sector) χout χsource β r) mi (fun _ ↦ 0)
        (graphBranchCutoff low j) (outputCutoff k) 0 y Kglobal),
    ∀ (hglobalSupport : ∀ sector : α, ∀ backward low j k, IsComparablePair c C a₀ b₀ ρ low j k →
      ∀ r ∈ Icc 0 Δ, ∀ y, tsupport (jointAmplitude ρ
        (orientedElapsedAmplitude backward (b sector) χout χsource β r) mi (fun _ ↦ 0)
        (graphBranchCutoff low j) (outputCutoff k) 0 y) ⊆ Kglobal),
    ∀ (F : α → Set E),
    ∀ (hF : ∀ sector : α, IsClosed (F sector)),
    ∀ (hzero : ∀ sector : α, (0 : E) ∉ (F sector)),
    ∀ (hβF : ∀ sector : α, tsupport β ⊆ (F sector)),
    ∀ (χ : α → ℕ → E → ℂ),
    ∀ (hχeq : ∀ sector : α, ∀ (A : FullAmplitude (d + 1) q), (∀ x y ξ, ξ ∉ (F sector) → A x y ξ = 0) →
      ∀ j, frequencyCutFullAmplitude ((χ sector) j) A =
        frequencyCutFullAmplitude (complexPhysicalCutoff j) A),
    ∀ (Treg : α → ℕ → ℝ → Hspace →L[ℂ] Hspace),
    ∀ (hreal : ∀ sector : α, ∀ j r, r ∈ Icc 0 Δ → ∀ u : graphTestSpace (d + 1) q,
      (Treg sector) j r (graphTestToLp u) =ᵐ[volume] graphTestOutput (elapsedPhase (Ψ sector) r)
        (frequencyCutFullAmplitude ((χ sector) j) (elapsedAmplitude (b sector) χout χsource β r)) u),
    ∀ (hrealAdj : ∀ sector : α, ∀ j r, r ∈ Icc 0 Δ → ∀ u : graphTestSpace (d + 1) q,
      ((Treg sector) j r).adjoint (graphTestToLp u) =ᵐ[volume] fun z ↦ WithLp.toLp 2
        (reverseGraphOperator (elapsedPhase (Ψ sector) r)
          (frequencyCutFullAmplitude (fun ξ ↦ star ((χ sector) j ξ))
            (fun x z ξ ↦ (elapsedAmplitude (b sector) χout χsource β r x z ξ).conjTranspose))
          (fun x ↦ (u.val x).ofLp) z)),
    ∀ (hm : ∀ sector : α, ∀ j u, AEStronglyMeasurable (fun r ↦ (Treg sector) j r u) (volume.restrict (Icc 0 Δ))),
    ∀ (hmAdj : ∀ sector : α, ∀ j u, AEStronglyMeasurable (fun r ↦ ((Treg sector) j r).adjoint u)
      (volume.restrict (Icc 0 Δ))),
    ∀ {LOW : α → ℝ},
    ∀ (hbound : ∀ sector : α, ∀ j r, r ∈ Icc 0 Δ → ‖(Treg sector) j r‖ ≤ (LOW sector)),
    ∀ (hlim : ∀ sector : α, ∀ r ∈ Icc 0 Δ, ∀ u, Tendsto (fun j ↦ (Treg sector) j r u) atTop
      (𝓝 (elapsedGraph (Ψ sector) (b sector) χout χsource β r u))),
    ∀ (hlimAdj : ∀ sector : α, ∀ r ∈ Icc 0 Δ, ∀ u, Tendsto (fun j ↦ ((Treg sector) j r).adjoint u) atTop
      (𝓝 ((elapsedGraph (Ψ sector) (b sector) χout χsource β r).adjoint u))),
    ∀ (Mi Mo : Hspace →L[ℂ] Hspace),
    ∀ (Q : α → Hspace →L[ℂ] Hspace),
    ∀ (hMi : ∀ u : Hspace, Mi u =ᵐ[volume] fun x ↦ WithLp.toLp 2
        (rightLocalizer ρ mi (fun y ↦ (u y).ofLp) x)),
    ∀ (_hMo : ∀ u : Hspace, (∀ i, Integrable (fun y ↦ u y i)) → Mo u =ᵐ[volume]
        fun x ↦ WithLp.toLp 2 (leftLocalizer ρ mo (fun y ↦ (u y).ofLp) x)),
    ∀ (_hQid : ∀ sector : α, ∀ u, (Q sector) u = elapsedGraphIntegral Δ (Ψoriginal sector)
        (directRetardedAmplitudes (Aoriginal sector) (Boriginal sector) (W₀original sector) (W₁original sector) (branch sector))
        χout χsource β u),
      let S := physicalPairedSectorSum Finset.univ Q
      ∀ (_hieven : ∀ y ξ, mi (y, -ξ) = mi (y, ξ))
        (_hoeven : ∀ y ξ, mo (y, -ξ) = mo (y, ξ))
        (N : ℕ) (backward : Bool) (U : Set E) (hU : MeasurableSet U),
        let T := if backward then S.adjoint else S
        ∀ u : Hspace, restrictL2 U ((1 - Mo) (T (Mi u))) ∈
          (restrictionSobolevScale U (EuclideanSpace ℂ (Fin q)) hU).level m ∧
        (restrictionSobolevScale U (EuclideanSpace ℂ (Fin q)) hU).gradeNorm m
          (restrictL2 U ((1 - Mo) (T (Mi u)))) ≤
          Cpair N * ρ ^ ((m : ℝ) + (max 0 s + (3 * (d + 1) : ℕ))) *
            L ^ bFixed * (L / ρ) ^ N * ‖u‖ := by
  classical
  intro KG hΨsupport hC hdiag hflow hR hqB hinit hphaseB hqI hclock hphaseI
    hGermB hGermI hsupported
  obtain ⟨bFixed, Cq, Cp, Cr, hCq, hCp, hCr, hprod⟩ :=
    exists_conic_directResidual_integral_fourier_bound
      eT eI eu ez J hJ s Δ hΔ m bo offset bt bs bg bb bi c C b₀ hc ha₀ hCi
      χout χsource β hχout hχsource hβsmooth hout hsource hBβ hCβ hβ hcone
      Pbase Bbase Ophysical hPbase hBbase hOphysical hK
      P₀ W O Qt Qs Qg Qb Qi hP₀ hQt hQs hQg hQb hQi hW hO
      Y hY ψ hψ hsψ hψb θ hθ hsθ hθone mi mo hi ho horange his hos hiAnn hiBound
      Dglobal hKglobal h Φ Cchart Ψsupport R ℓ Fchart
      hΨsupport hC hdiag hflow hR hqB hinit hphaseB hqI hclock hphaseI
      hGermB hGermI hsupported
  refine ⟨bFixed, fun N ↦ ∑ _ : α, Cp N,
    fun N ↦ Finset.sum_nonneg (fun _ _ ↦ hCp N), ?_⟩
  intro ρ L hρ hL Ψoriginal Ac Bc W₀ W₁ branch Ψ _hauxPhase Aoriginal Boriginal W₀original W₁original b
    hsmoothAuxAmplitude hmaskedAuxAmplitude Up Ua hUp hauxSmoothOn hauxPhaseGrades hauxAmplitudeGrades
    hauxAmplitudeCarrier hoBound hψmask hψmo hinputSupport _hphaseGerm _hphaseAgree hs a T hb hslabOut hslab
    hprimitivePhase hw hmo hprimitiveMasks Vphase Kphase g hVphase hKphase hKV hSphase hcarrier hg hcomp
    hglobalGrades hglobalSupport F hF hzero hβF χ hχeq Treg hreal hrealAdj hm hmAdj LOW hbound hlim hlimAdj Mi
    Mo Q hMi hMo hQid
    S hieven hoeven N backward U hU Top u
  let Tj := fun sector ↦ if backward then (Q sector).adjoint else Q sector
  have hj (sector : α) :=
    hprod sector ρ L hρ hL (Ac sector) (Bc sector) (W₀ sector) (W₁ sector) (branch sector) (Ψ sector)
      (_hauxPhase sector) (Aoriginal sector) (Boriginal sector) (W₀original sector) (W₁original sector)
      (hsmoothAuxAmplitude sector) (hmaskedAuxAmplitude sector) (Up sector) (Ua sector) (hUp sector)
      (hauxSmoothOn sector) (hauxPhaseGrades sector) (hauxAmplitudeGrades sector) (hauxAmplitudeCarrier
      sector) (hoBound sector) (hψmask sector) (hψmo sector) (hinputSupport sector) (_hphaseGerm sector)
      (_hphaseAgree sector) (hs sector) (a sector) (T sector) (hb sector) (hslabOut sector) (hslab sector)
      (hprimitivePhase sector) (hw sector) (hmo sector) (hprimitiveMasks sector) (Vphase sector) (Kphase
      sector) (g sector) (hVphase sector) (hKphase sector) (hKV sector) (hSphase sector) (hcarrier sector) (hg
      sector) (hcomp sector) (hglobalGrades sector) (hglobalSupport sector) (F sector) (hF sector) (hzero
      sector) (hβF sector) (χ sector) (hχeq sector) (Treg sector) (hreal sector) (hrealAdj sector) (hm sector)
      (hmAdj sector) (hbound sector) (hlim sector) (hlimAdj sector) Mi Mo (Q sector) hMi hMo (hQid sector)
  have hb sector := ((hj sector).2.2.2.2 hieven hoeven N backward U hU).1 u
  let Gs := restrictionSobolevScale U (EuclideanSpace ℂ (Fin q)) hU
  let v := fun sector ↦ restrictL2 U
    ((1 - Mo) ((Tj sector + boundedConjugate (Tj sector)) (Mi u)))
  have he : Top = ∑ sector, (Tj sector + boundedConjugate (Tj sector)) := by
    have hp (F : α → Hspace →L[ℂ] Hspace) :
        physicalPairedSectorSum Finset.univ F =
          ∑ j, (F j + boundedConjugate (F j)) := by
      apply ContinuousLinearMap.ext
      intro x
      change (∑ j, F j) x + star ((∑ j, F j) (star x)) =
        (∑ j, (F j + boundedConjugate (F j))) x
      simp only [sum_apply, add_apply]
      change (∑ j, F j x) + star (∑ j, F j (star x)) =
        ∑ j, (F j x + star (F j (star x)))
      rw [star_sum, Finset.sum_add_distrib]
    cases backward
    · exact hp Q
    · exact (physicalPairedSectorSum_adjoint_eq _ _).trans (hp _)
  have hv : restrictL2 U ((1 - Mo) (Top (Mi u))) = ∑ sector, v sector := by
    rw [he]
    simp only [sum_apply, map_sum, v]
  obtain ⟨hm, hn⟩ := ResponseTransfer.gradeNorm_sum_le Gs Finset.univ v m
    (fun sector _ ↦ (hb sector).1)
  rw [hv]
  refine ⟨hm, hn.trans ?_⟩
  simpa only [Finset.sum_mul] using Finset.sum_le_sum (fun sector _ ↦ (hb sector).2)

end JanetCartan.ArbitraryAccuracy.ResidualLocalization
