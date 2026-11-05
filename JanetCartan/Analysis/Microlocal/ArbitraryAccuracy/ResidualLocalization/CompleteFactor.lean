module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.FiniteElapsed
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.FiniteDiagonal
public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.CompleteResidual.SectorEquations
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.PolynomialCosts.Adjoints
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.ConicCollar
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.OperatorUniqueness
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.LocalizerReality
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.PhysicalLeakage

/-!
# Complete physical residual leakage on common proof localizers

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

open AmplitudeBound PhysicalShells.Comparable RegularSector.Realization KernelEstimates.NoncomparableGeometry
/-- Leakage of the complete literal physical residual from primitive phase,
amplitude and PDO grades and their exact realizations. The elapsed correction
and the three PDO branches are estimated by their actual producers; no successful
factor estimate is assumed. The original `1/i`, source and endpoint terms,
literal adjoints and ONE full identity subtraction are retained. Constants are
chosen before accuracy and current coefficients, on the SAME physical proof
localizers. Consumer: `finiteChain_observation_rapidDecayAt.hleak`
(`app:ch_regular_base:eq:energy-complete-residual`, `app:ch_regular:eq:chain-tail`).
The common physical masks are fixed inputs; applying the original chart identity
and the initialized-history primitive profiles remains with the parent. -/
theorem exists_completePhysicalResidual_restriction_bound
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
    (Fchart : α → TwoTimePoint (Euclidean d) → ℝ)
    (backward : Bool) (Dpdo : α × Fin 3 → AmplitudeProfiles)
    (hirange : ∀ p, mi p ∈ Icc (0 : ℝ) 1)
    {Ko Oo : Set (E × E)} (hobuf : IsBufferedLocalizer mo Ko Oo) (hKo : IsCompact Ko)
    (hdiagKo : tsupport mi ⊆ Ko)
    (hieven : ∀ y ξ, mi (y, -ξ) = mi (y, ξ))
    (hoeven : ∀ y ξ, mo (y, -ξ) = mo (y, ξ))
    (hdiagonalAnn : ∀ p ∈ tsupport mi, p.2 ∈ frequencyAnnulus a₀ b₀)
    (hpdoplateau : ∀ x ∈ leakageOutputCarrier backward
      (tsupport χout ×ˢ tsupport χsource) (Prod.fst '' tsupport mo), ψ x = 1) :
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
    let Kpdo := comparableJointCarrier 1 1 a₀ b₀
      ((Prod.fst '' (tsupport χout ×ˢ tsupport χsource)) ×ˢ frequencyAnnulus
        (a₀ / (16 * annulusFactor 1 1)) (4 * max 1 (4 * annulusFactor 1 1 * b₀)))
      (tsupport χout ×ˢ tsupport χsource) (frequencyAnnulus a₀ b₀)
    ∃ (bFixed : ℕ) (Cmq Creal : ℕ → ℝ),
      (∀ N, 0 ≤ Cmq N) ∧ (∀ N, 0 ≤ Creal N) ∧
    ∀ (ρ L : ℝ) (hρ : 1 ≤ ρ) (hL : 1 ≤ L) (hLρ : L ≤ ρ),
    let Ψoriginal := fun sector ↦ ConicPhase.curriedExtend (ℓ sector) (Fchart sector)
    ∀ (Ac : α → E → Fin (d + 1) → Mat),
    ∀ (Bc : α → E → Mat),
    ∀ (W₀ W₁ : α → TwoTimeAmplitude d q),
    ∀ (Ψ : α → TwoTimePhase d),
    ∀ (_hauxPhase : ∀ sector : α, ContDiff ℝ ∞ (SymbolBudgets.jointPhase (Ψ sector))),
    ∀ (Aoriginal : α → E → Fin (d + 1) → Mat),
    ∀ (Boriginal : α → E → Mat),
    ∀ (W₀original W₁original : α → TwoTimeAmplitude d q),
    let b := fun sector ↦ directRetardedAmplitudes (Ac sector) (Bc sector) (W₀ sector) (W₁ sector) true
    ∀ (hsmoothAuxAmplitude : ∀ sector : α, ContDiff ℝ ∞ (SymbolBudgets.jointAmplitude (b sector))),
    ∀ (hmaskedAuxAmplitude : ∀ sector : α, ∀ r ∈ Icc 0 Δ, elapsedAmplitude (b sector) χout χsource β r =
      elapsedAmplitude (directRetardedAmplitudes (Aoriginal sector) (Boriginal sector) (W₀original sector) (W₁original sector) true)
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
        (directRetardedAmplitudes (Aoriginal sector) (Boriginal sector) (W₀original sector) (W₁original sector) true)
        χout χsource β u),
    ∀ (bminus : α → E → E → Mat) (σ : α → E → Euclidean d → ℂ),
    let cP := fun j : α × Fin 3 ↦ directPDOSymbols
      (Aoriginal j.1) (Boriginal j.1) (W₁original j.1) (bminus j.1) (σ j.1) β (![1, 2, 3] j.2)
    let Ap := fun j ↦ orientedMaskedPDOAmplitude backward χout χsource (cP j)
    let P := fun j k ↦ maskedPhysicalPDO χout χsource
      (directPDOSymbols (Aoriginal j) (Boriginal j) (W₁original j) (bminus j) (σ j) β k)
    (∀ j, ContDiff ℝ ∞ (fun p : (E × E) × E ↦ Ap j p.1.1 p.1.2 p.2)) →
    (∀ j k p, p ∈ Kpdo → ‖iteratedFDeriv ℝ k (fun p : JointVariables E ↦
      Ap j p.1.1 p.1.2 (ρ • p.2.1)) p‖ ≤ ρ ^ s * (Dpdo j).symbol k * L ^ (k + (Dpdo j).symbolOffset)) →
    (∀ j, ∀ y ∈ (Prod.fst '' tsupport mi), ∀ k p, p ∈ Kpdo → ‖iteratedFDeriv ℝ k (fun p : JointVariables E ↦
      (mi (y, p.2.2.1) : ℂ)) p‖ ≤ (Dpdo j).inputMask k * L ^ (k + (Dpdo j).inputMaskOffset)) →
    (∀ j low l, ∀ ξ ∈ normalizedGraphCarrier ρ low l, ∀ z ∈ (tsupport χout ×ˢ tsupport χsource), ∀ k,
      ‖iteratedFDeriv ℝ k (fun z : E × E ↦ Ap j z.1 z.2 (ρ • ξ)) z‖ ≤
        (max 1 (branchRadius low l)) ^ s * (Dpdo j).symbol k * L ^ (k + (Dpdo j).symbolOffset)) →
    (∀ j x ζ k, ‖iteratedFDeriv ℝ k (fun t ↦ mo (t, ζ)) x‖ ≤
      (Dpdo j).outputMask k * L ^ (k + (Dpdo j).outputMaskOffset)) →
    ∀ F : (α × Fin 3) → Set E, (∀ j, IsClosed (F j)) → (∀ j, (0 : E) ∉ F j) →
    (∀ j x y ξ, ξ ∉ F j → Ap j x y ξ = 0) →
    ∀ χ : (α × Fin 3) → ℕ → E → ℂ,
    (∀ j (B : FullAmplitude (d + 1) q), (∀ x y ξ, ξ ∉ F j → B x y ξ = 0) →
      ∀ l, frequencyCutFullAmplitude (χ j l) B =
        frequencyCutFullAmplitude (complexPhysicalCutoff l) B) →
    ∀ Preg : (α × Fin 3) → ℕ → Hspace →L[ℂ] Hspace,
    (∀ j l (u : graphTestSpace (d + 1) q), Preg j l (graphTestToLp u) =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (((if backward then reverseGraphOperator else graphOperator)
        (fun x ξ ↦ inner ℝ x ξ) (frequencyCutFullAmplitude (χ j l) (Ap j))
        (fun y ↦ (u.val y).ofLp)) x)) →
    (∀ j u, Tendsto (fun l ↦ Preg j l u) atTop (𝓝 ((if backward then (P j.1 (![1, 2, 3] j.2)).adjoint else P j.1 (![1, 2, 3] j.2)) u))) →
    let R := fun j ↦ P j 2 + Q j + (1 / Complex.I) • P j 3
    let Efull := physicalPairedSectorSum Finset.univ (fun j ↦ P j 1 + R j) - 1
    ∀ N (U : Set E) (hU : MeasurableSet U),
      let Top := if backward then Efull.adjoint else Efull
      (∀ u : Hspace, restrictL2 U ((1 - Mo) (Top (Mi u))) ∈
        (restrictionSobolevScale U (EuclideanSpace ℂ (Fin q)) hU).level m ∧
        (restrictionSobolevScale U (EuclideanSpace ℂ (Fin q)) hU).gradeNorm m
          (restrictL2 U ((1 - Mo) (Top (Mi u)))) ≤
          Cmq N * ρ ^ ((m : ℝ) + (max 0 s + (3 * (d + 1) : ℕ))) *
            L ^ bFixed * (L / ρ) ^ N * ‖u‖) ∧
      ∀ u : Lp (EuclideanSpace ℝ (Fin q)) 2 (volume : Measure E),
        let v := l2RealPart (volume.restrict U)
          (restrictL2 U ((1 - Mo) (Top (Mi (l2ComplexInclusion volume u)))))
        v ∈ (restrictionSobolevScale U (EuclideanSpace ℝ (Fin q)) hU).level m ∧
        (restrictionSobolevScale U (EuclideanSpace ℝ (Fin q)) hU).gradeNorm m v ≤
          Creal N * ρ ^ ((m : ℝ) + (max 0 s + (3 * (d + 1) : ℕ))) *
            L ^ bFixed * (L / ρ) ^ N * ‖u‖ := by
  classical
  intro KG hΨsupport hC hdiag hflow hR hqB hinit hphaseB hqI hclock hphaseI
    hGermB hGermI hsupported Kpdo
  obtain ⟨bE, CE, hCE, hElapsed⟩ := exists_finiteConic_directResidual_restriction_bound
    eT eI eu ez J hJ s Δ hΔ m bo offset bt bs bg bb bi c C b₀ hc ha₀ hCi
    χout χsource β hχout hχsource hβsmooth hout hsource hBβ hCβ hβ hcone
    Pbase Bbase Ophysical hPbase hBbase hOphysical hK
    P₀ W O Qt Qs Qg Qb Qi hP₀ hQt hQs hQg hQb hQi hW hO
    Y hY ψ hψ hsψ hψb θ hθ hsθ hθone mi mo hi ho horange his hos hiAnn hiBound
    Dglobal hKglobal h Φ Cchart Ψsupport R ℓ Fchart
    hΨsupport hC hdiag hflow hR hqB hinit hphaseB hqI hclock hphaseI
    hGermB hGermI hsupported
  let weights : α × Fin 3 → ℂ := fun j ↦ ![1, 1, 1 / Complex.I] j.2
  let branches : α × Fin 3 → Fin 4 := fun j ↦ ![1, 2, 3] j.2
  obtain ⟨bP, CP, RP, hCP, hRP, hPdo⟩ := exists_finitePhysicalPDO_defect_restriction_bound
    eT eu ez backward s m weights branches ha₀ (fun _ ↦ χout) (fun _ ↦ χsource)
    (fun _ ↦ hout) (fun _ ↦ hsource) mi mo hi his hirange hobuf hKo hdiagKo hieven hoeven
    hdiagonalAnn J hJ ψ hψ hsψ (fun _ ↦ hpdoplateau) Dpdo
  let Ctotal := fun N ↦ CP N + CE N
  let Rpart := euclideanRealPart (ι := Fin q)
  refine ⟨bP + bE, Ctotal, fun N ↦ (‖Rpart‖ + 1) * Ctotal N,
    fun N ↦ add_nonneg (hCP N) (hCE N),
    fun N ↦ mul_nonneg (by positivity) (add_nonneg (hCP N) (hCE N)), ?_⟩
  intro ρ L hρ hL hLρ Ψoriginal Ac Bc W₀ W₁ Ψ _hauxPhase Aoriginal Boriginal W₀original W₁original b
    hsmoothAuxAmplitude hmaskedAuxAmplitude Up Ua hUp hauxSmoothOn hauxPhaseGrades hauxAmplitudeGrades
    hauxAmplitudeCarrier hoBound hψmask hψmo hinputSupport _hphaseGerm _hphaseAgree hs a T hb hslabOut hslab
    hprimitivePhase hw hmo hprimitiveMasks Vphase Kphase g hVphase hKphase hKV hSphase hcarrier hg hcomp
    hglobalGrades hglobalSupport F hF hzero hβF χ hχeq Treg hreal hrealAdj hm hmAdj LOW hbound hlim hlimAdj Mi
    Mo Q hMi hMo hQid
    bminus σ cP Ap P hAp hsymbol hin hbase houtGrade Fp hFp hzerop hAFp χp hχeqp Preg hrealp hlimp
    Rfull Efull N U hU Top
  have hEb := hElapsed ρ L hρ hL Ac Bc W₀ W₁ (fun _ ↦ true) Ψ _hauxPhase Aoriginal Boriginal W₀original
    W₁original hsmoothAuxAmplitude hmaskedAuxAmplitude Up Ua hUp hauxSmoothOn hauxPhaseGrades
    hauxAmplitudeGrades hauxAmplitudeCarrier hoBound hψmask hψmo hinputSupport _hphaseGerm _hphaseAgree hs a T
    hb hslabOut hslab hprimitivePhase hw hmo hprimitiveMasks Vphase Kphase g hVphase hKphase hKV hSphase
    hcarrier hg hcomp hglobalGrades hglobalSupport F hF hzero hβF χ hχeq Treg hreal hrealAdj hm hmAdj hbound
    hlim hlimAdj Mi Mo Q hMi hMo hQid hieven hoeven N backward U hU
  have hPb := (hPdo ρ L hL hLρ Mi Mo hMi hMo
    (fun j ↦ Aoriginal j.1) (fun j ↦ Boriginal j.1) (fun j ↦ W₁original j.1)
    (fun j ↦ bminus j.1) (fun j ↦ σ j.1) (fun _ ↦ β)
    hAp hsymbol hin hbase houtGrade Fp hFp hzerop hAFp χp hχeqp Preg hrealp hlimp N U hU).1
  let DP := physicalPairedSectorSum Finset.univ (fun j : α × Fin 3 ↦
    weights j • P j.1 (branches j)) - (1 : Hspace →L[ℂ] Hspace)
  let QE := physicalPairedSectorSum Finset.univ Q
  have hsplit : Efull = DP + QE := by
    have hs : (∑ j : α × Fin 3, weights j • P j.1 (branches j)) =
        ∑ j, (P j 1 + P j 2 + (1 / Complex.I) • P j 3) := by
      simp [weights, branches, Fintype.sum_prod_type, Fin.sum_univ_succ, add_assoc]
    have hp : physicalPairedSectorSum Finset.univ (fun j : α × Fin 3 ↦
        weights j • P j.1 (branches j)) =
        physicalPairedSectorSum Finset.univ (fun j ↦ P j 1 + P j 2 + (1 / Complex.I) • P j 3) := by
      simp only [physicalPairedSectorSum, hs]
    have hh : (fun j ↦ P j 1 + Rfull j) =
        fun j ↦ (P j 1 + P j 2 + (1 / Complex.I) • P j 3) + Q j := by
      funext j
      dsimp [Rfull]
      abel
    dsimp [Efull, DP, QE]
    rw [hp, hh, physicalPairedSectorSum_add]
    abel
  let Tp := if backward then DP.adjoint else DP
  let Tq := if backward then QE.adjoint else QE
  have hTop : Top = Tp + Tq := by
    dsimp only [Top, Tp, Tq]
    rw [hsplit]
    cases backward <;> simp only [Bool.false_eq_true, ite_false, ite_true, map_add]
  let Gs := restrictionSobolevScale U (EuclideanSpace ℂ (Fin q)) hU
  let exponent : ℝ := (m : ℝ) + (max 0 s + (3 * (d + 1) : ℕ))
  have hρpos : 0 < ρ := zero_lt_one.trans_le hρ
  have hLnonneg : 0 ≤ L := zero_le_one.trans hL
  have henlarge (A : ℝ) (hA : 0 ≤ A) (b : ℕ) (hb : b ≤ bP + bE) (u : Hspace) :
      A * ρ ^ exponent * L ^ b * (L / ρ) ^ N * ‖u‖ ≤
      A * ρ ^ exponent * L ^ (bP + bE) * (L / ρ) ^ N * ‖u‖ := by
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg u)
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg (div_nonneg hLnonneg hρpos.le) _)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL hb)
      (mul_nonneg hA (Real.rpow_nonneg hρpos.le _))
  have hcomplex (u : Hspace) : restrictL2 U ((1 - Mo) (Top (Mi u))) ∈ Gs.level m ∧
      Gs.gradeNorm m (restrictL2 U ((1 - Mo) (Top (Mi u)))) ≤
        Ctotal N * ρ ^ exponent * L ^ (bP + bE) * (L / ρ) ^ N * ‖u‖ := by
    have hp : restrictL2 U ((1 - Mo) (Tp (Mi u))) ∈ Gs.level m ∧
        Gs.gradeNorm m (restrictL2 U ((1 - Mo) (Tp (Mi u)))) ≤
          CP N * ρ ^ exponent * L ^ (bP + bE) * (L / ρ) ^ N * ‖u‖ :=
      ⟨(hPb u).1, (hPb u).2.trans (henlarge _ (hCP N) bP (Nat.le_add_right _ _) u)⟩
    have hq : restrictL2 U ((1 - Mo) (Tq (Mi u))) ∈ Gs.level m ∧
        Gs.gradeNorm m (restrictL2 U ((1 - Mo) (Tq (Mi u)))) ≤
          CE N * ρ ^ exponent * L ^ (bP + bE) * (L / ρ) ^ N * ‖u‖ :=
      ⟨(hEb u).1, (hEb u).2.trans (henlarge _ (hCE N) bE (Nat.le_add_left _ _) u)⟩
    rw [hTop, add_apply, map_add, map_add]
    exact ⟨(Gs.level m).add_mem hp.1 hq.1,
      (ResponseTransfer.gradeNorm_add_le Gs hp.1 hq.1).trans
        ((add_le_add hp.2 hq.2).trans_eq (by dsimp [Ctotal]; ring))⟩
  refine ⟨hcomplex, ?_⟩
  intro u v
  obtain ⟨hm, hn⟩ := hcomplex (l2ComplexInclusion volume u)
  obtain ⟨hr, hnr⟩ := compLp_restrictionSobolev_bound Rpart hm
  refine ⟨hr, ?_⟩
  change (restrictionSobolevScale U (EuclideanSpace ℝ (Fin q)) hU).gradeNorm m
    (Rpart.compLp _) ≤ _
  rw [restrictionSobolevScale_gradeNorm hU hr]
  apply hnr.trans
  rw [← restrictionSobolevScale_gradeNorm hU hm]
  have hu : ‖l2ComplexInclusion volume u‖ ≤ ‖u‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans ((mul_le_mul_of_nonneg_right
      (l2ComplexInclusion_norm_le volume) (norm_nonneg u)).trans_eq (one_mul _))
  have hcoef : 0 ≤ Ctotal N * ρ ^ exponent * L ^ (bP + bE) * (L / ρ) ^ N := by
    have : 0 ≤ Ctotal N := add_nonneg (hCP N) (hCE N)
    positivity
  have hfinal := hn.trans (mul_le_mul_of_nonneg_left hu hcoef)
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hfinal (show 0 ≤ ‖Rpart‖ + 1 by positivity)

end JanetCartan.ArbitraryAccuracy.ResidualLocalization
