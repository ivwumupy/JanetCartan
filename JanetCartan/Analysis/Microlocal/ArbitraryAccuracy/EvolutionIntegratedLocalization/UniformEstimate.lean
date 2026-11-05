module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.CompactSupport
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.SupportedMajorants
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.SupportedGlobalMajorant
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.OperatorUniqueness

/-!
# Unregularized elapsed localization from primitive joint grades

The shell-majorant premises are discharged by the quantitative joint half-space
and separated per-time estimates. The global majorant, compact-frequency
regularity, supported phase extension, summability and strong identification
are all instantiated for the same physical kernels. The constants precede
frequency, coefficient scale and original phase/amplitude data.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
open FourierIntegral FiniteChain.Graph KernelEstimates PhysicalShells CartesianJets KernelLimits
open PhysicalShells.Noncomparable
open FiniteChain.Retarded.KernelDecay FiniteChain.Retarded.HalfSpace JanetCartan.Localization
open RegularSector.Characteristic.EvolutionIntegral
open EvolutionLocalization.SobolevRealization Pseudodifferential
open LowBounds LowBounds.FrequencyCutoff FiniteChain.Retarded.KernelSobolev
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "V" => ℝ × JointVariables (Euclidean (d + 1))
local notation "Hspace" => SpacetimeL2 d q
attribute [local instance] KernelLimits.matrixContinuousENorm KernelLimits.matrixPseudoMetrizableSpace
set_option synthInstance.maxSize 256
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

/-- The actual localized elapsed integral, in both orientations, has the
`L² → Hᵐ` bound of `app:ch_regular:eq:chain-tail` from common primitive joint
phase/amplitude/cutoff grades and the identified per-time noncomparable graph
bounds. No integrated bound or shell-majorant conclusion is an input. The
fixed losses are `max 0 s + 3*(d+1)` and `max (m+bo+ba) (sup_{l≤m} bLoss(l))`.

`PhaseGrades` and `AmplitudeGrades` produce the joint grades from the original
two-time data; `UniformCollar` supplies the geometric inputs from the actual
compact buffered stationary exclusions. The finite test realizations, LOW
bounds and strong limits are the exact `EvolutionIntegral` producer outputs.
Actual finite-family geometric and coefficient data remain the response
parent's instantiation obligation. The phase is only required smooth on its
supported chart; the original operator and literal adjoint are retained
(`app:ch_regular_base:eq:fixed-time-representation`). -/
theorem exists_uniform_elapsedGraphIntegral_fourier_bound_of_joint_grades
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (eT : ι → JointVariables E) (eI : κ → V)
    (J : (ℝ × (Fin d → ℝ)) ≃L[ℝ] E)
    (hJ : MeasurePreserving (graphInputCoordinates J) volume volume)
    (s Δ : ℝ) (hΔ : 0 ≤ Δ) (m bo ba : ℕ) (bLoss : ℕ → ℕ)
    (c C b₀ : ℝ) {a₀ : ℝ} (ha₀ : 0 < a₀)
    {K : Set V} (hK : IsCompact K)
    (δT δI GT GI : ℝ) (hδT : 0 < δT) (hδI : 0 < δI)
    (P H W O A : ℕ → ℝ) (D : ℕ → ℕ → ℝ)
    (hH : ∀ j, 0 ≤ H j) (hW : ∀ j, 0 ≤ W j)
    (hO : ∀ j, 0 ≤ O j) (hA : ∀ j, 0 ≤ A j) (hD : ∀ l N, 0 ≤ D l N)
    (Y : Set E) (hY : IsCompact Y)
    (ψ : E → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hsψ : HasCompactSupport ψ)
    (hψb : ∀ x, ‖ψ x‖ ≤ 1)
    (θ : ℝ → ℂ) (hθ : ContDiff ℝ ∞ θ) (hsθ : HasCompactSupport θ)
    (hθone : ∀ r ∈ Icc 0 Δ, θ r = 1)
    (Dglobal : AmplitudeProfiles) {Kglobal : Set (JointVariables E)} (hKglobal : IsCompact Kglobal) :
    ∃ Cq : ℕ → ℝ, (∀ N, 0 ≤ Cq N) ∧
    ∀ (ρ L : ℝ) (hρ : 1 ≤ ρ) (hL : 1 ≤ L)
      (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q)
    (χout χsource β : E → ℂ) (mi mo : LocalizerSymbol (d + 1))
    (hi : ContDiff ℝ ∞ mi) (ho : ContDiff ℝ ∞ mo)
    (horange : ∀ p, mo p ∈ Icc (0 : ℝ) 1)
    (his : HasCompactSupport mi) (hos : HasCompactSupport mo)
    (hout : HasCompactSupport χout) (hsource : HasCompactSupport χsource)
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
    (hper : ∀ backward l, l ≤ m → ∀ N low j k, SeparatedRanges c C (a₀ * ρ) (b₀ * ρ)
        (graphLower low j) (graphUpper low j) (outputLower k) (outputUpper k) →
      ∀ r ∈ Icc 0 Δ, ∀ x ∈ tsupport ψ, ∀ y ∈ Prod.fst '' tsupport mi,
      ∀ v : Fin l → E, (∀ i, ‖v i‖ ≤ 1) →
      ‖iteratedFDeriv ℝ l (fun t ↦ KernelLimits.regularizedJointKernel backward
        (elapsedPhase Ψ r) (orientedElapsedAmplitude backward b χout χsource β r)
        (fun p ↦ mi (p.1, ρ⁻¹ • p.2)) (fun p ↦ mo (p.1, ρ⁻¹ • p.2))
          (graphBranchCutoff low j) (outputCutoff k) t y) x v‖ ≤
        D l N * ρ ^ (d + 1) * L ^ (bLoss l) * (L / ρ) ^ N * pairWeight low (d + 1) j k)
    (hglobalGrades : ∀ backward low j k, IsComparablePair c C a₀ b₀ ρ low j k →
      ∀ r ∈ Icc 0 Δ, ∀ y, HasAmplitudeGrades Dglobal ρ (ρ ^ s) L
        (orientedElapsedAmplitude backward b χout χsource β r) mi (fun _ ↦ 0)
        (graphBranchCutoff low j) (outputCutoff k) 0 y Kglobal)
    (hglobalSupport : ∀ backward low j k, IsComparablePair c C a₀ b₀ ρ low j k →
      ∀ r ∈ Icc 0 Δ, ∀ y, tsupport (jointAmplitude ρ
        (orientedElapsedAmplitude backward b χout χsource β r) mi (fun _ ↦ 0)
        (graphBranchCutoff low j) (outputCutoff k) 0 y) ⊆ Kglobal)
    (Dsep : ℝ) (hDsep : 0 ≤ Dsep)
    (hperGlobal : ∀ backward low j k, SeparatedRanges c C (a₀ * ρ) (b₀ * ρ)
        (graphLower low j) (graphUpper low j) (outputLower k) (outputUpper k) →
      ∀ r ∈ Icc 0 Δ, ∀ x y,
      ‖KernelLimits.regularizedJointKernel backward (elapsedPhase Ψ r)
        (orientedElapsedAmplitude backward b χout χsource β r)
        (fun p ↦ mi (p.1, ρ⁻¹ • p.2)) (fun p ↦ mo (p.1, ρ⁻¹ • p.2))
          (graphBranchCutoff low j) (outputCutoff k) x y‖ ≤
        Dsep * ρ ^ (d + 1) * L ^ (bLoss 0) * pairWeight low (d + 1) j k)
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
            L ^ (max ((m + bo) + ba) ((Finset.range (m + 1)).sup bLoss)) * (L / ρ) ^ N * ‖u‖ := by
  classical
  have hmajor (backward : Bool) (l : ℕ) :=
    exists_elapsedPhysicalShellKernel_majorants_of_supported_joint_grades
      (q := q) eT eI backward s Δ l bo ba (bLoss l) c C b₀ ha₀ hK δT δI GT GI hδT hδI
      P H W O A (D l) hH hW hO hA (hD l)
  choose Cjet hCjet hjet using hmajor
  let coeff := fun backward N ↦
    fourierComparisonConstant J m * ((q : ℝ) * q) *
      jetMajorant J (cutoffDerivativeProfile hψ hsψ) (fun l ↦ Cjet backward l N) m *
      compactSupportFactor volume volume
        ((fun y : (Fin d → ℝ) × ℝ ↦ J (y.2, y.1)) ⁻¹' Y)
        (Prod.swap ⁻¹' (J ⁻¹' tsupport ψ))
  refine ⟨fun N ↦ |coeff false N| + |coeff true N|, fun N ↦ by positivity, ?_⟩
  intro ρ L hρ hL Ψ b χout χsource β mi mo hi ho horange his hos hout hsource
    hψmask hψmo hinputSupport hSc hS hAmp Jphase Wphase hJphase hWphase hJW hPhase
    hPhaseSupport hmap hs a T hb hslabOut hslab χ UT UI ε hε hχ hUT hUI hχone hχT hχI
    hgapT hupperT hgapI hupperI hp hχbound hw hmo hab hper hglobalGrades hglobalSupport
    Dsep hDsep hperGlobal F hF hzero hβF χreg hχeq Treg hreal hrealAdj hm hmAdj
    LOW hbound hlim hlimAdj
  have hρ0 : 0 < ρ := zero_lt_one.trans_le hρ
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hAr (backward : Bool) (r : ℝ) : Continuous (fun p : (E × E) × E ↦
      orientedElapsedAmplitude backward b χout χsource β r p.1.1 p.1.2 p.2) :=
    (hAmp backward).continuous.comp (continuous_const.prodMk continuous_id)
  have hSr (r : ℝ) : Continuous (Function.uncurry (elapsedPhase Ψ r)) :=
    hSc.comp (continuous_const.prodMk (continuous_fst.prodMk continuous_snd))
  have hAnorm (backward : Bool) : ContDiff ℝ ∞ (fun p : V ↦
      orientedElapsedAmplitude backward b χout χsource β p.1 p.2.1.1 p.2.1.2 (ρ • p.2.2.1)) :=
    (hAmp backward).comp (show ContDiff ℝ ∞ (fun p : V ↦
      (p.1, ((p.2.1.1, p.2.1.2), ρ • p.2.2.1))) from by fun_prop)
  have ha (backward : Bool) (y : E) (low : Bool) (j k : ℕ) :
      ContDiff ℝ ∞ (fun p : V ↦ θ p.1 • jointElapsedAmplitude backward ρ b χout χsource β
        mi (fun _ ↦ 0) (graphBranchCutoff low j) (outputCutoff k) 0 y p) := by
    change E × E → ℝ at mi mo
    have hg := contDiff_graphBranchCutoff (n := d + 1) low j
    have hc := contDiff_outputCutoff (n := d + 1) k
    have hA' := hAnorm backward
    have hmask : ContDiff ℝ ∞ (fun p : V ↦
        graphBranchCutoff low j (ρ • p.2.2.1) * outputCutoff k (ρ • p.2.2.2.2) *
          (1 - (0 : ℝ)) * mi (y, p.2.2.2.1)) := by fun_prop
    exact (hθ.comp contDiff_fst).smul
      ((Complex.ofRealCLM.contDiff.comp hmask).smul hA')
  have hcompact (backward : Bool) (y : E) (low : Bool) (j k : ℕ) :=
    hasCompactSupport_cut_jointElapsedAmplitude backward hρ0.ne' b χout χsource β mi
      (fun _ ↦ 0) (graphBranchCutoff low j) (outputCutoff k) 0 y θ hsθ hout hsource his
      (hasCompactSupport_graphBranchCutoff low j) (hasCompactSupport_outputCutoff k)
  let carriers (backward : Bool) (j k : ℕ) (r : ℝ) :
      KernelLimits.RegularizedCarriers (orientedElapsedAmplitude backward b χout χsource β r)
        mi (graphCutoff j) (outputCutoff k) := {
    amplitudeBase := tsupport χout ×ˢ tsupport χsource
    inputBase := Prod.fst '' tsupport mi
    inputFrequency := Prod.snd '' tsupport mi
    compact_amplitudeBase := hout.prod hsource
    compact_inputBase := his.image continuous_fst
    compact_inputFrequency := his.image continuous_snd
    compact_graphCutoff := hasCompactSupport_graphCutoff j
    compact_outputCutoff := hasCompactSupport_outputCutoff k
    amplitude_zero := by
      intro u z ξ hz
      have hbzero : elapsedAmplitude b χout χsource β r u z ξ = 0 := by
        by_cases hu : u ∈ tsupport χout
        · have hzs : z ∉ tsupport χsource := fun hh ↦ hz ⟨hu, hh⟩
          exact elapsedAmplitude_eq_zero_of_mask b χout χsource β r u z ξ
            (Or.inr (Or.inl (image_eq_zero_of_notMem_tsupport hzs)))
        · exact elapsedAmplitude_eq_zero_of_mask b χout χsource β r u z ξ
            (Or.inl (image_eq_zero_of_notMem_tsupport hu))
      cases backward <;> simp only [orientedElapsedAmplitude, Bool.false_eq_true,
        ite_false, ite_true, hbzero, Matrix.conjTranspose_zero]
    input_zero := by
      intro y η h
      exact image_eq_zero_of_notMem_tsupport
        (fun hh ↦ h ⟨⟨(y, η), hh, rfl⟩, ⟨(y, η), hh, rfl⟩⟩) }
  have hinput : ∀ y ∉ Prod.fst '' tsupport mi, ∀ η, mi (y, η) = 0 := by
    intro y hy η
    exact image_eq_zero_of_notMem_tsupport (fun hh ↦ hy ⟨(y, η), hh, rfl⟩)
  have hmajActual (backward : Bool) (l : ℕ) (hl : l ≤ m) := hjet backward l ρ L hρ hL Ψ b
    χout χsource β mi mo θ (tsupport ψ) (Prod.fst '' tsupport mi) hinput hθone
    (fun r _ ↦ hSr r) (fun r _ ↦ hAr backward r) hi.continuous ho
    (fun j k r _ ↦ carriers backward j k r) Jphase Wphase hJphase hWphase hJW hPhase
    hPhaseSupport hmap (fun y _ ↦ ha backward y) (fun y _ ↦ hcompact backward y)
    (hs backward) a T hb hslabOut hslab (χ backward) (UT backward) (UI backward) ε hε
    (hχ backward) (hUT backward) (hUI backward) (hχone backward) (hχT backward)
    (hχI backward) (hgapT backward) (hupperT backward) (hgapI backward)
    (hupperI backward) (hp backward) (hχbound backward) hw hmo (hab backward) (hper backward l hl)
  choose M hM using hmajActual
  let B := fun backward l N ↦ if hl : l ≤ m then M backward l hl N else fun _ ↦ (0 : ℝ)
  obtain hglobal := exists_elapsedPhysicalShellKernel_global_majorant_of_supported_grades
    hρ hL Δ Ψ b χout χsource β mi mo hi.continuous ho horange his hout hsource
    (fun backward ↦ (hAmp backward).continuous) θ hθone ha hcompact
    hJphase hWphase hJW hPhase hPhaseSupport s c C b₀ ha₀ Dglobal hKglobal
    hglobalGrades hglobalSupport hDsep (bLoss 0) hperGlobal
  choose C₀ hs₀ hb₀ using hglobal
  have hgrades (N : ℕ) (backward : Bool) (l : ℕ) (hl : l ≤ m) :
      (∑' p, B backward l N p) ≤ Cjet backward l N *
        ρ ^ ((l : ℝ) + (max 0 s + (3 * (d + 1) : ℕ))) *
          L ^ (max ((m + bo) + ba) ((Finset.range (m + 1)).sup bLoss)) * (L / ρ) ^ N := by
    simp only [B, dite_eq_left hl]
    apply (hM backward l hl N).2.2.1.trans
    have horder : max ((l + bo) + ba) (bLoss l) ≤
        max ((m + bo) + ba) ((Finset.range (m + 1)).sup bLoss) :=
      max_le_max (by omega) (Finset.le_sup (Finset.mem_range.mpr (by omega)))
    gcongr
    exact mul_nonneg (hCjet backward l N) (Real.rpow_nonneg hρ0.le _)
  have hrealized (N : ℕ) :=
    exists_identified_elapsedGraphIntegral_fourier_bound J hJ hρ hL0 Δ hΔ Ψ b
      χout χsource β mi mo hi ho his hos hout hsource hSc hS hAmp
      hJphase hWphase hJW hPhase hPhaseSupport ψ hψ hsψ hψb hψmask hψmo
      F hF hzero hβF χreg hχeq Treg hreal hrealAdj hm hmAdj hbound hlim hlimAdj
      C₀ hs₀ (fun backward p ↦ hb₀ backward p.1 p.2)
      (fun backward l ↦ B backward l N)
      (fun backward l hl ↦ by simpa only [B, dite_eq_left hl] using (hM backward l hl N).1)
      (fun backward l hl ↦ by simpa only [B, dite_eq_left hl] using (hM backward l hl N).2.1)
      (fun backward p x hx y l hl v hv ↦ by
        simpa only [B, dite_eq_left hl] using
          (hM backward l hl N).2.2.2 x hx y v hv |>.1 p.1 p.2)
      (max 0 s + (3 * (d + 1) : ℕ)) (max ((m + bo) + ba) ((Finset.range (m + 1)).sup bLoss)) N
      (fun backward l ↦ Cjet backward l N) (fun backward l _ ↦ hCjet backward l N) (hgrades N)
  obtain ⟨Mi, Mo, Q, hMi, hMo, hQnorm, hQ, hQA, _⟩ := hrealized 0
  refine ⟨Mi, Mo, Q, hMi, hMo, hQnorm, hQ, hQA, ?_⟩
  intro N backward u
  obtain ⟨Mi', Mo', Q', hMi', hMo', _, hQ', _, hSob⟩ := hrealized N
  have hMiEq : Mi' = Mi := eq_of_rightLocalizer_representatives ρ mi Mi' Mi hMi' hMi
  have hMoEq : Mo' = Mo := eq_of_leftLocalizer_representatives ρ mo Mo' Mo hMo' hMo
  have hQEq : Q' = Q := ContinuousLinearMap.ext (fun u ↦ (hQ' u).trans (hQ u).symm)
  subst Mi' Mo' Q'
  refine ⟨(hSob backward u).1, (hSob backward u).2.trans ?_⟩
  have hc : coeff backward N ≤ |coeff false N| + |coeff true N| := by
    cases backward
    · exact (le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _))
    · exact (le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _))
  have hYC : IsCompact ((fun y : (Fin d → ℝ) × ℝ ↦ J (y.2, y.1)) ⁻¹' Y) :=
    ((Homeomorph.prodComm _ _).trans J.toHomeomorph).isCompact_preimage.mpr hY
  have hsf : compactSupportFactor volume volume
      ((fun y : (Fin d → ℝ) × ℝ ↦ J (y.2, y.1)) ⁻¹' (Prod.fst '' tsupport mi))
      (Prod.swap ⁻¹' (J ⁻¹' tsupport ψ)) ≤
      compactSupportFactor volume volume
        ((fun y : (Fin d → ℝ) × ℝ ↦ J (y.2, y.1)) ⁻¹' Y)
        (Prod.swap ⁻¹' (J ⁻¹' tsupport ψ)) :=
    mul_le_mul_of_nonneg_right
      (Real.sqrt_le_sqrt (measureReal_mono (preimage_mono hinputSupport) hYC.measure_ne_top))
      (Real.sqrt_nonneg _)
  have hcf := mul_le_mul_of_nonneg_left hsf
    (mul_nonneg (mul_nonneg (fourierComparisonConstant_pos J m).le
      (mul_nonneg (Nat.cast_nonneg q) (Nat.cast_nonneg q)))
      (jetMajorant_nonneg (m := m) J (cutoffDerivativeProfile_nonneg hψ hsψ)
        (fun l _ ↦ hCjet backward l N)))
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hcf.trans hc) (Real.rpow_nonneg hρ0.le _)) (pow_nonneg hL0 _))
      (pow_nonneg (div_nonneg hL0 hρ0.le) _)) (norm_nonneg u)

end JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
