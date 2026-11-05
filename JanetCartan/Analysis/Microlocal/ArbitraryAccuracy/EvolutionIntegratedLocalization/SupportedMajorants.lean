module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.KernelMajorants
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.SupportedSobolev

/-!
# Quantitative shell majorants for the original supported conic phase

The smooth extension is constructed once in both time variables. Its equality
locus is open, so intersecting the two integration domains with that locus
preserves all buffered carriers, gaps and primitive grades. This discharges
the global phase smoothness premise without changing any physical shell.
Consumer: the identified unregularized estimate of `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
open FourierIntegral FiniteChain.Graph KernelEstimates PhysicalShells
open PhysicalShells.Noncomparable
open FiniteChain.Retarded.KernelDecay FiniteChain.Retarded.HalfSpace JanetCartan.Localization
open RegularSector.Characteristic.EvolutionIntegral
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "V" => ℝ × JointVariables (Euclidean (d + 1))
attribute [local instance] KernelLimits.matrixContinuousENorm KernelLimits.matrixPseudoMetrizableSpace
set_option synthInstance.maxSize 256
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- Physical dilation preserves the germ of the original two-time phase.
Together with `jointElapsedPhase_eventuallyEq_of_twoTimePhase`, this transfers
all joint derivative grades, including elapsed derivatives
(`app:ch_regular:eq:high-phase`). -/
theorem normalizedTwoTimePhase_eventuallyEq_of_germ
    (ρ : ℝ) (Ψ Ψ' : TwoTimePhase d) (p : SymbolBudgets.TwoTimePoint d)
    (he : SymbolBudgets.jointPhase Ψ' =ᶠ[𝓝 (p.1, ρ • p.2)] SymbolBudgets.jointPhase Ψ) :
    SymbolBudgets.jointPhase (SymbolBudgets.normalizedTwoTimePhase ρ Ψ') =ᶠ[𝓝 p]
      SymbolBudgets.jointPhase (SymbolBudgets.normalizedTwoTimePhase ρ Ψ) := by
  have hc : Continuous (fun z : SymbolBudgets.TwoTimePoint d ↦ (z.1, ρ • z.2)) := by fun_prop
  filter_upwards [he.comp_tendsto (hc.tendsto p)] with z hz
  change ρ⁻¹ * SymbolBudgets.jointPhase Ψ' (z.1, ρ • z.2) =
    ρ⁻¹ * SymbolBudgets.jointPhase Ψ (z.1, ρ • z.2)
  exact congrArg (fun t : ℝ ↦ ρ⁻¹ * t) hz

/-- The complete shell majorant follows from primitive grades and separation
on the original supported conic phase. The extension and open equality domains
are constructed, and removed from both per-time and elapsed kernels. Constants
precede the scales and symbols; the only kernel estimates assumed are the
identified per-time separated estimates produced by `EvolutionLocalization`.
Both elapsed endpoints and the original adjoint order are retained
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_elapsedPhysicalShellKernel_majorants_of_supported_joint_grades
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (eT : ι → JointVariables E) (eI : κ → V)
    (backward : Bool) (s Δ : ℝ) (m bo ba bLoss : ℕ)
    (c C b₀ : ℝ) {a₀ : ℝ} (ha₀ : 0 < a₀)
    {K : Set V} (hK : IsCompact K)
    (δT δI GT GI : ℝ) (hδT : 0 < δT) (hδI : 0 < δI)
    (P H W O A D : ℕ → ℝ)
    (hH : ∀ j, 0 ≤ H j) (hW : ∀ j, 0 ≤ W j)
    (hO : ∀ j, 0 ≤ O j) (hA : ∀ j, 0 ≤ A j) (hD : ∀ j, 0 ≤ D j) :
    ∃ Cq : ℕ → ℝ, (∀ N, 0 ≤ Cq N) ∧
    ∀ (ρ L : ℝ), 1 ≤ ρ → 1 ≤ L →
    ∀ (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q)
      (χout χsource β : E → ℂ) (mi mo : LocalizerSymbol (d + 1))
      (θ : ℝ → ℂ) (X Y : Set E),
    (∀ y ∉ Y, ∀ η, mi (y, η) = 0) →
    (∀ r ∈ Icc 0 Δ, θ r = 1) →
    (∀ r ∈ Icc 0 Δ, Continuous (Function.uncurry (elapsedPhase Ψ r))) →
    (∀ r ∈ Icc 0 Δ, Continuous (fun p : (E × E) × E ↦
      orientedElapsedAmplitude backward b χout χsource β r p.1.1 p.1.2 p.2)) →
    Continuous mi → ContDiff ℝ ∞ mo →
    (∀ j k r, r ∈ Icc 0 Δ →
      KernelLimits.RegularizedCarriers (orientedElapsedAmplitude backward b χout χsource β r)
        mi (graphCutoff j) (outputCutoff k)) →
    ∀ (Jphase Wphase : Set (SymbolBudgets.TwoTimePoint d)),
    IsClosed Jphase → IsOpen Wphase → Jphase ⊆ Wphase →
    ContDiffOn ℝ ∞ (SymbolBudgets.jointPhase Ψ) Wphase →
    (∀ r ∈ Icc 0 Δ, ∀ u z ξ, elapsedAmplitude b χout χsource β r u z ξ ≠ 0 →
      ((u 0, u 0 - r, spatialPart u), spatialPart ξ) ∈ Jphase) →
    (∀ x ∈ X, ∀ y ∈ Y, ∀ p ∈ elapsedOutputJetCarrier K mi mo x y,
      ((elapsedJointCoordinates p).1, ρ • (elapsedJointCoordinates p).2) ∈ Jphase) →
    (∀ y ∈ Y, ∀ low j k, ContDiff ℝ ∞ (fun p : V ↦ θ p.1 •
      jointElapsedAmplitude backward ρ b χout χsource β mi (fun _ ↦ 0)
        (graphBranchCutoff low j) (outputCutoff k) 0 y p)) →
    (∀ y ∈ Y, ∀ low j k, HasCompactSupport (fun p : V ↦ θ p.1 •
      jointElapsedAmplitude backward ρ b χout χsource β mi (fun _ ↦ 0)
        (graphBranchCutoff low j) (outputCutoff k) 0 y p)) →
    (∀ y ∈ Y, ∀ low j k, IsComparablePair c C a₀ b₀ ρ low j k →
      tsupport (fun p : V ↦ θ p.1 •
        jointElapsedAmplitude backward ρ b χout χsource β mi (fun _ ↦ 0)
          (graphBranchCutoff low j) (outputCutoff k) 0 y p) ⊆ K) →
    ∀ (a T : ℝ), (∀ t t' u η, t' ≤ a → b t t' u η = 0) →
    (∀ u, T < u 0 → χout u = 0) → T - a ≤ Δ →
    ∀ (χ : E → E → V → ℂ) (UT UI : E → E → Set V) (ε : ℝ), 0 < ε →
    (∀ x ∈ X, ∀ y ∈ Y, ContDiff ℝ ∞ (χ x y)) →
    (∀ x ∈ X, ∀ y ∈ Y, IsOpen (UT x y)) →
    (∀ x ∈ X, ∀ y ∈ Y, IsOpen (UI x y)) →
    (∀ x ∈ X, ∀ y ∈ Y, ∀ p, |p.1| < ε → χ x y p = 1) →
    (∀ x ∈ X, ∀ y ∈ Y,
      elapsedOutputJetCarrier K mi mo x y ∩ tsupport (χ x y) ⊆ UT x y) →
    (∀ x ∈ X, ∀ y ∈ Y,
      (elapsedOutputJetCarrier K mi mo x y ∩ tsupport (1 - χ x y)) ∩
        {p | 0 < p.1} ⊆ UI x y) →
    (∀ x ∈ X, ∀ y ∈ Y, ∀ r, 0 ≤ r → ∀ p, (r, p) ∈ UT x y →
      δT ≤ phaseGradientSquare eT (fun w ↦
        jointElapsedPhase backward (SymbolBudgets.normalizedTwoTimePhase ρ Ψ) x y (r, w)) p) →
    (∀ x ∈ X, ∀ y ∈ Y, ∀ r, 0 ≤ r → ∀ p, (r, p) ∈ UT x y →
      ‖fderiv ℝ (jointElapsedPhase backward
        (SymbolBudgets.normalizedTwoTimePhase ρ Ψ) x y) (r, p)‖ ≤ GT) →
    (∀ x ∈ X, ∀ y ∈ Y, ∀ p ∈ UI x y ∩ {p | 0 < p.1},
      δI ≤ phaseGradientSquare eI
        (jointElapsedPhase backward (SymbolBudgets.normalizedTwoTimePhase ρ Ψ) x y) p) →
    (∀ x ∈ X, ∀ y ∈ Y, ∀ p ∈ UI x y ∩ {p | 0 < p.1},
      ‖fderiv ℝ (jointElapsedPhase backward
        (SymbolBudgets.normalizedTwoTimePhase ρ Ψ) x y) p‖ ≤ GI) →
    (∀ x ∈ X, ∀ y ∈ Y, ∀ p ∈ elapsedOutputJetCarrier K mi mo x y, ∀ j,
      ‖iteratedFDeriv ℝ j (fderiv ℝ (jointElapsedPhase backward
        (SymbolBudgets.normalizedTwoTimePhase ρ Ψ) x y)) p‖ ≤ P j * L ^ j) →
    (∀ x ∈ X, ∀ y ∈ Y, ∀ p ∈ elapsedOutputJetCarrier K mi mo x y, ∀ j,
      ‖iteratedFDeriv ℝ j (χ x y) p‖ ≤ H j) →
    (∀ x ∈ X, ∀ y ∈ Y, ∀ p ∈ elapsedOutputJetCarrier K mi mo x y, ∀ j,
      ‖iteratedFDeriv ℝ j outputJointWave (0, p.2.2.2.2)‖ ≤ W j) →
    (∀ x ∈ X, ∀ y ∈ Y, ∀ p ∈ elapsedOutputJetCarrier K mi mo x y, ∀ j,
      ‖iteratedFDeriv ℝ j mo (x, p.2.2.2.2)‖ ≤ O j * L ^ (j + bo)) →
    (∀ low j k, IsComparablePair c C a₀ b₀ ρ low j k →
      ∀ x ∈ X, ∀ y ∈ Y, ∀ p ∈ elapsedOutputJetCarrier K mi mo x y, ∀ l,
      ‖iteratedFDeriv ℝ l (fun w : V ↦ θ w.1 •
        jointElapsedAmplitude backward ρ b χout χsource β mi (fun _ ↦ 0)
          (graphBranchCutoff low j) (outputCutoff k) 0 y w) p‖ ≤
        ρ ^ s * A l * L ^ (l + ba)) →
    (∀ N low j k, SeparatedRanges c C (a₀ * ρ) (b₀ * ρ)
        (graphLower low j) (graphUpper low j) (outputLower k) (outputUpper k) →
      ∀ r ∈ Icc 0 Δ, ∀ x ∈ X, ∀ y ∈ Y, ∀ v : Fin m → E,
      (∀ i, ‖v i‖ ≤ 1) →
      ‖iteratedFDeriv ℝ m (fun t ↦ KernelLimits.regularizedJointKernel backward
        (elapsedPhase Ψ r) (orientedElapsedAmplitude backward b χout χsource β r)
        (fun p ↦ mi (p.1, ρ⁻¹ • p.2)) (fun p ↦ mo (p.1, ρ⁻¹ • p.2))
          (graphBranchCutoff low j) (outputCutoff k) t y) x v‖ ≤
        D N * ρ ^ (d + 1) * L ^ bLoss * (L / ρ) ^ N * pairWeight low (d + 1) j k) →
    ∃ M : ℕ → (ℕ × ℕ) → ℝ, ∀ N,
      (∀ p, 0 ≤ M N p) ∧ Summable (M N) ∧
      (∑' p, M N p) ≤ Cq N * ρ ^ ((m : ℝ) + (max 0 s + (3 * (d + 1) : ℕ))) *
        L ^ (max ((m + bo) + ba) bLoss) * (L / ρ) ^ N ∧
      ∀ x ∈ X, ∀ y, ∀ v : Fin m → E, (∀ i, ‖v i‖ ≤ 1) →
        (∀ j k, ‖iteratedFDeriv ℝ m (fun t ↦ elapsedPhysicalShellKernel backward ρ Δ Ψ b
          χout χsource β mi mo (graphCutoff j) (outputCutoff k) t y) x v‖ ≤ M N (j, k)) ∧
        Summable (fun p : ℕ × ℕ ↦ iteratedFDeriv ℝ m
          (fun t ↦ elapsedPhysicalShellKernel backward ρ Δ Ψ b χout χsource β mi mo
            (graphCutoff p.1) (outputCutoff p.2) t y) x v) := by
  obtain ⟨Cq, hCq, hmajor⟩ := exists_elapsedPhysicalShellKernel_majorants_of_joint_grades
    (q := q) eT eI backward s Δ m bo ba bLoss c C b₀ ha₀ hK δT δI GT GI hδT hδI
    P H W O A D hH hW hO hA hD
  refine ⟨Cq, hCq, ?_⟩
  intro ρ L hρ hL Ψ b χout χsource β mi mo θ X Y hiy hθ hΨ hbcont hi ho carriers
    Jphase Wphase hJphase hWphase hJW hPhase hPhaseSupport hmap
    ha hcompact hs a T hb hout hslab χ UT UI ε hε hχ hUT hUI hχ_one hχT hχI
    hgapT hupperT hgapI hupperI hp hχ_bound hw hmo hab hper
  obtain ⟨Ψ', hsm, hgerm, hF, hphysical, hshell⟩ :=
    exists_supported_elapsedPhysicalShellKernel_phase Δ Ψ b χout χsource β
      hJphase hWphase hJW hPhase hPhaseSupport
  let Ω : Set V := {p | SymbolBudgets.jointPhase
    (SymbolBudgets.normalizedTwoTimePhase ρ Ψ') =ᶠ[𝓝 (elapsedJointCoordinates p)]
      SymbolBudgets.jointPhase (SymbolBudgets.normalizedTwoTimePhase ρ Ψ)}
  have hΩ : IsOpen Ω := isOpen_setOfPred_eventually_nhds.preimage elapsedJointCoordinates.continuous
  have hmem (x : E) (hx : x ∈ X) (y : E) (hy : y ∈ Y)
      (p : V) (hp : p ∈ elapsedOutputJetCarrier K mi mo x y) : p ∈ Ω :=
    normalizedTwoTimePhase_eventuallyEq_of_germ ρ Ψ Ψ' (elapsedJointCoordinates p)
      (hgerm _ (hmap x hx y hy p hp))
  have he (x y : E) (p : V) (hp : p ∈ Ω) :
      jointElapsedPhase backward (SymbolBudgets.normalizedTwoTimePhase ρ Ψ') x y =ᶠ[𝓝 p]
        jointElapsedPhase backward (SymbolBudgets.normalizedTwoTimePhase ρ Ψ) x y :=
    jointElapsedPhase_eventuallyEq_of_twoTimePhase backward _ _ x y p hp
  have hSr (r : ℝ) : Continuous (Function.uncurry (elapsedPhase Ψ' r)) :=
    (contDiff_elapsedPhase_joint_of_twoTimePhase Ψ' hsm).continuous.comp
      (continuous_const.prodMk (continuous_fst.prodMk continuous_snd))
  have hphysical_fun (r : ℝ) (hr : r ∈ Icc 0 Δ) (low : Bool) (j k : ℕ) (y : E) :
      (fun x ↦ KernelLimits.regularizedJointKernel backward (elapsedPhase Ψ' r)
        (orientedElapsedAmplitude backward b χout χsource β r)
        (fun p ↦ mi (p.1, ρ⁻¹ • p.2)) (fun p ↦ mo (p.1, ρ⁻¹ • p.2))
        (graphBranchCutoff low j) (outputCutoff k) x y) =
      (fun x ↦ KernelLimits.regularizedJointKernel backward (elapsedPhase Ψ r)
        (orientedElapsedAmplitude backward b χout χsource β r)
        (fun p ↦ mi (p.1, ρ⁻¹ • p.2)) (fun p ↦ mo (p.1, ρ⁻¹ • p.2))
        (graphBranchCutoff low j) (outputCutoff k) x y) :=
    funext (fun x ↦ hphysical backward ρ r hr mi mo _ _ x y)
  have hresult := hmajor ρ L hρ hL Ψ' b χout χsource β mi mo θ X Y hiy hθ
    (fun r _ ↦ hSr r) hbcont hi ho carriers (fun y _ x ↦ hF ρ backward x y)
    ha hcompact hs a T hb hout hslab χ
    (fun x y ↦ UT x y ∩ Ω) (fun x y ↦ UI x y ∩ Ω) ε hε hχ
    (fun x hx y hy ↦ (hUT x hx y hy).inter hΩ)
    (fun x hx y hy ↦ (hUI x hx y hy).inter hΩ) hχ_one
    (fun x hx y hy p h ↦ ⟨hχT x hx y hy h, hmem x hx y hy p h.1⟩)
    (fun x hx y hy p h ↦ ⟨hχI x hx y hy h, hmem x hx y hy p h.1.1⟩)
    (by
      intro x hx y hy r hr p h
      have hs := fderiv_jointElapsedPhase_slice_eq_of_twoTimePhase_germ
        backward _ _ x y r p h.2
      simpa only [phaseGradientSquare, hs] using hgapT x hx y hy r hr p h.1)
    (by
      intro x hx y hy r hr p h
      rw [(he x y (r, p) h.2).fderiv_eq]
      exact hupperT x hx y hy r hr p h.1)
    (by
      intro x hx y hy p h
      simpa only [phaseGradientSquare, (he x y p h.1.2).fderiv_eq] using
        hgapI x hx y hy p ⟨h.1.1, h.2⟩)
    (by
      intro x hx y hy p h
      rw [(he x y p h.1.2).fderiv_eq]
      exact hupperI x hx y hy p ⟨h.1.1, h.2⟩)
    (by
      intro x hx y hy p h j
      rw [(((he x y p (hmem x hx y hy p h)).fderiv (𝕜 := ℝ)).iteratedFDeriv ℝ j).eq_of_nhds]
      exact hp x hx y hy p h j)
    hχ_bound hw hmo hab
    (by
      intro N low j k hsep r hr x hx y hy v hv
      rw [hphysical_fun r hr low j k y]
      exact hper N low j k hsep r hr x hx y hy v hv)
  simpa only [hshell] using hresult

end JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
