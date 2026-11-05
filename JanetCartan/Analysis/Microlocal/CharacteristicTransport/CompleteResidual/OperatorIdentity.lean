module

public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.CompleteResidual.UncutIdentity
public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.CompleteResidual.Regularity
public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.CompleteResidual.SectorEquations

/-!
# Constructing the bounded solver from the primitive graph outputs

Source: `app:ch_regular_base:eq:energy-complete-residual`.
The two retarded operators are constructed by the existing literal-kernel
producer, retaining both masks, the lower buffer and reversed-triangle
adjoints. The four PDO terms use the same frequency regularization and the
canonical physical phase. The inputs are precisely finite graph realizations,
LOW bounds and strong limits from `exists_fullGraphFamily_of_wholeImage_phase`;
no uncut equation or successful parametrix is assumed. Their primitive symbol
budget instantiation remains the sector parent's obligation.

The finite equation and weak passage are instantiated, then source density
extends the result from compact smooth sources to every vector L² source.
The same output's H¹ weak derivative yields the a.e. local equation. Its
actual history regularity remains the parent's obligation. The chart's
transport and complement identities are still explicit inputs; connecting the
local physical chart and its supported extension remains unfinished.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.CharacteristicTransport.CompleteResidual
open FourierIntegral FourierIntegral.FullLowBounds FourierIntegral.LowBounds.FrequencyCutoff
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "FV" => Fin q → ℂ
local notation "Mat" => Matrix (Fin q) (Fin q) ℂ
local notation "C2" => SpacetimeL2 d q

/-- The two actual retarded amplitudes, indexed by false for the solver and
true for its complete differentiated correction. Consumer:
`completeResidual_operators_of_graph_regularizations`.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
def directRetardedAmplitudes (A : E → Fin (d + 1) → Mat) (B : E → Mat)
    (W₀ W₁ : TwoTimeAmplitude d q) : Bool → TwoTimeAmplitude d q
  | false => W₀ + W₁
  | true => twoTimePhysicalApply A B W₁

/-- The four physical PDO symbols: algebraic solver, principal Op(α),
correction endpoint, and derivative of the entire algebraic symbol.
All multipliers remain in their original order. Consumer:
`completeResidual_operators_of_graph_regularizations`.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
def directPDOSymbols (A : E → Fin (d + 1) → Mat) (B : E → Mat)
    (W₁ : TwoTimeAmplitude d q) (bminus : E → E → Mat)
    (σ : E → Euclidean d → ℂ) (β : E → ℂ) : Fin 4 → E → E → Mat :=
  ![directAlgebraicSymbol bminus σ β,
    fun x ξ ↦ (σ x (spatialPart ξ) * β ξ) • (1 : Mat),
    fun x ξ ↦ β ξ • (A x 0 * W₁ (x 0) (x 0) (spatialPart x) (spatialPart ξ)),
    physicalSymbolApply A B (directAlgebraicSymbol bminus σ β)]

/-- The canonical graph PDO with the original two physical masks. Its
realization is established by the regularization inputs of the theorem
below; the choice definition alone does not assert realization.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
def maskedPhysicalPDO (χout χsource : E → ℂ) (c : E → E → Mat) : C2 →L[ℂ] C2 :=
  fullGraphOperator (fun x ξ ↦ inner ℝ x ξ) (fun x z ξ ↦ (χout x * χsource z) • c x ξ)

/-- Construct the two retarded operators, combine their literal limits with
all four canonical PDO limits, and prove the complete local tested equation
for all L² sources. The actual finite differential identity is proved by
`completeResidual_test_and_ae_of_component_limits`; its analytic limit
inputs are the primitive graph realization outputs. The same source mask and cutoff are
used by every term. The retarded literal adjoints and full solver adjoint
are retained. Local H¹ identifies the same output's a.e. action.
Source: `app:ch_regular_base:eq:energy-complete-residual`.
This does not instantiate the physical chart or uniform symbol budgets. -/
theorem completeResidual_operators_of_graph_regularizations
    (A : E → Fin (d + 1) → Matrix (Fin q) (Fin q) ℝ)
    (B : E → Matrix (Fin q) (Fin q) ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j))
    (Ψ : TwoTimePhase d) (W₀ W₁ : TwoTimeAmplitude d q)
    (bminus : E → E → Mat) (σ : E → Euclidean d → ℂ)
    (proj : E → Euclidean d → Mat) (β χout : E → ℂ)
    (θ : ℕ → E → ℂ) (a Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hΨ : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      Ψ p.1.1 p.1.2 p.2.1 p.2.2))
    (hW₀ : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      W₀ p.1.1 p.1.2 p.2.1 p.2.2))
    (hW₁ : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      W₁ p.1.1 p.1.2 p.2.1 p.2.2))
    (hc : ContDiff ℝ ∞ (Function.uncurry (directAlgebraicSymbol bminus σ β)))
    (hβ : ContDiff ℝ ∞ β) (ho : ContDiff ℝ ∞ χout)
    (hθ : ∀ k, ContDiff ℝ ∞ (θ k)) (hθcs : ∀ k, HasCompactSupport (θ k))
    {U : Set E} (hU : IsOpen U)
    (hσ : ∀ x ∈ U, Continuous (σ x))
    (hplateau : ∀ x ∈ U, χout =ᶠ[𝓝 x] fun _ ↦ (1 : ℂ))
    (hdiag : ∀ t y η, Ψ t t y η = inner ℝ y η)
    (hlead : ∀ x ∈ U, ∀ η,
      ((A x 0).map Complex.ofReal) * W₀ (x 0) (x 0) (spatialPart x) η = σ x η • proj x η)
    (hcomp : ∀ x ∈ U, ∀ ξ, β ξ ≠ 0 →
      (∑ j, (ξ j : ℂ) • (A x j).map Complex.ofReal) * bminus x ξ =
        1 - proj x (spatialPart ξ))
    (hcancel : ∀ x ∈ U, ∀ s η j, WKB.firstOrderApply
      (fun y i ↦ ((A y i).map Complex.ofReal).mulVecLin)
      (fun y ↦ ((B y).map Complex.ofReal).mulVecLin)
      (fun y ↦ Complex.exp (Complex.I * (Ψ (y 0) s (spatialPart y) η : ℂ)) •
        (fun i ↦ (W₀ + W₁) (y 0) s (spatialPart y) η i j)) x =
      Complex.exp (Complex.I * (Ψ (x 0) s (spatialPart x) η : ℂ)) •
        (fun i ↦ twoTimePhysicalApply (fun y j ↦ (A y j).map Complex.ofReal)
          (fun y ↦ (B y).map Complex.ofReal) W₁ (x 0) s (spatialPart x) η i j))
    (χsource : E → ℂ) (hs : ContDiff ℝ ∞ χsource)
    (hocs : HasCompactSupport χout) (hscs : HasCompactSupport χsource)
    (hout : ∀ x, χout x ≠ 0 → x 0 ∈ Icc a (a + Δ))
    (hzero₀ : ∀ t s y η, s ≤ a → W₀ t s y η = 0)
    (hzero₁ : ∀ t s y η, s ≤ a → W₁ t s y η = 0) :
    let b := directRetardedAmplitudes (fun x j ↦ (A x j).map Complex.ofReal)
      (fun x ↦ (B x).map Complex.ofReal) W₀ W₁
    let c := directPDOSymbols (fun x j ↦ (A x j).map Complex.ofReal)
      (fun x ↦ (B x).map Complex.ofReal) W₁ bminus σ β
    let P := fun k ↦ maskedPhysicalPDO χout χsource (c k)
    ∀ (Treg : Bool → ℕ → ℝ → C2 →L[ℂ] C2) (C : Bool → ℝ),
      (∀ k j r, r ∈ Icc 0 Δ → ∀ u : graphTestSpace (d + 1) q,
        Treg k j r (graphTestToLp u) =ᵐ[volume] graphTestOutput (elapsedPhase Ψ r)
          (frequencyCutFullAmplitude (θ j) (elapsedAmplitude (b k) χout χsource β r)) u) →
      (∀ k j r, r ∈ Icc 0 Δ → ∀ u : graphTestSpace (d + 1) q,
        (Treg k j r).adjoint (graphTestToLp u) =ᵐ[volume] fun z ↦ WithLp.toLp 2
          (reverseGraphOperator (elapsedPhase Ψ r)
            (frequencyCutFullAmplitude (fun ξ ↦ star (θ j ξ))
              (fun x z ξ ↦ (elapsedAmplitude (b k) χout χsource β r x z ξ).conjTranspose))
            (fun x ↦ (u.val x).ofLp) z)) →
      (∀ k j r, r ∈ Icc 0 Δ → ‖Treg k j r‖ ≤ C k) →
      (∀ k r, r ∈ Icc 0 Δ → ∀ u, Tendsto (fun j ↦ Treg k j r u) atTop
        (𝓝 (elapsedGraph Ψ (b k) χout χsource β r u))) →
      (∀ k r, r ∈ Icc 0 Δ → ∀ u, Tendsto (fun j ↦ (Treg k j r).adjoint u) atTop
        (𝓝 ((elapsedGraph Ψ (b k) χout χsource β r).adjoint u))) →
    ∀ Preg : Fin 4 → ℕ → C2 →L[ℂ] C2,
      (∀ k j u, Preg k j (graphTestToLp u) =ᵐ[volume] graphTestOutput
        (fun x ξ ↦ inner ℝ x ξ)
        (frequencyCutFullAmplitude (θ j) (fun x z ξ ↦ (χout x * χsource z) • c k x ξ)) u) →
      (∀ k u, Tendsto (fun j ↦ Preg k j u) atTop (𝓝 (P k u))) →
    ∃ Q : Bool → C2 →L[ℂ] C2,
      (∀ k, ‖Q k‖ ≤ Δ * C k) ∧
      (∀ k u, Q k u = elapsedGraphIntegral Δ Ψ (b k) χout χsource β u) ∧
      (∀ k u, (Q k).adjoint u =
        ∫ r in Icc 0 Δ, (elapsedGraph Ψ (b k) χout χsource β r).adjoint u) ∧
      let S := Q false + (1 / Complex.I) • P 0
      let R := P 2 + Q true + (1 / Complex.I) • P 3
      S.adjoint = (Q false).adjoint + star (1 / Complex.I) • (P 0).adjoint ∧
      (∀ f φ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U → ∀ i,
        physicalTestAction A B (fun x ↦ (S f x).ofLp) φ i =
          ∫ x, φ x • ((P 1 + R) f) x i) ∧
      (∀ f du, Mollification.HasWeakFDerivOn volume (fun x ↦ (S f x).ofLp) du U →
        physicalWeakApply A B (fun x ↦ (S f x).ofLp) du =ᵐ[volume.restrict U]
          fun x ↦ (((P 1 + R) f) x).ofLp) := by
  dsimp only
  let b := directRetardedAmplitudes (fun x j ↦ (A x j).map Complex.ofReal)
    (fun x ↦ (B x).map Complex.ofReal) W₀ W₁
  let c := directPDOSymbols (fun x j ↦ (A x j).map Complex.ofReal)
    (fun x ↦ (B x).map Complex.ofReal) W₁ bminus σ β
  let P := fun k ↦ maskedPhysicalPDO χout χsource (c k)
  intro Treg C ht htAdj htbound htlim htlimAdj Preg hp hplim
  have hb (k : Bool) : Continuous (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      b k p.1.1 p.1.2 p.2.1 p.2.2) := by
    cases k
    · exact (hW₀.add hW₁).continuous
    · exact (contDiff_twoTimePhysicalApply_of_real_coefficients A B hA hB W₁ hW₁).continuous
  have hzero (k : Bool) : ∀ t s y η, s ≤ a → b k t s y η = 0 := by
    intro t s y η hs
    cases k
    · change W₀ t s y η + W₁ t s y η = 0
      rw [hzero₀ t s y η hs, hzero₁ t s y η hs, add_zero]
    · exact twoTimePhysicalApply_eq_zero_of_lower_buffer _ _ W₁ a hzero₁ t s y η hs
  have hret (k : Bool) := exists_retardedOperator_of_regularizations Ψ (b k)
    χout χsource β Δ hΔ
    (fun _ _ _ _ _ _ ↦ hΨ.continuous.continuousAt)
    (fun _ _ _ _ _ _ ↦ (hb k).continuousAt) ho.continuous hs hβ hocs hscs
    θ hθ hθcs (Treg k) (ht k) (htAdj k) (htbound k) (htlim k) (htlimAdj k)
    a hout (hzero k)
  choose Q hQbound hQ hQAdj hrep using fun k ↦ (hret k).2.2
  let S := Q false + (1 / Complex.I) • P 0
  let R := P 2 + Q true + (1 / Complex.I) • P 3
  have htests (u : graphTestSpace (d + 1) q) :
      ∀ φ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U → ∀ i,
        physicalTestAction A B (fun x ↦ (S (graphTestToLp u) x).ofLp) φ i =
          ∫ x, φ x • ((P 1 + R) (graphTestToLp u)) x i := by
    let v := graphTestToSchwartz (complexSourceMaskTest χsource hs u)
    have hvcs : HasCompactSupport (v : E → FV) :=
      (complexSourceMaskTest χsource hs u).property.2.comp_left (g := WithLp.ofLp) rfl
    obtain ⟨tReg, _tAdj, htrep, _htAdjrep, htlim, _htAdjlim⟩ := hrep false u
    obtain ⟨rReg, _rAdj, hrrep, _hrAdjrep, hrlim, _hrAdjlim⟩ := hrep true u
    have htr (k : ℕ) : tReg k =ᵐ[volume] fun x ↦ WithLp.toLp 2
        (χout x • ∫ s in a..x 0, cutFixedTimeFourier Ψ (W₀ + W₁) β (θ k) v
          (x 0) s (spatialPart x)) := by
      apply (htrep k).trans
      exact Eventually.of_forall fun x ↦ by
        simp only [cutRetardedPhysical, b, directRetardedAmplitudes,
          cutFixedTimeFourier_eq_graphOperator Ψ (W₀ + W₁) β (θ k) v hβ (hθ k) (hθcs k)]
        rfl
    have hrr (k : ℕ) : rReg k =ᵐ[volume] fun x ↦ WithLp.toLp 2
        (χout x • ∫ s in a..x 0, cutFixedTimeFourier Ψ
          (twoTimePhysicalApply (fun x j ↦ (A x j).map Complex.ofReal)
            (fun x ↦ (B x).map Complex.ofReal) W₁) β (θ k) v
          (x 0) s (spatialPart x)) := by
      apply (hrrep k).trans
      exact Eventually.of_forall fun x ↦ by
        simp only [cutRetardedPhysical, b, directRetardedAmplitudes,
          cutFixedTimeFourier_eq_graphOperator Ψ _ β (θ k) v hβ (hθ k) (hθcs k)]
        rfl
    have hpr (l : Fin 4) (k : ℕ) : Preg l k (graphTestToLp u) =ᵐ[volume]
        fun x ↦ WithLp.toLp 2 (χout x • cutPhysicalPDO (θ k) (c l) v x) := by
      apply (hp l k u).trans
      exact Eventually.of_forall fun x ↦ congrArg (WithLp.toLp 2)
        (masked_cutPhysicalPDO_eq_graphOperator (c l) (θ k) χout χsource hs u x).symm
    have h := completeResidual_test_and_ae_of_component_limits A B hA hB
      Ψ W₀ W₁ bminus σ proj β χout θ a v hΨ hW₀ hW₁ hc hβ ho hθ hθcs hvcs
      hU hσ hplateau hdiag hlead hcomp hcancel
      tReg (fun k ↦ Preg 0 k (graphTestToLp u)) (fun k ↦ Preg 1 k (graphTestToLp u))
      (fun k ↦ Preg 2 k (graphTestToLp u)) rReg (fun k ↦ Preg 3 k (graphTestToLp u))
      (Q false (graphTestToLp u)) (P 0 (graphTestToLp u)) (P 1 (graphTestToLp u))
      (P 2 (graphTestToLp u)) (Q true (graphTestToLp u)) (P 3 (graphTestToLp u))
      htr (hpr 0) (hpr 1) (hpr 2) hrr (hpr 3)
      htlim (hplim 0 _) (hplim 1 _) (hplim 2 _) hrlim (hplim 3 _)
    simpa only [S, R, add_apply, smul_apply] using h.1
  have hall (f : C2) : ∀ φ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U → ∀ i,
      physicalTestAction A B (fun x ↦ (S f x).ofLp) φ i =
        ∫ x, φ x • ((P 1 + R) f) x i := by
    intro φ hφ hφcs hφU i
    exact physicalTestAction_eq_of_graphTests A B hA hB S (P 1 + R) hφ hφcs i
      (fun u ↦ htests u φ hφ hφcs hφU i) f
  refine ⟨Q, hQbound, hQ, hQAdj, ?_, hall, ?_⟩
  · simp only [map_add, map_smulₛₗ, starRingEnd_apply]
  · intro f du hdu
    let L : EuclideanSpace ℂ (Fin q) →L[ℝ] FV :=
      (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin q ↦ ℂ)).toContinuousLinearMap.restrictScalars ℝ
    have hg : MemLp (fun x ↦ (((P 1 + R) f) x).ofLp) 2 volume :=
      L.comp_memLp' (Lp.memLp _)
    exact physicalWeakApply_ae_eq_of_test A B hA hB hU hdu
      ((hg.locallyIntegrable (by norm_num)).locallyIntegrableOn U) (hall f)

end JanetCartan.CharacteristicTransport.CompleteResidual
