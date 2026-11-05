module

public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.CompleteResidual.FiniteIdentity
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification

/-!
# Matching the complete solver to the published regularizations

These identities keep the very same frequency cutoff, physical output mask,
and original right source mask in the retarded and algebraic pieces. The
retarded representative is exactly the one returned by
`exists_retardedOperator_of_regularizations`. The PDO is the canonical graph
with the full two-position amplitude, in physical covectors.
Source: `app:ch_regular_base:eq:energy-complete-residual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.CharacteristicTransport.CompleteResidual
open FourierIntegral FourierIntegral.LowBounds.FrequencyCutoff
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "FV" => Fin q → ℂ
local notation "Mat" => Matrix (Fin q) (Fin q) ℂ

/-- The canonical PDO has precisely the full two-position mask used by graph
regularization. The original source mask stays to the right of the PDO
(`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem masked_cutPhysicalPDO_eq_graphOperator (c : E → E → Mat)
    (θ χout χsource : E → ℂ) (hs : ContDiff ℝ ∞ χsource)
    (u : graphTestSpace (d + 1) q) (x : E) :
    χout x • cutPhysicalPDO θ c (graphTestToSchwartz (complexSourceMaskTest χsource hs u)) x =
      graphOperator (fun y ξ ↦ inner ℝ y ξ)
        (frequencyCutFullAmplitude θ (fun y z ξ ↦ (χout y * χsource z) • c y ξ))
        (fun z ↦ (u.val z).ofLp) x := by
  have hv : (graphTestToSchwartz (complexSourceMaskTest χsource hs u) : E → FV) =
      fun z ↦ χsource z • (u.val z).ofLp := rfl
  rw [cutPhysicalPDO, hv, graphOperator_source_mul]
  rw [← graphOperator_target_mul]
  congr 2
  funext y z ξ
  simp only [frequencyCutFullAmplitude, smul_smul]
  congr 1
  ring

/-- The finite solver is the sum of the exact physical retarded representative
returned by the producer and the canonical masked PDO. This equality holds
at every point, without differentiating the uncut output
(`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem cutDirectSolver_eq_retardedPhysical_add_PDO
    (Ψ : TwoTimePhase d) (W₀ W₁ : TwoTimeAmplitude d q)
    (bminus : E → E → Mat) (σ : E → Euclidean d → ℂ)
    (β θ χout χsource : E → ℂ) (hs : ContDiff ℝ ∞ χsource)
    (hβ : ContDiff ℝ ∞ β) (hθ : ContDiff ℝ ∞ θ) (hθcs : HasCompactSupport θ)
    (a : ℝ) (u : graphTestSpace (d + 1) q) (x : E) :
    cutDirectSolver Ψ W₀ W₁ bminus σ β θ χout a
      (graphTestToSchwartz (complexSourceMaskTest χsource hs u)) x =
      cutRetardedPhysical Ψ (W₀ + W₁) χout χsource β θ hs hβ hθ hθcs a u x +
        (1 / Complex.I) • graphOperator (fun y ξ ↦ inner ℝ y ξ)
          (frequencyCutFullAmplitude θ (fun y z ξ ↦
            (χout y * χsource z) • directAlgebraicSymbol bminus σ β y ξ))
          (fun z ↦ (u.val z).ofLp) x := by
  simp only [cutDirectSolver, cutDirectCore, smul_add]
  rw [smul_comm (χout x) (1 / Complex.I), masked_cutPhysicalPDO_eq_graphOperator]
  congr 1
  simp only [cutRetardedPhysical,
    cutFixedTimeFourier_eq_graphOperator Ψ (W₀ + W₁) β θ _ hβ hθ hθcs]

/-- The same finite solver is the sum of its literal fixed-slab graph integral
and its canonical graph PDO. The lower buffer kills the excess elapsed-time
interval and the fixed output slab is retained, including both endpoints.
Consumer: common-frequency strong-limit assembly in
`app:ch_regular_base:eq:energy-complete-residual`. -/
theorem cutDirectSolver_eq_elapsedGraph_add_PDO
    (Ψ : TwoTimePhase d) (W₀ W₁ : TwoTimeAmplitude d q)
    (bminus : E → E → Mat) (σ : E → Euclidean d → ℂ)
    (β θ χout χsource : E → ℂ)
    (hΨ : Continuous (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      Ψ p.1.1 p.1.2 p.2.1 p.2.2))
    (hW : Continuous (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      (W₀ + W₁) p.1.1 p.1.2 p.2.1 p.2.2))
    (ho : Continuous χout) (hs : ContDiff ℝ ∞ χsource)
    (hβ : ContDiff ℝ ∞ β) (hθ : ContDiff ℝ ∞ θ)
    (hscs : HasCompactSupport χsource) (hθcs : HasCompactSupport θ)
    (a Δ : ℝ) (hout : ∀ x, χout x ≠ 0 → x 0 ∈ Icc a (a + Δ))
    (hzero : ∀ t s y η, s ≤ a → (W₀ + W₁) t s y η = 0)
    (u : graphTestSpace (d + 1) q) (x : E) :
    cutDirectSolver Ψ W₀ W₁ bminus σ β θ χout a
      (graphTestToSchwartz (complexSourceMaskTest χsource hs u)) x =
      (∫ r in Icc 0 Δ, graphOperator (elapsedPhase Ψ r)
        (frequencyCutFullAmplitude θ (elapsedAmplitude (W₀ + W₁) χout χsource β r))
        (fun z ↦ (u.val z).ofLp) x) +
      (1 / Complex.I) • graphOperator (fun y ξ ↦ inner ℝ y ξ)
        (frequencyCutFullAmplitude θ (fun y z ξ ↦
          (χout y * χsource z) • directAlgebraicSymbol bminus σ β y ξ))
        (fun z ↦ (u.val z).ofLp) x := by
  rw [cutDirectSolver_eq_retardedPhysical_add_PDO Ψ W₀ W₁ bminus σ β θ χout χsource
    hs hβ hθ hθcs a u x,
    integral_cut_elapsedGraph_eq_retardedPhysical Ψ (W₀ + W₁) χout χsource β θ
      hΨ hW ho hs hβ hθ hscs hθcs a Δ hout hzero u x]

end JanetCartan.CharacteristicTransport.CompleteResidual
