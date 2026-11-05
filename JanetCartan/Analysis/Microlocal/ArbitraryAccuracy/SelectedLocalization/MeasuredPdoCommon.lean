module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.MeasuredAmplitudeProfiles

/-!
# Actual measured regularizations of the selected PDO branches

The retained source, algebraic and endpoint normal-amplitude certificates
supply the literal measured operators, with both original measurement masks.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open FourierIntegral FullLowBounds LowBounds LowBounds.FrequencyCutoff
open RegularSector RegularSector.Characteristic RegularSector.Characteristic.PdoRealization
open RegularSector.Characteristic.EvolutionIntegral RegularSector.Characteristic.ResidualCoordinates
open RegularSector.Characteristic.RootFamily RegularSector.FiniteAssembly
open RegularSector.FiniteMasks RegularSector.FiniteMasks.ActualFamily
open RegularSector.FiniteAlgebraic RegularSector.FinitePdo
open CharacteristicTransport.CompleteResidual ResidualLocalization
open RegularSector.FiniteResidual.SelectedChart
variable {d q : ℕ}
local notation "E" => Euclidean (d+1)
local notation "CMat" => Matrix (Fin q) (Fin q) ℂ
local notation "H" => SpacetimeL2 d q

/-- Physical multiplication composes in place on the original L² space
(`app:ch_regular_base:eq:measured-adjoint`). -/
private theorem sourceCutMultiplier_product
    (μ ψ : E → ℝ) (hμ : Continuous μ) (hψ : Continuous ψ)
    (hμb : ∀ x, ‖μ x‖ ≤ 1) (hψb : ∀ x, ‖ψ x‖ ≤ 1)
    (hb : ∀ x, ‖μ x * ψ x‖ ≤ 1) :
    (sourceCutMultiplier μ hμ hμb (r := q)).comp (sourceCutMultiplier ψ hψ hψb) =
      sourceCutMultiplier (fun x ↦ μ x * ψ x) (hμ.mul hψ) hb := by
  ext1 u
  apply Lp.ext
  filter_upwards [sourceCutMultiplier_coeFn μ hμ hμb (sourceCutMultiplier ψ hψ hψb u),
    sourceCutMultiplier_coeFn ψ hψ hψb u,
    sourceCutMultiplier_coeFn (fun x ↦ μ x * ψ x) (hμ.mul hψ) hb u] with x hx hy hz
  change (sourceCutMultiplier μ hμ hμb (sourceCutMultiplier ψ hψ hψb u)) x = _
  rw [hx, hy, hz, smul_smul, Complex.ofReal_mul]

/-- The common output combines only with the output measurement mask; the
source measurement stays on the right (`app:ch_regular_base:eq:measured-adjoint`). -/
private theorem measuredOperator_output_product
    (μ ν ψ : E → ℝ) (hμ : Continuous μ) (hν : Continuous ν) (hψ : Continuous ψ)
    (hμb : ∀ x, ‖μ x‖ ≤ 1) (hνb : ∀ x, ‖ν x‖ ≤ 1) (hψb : ∀ x, ‖ψ x‖ ≤ 1)
    (hb : ∀ x, ‖μ x * ψ x‖ ≤ 1) (T : H →L[ℂ] H) :
    measuredOperator μ ν hμ hν hμb hνb ((sourceCutMultiplier ψ hψ hψb).comp T) =
      measuredOperator (fun x ↦ μ x*ψ x) ν (hμ.mul hψ) hν hb hνb T := by
  ext1 u
  exact DFunLike.congr_fun (sourceCutMultiplier_product μ ψ hμ hψ hμb hψb hb)
    (T (sourceCutMultiplier ν hν hνb u))

/-- The actual measured common-output PDO is the canonical PDO with both
measurement masks in their original positions. Its retained normal certificate
is only required on the original larger output, as supplied by the selected
algebraic constructor (`app:ch_regular_base:eq:measured-adjoint`). -/
theorem measured_commonOutputPDO_eq
    (χout χsource : E → ℂ) (c : E → E → CMat) {R M : ℝ}
    (hb : GraphNormalAmplitudeBounds (maskedPhysicalPDOCycleSymbol χout χsource c) R M)
    (ψ : E → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψb : ∀ x, ‖ψ x‖ ≤ 1)
    (hp : ∀ x, (ψ x : ℂ) * χout x = (ψ x : ℂ))
    (μ ν : E → ℝ) (hμ : ContDiff ℝ ∞ μ) (hν : ContDiff ℝ ∞ ν)
    (hμb : ∀ x, ‖μ x‖ ≤ 1) (hνb : ∀ x, ‖ν x‖ ≤ 1) :
    measuredOperator μ ν hμ.continuous hν.continuous hμb hνb
      (maskedPhysicalPDO (fun x ↦ (ψ x : ℂ)) χsource c) =
    maskedPhysicalPDO (fun x ↦ (μ x : ℂ)*(ψ x : ℂ))
      (fun y ↦ (ν y : ℂ)*χsource y) c := by
  have hmb (x : E) : ‖μ x * ψ x‖ ≤ 1 := by
    rw [norm_mul]
    exact (mul_le_mul (hμb x) (hψb x) (norm_nonneg _) zero_le_one).trans (by norm_num)
  have hP := sourceCutMultiplier_maskedPhysicalPDO χout χsource c R M hb
    ψ hψ.continuous hψb hp
  have he : (fun x ↦ ((μ x * ψ x : ℝ) : ℂ)*χout x) =
      (fun x ↦ (μ x : ℂ)*(ψ x : ℂ)) := by
    funext x
    rw [Complex.ofReal_mul, mul_assoc, hp]
  calc
    _ = measuredOperator μ ν hμ.continuous hν.continuous hμb hνb
        ((sourceCutMultiplier ψ hψ.continuous hψb).comp (maskedPhysicalPDO χout χsource c)) :=
      congrArg (fun T : H →L[ℂ] H ↦ measuredOperator μ ν hμ.continuous hν.continuous hμb hνb T)
        hP.symm
    _ = measuredOperator (fun x ↦ μ x*ψ x) ν (hμ.mul hψ).continuous
        hν.continuous hmb hνb (maskedPhysicalPDO χout χsource c) :=
      measuredOperator_output_product μ ν ψ hμ.continuous hν.continuous hψ.continuous
        hμb hνb hψb hmb _
    _ = _ := (measured_maskedPhysicalPDO_eq χout χsource c hb (fun x ↦ μ x*ψ x) ν
        (hμ.mul hψ) hν hmb hνb).trans
      (congrArg (fun χ ↦ maskedPhysicalPDO χ (fun y ↦ (ν y : ℂ)*χsource y) c) he)

/-- The original normal-amplitude realization supplies all measured
common-output PDO regularizations and both literal strong limits. No smaller
normal certificate is assumed. Consumer: all selected measured PDO branches
(`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem exists_measured_commonOutputPDO_oriented_regularizations
    (χout χsource : E → ℂ) (c : E → E → CMat)
    (hout : HasCompactSupport χout) (hsource : HasCompactSupport χsource) {R M : ℝ}
    (hb : GraphNormalAmplitudeBounds (maskedPhysicalPDOCycleSymbol χout χsource c) R M)
    (ψ : E → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψb : ∀ x, ‖ψ x‖ ≤ 1)
    (hp : ∀ x, (ψ x : ℂ) * χout x = (ψ x : ℂ))
    (μ ν : E → ℝ) (hμ : ContDiff ℝ ∞ μ) (hν : ContDiff ℝ ∞ ν)
    (hμb : ∀ x, ‖μ x‖ ≤ 1) (hνb : ∀ x, ‖ν x‖ ≤ 1) :
    let χo := fun x ↦ (μ x : ℂ)*(ψ x : ℂ)
    let χs := fun y ↦ (ν y : ℂ)*χsource y
    (∀ backward, ContDiff ℝ ∞ (fun p : (E × E) × E ↦
      orientedMaskedPDOAmplitude backward χo χs c p.1.1 p.1.2 p.2)) ∧
    ∃ Preg : Bool → ℕ → H →L[ℂ] H,
      (∀ j, Preg true j = (Preg false j).adjoint) ∧
      (∀ backward j (u : graphTestSpace (d+1) q),
        Preg backward j (graphTestToLp u) =ᵐ[volume] fun x ↦ WithLp.toLp 2
          (((if backward then reverseGraphOperator else graphOperator)
            (fun x ξ ↦ inner ℝ x ξ)
            (frequencyCutFullAmplitude (complexPhysicalCutoff j)
              (orientedMaskedPDOAmplitude backward χo χs c))
            (fun y ↦ (u.val y).ofLp)) x)) ∧
      (∀ backward u, Tendsto (fun j ↦ Preg backward j u) atTop
        (𝓝 ((if backward then (maskedPhysicalPDO χo χs c).adjoint
          else maskedPhysicalPDO χo χs c) u))) := by
  intro χo χs
  have hmb (x : E) : ‖μ x * ψ x‖ ≤ 1 := by
    rw [norm_mul]
    exact (mul_le_mul (hμb x) (hψb x) (norm_nonneg _) zero_le_one).trans (by norm_num)
  have he : (fun x ↦ ((μ x * ψ x : ℝ) : ℂ)*χout x) = χo := by
    funext x
    dsimp only [χo]
    rw [Complex.ofReal_mul, mul_assoc, hp]
  simpa only [he] using exists_measured_maskedPDO_oriented_regularizations
    χout χsource c hout hsource hb (fun x ↦ μ x*ψ x) ν (hμ.mul hψ) hν hmb hνb

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
