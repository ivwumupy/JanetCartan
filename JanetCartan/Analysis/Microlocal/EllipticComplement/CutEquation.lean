module

public import JanetCartan.Analysis.Microlocal.EllipticComplement.Symbol

/-!
# Exact compact-frequency elliptic equation

The commutator with the original output cutoff is displayed before restricting
to its measurement plateau. The datum in the tested realization is the
original source-masked test. Source: `app:ch_regular_base:sec:energy-construction`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.EllipticComplement
open ActualCarriers FiniteMasks.ActualFamily Characteristic FourierIntegral
open JanetCartan.CharacteristicTransport.CompleteResidual
variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "Mat" => MetricTensor (d+1)
local notation "FV" => Fin (d+1) → ℂ
local notation "CMat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ
local notation "Coeff" => Fin (d+1) → Mat
variable {Ω : Set (Euclidean (d + 1))} {x : Euclidean (d + 1)} {RQ M : ℝ}
variable {A₀ : Fin (d + 1) → MetricTensor (d + 1)} {K : Set (Euclidean (d + 1))}
variable (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K)

/-- The finite elliptic equation including the full output commutator.
`θ` is any smooth compact frequency regularization; the elliptic symbol
itself always retains its own low collar (`energy-complete-residual`). -/
theorem firstOrderApply_cutEllipticSolver (hΩ : IsOpen Ω) {L : ℝ} (hL : 0 < L)
    (Q : E → Coeff) (B : E → Mat) (hQ : ContDiffOn ℝ ∞ Q Ω)
    (hmap : MapsTo Q Ω (closedBall A₀ f.coefficientRadius))
    (θ : E → ℂ) (hθ : ContDiff ℝ ∞ θ) (hθc : HasCompactSupport θ)
    (v : SchwartzMap E FV) (hv : HasCompactSupport (v : E → FV)) (y : E) :
    let core := fun z ↦ (1 / Complex.I) • cutPhysicalPDO θ (ellipticInverseSymbol f hK L Q) v z
    WKB.firstOrderApply (complexPencilCoefficient Q) (complexPencilZeroth B)
      (fun z ↦ (f.outputMask z : ℂ) • core z) y =
        (∑ a, partialDeriv (fun z ↦ (f.outputMask z : ℂ)) y a •
          complexPencilCoefficient Q y a (core y)) +
        (f.outputMask y : ℂ) • (cutPhysicalPDO θ (ellipticSourceSymbol f hK L) v y +
          (1 / Complex.I) • cutPhysicalPDO θ (ellipticResidualSymbol f hK L Q B) v y) := by
  intro core
  let c := ellipticInverseSymbol f hK L Q
  let A := fun y a ↦ (pencil (Q y) (EuclideanSpace.single a 1)).map Complex.ofReal
  let Hc := fun z ξ ↦ (∑ a, (ξ a : ℂ) • A z a) * c z ξ
  have hc := contDiff_ellipticInverseSymbol f hK hΩ hL Q hQ hmap
  have hk : DifferentiableAt ℝ core y := ((contDiff_cutPhysicalPDO θ c v hθ hθc hc hv).const_smul
    (1 / Complex.I)).differentiable (by simp) y
  have ho : DifferentiableAt ℝ (fun z ↦ (f.outputMask z : ℂ)) y :=
    (Complex.ofRealCLM.contDiff.comp f.outputMask_smooth).differentiable (by simp) y
  rw [firstOrderApply_smul (complexPencilCoefficient Q) (complexPencilZeroth B) ho hk]
  congr 1
  by_cases hzero : f.outputMask y = 0
  · simp only [hzero, Complex.ofReal_zero, zero_smul]
  have hy := ball_subset_closedBall (f.outputMask_support (subset_tsupport _ hzero))
  have hact : WKB.firstOrderApply (complexPencilCoefficient Q) (complexPencilZeroth B) core y =
      cutPhysicalPDO θ (fun z ξ ↦ Hc z ξ + (1 / Complex.I) • ellipticResidualSymbol f hK L Q B z ξ)
        v y := firstOrderApply_inverseI_cutPDO A (fun z ↦ (B z).map Complex.ofReal) c
          θ hθ hθc isOpen_univ hc.contDiffOn v (v.smooth ⊤) hv (mem_univ y)
  have hprincipal : Hc y = ellipticSourceSymbol f hK L y :=
    funext (principalMatrix_mul_ellipticInverseSymbol f hK hL Q hmap hy)
  have hH : Continuous (Hc y) := by
    rw [hprincipal]
    exact (Complex.ofRealCLM.continuous.comp (ellipticSourceMask_properties f hK L).1.continuous).smul
      continuous_const
  have hp := continuous_physicalSymbolApply_frequency A (fun z ↦ (B z).map Complex.ofReal) c hc y
  rw [hact, cutPhysicalPDO_add θ Hc _ v y hθ.continuous hθc hH (hp.const_smul (1 / Complex.I : ℂ)),
    cutPhysicalPDO_smul]
  have he : cutPhysicalPDO θ Hc v y = cutPhysicalPDO θ (ellipticSourceSymbol f hK L) v y := by
    simp only [cutPhysicalPDO, graphOperator_eq_sourceFourierIntegral]
    rw [hprincipal]
  rw [he]

/-- The genuine output plateau removes the commutator from the exact cut
equation. Both residual and principal terms keep their output factor for
passage to the strong operator limits (`sector-theorem-identity`). -/
theorem firstOrderApply_cutEllipticSolver_on_plateau (hΩ : IsOpen Ω) {L : ℝ} (hL : 0 < L)
    (Q : E → Coeff) (B : E → Mat) (hQ : ContDiffOn ℝ ∞ Q Ω)
    (hmap : MapsTo Q Ω (closedBall A₀ f.coefficientRadius))
    (θ : E → ℂ) (hθ : ContDiff ℝ ∞ θ) (hθc : HasCompactSupport θ)
    (v : SchwartzMap E FV) (hv : HasCompactSupport (v : E → FV))
    {y : E} (hy : y ∈ closedBall x f.physicalRadius) :
    WKB.firstOrderApply (complexPencilCoefficient Q) (complexPencilZeroth B)
      (fun z ↦ (f.outputMask z : ℂ) • (1 / Complex.I) •
        cutPhysicalPDO θ (ellipticInverseSymbol f hK L Q) v z) y =
      (f.outputMask y : ℂ) • (cutPhysicalPDO θ (ellipticSourceSymbol f hK L) v y +
        (1 / Complex.I) • cutPhysicalPDO θ (ellipticResidualSymbol f hK L Q B) v y) := by
  have he : (fun z ↦ (f.outputMask z : ℂ)) =ᶠ[𝓝 y] (fun _ ↦ (1 : ℂ)) := by
    filter_upwards [isOpen_interior.mem_nhds (f.outputMask_plateau hy)] with z hz
    exact_mod_cast (interior_subset (s := {z | f.outputMask z = 1}) hz)
  have hd : fderiv ℝ (fun z ↦ (f.outputMask z : ℂ)) y = 0 := by simpa using he.fderiv_eq (𝕜 := ℝ)
  simpa only [partialDeriv, hd, zero_apply, zero_smul, Finset.sum_const_zero,
    zero_add] using firstOrderApply_cutEllipticSolver f hK hΩ hL Q B hQ hmap θ hθ hθc v hv y

end JanetCartan.RegularSector.EllipticComplement
