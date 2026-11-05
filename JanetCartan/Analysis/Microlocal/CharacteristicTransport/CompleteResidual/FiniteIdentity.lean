module

public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.CompleteResidual.Endpoint
public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.CompleteResidual.PdoAlgebra

/-!
# The three-term finite-cutoff residual identity

Source: `paper-v2.tex`, `app:ch_regular_base:eq:energy-complete-residual`.
The local kernel producer supplies the column cancellation and leading
diagonal; the complement producer supplies H b₋₁ = I - proj on the multiplier
support. The conclusion combines these with the literal retarded derivative
and the physical PDO action. No uncut residual equation is an input.

The source-masked Schwartz datum is identical in every term. The output
commutator is retained until a neighborhood plateau is supplied. This is the
finite-frequency input to the strong-limit passage, not a uniform sector
construction or a claim that Op(α) is the identity.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.CharacteristicTransport.CompleteResidual
open FourierIntegral KernelDifferentiation
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "FV" => Fin q → ℂ
local notation "Mat" => Matrix (Fin q) (Fin q) ℂ

/-- The complete algebraic symbol b₋₁ α, with α = σ β. Physical derivatives
act on this entire product (`app:ch_regular_base:eq:energy-complete-residual`). -/
def directAlgebraicSymbol (bminus : E → E → Mat) (σ : E → Euclidean d → ℂ)
    (β : E → ℂ) (x ξ : E) : Mat := (σ x (spatialPart ξ) * β ξ) • bminus x ξ

/-- The matrix P W₁ with source time and spatial frequency held fixed,
including the zeroth-order coefficient B₀
(`app:ch_regular_base:eq:energy-complete-residual`). -/
def twoTimePhysicalApply (A : E → Fin (d + 1) → Mat) (B : E → Mat)
    (W : TwoTimeAmplitude d q) : TwoTimeAmplitude d q := fun t s y η ↦
  physicalSymbolApply A B (fun x _ ↦ W (x 0) s (spatialPart x) η)
    (timeSpacePoint t y) 0

/-- The literal core E_(W₀+W₁) Bβ + (1/i) Op(b₋₁ α). The lower buffer a
is fixed, and v is the same original source-masked input in both pieces
(`app:ch_regular_base:eq:energy-complete-residual`). -/
def cutDirectCore (Ψ : TwoTimePhase d) (W₀ W₁ : TwoTimeAmplitude d q)
    (bminus : E → E → Mat) (σ : E → Euclidean d → ℂ) (β θ : E → ℂ)
    (a : ℝ) (v : SchwartzMap E FV) (x : E) : FV :=
  (∫ s in a..x 0, cutFixedTimeFourier Ψ (W₀ + W₁) β θ v (x 0) s (spatialPart x)) +
    (1 / Complex.I) • cutPhysicalPDO θ (directAlgebraicSymbol bminus σ β) v x

/-- The literal masked physical solver with the physical 1/i normalization
(`app:ch_regular_base:eq:energy-complete-residual`). -/
def cutDirectSolver (Ψ : TwoTimePhase d) (W₀ W₁ : TwoTimeAmplitude d q)
    (bminus : E → E → Mat) (σ : E → Euclidean d → ℂ) (β θ χout : E → ℂ)
    (a : ℝ) (v : SchwartzMap E FV) (x : E) : FV :=
  χout x • cutDirectCore Ψ W₀ W₁ bminus σ β θ a v x

/-- All three actual residual terms: the W₁ endpoint, the retarded P W₁,
and the physical derivative of the entire algebraic symbol. The original
right multiplier and source-masked datum retain their order
(`app:ch_regular_base:eq:energy-complete-residual`). -/
def cutCompleteResidual (A : E → Fin (d + 1) → Mat) (B : E → Mat)
    (Ψ : TwoTimePhase d) (W₁ : TwoTimeAmplitude d q)
    (bminus : E → E → Mat) (σ : E → Euclidean d → ℂ) (β θ : E → ℂ)
    (a : ℝ) (v : SchwartzMap E FV) (x : E) : FV :=
  cutPhysicalPDO θ (fun y ξ ↦ β ξ •
    (A y 0 * W₁ (y 0) (y 0) (spatialPart y) (spatialPart ξ))) v x +
  (∫ s in a..x 0, cutFixedTimeFourier Ψ (twoTimePhysicalApply A B W₁)
    β θ v (x 0) s (spatialPart x)) +
  (1 / Complex.I) • cutPhysicalPDO θ
    (physicalSymbolApply A B (directAlgebraicSymbol bminus σ β)) v x

private theorem firstOrderApply_add (A : E → Fin (d + 1) → Mat) (B : E → Mat)
    {f g : E → FV} {x : E} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    WKB.firstOrderApply (fun y j ↦ (A y j).mulVecLin) (fun y ↦ (B y).mulVecLin)
      (fun y ↦ f y + g y) x =
    WKB.firstOrderApply (fun y j ↦ (A y j).mulVecLin) (fun y ↦ (B y).mulVecLin) f x +
    WKB.firstOrderApply (fun y j ↦ (A y j).mulVecLin) (fun y ↦ (B y).mulVecLin) g x := by
  simp only [WKB.firstOrderApply, partialDeriv, fderiv_fun_add hf hg,
    add_apply, map_add, Finset.sum_add_distrib]
  abel

/-- Smoothness of the finite solver is derived from the primitive phase,
amplitudes and whole algebraic symbol. This is the regularity input for
integration by parts before the uncut limit
(`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem contDiff_cutDirectCore
    (Ψ : TwoTimePhase d) (W₀ W₁ : TwoTimeAmplitude d q)
    (bminus : E → E → Mat) (σ : E → Euclidean d → ℂ) (β θ : E → ℂ)
    (a : ℝ) (v : SchwartzMap E FV)
    (hΨ : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      Ψ p.1.1 p.1.2 p.2.1 p.2.2))
    (hW : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      (W₀ + W₁) p.1.1 p.1.2 p.2.1 p.2.2))
    (hc : ContDiff ℝ ∞ (Function.uncurry (directAlgebraicSymbol bminus σ β)))
    (hβ : ContDiff ℝ ∞ β) (hθ : ContDiff ℝ ∞ θ) (hθcs : HasCompactSupport θ)
    (hvcs : HasCompactSupport (v : E → FV)) :
    ContDiff ℝ ∞ (cutDirectCore Ψ W₀ W₁ bminus σ β θ a v) := by
  have hr := contDiff_cutFixedTimeFourier Ψ (W₀ + W₁) β θ v hΨ hW hβ hθ hθcs
  exact (((contDiff_retardedPrimitive hr a).comp
    ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1))).contDiff.prodMk contDiff_id))).add
      ((contDiff_cutPhysicalPDO θ _ v hθ hθcs hc hvcs).const_smul (1 / Complex.I))

/-- Complete finite-cutoff identity, with its output commutator. The inputs
are the local column identity from `exists_physical_pencil_kernel`, its
leading diagonal, and the complement equation on the support of β from
`complementInverse_identity`. They are combined here; no finite or uncut
solver equation is assumed. The residual retains all three terms, and the
principal term remains Op(α), including low frequencies
(`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem firstOrderApply_cutDirectSolver
    (A : E → Fin (d + 1) → Mat) (B : E → Mat)
    (Ψ : TwoTimePhase d) (W₀ W₁ : TwoTimeAmplitude d q)
    (bminus : E → E → Mat) (σ : E → Euclidean d → ℂ)
    (proj : E → Euclidean d → Mat) (β θ χout : E → ℂ)
    (a : ℝ) (v : SchwartzMap E FV) (x : E)
    (hΨ : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      Ψ p.1.1 p.1.2 p.2.1 p.2.2))
    (hW₀ : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      W₀ p.1.1 p.1.2 p.2.1 p.2.2))
    (hW₁ : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      W₁ p.1.1 p.1.2 p.2.1 p.2.2))
    (hc : ContDiff ℝ ∞ (Function.uncurry (directAlgebraicSymbol bminus σ β)))
    (hσ : Continuous (σ x)) (hβ : ContDiff ℝ ∞ β)
    (hθ : ContDiff ℝ ∞ θ) (hθcs : HasCompactSupport θ)
    (hvcs : HasCompactSupport (v : E → FV)) (ho : DifferentiableAt ℝ χout x)
    (hdiag : ∀ t y η, Ψ t t y η = inner ℝ y η)
    (hlead : ∀ η, A x 0 * W₀ (x 0) (x 0) (spatialPart x) η = σ x η • proj x η)
    (hcomp : ∀ ξ, β ξ ≠ 0 →
      (∑ j, (ξ j : ℂ) • A x j) * bminus x ξ = 1 - proj x (spatialPart ξ))
    (hcancel : ∀ s η j, WKB.firstOrderApply
      (fun y i ↦ (A y i).mulVecLin) (fun y ↦ (B y).mulVecLin)
      (fun y ↦ Complex.exp (Complex.I * (Ψ (y 0) s (spatialPart y) η : ℂ)) •
        (fun i ↦ (W₀ + W₁) (y 0) s (spatialPart y) η i j)) x =
      Complex.exp (Complex.I * (Ψ (x 0) s (spatialPart x) η : ℂ)) •
        (fun i ↦ twoTimePhysicalApply A B W₁ (x 0) s (spatialPart x) η i j)) :
    WKB.firstOrderApply (fun y j ↦ (A y j).mulVecLin) (fun y ↦ (B y).mulVecLin)
      (cutDirectSolver Ψ W₀ W₁ bminus σ β θ χout a v) x =
      (∑ j, partialDeriv χout x j • (A x j).mulVec
        (cutDirectCore Ψ W₀ W₁ bminus σ β θ a v x)) +
      χout x • (cutPhysicalPDO θ
        (fun y ξ ↦ (σ y (spatialPart ξ) * β ξ) • (1 : Mat)) v x +
        cutCompleteResidual A B Ψ W₁ bminus σ β θ a v x) := by
  let c := directAlgebraicSymbol bminus σ β
  let e : E → E → Mat := fun y ξ ↦ β ξ •
    (A y 0 * (W₀ + W₁) (y 0) (y 0) (spatialPart y) (spatialPart ξ))
  let e₁ : E → E → Mat := fun y ξ ↦ β ξ •
    (A y 0 * W₁ (y 0) (y 0) (spatialPart y) (spatialPart ξ))
  let Hc : E → E → Mat := fun y ξ ↦ (∑ j, (ξ j : ℂ) • A y j) * c y ξ
  let α : E → E → Mat := fun y ξ ↦ (σ y (spatialPart ξ) * β ξ) • (1 : Mat)
  have hW : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      (W₀ + W₁) p.1.1 p.1.2 p.2.1 p.2.2) := hW₀.add hW₁
  have hsW := contDiff_cutFixedTimeFourier Ψ (W₀ + W₁) β θ v hΨ hW hβ hθ hθcs
  have hretD : DifferentiableAt ℝ (fun y ↦ ∫ s in a..y 0,
      cutFixedTimeFourier Ψ (W₀ + W₁) β θ v (y 0) s (spatialPart y)) x :=
    (((contDiff_retardedPrimitive hsW a).comp
      ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1))).contDiff.prodMk
        contDiff_id)).differentiable (by simp)) x
  have hcD := ((contDiff_cutPhysicalPDO θ c v hθ hθcs hc hvcs).const_smul
    (1 / Complex.I)).differentiable (by simp) x
  have hret := firstOrderApply_masked_retarded_of_column_cancellation
    Ψ (W₀ + W₁) (twoTimePhysicalApply A B W₁) β θ (fun _ ↦ 1) v
    hΨ hW hβ hθ hθcs (fun y j ↦ (A y j).mulVecLin.toContinuousLinearMap)
    (fun y ↦ (B y).mulVecLin.toContinuousLinearMap) a x (differentiableAt_const 1) hcancel
  simp [partialDeriv] at hret
  have hb : Continuous ((W₀ + W₁) (x 0) (x 0) (spatialPart x)) :=
    hW.continuous.comp (f := fun η ↦ ((x 0, x 0), (spatialPart x, η)))
      (continuous_const.prodMk (continuous_const.prodMk continuous_id))
  have hend := timeCoefficient_cutFixedTimeFourier_diagonal_eq_spacetimePDO
    Ψ (W₀ + W₁) β θ v (fun y ↦ A y 0) x hdiag hb hβ.continuous hθ.continuous hθcs
  have hend' : (A x 0).mulVec
      (cutFixedTimeFourier Ψ (W₀ + W₁) β θ v (x 0) (x 0) (spatialPart x)) =
      cutPhysicalPDO θ e v x := by
    simpa only [cutPhysicalPDO, e, smul_smul] using hend
  have hpdo : WKB.firstOrderApply (fun y j ↦ (A y j).mulVecLin)
      (fun y ↦ (B y).mulVecLin) (fun y ↦ (1 / Complex.I) • cutPhysicalPDO θ c v y) x =
      cutPhysicalPDO θ (fun y ξ ↦ Hc y ξ + (1 / Complex.I) • physicalSymbolApply A B c y ξ) v x :=
    firstOrderApply_inverseI_cutPDO A B c θ hθ hθcs isOpen_univ hc.contDiffOn
      v (v.smooth ⊤) hvcs (mem_univ x)
  have hec : Continuous (e x) := hβ.continuous.smul
    (continuous_const.mul (hb.comp continuous_spatialPart))
  have he₁c : Continuous (e₁ x) := hβ.continuous.smul (continuous_const.mul
    (hW₁.continuous.comp (f := fun ξ ↦ ((x 0, x 0), (spatialPart x, spatialPart ξ)))
      (continuous_const.prodMk (continuous_const.prodMk continuous_spatialPart))))
  have hHc : Continuous (Hc x) := by
    apply Continuous.mul
    · apply continuous_finsetSum
      intro j _
      exact (Complex.continuous_ofReal.comp (EuclideanSpace.proj j).continuous).smul continuous_const
    · exact hc.continuous.comp (continuous_const.prodMk continuous_id)
  have hα : Continuous (α x) := ((hσ.comp continuous_spatialPart).mul hβ.continuous).smul
    continuous_const
  have hPc := continuous_physicalSymbolApply_frequency A B c hc x
  have hcancelSymbol (ξ : E) : e x ξ + Hc x ξ = α x ξ + e₁ x ξ := by
    dsimp only [e, Hc, c, directAlgebraicSymbol, α, e₁]
    simp only [Pi.add_apply]
    by_cases hz : β ξ = 0
    · simp [hz]
    · rw [Matrix.mul_add, hlead, Matrix.mul_smul, hcomp ξ hz]
      simp only [smul_add, smul_smul, smul_sub]
      rw [mul_comm (β ξ) (σ x (spatialPart ξ))]
      abel
  have hsum : cutPhysicalPDO θ e v x + cutPhysicalPDO θ Hc v x =
      cutPhysicalPDO θ α v x + cutPhysicalPDO θ e₁ v x := by
    rw [← cutPhysicalPDO_add θ e Hc v x hθ.continuous hθcs hec hHc,
      ← cutPhysicalPDO_add θ α e₁ v x hθ.continuous hθcs hα he₁c]
    simp only [cutPhysicalPDO, graphOperator_eq_sourceFourierIntegral]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with ξ
    rw [hcancelSymbol]
  change WKB.firstOrderApply _ _ (fun y ↦ χout y • cutDirectCore Ψ W₀ W₁ bminus σ β θ a v y) x = _
  have hcoreD : DifferentiableAt ℝ (cutDirectCore Ψ W₀ W₁ bminus σ β θ a v) x :=
    hretD.add hcD
  rw [RegularSector.Characteristic.firstOrderApply_smul _ _ ho hcoreD]
  congr 1
  congr 1
  change WKB.firstOrderApply _ _ (fun y ↦ _ + _) x = _
  rw [firstOrderApply_add A B hretD hcD, hret, hend', hpdo]
  change cutPhysicalPDO θ e v x + _ +
    cutPhysicalPDO θ (fun y ξ ↦ Hc y ξ + (1 / Complex.I) • physicalSymbolApply A B c y ξ) v x = _
  rw [cutPhysicalPDO_add θ Hc _ v x hθ.continuous hθcs hHc (hPc.const_smul (1 / Complex.I : ℂ)),
    cutPhysicalPDO_smul]
  change _ = cutPhysicalPDO θ α v x + (cutPhysicalPDO θ e₁ v x + _ + _)
  calc
    _ = (cutPhysicalPDO θ e v x + cutPhysicalPDO θ Hc v x) +
      ((∫ s in a..x 0, cutFixedTimeFourier Ψ (twoTimePhysicalApply A B W₁)
        β θ v (x 0) s (spatialPart x)) +
        (1 / Complex.I) • cutPhysicalPDO θ (physicalSymbolApply A B c) v x) := by abel
    _ = _ := by rw [hsum]; abel

/-- Restriction to the measurement plateau removes precisely the output
commutator. The low-frequency principal defect remains explicit
(`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem firstOrderApply_cutDirectSolver_on_plateau
    (A : E → Fin (d + 1) → Mat) (B : E → Mat)
    (Ψ : TwoTimePhase d) (W₀ W₁ : TwoTimeAmplitude d q)
    (bminus : E → E → Mat) (σ : E → Euclidean d → ℂ)
    (proj : E → Euclidean d → Mat) (β θ χout : E → ℂ)
    (a : ℝ) (v : SchwartzMap E FV) (x : E)
    (hΨ : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      Ψ p.1.1 p.1.2 p.2.1 p.2.2))
    (hW₀ : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      W₀ p.1.1 p.1.2 p.2.1 p.2.2))
    (hW₁ : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      W₁ p.1.1 p.1.2 p.2.1 p.2.2))
    (hc : ContDiff ℝ ∞ (Function.uncurry (directAlgebraicSymbol bminus σ β)))
    (hσ : Continuous (σ x)) (hβ : ContDiff ℝ ∞ β)
    (hθ : ContDiff ℝ ∞ θ) (hθcs : HasCompactSupport θ)
    (hvcs : HasCompactSupport (v : E → FV)) (hplateau : χout =ᶠ[𝓝 x] fun _ ↦ (1 : ℂ))
    (hdiag : ∀ t y η, Ψ t t y η = inner ℝ y η)
    (hlead : ∀ η, A x 0 * W₀ (x 0) (x 0) (spatialPart x) η = σ x η • proj x η)
    (hcomp : ∀ ξ, β ξ ≠ 0 →
      (∑ j, (ξ j : ℂ) • A x j) * bminus x ξ = 1 - proj x (spatialPart ξ))
    (hcancel : ∀ s η j, WKB.firstOrderApply
      (fun y i ↦ (A y i).mulVecLin) (fun y ↦ (B y).mulVecLin)
      (fun y ↦ Complex.exp (Complex.I * (Ψ (y 0) s (spatialPart y) η : ℂ)) •
        (fun i ↦ (W₀ + W₁) (y 0) s (spatialPart y) η i j)) x =
      Complex.exp (Complex.I * (Ψ (x 0) s (spatialPart x) η : ℂ)) •
        (fun i ↦ twoTimePhysicalApply A B W₁ (x 0) s (spatialPart x) η i j)) :
    WKB.firstOrderApply (fun y j ↦ (A y j).mulVecLin) (fun y ↦ (B y).mulVecLin)
      (cutDirectSolver Ψ W₀ W₁ bminus σ β θ χout a v) x =
      cutPhysicalPDO θ (fun y ξ ↦ (σ y (spatialPart ξ) * β ξ) • (1 : Mat)) v x +
        cutCompleteResidual A B Ψ W₁ bminus σ β θ a v x := by
  have ho : DifferentiableAt ℝ χout x :=
    hplateau.differentiableAt_iff.mpr (differentiableAt_const (1 : ℂ))
  have hid := firstOrderApply_cutDirectSolver A B Ψ W₀ W₁ bminus σ proj β θ χout a v x
    hΨ hW₀ hW₁ hc hσ hβ hθ hθcs hvcs ho hdiag hlead hcomp hcancel
  have hz := outputMask_commutator_eq_zero_of_plateau χout
    (fun y j ↦ (A y j).mulVecLin.toContinuousLinearMap) x
    (cutDirectCore Ψ W₀ W₁ bminus σ β θ a v x) hplateau
  change (∑ j, partialDeriv χout x j • (A x j).mulVec
    (cutDirectCore Ψ W₀ W₁ bminus σ β θ a v x)) = 0 at hz
  simpa only [hz, hplateau.eq_of_nhds, zero_add, one_smul] using hid

end JanetCartan.CharacteristicTransport.CompleteResidual
