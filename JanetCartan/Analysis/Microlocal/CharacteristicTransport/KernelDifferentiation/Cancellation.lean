module

public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.KernelDifferentiation.RetardedAction
public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.KernelDifferentiation.FrequencyInterchange
public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.KernelDifferentiation.Columns

/-!
# Passing the two-term column cancellation through the literal kernel

For `app:ch_regular_base:eq:two-term-null-identity`, instantiate `b = W₀ + W₁`
and `r = P W₁`, with the column identity supplied by
`RegularSector.Characteristic.firstOrder_directCorrection_identity`.
These results prove the finite-cutoff implication, including the retarded
endpoint and output commutator; the parent supplies its actual amplitudes.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.CharacteristicTransport.KernelDifferentiation
open WKB
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "FV" => Fin q → ℂ

/-- The pointwise cancellation itself determines the residual amplitude,
whose continuity follows from primitive joint smoothness of the oscillatory
columns. Consumer: frequency Fubini after cancellation in
`app:ch_regular_base:eq:energy-complete-residual`; no regularity premise on the
requested differentiated action is needed. -/
theorem continuous_residual_of_column_cancellation (Ψ : TwoTimePhase d) (b r : TwoTimeAmplitude d q)
    (hΨ : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      Ψ p.1.1 p.1.2 p.2.1 p.2.2))
    (hb : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      b p.1.1 p.1.2 p.2.1 p.2.2))
    (C : E → Fin (d + 1) → FV →L[ℂ] FV) (D : E → FV →L[ℂ] FV)
    (s : ℝ) (x : E)
    (hcancel : ∀ η j, firstOrderApply
      (fun y i ↦ (C y i).toLinearMap) (fun y ↦ (D y).toLinearMap)
      (fun y ↦ Complex.exp (Complex.I * (Ψ (y 0) s (spatialPart y) η : ℂ)) •
        (fun i ↦ b (y 0) s (spatialPart y) η i j)) x =
      Complex.exp (Complex.I * (Ψ (x 0) s (spatialPart x) η : ℂ)) •
        (fun i ↦ r (x 0) s (spatialPart x) η i j)) :
    Continuous (r (x 0) s (spatialPart x)) := by
  have hp : ContDiff ℝ ∞ (fun p : E × Euclidean d ↦
      ((p.1 0,s),(spatialPart p.1,p.2))) :=
    (((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1))).contDiff.comp contDiff_fst).prodMk
      contDiff_const).prodMk ((spatialPartCLM.contDiff.comp contDiff_fst).prodMk contDiff_snd)
  have he : ContDiff ℝ ∞ (fun p : E × Euclidean d ↦
      Complex.exp (Complex.I * (Ψ (p.1 0) s (spatialPart p.1) p.2 : ℂ))) :=
    ((contDiff_const (c := Complex.I)).mul (Complex.ofRealCLM.contDiff.comp (hΨ.comp hp))).cexp
  apply continuous_matrix
  intro i j
  let f : E × Euclidean d → FV := fun p ↦
    Complex.exp (Complex.I * (Ψ (p.1 0) s (spatialPart p.1) p.2 : ℂ)) •
      (fun k ↦ b (p.1 0) s (spatialPart p.1) p.2 k j)
  have hf : ContDiff ℝ ∞ f := by
    apply he.smul
    apply contDiff_pi.mpr
    intro k
    exact (Matrix.entryLinearMap ℝ ℂ k j).toContinuousLinearMap.contDiff.comp (hb.comp hp)
  have hfd : Continuous (fun p : E × Euclidean d ↦ fderiv ℝ (fun y ↦ f (y,p.2)) p.1) := by
    have hh := contDiffOn_parameterFDeriv (U := univ) (V := univ)
      isOpen_univ isOpen_univ hf.contDiffOn
    exact (contDiffOn_univ.mp (by simpa using hh)).continuous
  have hP : Continuous (fun η ↦ firstOrderApply (fun y k ↦ (C y k).toLinearMap)
      (fun y ↦ (D y).toLinearMap) (fun y ↦ f (y,η)) x) := by
    unfold firstOrderApply partialDeriv
    apply Continuous.add
    · apply continuous_finsetSum
      intro k _
      exact (C x k).continuous.comp
        ((hfd.comp (continuous_const.prodMk continuous_id)).clm_apply continuous_const)
    · exact (D x).continuous.comp (hf.continuous.comp (continuous_const.prodMk continuous_id))
  have hei : Continuous (fun η ↦
      (Complex.exp (Complex.I * (Ψ (x 0) s (spatialPart x) η : ℂ)))⁻¹) :=
    (he.continuous.comp (continuous_const.prodMk continuous_id)).inv₀
      (fun _ ↦ Complex.exp_ne_zero _)
  have hc := hei.mul ((continuous_apply i).comp hP)
  apply hc.congr
  intro η
  have hid := congrFun (hcancel η j) i
  change (firstOrderApply (fun y k ↦ (C y k).toLinearMap)
    (fun y ↦ (D y).toLinearMap) (fun y ↦ f (y,η)) x) i =
    Complex.exp (Complex.I * (Ψ (x 0) s (spatialPart x) η : ℂ)) *
      r (x 0) s (spatialPart x) η i j at hid
  dsimp only [Pi.mul_apply, Function.comp_apply]
  rw [hid]
  simp [Complex.exp_ne_zero]

/-- The exact pointwise identity for each column passes through the actual
finite-frequency kernel. The right multiplier `θ β` and its initial source-time
slice are unchanged (`app:ch_regular_base:eq:two-term-null-identity`). -/
theorem firstOrderApply_cutFixedTimeFourier_of_column_cancellation (Ψ : TwoTimePhase d) (b r : TwoTimeAmplitude d q) (β θ : E → ℂ)
    (v : SchwartzMap E FV)
    (hΨ : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      Ψ p.1.1 p.1.2 p.2.1 p.2.2))
    (hb : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      b p.1.1 p.1.2 p.2.1 p.2.2))
    (hβ : ContDiff ℝ ∞ β) (hθ : ContDiff ℝ ∞ θ) (hθcs : HasCompactSupport θ)
    (C : E → Fin (d + 1) → FV →L[ℂ] FV) (D : E → FV →L[ℂ] FV)
    (s : ℝ) (x : E)
    (hcancel : ∀ η j, firstOrderApply
      (fun y i ↦ (C y i).toLinearMap) (fun y ↦ (D y).toLinearMap)
      (fun y ↦ Complex.exp (Complex.I * (Ψ (y 0) s (spatialPart y) η : ℂ)) •
        (fun i ↦ b (y 0) s (spatialPart y) η i j)) x =
      Complex.exp (Complex.I * (Ψ (x 0) s (spatialPart x) η : ℂ)) •
        (fun i ↦ r (x 0) s (spatialPart x) η i j)) :
    firstOrderApply (fun y j ↦ (C y j).toLinearMap) (fun y ↦ (D y).toLinearMap)
      (fun y ↦ cutFixedTimeFourier Ψ b β θ v (y 0) s (spatialPart y)) x =
        cutFixedTimeFourier Ψ r β θ v (x 0) s (spatialPart x) := by
  have hr := continuous_residual_of_column_cancellation Ψ b r hΨ hb C D s x hcancel
  rw [firstOrderApply_cutFixedTimeFourier Ψ b β θ v hΨ hb hβ hθ hθcs C D s x]
  rw [← integral_cutFixedTimeFourier Ψ r β θ v (x 0) s (spatialPart x)
    (hΨ.continuous.comp (f := fun η ↦ ((x 0,s),(spatialPart x,η)))
      (continuous_const.prodMk (continuous_const.prodMk continuous_id)))
    hr hβ.continuous hθ.continuous hθcs]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with ξ
  have hp : ContDiff ℝ ∞ (fun y : E ↦ ((y 0,s),(spatialPart y,spatialPart ξ))) :=
    ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1))).contDiff.prodMk contDiff_const).prodMk
      (spatialPartCLM.contDiff.prodMk contDiff_const)
  have hcol (j : Fin q) : DifferentiableAt ℝ
      (fun y : E ↦ fun i ↦ b (y 0) s (spatialPart y) (spatialPart ξ) i j) x := by
    apply differentiableAt_pi.mpr
    intro i
    exact (((Matrix.entryLinearMap ℝ ℂ i j).toContinuousLinearMap.contDiff.comp
      (hb.comp hp)).differentiable (by simp)) x
  let u : FV := (θ ξ * β ξ) • FourierIntegral.sourceInputFourierTransform v ξ
  have hid := firstOrderApply_oscillatory_mulVec_of_columns
    (fun y j ↦ (C y j).toLinearMap) (fun y ↦ (D y).toLinearMap)
    (r (x 0) s (spatialPart x) (spatialPart ξ))
    (((hΨ.comp hp).differentiable (by simp)) x) hcol (hcancel (spatialPart ξ)) u
  have hm : DifferentiableAt ℝ (fun y : E ↦
      Complex.exp (Complex.I * (Ψ (y 0) s (spatialPart y) (spatialPart ξ) : ℂ)) •
        (b (y 0) s (spatialPart y) (spatialPart ξ)).mulVec u) x := by
    have hc : ContDiff ℝ ∞ (fun y : E ↦
        (b (y 0) s (spatialPart y) (spatialPart ξ)).mulVec u) := by
      apply contDiff_pi.mpr
      intro i
      simp only [Matrix.mulVec, dotProduct]
      apply ContDiff.sum
      intro j _
      exact (((Matrix.entryLinearMap ℝ ℂ i j).toContinuousLinearMap.contDiff.comp
        (hb.comp hp)).mul contDiff_const)
    exact (((contDiff_const (c := Complex.I)).mul
      (Complex.ofRealCLM.contDiff.comp (hΨ.comp hp))).cexp.smul hc).differentiable (by simp) x
  unfold cutFixedTimeFourierIntegrand
  rw [firstOrderApply_const_smul _ _ hm]
  exact congrArg (Complex.exp (Complex.I * ((s * ξ 0 : ℝ) : ℂ)) • ·) hid

/-- The finite-cutoff retarded residual from the exact columnwise two-term
identity. For the direct correction `r = P W₁`; the upper endpoint contains
all of `W₀ + W₁`, including the endpoint correction. Source:
`app:ch_regular_base:eq:energy-complete-residual`. -/
theorem firstOrderApply_masked_retarded_of_column_cancellation
    (Ψ : TwoTimePhase d) (b r : TwoTimeAmplitude d q) (β θ χout : E → ℂ)
    (v : SchwartzMap E FV)
    (hΨ : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      Ψ p.1.1 p.1.2 p.2.1 p.2.2))
    (hb : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      b p.1.1 p.1.2 p.2.1 p.2.2))
    (hβ : ContDiff ℝ ∞ β) (hθ : ContDiff ℝ ∞ θ) (hθcs : HasCompactSupport θ)
    (C : E → Fin (d + 1) → FV →L[ℂ] FV) (D : E → FV →L[ℂ] FV)
    (a : ℝ) (x : E) (hout : DifferentiableAt ℝ χout x)
    (hcancel : ∀ s η j, firstOrderApply
      (fun y i ↦ (C y i).toLinearMap) (fun y ↦ (D y).toLinearMap)
      (fun y ↦ Complex.exp (Complex.I * (Ψ (y 0) s (spatialPart y) η : ℂ)) •
        (fun i ↦ b (y 0) s (spatialPart y) η i j)) x =
      Complex.exp (Complex.I * (Ψ (x 0) s (spatialPart x) η : ℂ)) •
        (fun i ↦ r (x 0) s (spatialPart x) η i j)) :
    firstOrderApply (fun y j ↦ (C y j).toLinearMap) (fun y ↦ (D y).toLinearMap)
      (fun y ↦ χout y • ∫ s in a..y 0,
        cutFixedTimeFourier Ψ b β θ v (y 0) s (spatialPart y)) x =
      (∑ j, partialDeriv χout x j • C x j
        (∫ s in a..x 0, cutFixedTimeFourier Ψ b β θ v (x 0) s (spatialPart x))) +
      χout x • (C x 0 (cutFixedTimeFourier Ψ b β θ v (x 0) (x 0) (spatialPart x)) +
        ∫ s in a..x 0,
          cutFixedTimeFourier Ψ r β θ v (x 0) s (spatialPart x)) := by
  rw [firstOrderApply_masked_retarded_cutFixedTimeFourier
    Ψ b β θ χout v hΨ hb hβ hθ hθcs C D a x hout]
  congr 3
  apply intervalIntegral.integral_congr
  intro s _
  exact firstOrderApply_cutFixedTimeFourier_of_column_cancellation
    Ψ b r β θ v hΨ hb hβ hθ hθcs C D s x (hcancel s)

end JanetCartan.CharacteristicTransport.KernelDifferentiation
