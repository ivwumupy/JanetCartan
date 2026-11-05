module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Reconstruction.GradedBounds.Expansion

/-!
# Product rule for the physical reconstruction derivative

The coefficient formula is differentiated before applying the observation
cutoff, as required in `app:ch_response:eq:response-graded-derivative`.
Coefficient differentiability is required only at the observation point.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.ResponseTransfer
variable {n N : ℕ}
local notation "E" => Euclidean n

private theorem fderiv_sum_products {J : Type*} [Fintype J]
    (c u : J → E → ℂ) {x : E}
    (hc : ∀ j, DifferentiableAt ℝ (c j) x) (hu : ∀ j, DifferentiableAt ℝ (u j) x)
    (v : E) :
    fderiv ℝ (fun y ↦ ∑ j, c j y * u j y) x v =
      ∑ j, (fderiv ℝ (c j) x v * u j x + c j x * fderiv ℝ (u j) x v) := by
  rw [fderiv_fun_sum (u := Finset.univ) (A := fun j y ↦ c j y * u j y)
    (fun j _ ↦ (hc j).mul (hu j))]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [show (fun y ↦ c j y * u j y) = c j * u j from rfl, fderiv_mul (hc j) (hu j)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- Ordinary derivative of the explicit reconstruction amplitude. Every
coefficient and source-cutoff derivative is retained, as required by
`app:ch_response:eq:response-reconstruction-grading`. The additional physical
carrier term is supplied separately in the demodulated derivative theorem. -/
def reconstructionAmplitudeDifferential (F : E → Euclidean N) (ρ : ℝ)
    (φ χ : E → ℝ) (g : E → EuclideanSpace ℂ (Fin n))
    (a : E → Matrix (Fin n) (Fin n) ℂ) (x v : E) (k : Fin N) : ℂ :=
  (∑ j, (fderiv ℝ (reconstructionValueEntry F k j) x v * g x j +
    reconstructionValueEntry F k j x * fderiv ℝ (fun y ↦ g y j) x v)) +
  (∑ ij : Fin n × Fin n,
    (fderiv ℝ (reconstructionDerivativeEntry F k ij) x v *
      waveFirstAmplitude ρ φ (fun y ↦ g y ij.2) x (EuclideanSpace.single ij.1 1) +
    reconstructionDerivativeEntry F k ij x *
      ((Complex.I * (ρ : ℂ)) *
        (((fderiv ℝ (fun y ↦ partialDeriv φ y ij.1) x v : ℝ) : ℂ) * g x ij.2 +
          ((partialDeriv φ x ij.1 : ℝ) : ℂ) * fderiv ℝ (fun y ↦ g y ij.2) x v) +
        fderiv ℝ (fun y ↦ partialDeriv (fun z ↦ g z ij.2) y ij.1) x v))) +
  ∑ ij : Fin n × Fin n,
    ((((fderiv ℝ χ x v : ℝ) : ℂ) * reconstructionSourceEntry F k ij x +
        (χ x : ℂ) * fderiv ℝ (reconstructionSourceEntry F k ij) x v) * a x ij.1 ij.2 +
      ((χ x : ℂ) * reconstructionSourceEntry F k ij x) *
        fderiv ℝ (fun y ↦ a y ij.1 ij.2) x v)

/-- The literal amplitude has the stated product derivative, derived from
primitive coefficient regularity. This discharges amplitude differentiability
in the physical identity for `app:ch_response:eq:response-graded-derivative`;
no ambient regularity or bound is assumed. -/
theorem reconstructionAmplitude_coordinate_differential (F : E → Euclidean N)
    (ρ : ℝ) {φ χ : E → ℝ} {g : E → EuclideanSpace ℂ (Fin n)}
    (a : E → Matrix (Fin n) (Fin n) ℂ) {x : E}
    (hφ : ContDiff ℝ 2 φ) (hg : ContDiff ℝ 2 g)
    (hχ : DifferentiableAt ℝ χ x)
    (ha : ∀ i j, DifferentiableAt ℝ (fun y ↦ a y i j) x)
    (k : Fin N)
    (hV : ∀ j, DifferentiableAt ℝ (reconstructionValueEntry F k j) x)
    (hD : ∀ ij, DifferentiableAt ℝ (reconstructionDerivativeEntry F k ij) x)
    (hS : ∀ ij, DifferentiableAt ℝ (reconstructionSourceEntry F k ij) x) :
    DifferentiableAt ℝ (fun y ↦ reconstructionAmplitude F ρ φ χ g a y k) x ∧
      ∀ v, fderiv ℝ (fun y ↦ reconstructionAmplitude F ρ φ χ g a y k) x v =
        reconstructionAmplitudeDifferential F ρ φ χ g a x v k := by
  have hgj (j : Fin n) := (contDiff_piLp 2).mp hg j
  have hgjd (j : Fin n) := (hgj j).differentiable (by norm_num) x
  have hχc : DifferentiableAt ℝ (fun y ↦ (χ y : ℂ)) x :=
    Complex.ofRealCLM.differentiableAt.comp x hχ
  have hW (ij : Fin n × Fin n) :=
    differentiable_waveFirstAmplitude (lam := ρ) hφ (hgj ij.2)
      (EuclideanSpace.single ij.1 1) x
  have hχS (ij : Fin n × Fin n) := hχc.mul (hS ij)
  have hVS := DifferentiableAt.fun_sum (fun j (_ : j ∈ Finset.univ) ↦ (hV j).mul (hgjd j))
  have hDS := DifferentiableAt.fun_sum (fun ij (_ : ij ∈ Finset.univ) ↦ (hD ij).mul (hW ij))
  have hSS := DifferentiableAt.fun_sum
    (fun ij (_ : ij ∈ Finset.univ) ↦ (hχS ij).mul (ha ij.1 ij.2))
  have he : (fun y ↦ reconstructionAmplitude F ρ φ χ g a y k) =
      fun y ↦ (∑ j, reconstructionValueEntry F k j y * g y j) +
        (∑ ij : Fin n × Fin n, reconstructionDerivativeEntry F k ij y *
          waveFirstAmplitude ρ φ (fun z ↦ g z ij.2) y (EuclideanSpace.single ij.1 1)) +
        ∑ ij : Fin n × Fin n,
          ((χ y : ℂ) * reconstructionSourceEntry F k ij y) * a y ij.1 ij.2 := by
    funext y
    simpa only [waveFirstAmplitude, smul_eq_mul, partialDeriv] using
      reconstructionAmplitude_coordinate F ρ φ χ g a y k
  rw [he]
  refine ⟨(hVS.add hDS).add hSS, fun v ↦ ?_⟩
  simp only [Pi.mul_apply] at hVS hDS hSS
  erw [fderiv_fun_add (hVS.add hDS) hSS, fderiv_fun_add hVS hDS]
  simp only [add_apply]
  erw [fderiv_sum_products _ _ hV hgjd, fderiv_sum_products _ _ hD hW,
    fderiv_sum_products _ _ hχS (fun ij ↦ ha ij.1 ij.2)]
  unfold reconstructionAmplitudeDifferential
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro ij _
    rw [fderiv_waveFirstAmplitude hφ (hgj ij.2)]
    rfl
  · apply Finset.sum_congr rfl
    intro ij _
    have hd := (hχc.hasFDerivAt.mul (hS ij).hasFDerivAt).fderiv
    rw [hd]
    have hχder := (Complex.ofRealCLM.hasFDerivAt.comp x hχ.hasFDerivAt).fderiv
    erw [hχder]
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, smul_eq_mul, Pi.mul_apply]
    ring

/-- The demodulated physical derivative of the same completed variation,
with its full product expansion and the observation cutoff outside the
derivative (`app:ch_response:eq:response-graded-derivative`). -/
theorem demodulated_physicalDerivative_coordinate_expansion (F : E → Euclidean N)
    (ρ : ℝ) {φ χ : E → ℝ} (ψ : E → ℝ)
    {g : E → EuclideanSpace ℂ (Fin n)} (a : E → Matrix (Fin n) (Fin n) ℂ)
    {x : E} (hφ : ContDiff ℝ 2 φ) (hg : ContDiff ℝ 2 g)
    (hχ : DifferentiableAt ℝ χ x)
    (ha : ∀ i j, DifferentiableAt ℝ (fun y ↦ a y i j) x)
    (hV : ∀ k j, DifferentiableAt ℝ (reconstructionValueEntry F k j) x)
    (hD : ∀ k ij, DifferentiableAt ℝ (reconstructionDerivativeEntry F k ij) x)
    (hS : ∀ k ij, DifferentiableAt ℝ (reconstructionSourceEntry F k ij) x)
    (v : E) (k : Fin N) :
    (waveCarrier (-ρ) φ x • ((ψ x : ℂ) •
      fderiv ℝ (completedVariationComplex F (modulatedWave ρ φ g)
        (fun y ↦ waveCarrier ρ φ y • ((χ y : ℂ) • a y))) x v)) k =
      (ψ x : ℂ) *
        (Complex.I * (ρ : ℂ) * ((fderiv ℝ φ x v : ℝ) : ℂ) *
          reconstructionAmplitude F ρ φ χ g a x k +
          reconstructionAmplitudeDifferential F ρ φ χ g a x v k) := by
  have hc := fun k ↦ reconstructionAmplitude_coordinate_differential F ρ a
    hφ hg hχ ha k (hV k) (hD k) (hS k)
  have hB : DifferentiableAt ℝ (reconstructionAmplitude F ρ φ χ g a) x :=
    (differentiableAt_piLp 2).mpr (fun k ↦ (hc k).1)
  rw [demodulated_physicalDerivative_completedVariationComplex F χ ψ a
    (hφ.differentiable (by norm_num)) (hg.differentiable (by norm_num)) x v hB]
  have hp := ((PiLp.proj 2 (fun _ : Fin N ↦ ℂ) k :
    EuclideanSpace ℂ (Fin N) →L[ℝ] ℂ).hasFDerivAt.comp x hB.hasFDerivAt).fderiv
  have he : fderiv ℝ (fun y ↦ reconstructionAmplitude F ρ φ χ g a y k) x v =
      (fderiv ℝ (reconstructionAmplitude F ρ φ χ g a) x v) k :=
    congrArg (fun T : E →L[ℝ] ℂ ↦ T v) hp
  simp only [PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
  rw [← he, (hc k).2 v]

end JanetCartan.ResponseTransfer
