module

public import JanetCartan.Analysis.Fourier.Periodic.LocalL2.Transfer

/-!
# Transfer of compact outputs with unchanged input measure

For the carrier channel in `app:ch_background:eq:bg-T` only the output variable
passes to the torus. The domain and its initial-variable Lebesgue measure are
left literal. This is distinct from two-sided Euclidean PDO transport.
-/

@[expose] public noncomputable section
open MeasureTheory
open JanetCartan.AmplitudeBound

namespace JanetCartan.PeriodicLocalL2
variable {n : ℕ} {𝕜 H F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup H] [NormedAddCommGroup F]

section Normed
variable [NormedSpace 𝕜 H] [NormedSpace 𝕜 F]

/-- Pass only the output of a physical channel to the torus, keeping its
original input space (`app:ch_background:eq:bg-T`). -/
def transferOutputOperator (A : H →L[𝕜] EuclideanL2 n F) : H →L[𝕜] PeriodicL2 n F :=
  toTorus ∘L A

/-- Output transfer preserves the original boundedness constant
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem norm_transferOutputOperator_le (A : H →L[𝕜] EuclideanL2 n F) :
    ‖transferOutputOperator A‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro f
  exact (norm_toTorusFun_le (A f)).trans (A.le_opNorm f)

/-- A supported output keeps its exact norm (`app:ch_background:eq:bg-T`). -/
theorem norm_transferOutputOperator_apply (A : H →L[𝕜] EuclideanL2 n F)
    (hA : ∀ f, ∀ᵐ x ∂volume, x ∉ halfOpenCell n → A f x = 0) (f : H) :
    ‖transferOutputOperator A f‖ = ‖A f‖ := norm_toTorus_of_supported (𝕜 := 𝕜) _ (hA f)

end Normed

section Kernel
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
variable [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [NormedSpace ℝ F]
variable {μ : Measure X}

/-- The original initial-variable measure is unchanged in the literal carrier
kernel formula (`app:ch_background:eq:bg-T`). -/
theorem transferOutputOperator_kernel
    (A : Lp E 2 μ →L[𝕜] EuclideanL2 n F)
    (k : EuclideanSpace ℝ (Fin n) → X → E →L[𝕜] F)
    (hA : ∀ f, A f =ᵐ[volume] fun x ↦ ∫ y, k x y (f y) ∂μ) (f : Lp E 2 μ) :
    transferOutputOperator A f =ᵐ[volume] fun z ↦
      ∫ y, k (centeredTorusRepresentative z) y (f y) ∂μ :=
  (toTorus_coe (𝕜 := 𝕜) (A f)).trans
    (measurePreserving_representative.quasiMeasurePreserving.ae_eq_comp (hA f).restrict)

end Kernel

section Inner
variable [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 F] [CompleteSpace H] [CompleteSpace F]

/-- The carrier adjoint receives the Euclidean chart lift, while returning
data in the original input space (`app:ch_background:eq:bg-T`). -/
theorem transferOutputOperator_adjoint (A : H →L[𝕜] EuclideanL2 n F) :
    (transferOutputOperator A).adjoint = A.adjoint ∘L toEuclidean.toContinuousLinearMap := by
  simp only [transferOutputOperator, ContinuousLinearMap.adjoint_comp, toTorus_adjoint]

/-- The full carrier normal is the two-sided transport of the Euclidean normal
(`app:ch_background:prop:bg-frame`, Step 1), with the original input Hilbert
space unchanged. -/
theorem transferOutputOperator_normal (A : H →L[𝕜] EuclideanL2 n F) :
    transferOutputOperator A ∘L (transferOutputOperator A).adjoint =
      transferOperator (A ∘L A.adjoint) := by
  rw [transferOutputOperator_adjoint]
  simp only [transferOutputOperator, transferOperator, ContinuousLinearMap.comp_assoc]

end Inner
end JanetCartan.PeriodicLocalL2
