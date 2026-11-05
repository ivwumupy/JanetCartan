module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Quadratures

/-! # Zero extension of the same admitted primary input

The input to the original uncut inverse is already supported on the tensor
cutoff. Its local representative therefore supplies the whole-space source
required by `SampledMask.first_mask`, without applying another cutoff.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

open Set MeasureTheory Filter
open scoped Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceData

open LocalSobolev SmallSupport CorrectedAtoms PrimarySourceAdmission
open ResponseSourceExtension

/-- Globalize the actual local tensor-source representative across its
original support inclusion (`app:ch_regular:eq:exact-physical`). -/
theorem zeroExtend_tensor_input_of_ae {n : ℕ} {S W : Set (Euclidean n)}
    (Q : Euclidean n → Fin n → MetricTensor n) (η : Euclidean n → ℝ)
    (t : compactSmoothSources S) (u : LocalL2 W (Euclidean n))
    (hW : MeasurableSet W) (hSW : S ⊆ W)
    (hu : u =ᵐ[volume.restrict W] euclideanCutoffStressSource Q η t) :
    zeroExtend hW u =ᵐ[volume] euclideanCutoffStressSource Q η t := by
  apply (zeroExtend_coeFn hW u).trans
  apply ((ae_eq_restrict_iff_indicator_ae_eq hW).mp hu).trans
  apply Eventually.of_forall
  intro x
  by_cases hx : x ∈ W
  · exact indicator_of_mem hx _
  · rw [indicator_of_notMem hx]
    exact (image_eq_zero_of_notMem_tsupport (fun hs ↦ hx
      (hSW (t.property.2.2 (tsupport_euclideanCutoffStressSource_subset Q η t hs))))).symm

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceData
end
