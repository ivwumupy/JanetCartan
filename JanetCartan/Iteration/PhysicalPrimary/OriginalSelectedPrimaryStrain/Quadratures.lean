module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalPrimaryStrainMaskData

/-!
# The two original primary strain source quadratures

The actual primary is complex before its final real sampling. Both stress
quadratures must use the same frequency, cutoffs and inverse. The imaginary
quadrature rotates only the full raw derivative amplitude by `-I`; neither
the carrier nor the source cutoff is doubled (`main:eq:primary-strain`,
`app:ch_regular:eq:source-tail`). These lemmas feed the actual source-family
first-mask and negative-moment applications.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

open Set MeasureTheory Filter
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain

open CorrectedAtoms PrimarySourceAdmission PhysicalPairs.SampledMask ResponseSourceExtension
open LocalSobolev SmallSupport

/-- The original real and imaginary quadratures use unit complex scalars. -/
def quadratureScalar (imaginary : Bool) : ℂ := if imaginary then -Complex.I else 1

theorem norm_quadratureScalar (imaginary : Bool) : ‖quadratureScalar imaginary‖ = 1 := by
  cases imaginary <;> simp [quadratureScalar]

/-- Both real tensor sources remain in the same compact source class. -/
theorem quadrature_admitted {n : ℕ} {S : Set (Euclidean n)}
    (H : Euclidean n → Matrix (Fin n) (Fin n) ℂ)
    (hre : tensorFieldRealPart H ∈ compactSmoothSources S)
    (him : tensorFieldImagPart H ∈ compactSmoothSources S) (imaginary : Bool) :
    tensorFieldRealPart (quadratureScalar imaginary • H) ∈ compactSmoothSources S := by
  cases imaginary with
  | false => simpa only [quadratureScalar, Bool.false_eq_true, ite_false, one_smul] using hre
  | true =>
    have he : tensorFieldRealPart ((-Complex.I) • H) = tensorFieldImagPart H := by
      ext x i j
      change (-Complex.I * H x i j).re = (H x i j).im
      simp
    simpa only [quadratureScalar, ite_true, he] using him

/-- Rotating a raw amplitude does not change any physical derivative budget. -/
theorem quadrature_profile {n N : ℕ} {U : Set (Euclidean n)} (hU : IsOpen U)
    (A : Euclidean n → Matrix (Fin N) (Fin n) ℂ) (C : ℕ → ℝ) (R : ℝ)
    (hA : ContDiffOn ℝ ∞ A U)
    (hjets : ∀ q x, x ∈ U → ‖iteratedFDeriv ℝ q A x‖ ≤ C q * R ^ q)
    (imaginary : Bool) :
    ContDiffOn ℝ ∞ (quadratureScalar imaginary • A) U ∧
      ∀ q x, x ∈ U →
        ‖iteratedFDeriv ℝ q (quadratureScalar imaginary • A) x‖ ≤ C q * R ^ q := by
  refine ⟨hA.const_smul (quadratureScalar imaginary), ?_⟩
  intro q x hx
  have hAt : ContDiffAt ℝ q A x :=
    (hA.contDiffAt (hU.mem_nhds hx)).of_le (by simp)
  rw [iteratedFDeriv_const_smul_apply hAt, norm_smul, norm_quadratureScalar, one_mul]
  exact hjets q x hx

/-- The actual local source inherits the support of its global reduced-wave
representative, without applying the source cutoff again. -/
theorem local_source_support_of_reduced_wave {d N : ℕ}
    {W : Set (Euclidean (d+1))} (hW : MeasurableSet W)
    (u : LocalL2 W (Euclidean (d+1)))
    (χ ψ φ : Euclidean (d+1) → ℝ)
    (Q : Euclidean (d+1) → Fin (d+1) → MetricTensor (d+1))
    (A B : Euclidean (d+1) → Matrix (Fin N) (Fin (d+1)) ℂ) (ρ : ℝ)
    (he : zeroExtend hW u =ᵐ[volume] fun y ↦
      euclideanRealPart (reduced_wave χ ψ Q A B false φ ρ y)) :
    ∀ᵐ y ∂volume.restrict W, y ∉ tsupport χ → u y = 0 := by
  filter_upwards [ae_restrict_of_ae he, ae_restrict_of_ae (zeroExtend_coeFn hW u),
    ae_restrict_mem hW] with y hy hext hyW
  intro hyχ
  have hz : χ y = 0 := image_eq_zero_of_notMem_tsupport hyχ
  have hval := (hext.trans (indicator_of_mem hyW u)).symm.trans hy
  simpa only [reduced_wave, ResponseTransfer.SourceNegative.modulatedSource,
    hz, zero_smul, map_zero] using hval

/-- The canonical tensor input is supported before any inverse or additional
measurement acts. Its already-present tensor cutoff is sufficient. -/
theorem cutoff_stress_input_support {n : ℕ} {S W : Set (Euclidean n)}
    (Q : Euclidean n → Fin n → MetricTensor n) (η : Euclidean n → ℝ)
    (t : compactSmoothSources S) (u : LocalL2 W (Euclidean n))
    (hu : u =ᵐ[volume.restrict W] euclideanCutoffStressSource Q η t) :
    ∀ᵐ y ∂volume.restrict W, y ∉ S → u y = 0 := by
  filter_upwards [hu] with y hy
  intro hyS
  rw [hy]
  apply image_eq_zero_of_notMem_tsupport
  intro hys
  exact hyS (t.property.2.2 (tsupport_euclideanCutoffStressSource_subset Q η t hys))

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain
end
