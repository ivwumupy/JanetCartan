module

public import JanetCartan.Analysis.Fourier.Periodic.LocalL2.Operators

/-!
# Literal inverse and adjoint identities in the physical cell

The cell maps for `app:ch_background:defn:bg-row` are adjoints. Their Euclidean
composition is multiplication by the cell indicator, so norm preservation in
the Euclidean-to-torus direction requires the stated support hypothesis.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open JanetCartan.AmplitudeBound

namespace JanetCartan.PeriodicLocalL2

variable {n : ℕ} {𝕜 F : Type*} [RCLike 𝕜] [NormedAddCommGroup F]

section Normed
variable [NormedSpace 𝕜 F]

/-- Restriction after extension is the identity (`app:ch_background:defn:bg-row`). -/
theorem toTorus_toEuclidean (f : PeriodicL2 n F) :
    toTorus (𝕜 := 𝕜) (toEuclidean (𝕜 := 𝕜) f) = f := by
  apply Lp.ext
  filter_upwards [toTorus_coe (𝕜 := 𝕜) (toEuclidean (𝕜 := 𝕜) f),
    measurePreserving_representative.quasiMeasurePreserving.ae_eq_comp
      (toEuclidean_coe (𝕜 := 𝕜) f).restrict] with z h₁ h₂
  exact h₁.trans (h₂.trans (by
    simp only [Function.comp_apply, indicator_of_mem (representative_mem_halfOpenCell z),
      periodicLift, torusQuotient_centeredTorusRepresentative]))

/-- Extension after restriction is the cell indicator on representatives
(`app:ch_background:defn:bg-row`). -/
theorem toEuclidean_toTorus_coe (f : EuclideanL2 n F) :
    toEuclidean (𝕜 := 𝕜) (toTorus (𝕜 := 𝕜) f) =ᵐ[volume] (halfOpenCell n).indicator f := by
  have hf := (ae_restrict_iff' measurableSet_halfOpenCell).mp
    (measurePreserving_quotient.quasiMeasurePreserving.ae_eq_comp (toTorus_coe (𝕜 := 𝕜) f))
  filter_upwards [toEuclidean_coe (𝕜 := 𝕜) (toTorus (𝕜 := 𝕜) f), hf] with x hx hfx
  rw [hx]
  by_cases h : x ∈ halfOpenCell n
  · simp only [indicator_of_mem h, periodicLift, Function.comp_apply]
    simpa only [Function.comp_apply, centeredTorusRepresentative_quotient h] using hfx h
  · simp only [indicator_of_notMem h]

/-- On cell-supported Euclidean data, restriction and extension are inverse
(`app:ch_background:defn:bg-row`). -/
theorem toEuclidean_toTorus (f : EuclideanL2 n F)
    (hf : ∀ᵐ x ∂volume, x ∉ halfOpenCell n → f x = 0) :
    toEuclidean (𝕜 := 𝕜) (toTorus (𝕜 := 𝕜) f) = f := by
  apply Lp.ext
  filter_upwards [toEuclidean_toTorus_coe (𝕜 := 𝕜) f, hf] with x hx hfx
  rw [hx]
  by_cases h : x ∈ halfOpenCell n
  · exact indicator_of_mem h _
  · simp only [indicator_of_notMem h, hfx h]

/-- Exact norm preservation for cell-supported physical data
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem norm_toTorus_of_supported (f : EuclideanL2 n F)
    (hf : ∀ᵐ x ∂volume, x ∉ halfOpenCell n → f x = 0) :
    ‖toTorus (𝕜 := 𝕜) f‖ = ‖f‖ := by
  rw [← (toEuclidean (𝕜 := 𝕜)).norm_map, toEuclidean_toTorus f hf]

end Normed

section Inner
variable [InnerProductSpace 𝕜 F]

/-- The literal integral pairing of restriction and zero extension
(`app:ch_background:defn:bg-row`), valid over both real and complex scalars. -/
theorem inner_toTorus (f : EuclideanL2 n F) (g : PeriodicL2 n F) :
    inner 𝕜 (toTorus (𝕜 := 𝕜) f) g = inner 𝕜 f (toEuclidean (𝕜 := 𝕜) g) := by
  rw [L2.inner_def, L2.inner_def]
  calc
    (∫ z, inner 𝕜 (toTorus (𝕜 := 𝕜) f z) (g z)) =
        ∫ z, inner 𝕜 (f (centeredTorusRepresentative z)) (g z) := by
      apply integral_congr_ae
      filter_upwards [toTorus_coe (𝕜 := 𝕜) f] with z hz
      rw [hz, Function.comp_apply]
    _ = ∫ x in halfOpenCell n, inner 𝕜 (f x) (periodicLift g x) := by
      rw [← integral_representative]
      simp only [periodicLift, Function.comp_apply, torusQuotient_centeredTorusRepresentative]
    _ = ∫ x, inner 𝕜 (f x) ((halfOpenCell n).indicator (periodicLift g) x) := by
      rw [← integral_indicator measurableSet_halfOpenCell]
      congr 1
      funext x
      by_cases hx : x ∈ halfOpenCell n <;> simp [hx]
    _ = ∫ x, inner 𝕜 (f x) (toEuclidean (𝕜 := 𝕜) g x) := by
      apply integral_congr_ae
      filter_upwards [toEuclidean_coe (𝕜 := 𝕜) g] with x hx
      rw [hx]

variable [CompleteSpace F]

/-- Restriction is the Hilbert adjoint of the literal zero extension
(`app:ch_background:defn:bg-row`). -/
theorem toEuclidean_adjoint :
    (toEuclidean (n := n) (𝕜 := 𝕜) (F := F)).toContinuousLinearMap.adjoint = toTorus :=
  ((ContinuousLinearMap.eq_adjoint_iff _ _).mpr inner_toTorus).symm

/-- The adjoint of restriction is the literal zero extension
(`app:ch_background:defn:bg-row`). -/
theorem toTorus_adjoint :
    (toTorus (n := n) (𝕜 := 𝕜) (F := F)).adjoint = toEuclidean.toContinuousLinearMap := by
  rw [← toEuclidean_adjoint, ContinuousLinearMap.adjoint_adjoint]

end Inner
end JanetCartan.PeriodicLocalL2
