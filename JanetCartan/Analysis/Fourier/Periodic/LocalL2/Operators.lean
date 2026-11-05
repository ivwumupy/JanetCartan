module

public import JanetCartan.Analysis.Fourier.Periodic.LocalL2.Measure
public import JanetCartan.Analysis.Fourier.Periodic.SobolevScale.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# L² restriction and extension in the unit cell

The maps used by `app:ch_background:defn:bg-row` and Step 1 of
`app:ch_background:prop:bg-frame`. All Euclidean spaces carry Lebesgue measure.
The lift is zero outside the chosen cell; the unrestricted periodic lift is
not asserted to belong to Euclidean L².
-/

@[expose] public noncomputable section

open MeasureTheory Set
open JanetCartan.AmplitudeBound

namespace JanetCartan.PeriodicLocalL2

variable {n : ℕ} {𝕜 F : Type*} [RCLike 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Euclidean Lebesgue L² for the physical chart of `app:ch_background:defn:bg-row`. -/
abbrev EuclideanL2 (n : ℕ) (F : Type*) [NormedAddCommGroup F] :=
  Lp F 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))

/-- Cell restriction preserves square integrability (`app:ch_background:defn:bg-row`). -/
theorem memLp_representative (f : EuclideanL2 n F) :
    MemLp (f ∘ centeredTorusRepresentative) 2 (volume : Measure (Torus n)) :=
  ((Lp.memLp f).restrict (halfOpenCell n)).comp_measurePreserving
    measurePreserving_representative

/-- Zero extension of a cell lift is square integrable (`app:ch_background:defn:bg-row`). -/
theorem memLp_cellLift (f : PeriodicL2 n F) :
    MemLp ((halfOpenCell n).indicator (periodicLift f)) 2 volume :=
  (memLp_indicator_iff_restrict measurableSet_halfOpenCell.nullMeasurableSet).mpr
    ((Lp.memLp f).comp_measurePreserving measurePreserving_quotient)

/-- Restrict Euclidean data to the cell and pass to the torus
(`app:ch_background:defn:bg-row`). -/
def toTorusFun (f : EuclideanL2 n F) : PeriodicL2 n F :=
  (memLp_representative f).toLp _

/-- Lift torus data on the cell and extend by zero on its complement
(`app:ch_background:defn:bg-row`). -/
def toEuclideanFun (f : PeriodicL2 n F) : EuclideanL2 n F :=
  (memLp_cellLift f).toLp _

/-- The restriction map has its literal representative formula
(`app:ch_background:defn:bg-row`). -/
theorem toTorusFun_coe (f : EuclideanL2 n F) :
    toTorusFun f =ᵐ[volume] f ∘ centeredTorusRepresentative :=
  (memLp_representative f).coeFn_toLp

/-- The lift vanishes outside one cell (`app:ch_background:defn:bg-row`). -/
theorem toEuclideanFun_coe (f : PeriodicL2 n F) :
    toEuclideanFun f =ᵐ[volume] (halfOpenCell n).indicator (periodicLift f) :=
  (memLp_cellLift f).coeFn_toLp

/-- Restriction has operator norm at most one (`app:ch_background:prop:bg-frame`). -/
theorem norm_toTorusFun_le (f : EuclideanL2 n F) : ‖toTorusFun f‖ ≤ ‖f‖ := by
  rw [toTorusFun, Lp.norm_toLp, Lp.norm_def,
    eLpNorm_comp_measurePreserving ((Lp.memLp f).restrict _).aestronglyMeasurable
      measurePreserving_representative]
  exact ENNReal.toReal_mono (Lp.memLp f).eLpNorm_ne_top
    (eLpNorm_mono_measure _ Measure.restrict_le_self)

/-- Zero extension preserves the exact norm, without a measure factor
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem norm_toEuclideanFun (f : PeriodicL2 n F) : ‖toEuclideanFun f‖ = ‖f‖ := by
  rw [toEuclideanFun, Lp.norm_toLp,
    eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_halfOpenCell.nullMeasurableSet]
  change (eLpNorm (f ∘ torusQuotient) 2 (volume.restrict (halfOpenCell n))).toReal = _
  rw [eLpNorm_comp_measurePreserving (Lp.memLp f).aestronglyMeasurable
    measurePreserving_quotient, Lp.norm_def]

/-- The bounded cell restriction map (`app:ch_background:defn:bg-row`). -/
def toTorus : EuclideanL2 n F →L[𝕜] PeriodicL2 n F :=
  LinearMap.mkContinuous
    { toFun := toTorusFun
      map_add' := fun f g ↦ by
        apply Lp.ext
        filter_upwards [toTorusFun_coe (f + g), toTorusFun_coe f, toTorusFun_coe g,
          Lp.coeFn_add (toTorusFun f) (toTorusFun g),
          measurePreserving_representative.quasiMeasurePreserving.ae_eq_comp
            (Lp.coeFn_add f g).restrict] with z h h₁ h₂ h₃ h₄
        exact h.trans (h₄.trans (h₃.trans (congrArg₂ (· + ·) h₁ h₂)).symm)
      map_smul' := fun c f ↦ by
        apply Lp.ext
        filter_upwards [toTorusFun_coe (c • f), toTorusFun_coe f,
          Lp.coeFn_smul c (toTorusFun f),
          measurePreserving_representative.quasiMeasurePreserving.ae_eq_comp
            (Lp.coeFn_smul c f).restrict] with z h h₁ h₂ h₃
        exact h.trans (h₃.trans (h₂.trans (congrArg (c • ·) h₁)).symm) }
    1 (fun f ↦ by simpa using norm_toTorusFun_le f)

/-- The linear isometric zero extension of cell lifts
(`app:ch_background:defn:bg-row`). -/
def toEuclidean : PeriodicL2 n F →ₗᵢ[𝕜] EuclideanL2 n F where
  toFun := toEuclideanFun
  map_add' f g := by
    apply Lp.ext
    have hfg := (ae_restrict_iff' measurableSet_halfOpenCell).mp
      (measurePreserving_quotient.quasiMeasurePreserving.ae_eq_comp (Lp.coeFn_add f g))
    filter_upwards [toEuclideanFun_coe (f + g), toEuclideanFun_coe f,
      toEuclideanFun_coe g, Lp.coeFn_add (toEuclideanFun f) (toEuclideanFun g), hfg]
      with x h h₁ h₂ h₃ h₄
    simp only [h, h₃, Pi.add_apply, h₁, h₂]
    by_cases hx : x ∈ halfOpenCell n
    · simpa only [indicator_of_mem hx, periodicLift, Function.comp_apply, Pi.add_apply]
        using h₄ hx
    · simp only [indicator_of_notMem hx, add_zero]
  map_smul' c f := by
    apply Lp.ext
    have hcf := (ae_restrict_iff' measurableSet_halfOpenCell).mp
      (measurePreserving_quotient.quasiMeasurePreserving.ae_eq_comp (Lp.coeFn_smul c f))
    filter_upwards [toEuclideanFun_coe (c • f), toEuclideanFun_coe f,
      Lp.coeFn_smul c (toEuclideanFun f), hcf] with x h h₁ h₂ h₃
    simp only [RingHom.id_apply, h, h₂, Pi.smul_apply, h₁]
    by_cases hx : x ∈ halfOpenCell n
    · simpa only [indicator_of_mem hx, periodicLift, Function.comp_apply, Pi.smul_apply]
        using h₃ hx
    · simp only [indicator_of_notMem hx, smul_zero]
  norm_map' := norm_toEuclideanFun

/-- Literal representative formula for the bounded restriction
(`app:ch_background:defn:bg-row`). -/
theorem toTorus_coe (f : EuclideanL2 n F) :
    toTorus (𝕜 := 𝕜) f =ᵐ[volume] f ∘ centeredTorusRepresentative := toTorusFun_coe f

/-- Literal representative formula for zero extension
(`app:ch_background:defn:bg-row`). -/
theorem toEuclidean_coe (f : PeriodicL2 n F) :
    toEuclidean (𝕜 := 𝕜) f =ᵐ[volume] (halfOpenCell n).indicator (periodicLift f) :=
  toEuclideanFun_coe f

end JanetCartan.PeriodicLocalL2
