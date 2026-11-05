module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification.RetardedFourier

/-!
# Reversing the retarded time triangle

The compact adjoint kernel in `app:ch_regular_base:lem:retarded-kernel` requires
Fubini on the actual time triangle. The lower buffer is used before swapping
the two times; neither endpoint nor a physical mask is discarded.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification

variable {q d : ℕ}
local notation "V" => Fin q → ℂ

private theorem lower_triangle (a c t : ℝ) (ht : t ∈ Icc a c) (f : ℝ → V) :
    (∫ s in Icc a c, if s ≤ t then f s else 0) = ∫ s in a..t, f s := by
  change (∫ s in Icc a c, (Iic t).indicator f s) = _
  rw [integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
  have he : Iic t ∩ Icc a c = Icc a t := by
    ext s
    simp only [mem_inter_iff, mem_Iic, mem_Icc]
    constructor
    · tauto
    · exact fun h ↦ ⟨h.2, h.1, h.2.trans ht.2⟩
  rw [he, integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le ht.1]

private theorem upper_triangle (a c s : ℝ) (hs : s ∈ Icc a c) (f : ℝ → V) :
    (∫ t in Icc a c, if s ≤ t then f t else 0) = ∫ t in s..c, f t := by
  change (∫ t in Icc a c, (Ici s).indicator f t) = _
  rw [integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
  have he : Ici s ∩ Icc a c = Icc s c := by
    ext t
    simp only [mem_inter_iff, mem_Ici, mem_Icc]
    constructor
    · tauto
    · exact fun h ↦ ⟨h.1, hs.1.trans h.1, h.2⟩
  rw [he, integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hs.2]

/-- Vector-valued time-triangle Fubini for the actual compact reverse kernel.
Continuity on the finite time square supplies integrability; the triangular
indicator is not an assumed kernel identity. Consumer:
`integral_elapsed_space_eq_reverse_triangle`, for
`app:ch_regular_base:lem:retarded-kernel`. -/
theorem integral_retarded_triangle_swap (a c : ℝ) (f : ℝ → ℝ → V)
    (hf : Continuous (Function.uncurry f)) :
    (∫ t in Icc a c, ∫ s in a..t, f t s) =
      ∫ s in Icc a c, ∫ t in s..c, f t s := by
  have hi : Integrable (Function.uncurry f)
      ((volume.restrict (Icc a c)).prod (volume.restrict (Icc a c))) := by
    rw [Measure.prod_restrict]
    exact hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have ht := hi.indicator (measurableSet_le measurable_snd measurable_fst)
  calc
    _ = ∫ t in Icc a c, ∫ s in Icc a c, if s ≤ t then f t s else 0 := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro t ht
      exact (lower_triangle a c t ht (f t)).symm
    _ = ∫ s in Icc a c, ∫ t in Icc a c, if s ≤ t then f t s else 0 :=
      integral_integral_swap ht
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro s hs
      exact upper_triangle a c s hs (fun t ↦ f t s)

/-- Splitting physical spacetime in time-first order, with the same unit
Jacobian as `integral_eq_space_time`. Consumer: the reversed retarded triangle
in `app:ch_regular_base:lem:retarded-kernel`. -/
theorem integral_eq_time_space (f : Euclidean (d + 1) → V) (hf : Integrable f) :
    (∫ x, f x) = ∫ t : ℝ, ∫ y : Euclidean d, f (timeSpacePoint t y) := by
  have hp := measurePreserving_timeSpaceMeasurableEquiv (d := d)
  have hi := hp.symm.integrable_comp_of_integrable hf
  rw [← hp.symm.integral_comp' f]
  exact integral_prod _ hi

/-- The original fixed elapsed slab and compact physical integration become
the reversed time triangle. Its lower buffer is discharged using
`Basic.integral_fixed_slab_eq_retarded`. The compact spatial carrier is removed
again in the conclusion. Consumer: the literal adjoint spectral kernel of
`app:ch_regular_base:lem:retarded-kernel`. -/
theorem integral_elapsed_space_eq_reverse_triangle
    (F : ℝ → ℝ → Euclidean d → V)
    (hF : Continuous (fun p : (ℝ × ℝ) × Euclidean d ↦ F p.1.1 p.1.2 p.2))
    {Y : Set (Euclidean d)} (hY : IsCompact Y) (a c Δ : ℝ) (hcΔ : c - a ≤ Δ)
    (hs : ∀ t s y, t ∉ Icc a c ∨ y ∉ Y → F t s y = 0)
    (hz : ∀ t s y, s ≤ a → F t s y = 0) :
    (∫ r in Icc 0 Δ, ∫ x : Euclidean (d + 1), F (x 0) (x 0 - r) (spatialPart x)) =
      ∫ s in Icc a c, ∫ t in s..c, ∫ y, F t s y := by
  have hy (t s : ℝ) : (∫ y, F t s y) = ∫ y in Y, F t s y :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun y hy ↦ hs t s y (Or.inr hy))).symm
  let f : ℝ → ℝ → V := fun t s ↦ ∫ y in Y, F t s y
  have hf : Continuous (Function.uncurry f) :=
    continuous_parametric_integral_of_continuous hF hY
  have hzero (t s : ℝ) (hsa : s ≤ a) : f t s = 0 := by simp [f, hz t s _ hsa]
  have hsplit (r : ℝ) : (∫ x : Euclidean (d + 1), F (x 0) (x 0 - r) (spatialPart x)) =
      ∫ t in Icc a c, f t (t - r) := by
    have hcont : Continuous (fun x : Euclidean (d + 1) ↦
        F (x 0) (x 0 - r) (spatialPart x)) :=
      hF.comp (((show Continuous (fun x : Euclidean (d + 1) ↦ x 0) by fun_prop).prodMk
        (by fun_prop)).prodMk continuous_spatialPart)
    have hcompact : HasCompactSupport (fun x : Euclidean (d + 1) ↦
        F (x 0) (x 0 - r) (spatialPart x)) := by
      apply HasCompactSupport.intro
        ((isCompact_Icc.prod hY).image continuous_timeSpacePoint)
      intro x hx
      apply hs
      by_contra hn
      push Not at hn
      apply hx
      refine ⟨(x 0, spatialPart x), hn, ?_⟩
      exact timeSpaceMeasurableEquiv.symm_apply_apply x
    rw [integral_eq_time_space _ (hcont.integrable_of_hasCompactSupport hcompact)]
    simp only [timeSpacePoint_time, spatialPart_timeSpacePoint, hy]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero (fun t ht ↦ by
      simp [hs t _ _ (Or.inl ht)])).symm
  simp_rw [hsplit]
  have hcont : Continuous (fun p : ℝ × ℝ ↦ f p.2 (p.2 - p.1)) :=
    hf.comp (continuous_snd.prodMk (continuous_snd.sub continuous_fst))
  have hi : Integrable (fun p : ℝ × ℝ ↦ f p.2 (p.2 - p.1))
      ((volume.restrict (Icc 0 Δ)).prod (volume.restrict (Icc a c))) := by
    rw [Measure.prod_restrict]
    exact hcont.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  rw [integral_integral_swap hi]
  calc
    _ = ∫ t in Icc a c, ∫ s in a..t, f t s := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro t ht
      apply integral_fixed_slab_eq_retarded ht.1 (by linarith [ht.2]) (f t)
      · exact (hf.comp (continuous_const.prodMk (continuous_const.sub continuous_id))).intervalIntegrable 0 Δ
      · exact hzero t
    _ = ∫ s in Icc a c, ∫ t in s..c, f t s := integral_retarded_triangle_swap a c f hf
    _ = _ := by simp only [hy, f]

end JanetCartan.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
