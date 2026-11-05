module

public import JanetCartan.Analysis.Sobolev.Local.Basic
public import JanetCartan.Analysis.Extension.Mollification
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Passing smooth Sobolev bounds to weak restriction spaces

For `app:ch_regular:thm:exact-correction` and `app:not:fourier`, normalized
mollification passes a uniform smooth estimate to every actual weak extension.
Taking the infimum over those extensions then gives the restriction norm bound.
The smooth estimate is an explicit premise of these transfer lemmas; its
dimension-dependent proof belongs to the embedding theorem.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff Topology

namespace JanetCartan.LocalSobolev

variable {n : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {U : Set (EuclideanSpace ℝ (Fin n))} {p C : ℝ≥0}

/-- The smooth estimate in `app:ch_regular:thm:exact-correction` passes to
arbitrary weak H¹ extensions by L² mollification and lower semicontinuity.
Representative agreement on the local domain is used explicitly. -/
theorem SobolevExtension.eLpNorm_le_of_smooth_estimate
    (hsmooth : ∀ g : EuclideanSpace ℝ (Fin n) → F,
      ContDiff ℝ ∞ g → MemLp g 2 volume →
      MemLp (iteratedFDeriv ℝ 1 g) 2 volume →
      eLpNorm g p (volume.restrict U) ≤ C *
        (eLpNorm g 2 volume + eLpNorm (iteratedFDeriv ℝ 1 g) 2 volume))
    {u : LocalL2 U F} (e : SobolevExtension U 1 u) :
    eLpNorm u p (volume.restrict U) ≤ C *
      (eLpNorm e.toFun 2 volume + eLpNorm (e.jet 1) 2 volume) := by
  let φ : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) := fun k ↦
    ⟨(1 / ((k : ℝ) + 1)) / 2, 1 / ((k : ℝ) + 1), by positivity,
      half_lt_self (by positivity)⟩
  have hφ : Tendsto (fun k ↦ (φ k).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  let g := fun k ↦ Mollification.mollify volume (φ k) e.toFun
  have hg (k : ℕ) : ContDiff ℝ ∞ (g k) :=
    Mollification.contDiff_mollify volume _ (e.memLp_fun.locallyIntegrable (by norm_num))
  have h₀ (k : ℕ) : eLpNorm (g k) 2 volume ≤ eLpNorm e.toFun 2 volume :=
    Mollification.eLpNorm_mollify_le volume _ e.memLp_fun
  have h₁ (k : ℕ) : eLpNorm (iteratedFDeriv ℝ 1 (g k)) 2 volume ≤
      eLpNorm (e.jet 1) 2 volume :=
    e.weakJet.eLpNorm_iteratedFDeriv_mollify_le volume _ 1 le_rfl (e.memLp_jet 1 le_rfl)
  have hb (k : ℕ) : eLpNorm (g k) p (volume.restrict U) ≤ C *
      (eLpNorm e.toFun 2 volume + eLpNorm (e.jet 1) 2 volume) := by
    apply (hsmooth (g k) (hg k) ((h₀ k).trans_lt e.memLp_fun.eLpNorm_lt_top)
      ((h₁ k).trans_lt (e.memLp_jet 1 le_rfl).eLpNorm_lt_top)).trans
    gcongr
    · exact h₀ k
    · exact h₁ k
  have ht : Tendsto (fun k ↦ eLpNorm (g k - e.toFun) 2 (volume.restrict U))
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (Mollification.tendsto_eLpNorm_mollify_sub volume hφ e.memLp_fun)
      (fun _ ↦ bot_le)
    exact fun k ↦ eLpNorm_restrict_le (g k - e.toFun) 2 volume U
  rw [← eLpNorm_congr_ae e.restrict_eq]
  exact eLpNorm_le_of_tendstoInMeasure (Eventually.of_forall hb)
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0) ht)
    (fun k ↦ (hg k).continuous.aestronglyMeasurable)

omit [FiniteDimensional ℝ F] in
/-- The two L² terms in the H¹ extension estimate equal its auxiliary jet norm
(`app:not:fourier`). -/
theorem SobolevExtension.jetNorm_one {u : LocalL2 U F} (e : SobolevExtension U 1 u) :
    e.jetNorm = (eLpNorm e.toFun 2 volume).toReal +
      (eLpNorm (e.jet 1) 2 volume).toReal := by
  simp [SobolevExtension.jetNorm, Finset.sum_range_succ, e.eLpNorm_jet_zero]

omit [FiniteDimensional ℝ F] in
/-- An estimate valid for every actual extension descends to the infimum
restriction norm (`app:not:fourier`), with no chosen extension operator. -/
theorem memLp_and_norm_le_restrictionSobolevNorm_of_extension_estimate
    (hC : 0 < C)
    (hext : ∀ (u : LocalL2 U F) (e : SobolevExtension U 1 u),
      eLpNorm u p (volume.restrict U) ≤ C *
        (eLpNorm e.toFun 2 volume + eLpNorm (e.jet 1) 2 volume))
    {u : LocalL2 U F} (hu : MemRestrictionSobolev U 1 u) :
    MemLp u p (volume.restrict U) ∧
      (eLpNorm u p (volume.restrict U)).toReal ≤ (C : ℝ) * restrictionSobolevNorm U 1 u := by
  have hfin (e : SobolevExtension U 1 u) :
      C * (eLpNorm e.toFun 2 volume + eLpNorm (e.jet 1) 2 volume) ≠ ⊤ := by
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ENNReal.add_ne_top.mpr ⟨e.memLp_fun.eLpNorm_ne_top,
        (e.memLp_jet 1 le_rfl).eLpNorm_ne_top⟩)
  refine ⟨(hext u hu.some).trans_lt (hfin hu.some).lt_top, ?_⟩
  have hbound (e : SobolevExtension U 1 u) :
      (eLpNorm u p (volume.restrict U)).toReal ≤ (C : ℝ) * e.jetNorm := by
    have h := ENNReal.toReal_mono (hfin e) (hext u e)
    simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal,
      ENNReal.toReal_add e.memLp_fun.eLpNorm_ne_top (e.memLp_jet 1 le_rfl).eLpNorm_ne_top,
      e.jetNorm_one] using h
  rw [mul_comm (C : ℝ)]
  apply (div_le_iff₀ (show (0 : ℝ) < C from hC)).mp
  apply le_csInf (show (Set.range (SobolevExtension.jetNorm (U := U) (s := 1)
    (u := u))).Nonempty from ⟨hu.some.jetNorm, hu.some, rfl⟩)
  rintro _ ⟨e, rfl⟩
  exact (div_le_iff₀ (show (0 : ℝ) < C from hC)).mpr (by simpa [mul_comm] using hbound e)

/-- Combining mollification and the infimum step gives the restriction-space
estimate from its smooth whole-space version
(`app:ch_regular:thm:exact-correction`). The final embedding theorem must supply
the smooth estimate and choose a finite exponent strictly greater than two. -/
theorem memLp_and_norm_le_restrictionSobolevNorm_of_smooth_estimate
    (hC : 0 < C)
    (hsmooth : ∀ g : EuclideanSpace ℝ (Fin n) → F,
      ContDiff ℝ ∞ g → MemLp g 2 volume →
      MemLp (iteratedFDeriv ℝ 1 g) 2 volume →
      eLpNorm g p (volume.restrict U) ≤ C *
        (eLpNorm g 2 volume + eLpNorm (iteratedFDeriv ℝ 1 g) 2 volume))
    {u : LocalL2 U F} (hu : MemRestrictionSobolev U 1 u) :
    MemLp u p (volume.restrict U) ∧
      (eLpNorm u p (volume.restrict U)).toReal ≤ (C : ℝ) * restrictionSobolevNorm U 1 u :=
  memLp_and_norm_le_restrictionSobolevNorm_of_extension_estimate hC
    (fun _ e ↦ e.eLpNorm_le_of_smooth_estimate hsmooth) hu

end JanetCartan.LocalSobolev
