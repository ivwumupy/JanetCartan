module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputRealization.Spaces
public import JanetCartan.Analysis.Operator.SmallSupport.ZeroExtension
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Complex annular restriction and zero extension

The adjunction needed for the actual annular synthesis in
`app:ch_waves:thm:individual` and its normal in
`app:ch_waves:eq:sampling-prefix-normal`. The measure is unchanged.
-/

@[expose] public noncomputable section

open MeasureTheory Filter

namespace JanetCartan.RawInputHilbert

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}

/-- Complex-linear version of zero extension, for the annular inputs of
`app:ch_waves:thm:individual`. -/
def zeroExtension (hs : MeasurableSet s) : Lp ℂ 2 (μ.restrict s) →ₗᵢ[ℂ] Lp ℂ 2 μ where
  toFun := SmallSupport.zeroExtend hs
  map_add' := map_add (SmallSupport.zeroExtend hs)
  map_smul' c f := by
    apply Lp.ext
    have hi := (ae_eq_restrict_iff_indicator_ae_eq hs).mp (Lp.coeFn_smul c f)
    filter_upwards [SmallSupport.zeroExtend_coeFn hs (c • f), hi,
      SmallSupport.zeroExtend_coeFn hs f,
      Lp.coeFn_smul c (SmallSupport.zeroExtend hs f)] with x h₁ h₂ h₃ h₄
    by_cases hx : x ∈ s <;> simp_all [Set.indicator]
  norm_map' := (SmallSupport.zeroExtend hs).norm_map

/-- Literal representative of complex zero extension
(`app:ch_waves:thm:individual`). -/
theorem zeroExtension_coeFn (hs : MeasurableSet s) (f : Lp ℂ 2 (μ.restrict s)) :
    zeroExtension hs f =ᵐ[μ] s.indicator (fun x ↦ f x) :=
  SmallSupport.zeroExtend_coeFn hs f

/-- Restriction on the same measure space, used by the raw adjoint in
`app:ch_waves:eq:sampling-prefix-normal`. -/
def restriction (s : Set α) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 (μ.restrict s) := by
  let T : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 (μ.restrict s) :=
    { toFun := fun f ↦ ((Lp.memLp f).restrict s).toLp f
      map_add' := fun f g ↦ by
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp ((Lp.memLp (f + g)).restrict s),
          ae_restrict_of_ae (Lp.coeFn_add f g),
          MemLp.coeFn_toLp ((Lp.memLp f).restrict s),
          MemLp.coeFn_toLp ((Lp.memLp g).restrict s),
          Lp.coeFn_add (((Lp.memLp f).restrict s).toLp f)
            (((Lp.memLp g).restrict s).toLp g)] with x h₁ h₂ h₃ h₄ h₅
        simp_all
      map_smul' := fun c f ↦ by
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp ((Lp.memLp (c • f)).restrict s),
          ae_restrict_of_ae (Lp.coeFn_smul c f),
          MemLp.coeFn_toLp ((Lp.memLp f).restrict s),
          Lp.coeFn_smul c (((Lp.memLp f).restrict s).toLp f)] with x h₁ h₂ h₃ h₄
        simp_all }
  refine T.mkContinuous 1 fun f ↦ ?_
  change ‖((Lp.memLp f).restrict s).toLp f‖ ≤ _
  rw [Lp.norm_toLp, Lp.norm_def, one_mul]
  exact ENNReal.toReal_mono (Lp.memLp f).eLpNorm_ne_top (eLpNorm_restrict_le _ _ _ _)

/-- Restriction agrees with the full-space datum on the restricted measure
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem restriction_coeFn (s : Set α) (f : Lp ℂ 2 μ) :
    restriction s f =ᵐ[μ.restrict s] f :=
  MemLp.coeFn_toLp ((Lp.memLp f).restrict s)

/-- Restriction is a contraction (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem norm_restriction_le (s : Set α) : ‖restriction (μ := μ) s‖ ≤ 1 :=
by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖((Lp.memLp f).restrict s).toLp f‖ ≤ _
  rw [Lp.norm_toLp, Lp.norm_def, one_mul]
  exact ENNReal.toReal_mono (Lp.memLp f).eLpNorm_ne_top (eLpNorm_restrict_le _ _ _ _)

/-- The genuine restriction/extension pairing, retaining both complex
quadratures (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem inner_zeroExtension (hs : MeasurableSet s)
    (f : Lp ℂ 2 (μ.restrict s)) (g : Lp ℂ 2 μ) :
    inner ℂ (zeroExtension hs f) g = inner ℂ f (restriction s g) := by
  rw [L2.inner_def, L2.inner_def]
  calc
    _ = ∫ x, s.indicator (fun y ↦ inner ℂ (f y) (g y)) x ∂μ := by
      apply integral_congr_ae
      filter_upwards [zeroExtension_coeFn hs f] with x hx
      rw [hx]
      by_cases hxs : x ∈ s <;> simp [hxs]
    _ = ∫ x in s, inner ℂ (f x) (g x) ∂μ := integral_indicator hs
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [restriction_coeFn s g] with x hx
      rw [hx]

/-- Exact Hilbert adjoint of zero extension
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem adjoint_zeroExtension (hs : MeasurableSet s) :
    (zeroExtension (μ := μ) hs).toContinuousLinearMap.adjoint = restriction s := by
  rw [← ContinuousLinearMap.adjoint_adjoint (restriction (μ := μ) s)]
  congr 1
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  exact inner_zeroExtension hs

end JanetCartan.RawInputHilbert
