module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.LowBounds.SymbolJets
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.LowBounds.Realization

/-!
# Identifying the compact modified normal with the PDO realization

The source/frequency Fubini step of `app:ch_background:prop:bg-adjoint`.
The consumer is the modified carrier bound. The scalar entry of the checked
matrix PDO is sufficient, since an individual expansion term is scalar.
-/

@[expose] public noncomputable section
open MeasureTheory Filter Set
open scoped ContDiff FourierTransform RealInnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint.DerivativeKernels
open ContinuumRow AmplitudeBound Pseudodifferential FourierIntegral
variable {n : ℕ}

/-- Compactness in source and frequency gives absolute convergence against
arbitrary measurement L² data (`app:ch_background:prop:bg-adjoint`). This is
used only after the compact image of the regularized conic chart is proved. -/
theorem integrable_compactAmplitude_L2_weight
    {b : Euclidean n × Euclidean n → ℂ} (hb : Continuous b)
    (hbs : HasCompactSupport b) (f : Lp (α := Euclidean n) ℂ 2) :
    Integrable (fun p ↦ b p * f p.1) (volume.prod volume) := by
  let X := Prod.fst '' tsupport b
  let V := Prod.snd '' tsupport b
  have hX : IsCompact X := hbs.image continuous_fst
  have hV : IsCompact V := hbs.image continuous_snd
  have hf := ((Lp.memLp f).locallyIntegrable (by norm_num)).integrableOn_isCompact hX
    |>.integrable_indicator hX.measurableSet
  have hv := (continuous_const.continuousOn.integrableOn_compact (μ := (volume : Measure (Euclidean n)))
    hV : IntegrableOn (fun _ ↦ (1 : ℂ)) V).integrable_indicator hV.measurableSet
  obtain ⟨C, hC⟩ := hbs.exists_bound_of_continuous hb
  apply ((hf.mul_prod hv).bdd_mul hb.aestronglyMeasurable
    (Eventually.of_forall hC)).congr
  filter_upwards [] with p
  by_cases hp : b p = 0
  · simp [hp]
  · have hx : p.1 ∈ X := ⟨p, subset_tsupport b hp, rfl⟩
    have hv : p.2 ∈ V := ⟨p, subset_tsupport b hp, rfl⟩
    simp [indicator_of_mem hx, indicator_of_mem hv]

/-- The source-first full PDO is the frequency-first paired kernel whenever
the compact conic image gives compact source/frequency support. The Fourier
character has exactly the cycles-per-unit normalization
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem fullAmplitudeOperator_eq_compact_kernel
    (b : Euclidean n → Euclidean (2 * n) → ℂ)
    (hb : Continuous (Function.uncurry b))
    (hbs : ∀ x, HasCompactSupport
      (fun p : Euclidean n × Euclidean n ↦ b p.2 (pairedPosition x p.1)))
    (f : Lp (α := Euclidean n) ℂ 2) (x : Euclidean n) :
    fullAmplitudeOperator (fun x y ξ ↦ b ξ (pairedPosition x y)) f x =
      ∫ y, (∫ ξ, Real.fourierChar ⟪x - y, ξ⟫ * b ξ (pairedPosition x y)) * f y := by
  have hc : Continuous (fun p : Euclidean n × Euclidean n ↦
      (Real.fourierChar ⟪x - p.1, p.2⟫ : ℂ) * b p.2 (pairedPosition x p.1)) := by
    apply Continuous.mul
    · fun_prop
    · exact hb.comp (continuous_snd.prodMk
        (continuous_pairedPosition.comp (continuous_const.prodMk continuous_fst)))
  have hs : HasCompactSupport (fun p : Euclidean n × Euclidean n ↦
      (Real.fourierChar ⟪x - p.1, p.2⟫ : ℂ) * b p.2 (pairedPosition x p.1)) :=
    (hbs x).mul_left
  have hi := integrable_compactAmplitude_L2_weight hc hs f
  unfold fullAmplitudeOperator sourceAmplitudeTransform
  simp only [Real.fourierInv_eq, Real.fourier_eq, Circle.smul_def, smul_eq_mul]
  simp_rw [← integral_const_mul]
  calc
    _ = ∫ ξ, ∫ y, (Real.fourierChar ⟪x - y, ξ⟫ : ℂ) *
        b ξ (pairedPosition x y) * f y := by
      apply integral_congr_ae
      filter_upwards [] with ξ
      apply integral_congr_ae
      filter_upwards [] with y
      rw [← mul_assoc, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
      rw [show ⟪ξ, x⟫ + -⟪y, ξ⟫ = ⟪x - y, ξ⟫ by
        simp only [inner_sub_left]
        rw [real_inner_comm ξ x]
        ring]
      ring
    _ = ∫ y, ∫ ξ, (Real.fourierChar ⟪x - y, ξ⟫ : ℂ) *
        b ξ (pairedPosition x y) * f y := (integral_integral_swap hi).symm
    _ = _ := by simp only [integral_mul_const]

/-- Compact source/frequency support supplies the integrability premise of
the existing bounded PDO realization (`app:ch_background:prop:bg-adjoint`). -/
theorem integrable_sourceAmplitudeTransform_of_compact_support
    (b : Euclidean n → Euclidean (2 * n) → ℂ)
    (hb : Continuous (Function.uncurry b))
    (hbs : ∀ x, HasCompactSupport
      (fun p : Euclidean n × Euclidean n ↦ b p.2 (pairedPosition x p.1)))
    (f : Lp (α := Euclidean n) ℂ 2) (x : Euclidean n) :
    Integrable (sourceAmplitudeTransform (fun x y ξ ↦ b ξ (pairedPosition x y)) f x) := by
  have hc : Continuous (fun p : Euclidean n × Euclidean n ↦
      (Real.fourierChar (-⟪p.1, p.2⟫) : ℂ) * b p.2 (pairedPosition x p.1)) := by
    apply Continuous.mul
    · fun_prop
    · exact hb.comp (continuous_snd.prodMk
        (continuous_pairedPosition.comp (continuous_const.prodMk continuous_fst)))
  have hi := integrable_compactAmplitude_L2_weight hc ((hbs x).mul_left) f
  convert hi.integral_prod_right using 1
  funext ξ
  simp only [sourceAmplitudeTransform, Real.fourier_eq, Circle.smul_def, smul_eq_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  ring

/-- A literal compact paired normal equals the scalar entry of the matrix PDO
on all L² data, with its bound obtained from the checked amplitude theorem.
The actual conic normal identity and compact image are discharged separately
by the modified-carrier construction (`app:ch_background:prop:bg-adjoint`). -/
theorem norm_scalarCarrierAdjoint_of_compact_normal
    (hn : 0 < n) (R M : ℝ) (hM : 0 ≤ M)
    (b : Euclidean n → Euclidean (2 * n) → Matrix (Fin 1) (Fin 1) ℂ)
    (hb : GraphNormalAmplitudeBounds b R M)
    (hbs : ∀ x, HasCompactSupport
      (fun p : Euclidean n × Euclidean n ↦ b p.2 (pairedPosition x p.1) 0 0))
    (T : CarrierL2 n →L[ℂ] Lp (α := Euclidean n) ℂ 2)
    (hN : ∀ f, T (T.adjoint f) =ᵐ[volume]
      fun x ↦ ∫ y, (∫ ξ, Real.fourierChar ⟪x - y, ξ⟫ *
        b ξ (pairedPosition x y) 0 0) * f y) :
    ‖T.adjoint‖ ≤ Real.sqrt (fixedBoxAmplitudeConstant n R * M) := by
  let c := fun ξ z ↦ b ξ z 0 0
  have hc : ContDiff ℝ ∞ (Function.uncurry c) :=
    (matrixEntryEvaluation (0 : Fin 1) (0 : Fin 1)).contDiff.comp hb.smooth
  let P := twoPositionL2Operator hn R c hc (fun ξ ↦ hb.support ξ 0 0) M
    (hb.entry_bound 0 0)
  have he : T.comp T.adjoint = P := by
    apply ContinuousLinearMap.ext
    intro f
    apply Lp.ext
    have hp := twoPositionL2Operator_ae_fullAmplitudeOperator hn R c hc
      (fun ξ ↦ hb.support ξ 0 0) M (hb.entry_bound 0 0) f
      (Eventually.of_forall (integrable_sourceAmplitudeTransform_of_compact_support
        c hc.continuous hbs f))
    exact (hN f).trans (hp.trans (Eventually.of_forall
      (fullAmplitudeOperator_eq_compact_kernel c hc.continuous hbs f))).symm
  apply (Real.le_sqrt (norm_nonneg _) (mul_nonneg
    (fixedBoxAmplitudeConstant_nonneg n R) hM)).mpr
  rw [sq, ← ContinuousLinearMap.norm_adjoint_comp_self T.adjoint,
    ContinuousLinearMap.adjoint_adjoint, he]
  exact norm_twoPositionL2Operator_le ..

end JanetCartan.ContinuumAdjoint.DerivativeKernels
