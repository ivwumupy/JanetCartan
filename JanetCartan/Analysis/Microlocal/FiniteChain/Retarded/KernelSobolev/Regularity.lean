module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.KernelSobolev.Basic
public import JanetCartan.Analysis.Calculus.CompactParameterIntegral

/-!
# Smooth kernel integration and Cartesian jet commutation

Regularity for the common kernel estimate in `app:ch_regular:lem:finite-chain`
and `app:ch_regular:eq:chain-tail`. The compact input support reduces the literal
integral to the shared compact-parameter integral API. That API derives domination
from joint smoothness on compact output neighborhoods times the input support.
The actual transverse and time derivatives commute with this integral, so the
resulting complex linear map on test fields supplies the formula consumed by
`jetMap_bound_of_kernelJet_formula` and `exists_extension_of_kernelJet_formula`.
All coordinate spaces retain their Cartesian product norms.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff
open JanetCartan.RetardedSobolev JanetCartan.RetardedSobolev.Spaces

namespace JanetCartan.FiniteChain.Retarded.KernelSobolev

variable {d e : ℕ}

private theorem contDiff_columnFDeriv
    {g : (ℝ × (Fin e → ℝ)) × ((Fin d → ℝ) × ℝ) → ℂ}
    (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun p : (ℝ × (Fin e → ℝ)) × ((Fin d → ℝ) × ℝ) ↦
      fderiv ℝ (fun x ↦ g (x, p.2)) p.1) := by
  rw [← contDiffOn_univ]
  simpa only [univ_prod_univ] using
    contDiffOn_parameterFDeriv isOpen_univ isOpen_univ
      (hg.contDiffOn (s := univ ×ˢ univ))

private theorem contDiff_columnTransverseJet
    {g : (ℝ × (Fin e → ℝ)) × ((Fin d → ℝ) × ℝ) → ℂ}
    (hg : ContDiff ℝ ∞ g) (vs : List (Fin e → ℝ)) :
    ContDiff ℝ ∞ (fun p : (ℝ × (Fin e → ℝ)) × ((Fin d → ℝ) × ℝ) ↦
      transverseJet vs (fun x ↦ g (x, p.2)) p.1) := by
  induction vs with
  | nil => exact hg
  | cons v vs ih =>
    have he : (fun p : (ℝ × (Fin e → ℝ)) × ((Fin d → ℝ) × ℝ) ↦
        transverseJet (v :: vs) (fun x ↦ g (x, p.2)) p.1) =
        fun p : (ℝ × (Fin e → ℝ)) × ((Fin d → ℝ) × ℝ) ↦
          (fderiv ℝ (fun x ↦ transverseJet vs (fun x ↦ g (x, p.2)) x) p.1)
            (0, v) := by
      funext p
      rw [transverseJet, transverseDeriv_eq_fderiv v
        ((contDiff_transverseJet (f := fun x ↦ g (x, p.2))
          (hg.comp (contDiff_id.prodMk (contDiff_const (c := p.2)))) vs).differentiable
          (by simp))]
    rw [he]
    exact (contDiff_columnFDeriv ih).clm_apply contDiff_const

private theorem contDiff_columnTimeJet
    {g : (ℝ × (Fin e → ℝ)) × ((Fin d → ℝ) × ℝ) → ℂ}
    (hg : ContDiff ℝ ∞ g) (j : ℕ) :
    ContDiff ℝ ∞ (fun p : (ℝ × (Fin e → ℝ)) × ((Fin d → ℝ) × ℝ) ↦
      timeJet j (fun x ↦ g (x, p.2)) p.1) := by
  induction j with
  | zero => simpa only [timeJet_zero] using hg
  | succ j ih =>
    have he : (fun p : (ℝ × (Fin e → ℝ)) × ((Fin d → ℝ) × ℝ) ↦
        timeJet (j + 1) (fun x ↦ g (x, p.2)) p.1) =
        fun p : (ℝ × (Fin e → ℝ)) × ((Fin d → ℝ) × ℝ) ↦
          (fderiv ℝ (fun x ↦ timeJet j (fun x ↦ g (x, p.2)) x) p.1)
            (1, 0) := by
      funext p
      rw [timeJet_succ, timeDeriv_eq_fderiv
        ((contDiff_timeJet (f := fun x ↦ g (x, p.2))
          (hg.comp (contDiff_id.prodMk (contDiff_const (c := p.2)))) j).differentiable
          (by simp))]
    rw [he]
    exact (contDiff_columnFDeriv ih).clm_apply contDiff_const

private theorem contDiff_compactIntegral
    (μ : Measure ((Fin d → ℝ) × ℝ)) {S : Set ((Fin d → ℝ) × ℝ)}
    [IsFiniteMeasure (μ.restrict S)] (hS : IsCompact S)
    {g : (ℝ × (Fin e → ℝ)) × ((Fin d → ℝ) × ℝ) → ℂ}
    (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun x ↦ ∫ y in S, g (x, y) ∂μ) := by
  rw [← contDiffOn_univ]
  exact contDiffOn_compactParameterIntegral isOpen_univ isOpen_univ hS (subset_univ _)
    hg.contDiffOn

private theorem fderiv_compactIntegral_apply
    (μ : Measure ((Fin d → ℝ) × ℝ)) {S : Set ((Fin d → ℝ) × ℝ)}
    [IsFiniteMeasure (μ.restrict S)] (hS : IsCompact S)
    {g : (ℝ × (Fin e → ℝ)) × ((Fin d → ℝ) × ℝ) → ℂ}
    (hg : ContDiff ℝ ∞ g) (x v : ℝ × (Fin e → ℝ)) :
    fderiv ℝ (fun x ↦ ∫ y in S, g (x, y) ∂μ) x v =
      ∫ y in S, fderiv ℝ (fun x ↦ g (x, y)) x v ∂μ := by
  rw [fderiv_compactParameterIntegral isOpen_univ isOpen_univ hS (subset_univ _)
    hg.contDiffOn (mem_univ x)]
  exact ContinuousLinearMap.integral_apply
    (integrableOn_parameterFDeriv isOpen_univ isOpen_univ hS (subset_univ _)
      hg.contDiffOn (mem_univ x)) v

private theorem transverseJet_compactIntegral
    (μ : Measure ((Fin d → ℝ) × ℝ)) {S : Set ((Fin d → ℝ) × ℝ)}
    [IsFiniteMeasure (μ.restrict S)] (hS : IsCompact S)
    {g : (ℝ × (Fin e → ℝ)) × ((Fin d → ℝ) × ℝ) → ℂ}
    (hg : ContDiff ℝ ∞ g) (vs : List (Fin e → ℝ)) :
    transverseJet vs (fun x ↦ ∫ y in S, g (x, y) ∂μ) =
      fun x ↦ ∫ y in S, transverseJet vs (fun x ↦ g (x, y)) x ∂μ := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    rw [transverseJet, ih,
      transverseDeriv_eq_fderiv v
        ((contDiff_compactIntegral μ hS (contDiff_columnTransverseJet hg vs)).differentiable
          (by simp))]
    funext x
    rw [fderiv_compactIntegral_apply μ hS (contDiff_columnTransverseJet hg vs)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y ↦ by
      dsimp only
      rw [transverseJet, transverseDeriv_eq_fderiv v
        ((contDiff_transverseJet (f := fun x ↦ g (x, y))
          (hg.comp (contDiff_id.prodMk (contDiff_const (c := y)))) vs).differentiable
          (by simp))]

private theorem timeJet_compactIntegral
    (μ : Measure ((Fin d → ℝ) × ℝ)) {S : Set ((Fin d → ℝ) × ℝ)}
    [IsFiniteMeasure (μ.restrict S)] (hS : IsCompact S)
    {g : (ℝ × (Fin e → ℝ)) × ((Fin d → ℝ) × ℝ) → ℂ}
    (hg : ContDiff ℝ ∞ g) (j : ℕ) :
    timeJet j (fun x ↦ ∫ y in S, g (x, y) ∂μ) =
      fun x ↦ ∫ y in S, timeJet j (fun x ↦ g (x, y)) x ∂μ := by
  induction j with
  | zero => simp only [timeJet_zero]
  | succ j ih =>
    rw [timeJet_succ, ih,
      timeDeriv_eq_fderiv
        ((contDiff_compactIntegral μ hS (contDiff_columnTimeJet hg j)).differentiable
          (by simp))]
    funext x
    rw [fderiv_compactIntegral_apply μ hS (contDiff_columnTimeJet hg j)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y ↦ by
      dsimp only
      rw [timeJet_succ, timeDeriv_eq_fderiv
        ((contDiff_timeJet (f := fun x ↦ g (x, y))
          (hg.comp (contDiff_id.prodMk (contDiff_const (c := y)))) j).differentiable
          (by simp))]

/-- Joint smoothness of the actual Cartesian kernel jets, used to supply
measurability in the common kernel estimate of `app:ch_regular:lem:finite-chain`. -/
theorem kernelJet_contDiff {m : ℕ} (K : SupportedSmoothKernel d e) (i : JetIndex e m) :
    ContDiff ℝ ∞ (Function.uncurry (kernelJet K i)) := by
  have h := contDiff_columnTimeJet
    (contDiff_columnTransverseJet K.smooth
      (List.ofFn (fun j ↦ Pi.single (i.2.1 j) 1))) i.2.2.val
  exact h.comp ((contDiff_fst.snd.prodMk contDiff_fst.fst).prodMk contDiff_snd)

/-- Measurability of every kernel jet follows from joint kernel smoothness,
with no measure finiteness hypothesis (`app:ch_regular:eq:chain-tail`). -/
theorem kernelJet_aestronglyMeasurable {m : ℕ} (K : SupportedSmoothKernel d e)
    (μ : Measure ((Fin d → ℝ) × ℝ)) (i : JetIndex e m) (p : (Fin e → ℝ) × ℝ) :
    AEStronglyMeasurable (kernelJet K i p) μ :=
  ((kernelJet_contDiff K i).continuous.comp
    (continuous_const.prodMk continuous_id)).aestronglyMeasurable

private theorem contDiff_kernelIntegrand (K : SupportedSmoothKernel d e) (f : Test d) :
    ContDiff ℝ ∞ (fun p : (ℝ × (Fin e → ℝ)) × ((Fin d → ℝ) × ℝ) ↦
      K.toFun p.1 p.2 * f.val (p.2.2, p.2.1)) :=
  K.smooth.mul (f.property.1.comp (contDiff_snd.snd.prodMk contDiff_snd.fst))

private theorem kernelIntegral_eq_compactIntegral (K : SupportedSmoothKernel d e)
    (μ : Measure ((Fin d → ℝ) × ℝ)) (f : (ℝ × (Fin d → ℝ)) → ℂ) :
    kernelIntegral K μ f = fun x ↦ ∫ y in K.inputSupport, K.toFun x y * f (y.2, y.1) ∂μ := by
  funext x
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun y hy ↦ by rw [K.zero_off_input x y hy, zero_mul])).symm

/-- Smoothness of the literal kernel integral, derived from compact input support
and joint smoothness (`app:ch_regular:lem:finite-chain`, common kernel estimate). -/
theorem kernelIntegral_contDiff (K : SupportedSmoothKernel d e)
    (μ : Measure ((Fin d → ℝ) × ℝ)) [IsFiniteMeasureOnCompacts μ] (f : Test d) :
    ContDiff ℝ ∞ (kernelIntegral K μ f.val) := by
  let : IsFiniteMeasure (μ.restrict K.inputSupport) :=
    isFiniteMeasure_restrict.mpr K.compact_inputSupport.measure_lt_top.ne
  rw [kernelIntegral_eq_compactIntegral]
  exact contDiff_compactIntegral μ K.compact_inputSupport (contDiff_kernelIntegrand K f)

/-- The literal integral inherits the prescribed output support
(`app:ch_regular:eq:chain-tail`). -/
theorem kernelIntegral_zero_off_output (K : SupportedSmoothKernel d e)
    (μ : Measure ((Fin d → ℝ) × ℝ)) (f : (ℝ × (Fin d → ℝ)) → ℂ)
    (x : ℝ × (Fin e → ℝ)) (hx : x ∉ K.outputSupport) :
    kernelIntegral K μ f x = 0 := by
  simp only [kernelIntegral, K.zero_off_output x _ hx, zero_mul, integral_zero]

/-- Compact output support of the integral is a consequence of the kernel support
(`app:ch_regular:lem:finite-chain`). -/
theorem kernelIntegral_hasCompactSupport (K : SupportedSmoothKernel d e)
    (μ : Measure ((Fin d → ℝ) × ℝ)) (f : (ℝ × (Fin d → ℝ)) → ℂ) :
    HasCompactSupport (kernelIntegral K μ f) := by
  apply HasCompactSupport.of_support_subset_isCompact K.compact_outputSupport
  intro x hx
  by_contra hn
  exact hx (kernelIntegral_zero_off_output K μ f x hn)

private theorem kernelIntegrand_integrable (K : SupportedSmoothKernel d e)
    (μ : Measure ((Fin d → ℝ) × ℝ)) [IsFiniteMeasureOnCompacts μ]
    (f : Test d) (x : ℝ × (Fin e → ℝ)) :
    Integrable (fun y ↦ K.toFun x y * f.val (y.2, y.1)) μ := by
  apply ((contDiff_kernelIntegrand K f).continuous.comp
    (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact K.compact_inputSupport
  intro y hy
  by_contra hn
  exact hy (by
    change K.toFun x y * _ = 0
    rw [K.zero_off_input x y hn, zero_mul])

/-- Integration against the actual smooth kernel is a complex linear map on test
fields, for the common kernel estimate of `app:ch_regular:lem:finite-chain`. -/
def kernelIntegralLinear (K : SupportedSmoothKernel d e)
    (μ : Measure ((Fin d → ℝ) × ℝ)) [IsFiniteMeasureOnCompacts μ] : Test d →ₗ[ℂ] Test e where
  toFun f := ⟨kernelIntegral K μ f.val,
    kernelIntegral_contDiff K μ f, kernelIntegral_hasCompactSupport K μ f.val⟩
  map_add' f g := by
    apply Subtype.ext
    funext x
    change (∫ y, K.toFun x y * (f.val (y.2, y.1) + g.val (y.2, y.1)) ∂μ) = _
    simp only [mul_add]
    exact integral_add (kernelIntegrand_integrable K μ f x) (kernelIntegrand_integrable K μ g x)
  map_smul' c f := by
    apply Subtype.ext
    funext x
    change (∫ y, K.toFun x y * (c * f.val (y.2, y.1)) ∂μ) =
      c * ∫ y, K.toFun x y * f.val (y.2, y.1) ∂μ
    simp only [mul_left_comm (K.toFun x _) c]
    exact integral_const_mul c _

/-- The test-field operator has exactly the literal kernel integral as its value
(`app:ch_regular:eq:chain-tail`). -/
@[simp] theorem kernelIntegralLinear_val (K : SupportedSmoothKernel d e)
    (μ : Measure ((Fin d → ℝ) × ℝ)) [IsFiniteMeasureOnCompacts μ] (f : Test d) :
    (kernelIntegralLinear K μ f).val = kernelIntegral K μ f.val := rfl

/-- Every Cartesian mixed jet passes under the literal kernel integral, with all
output derivatives falling on the kernel. This supplies the exact formula used
by `jetMap_bound_of_kernelJet_formula` for `app:ch_regular:eq:chain-tail`. -/
theorem kernelIntegral_jet {m : ℕ} (K : SupportedSmoothKernel d e)
    (μ : Measure ((Fin d → ℝ) × ℝ)) [IsFiniteMeasureOnCompacts μ]
    (i : JetIndex e m) (f : Test d) (p : (Fin e → ℝ) × ℝ) :
    jet i (kernelIntegral K μ f.val) p =
      ∫ y, kernelJet K i p y * f.val (y.2, y.1) ∂μ := by
  let : IsFiniteMeasure (μ.restrict K.inputSupport) :=
    isFiniteMeasure_restrict.mpr K.compact_inputSupport.measure_lt_top.ne
  have hj (y : (Fin d → ℝ) × ℝ) :
      jet i (fun x ↦ K.toFun x y * f.val (y.2, y.1)) p =
        kernelJet K i p y * f.val (y.2, y.1) := by
    have hs : HasCompactSupport (fun x ↦ K.toFun x y) := by
      apply HasCompactSupport.of_support_subset_isCompact K.compact_outputSupport
      intro x hx
      by_contra hn
      exact hx (K.zero_off_output x y hn)
    let k : Test e := ⟨fun x ↦ K.toFun x y, kernelColumn_contDiff K y, hs⟩
    have he := congrFun ((jetLinear i).map_smul (f.val (y.2, y.1)) k) p
    change jet i (fun x ↦ f.val (y.2, y.1) * K.toFun x y) p =
      f.val (y.2, y.1) * kernelJet K i p y at he
    simpa only [mul_comm] using he
  rw [kernelIntegral_eq_compactIntegral]
  unfold jet
  rw [transverseJet_compactIntegral μ K.compact_inputSupport (contDiff_kernelIntegrand K f)]
  rw [timeJet_compactIntegral μ K.compact_inputSupport
    (contDiff_columnTransverseJet (contDiff_kernelIntegrand K f) _)]
  change (∫ y in K.inputSupport,
    jet i (fun x ↦ K.toFun x y * f.val (y.2, y.1)) p ∂μ) = _
  simp_rw [hj]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun y hy ↦ by rw [kernelJet_zero_off_input K i p y hy, zero_mul])

/-- The concrete test-field map satisfies the jet formula required by the
Sobolev completion step (`app:ch_regular:eq:chain-tail`). -/
theorem kernelIntegralLinear_jet {m : ℕ} (K : SupportedSmoothKernel d e)
    (μ : Measure ((Fin d → ℝ) × ℝ)) [IsFiniteMeasureOnCompacts μ]
    (i : JetIndex e m) (f : Test d) (p : (Fin e → ℝ) × ℝ) :
    jet i (kernelIntegralLinear K μ f).val p =
      ∫ y, kernelJet K i p y * f.val (y.2, y.1) ∂μ :=
  kernelIntegral_jet K μ i f p

end JanetCartan.FiniteChain.Retarded.KernelSobolev
