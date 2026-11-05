module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Differential.Chart.Compact
public import JanetCartan.Analysis.Fourier.Periodic.SobolevScale.WeakDerivative

/-!
# Transposition of the chart commutator

For `app:ch_background:eq:bg-commutator`, test the Euclidean distribution with
compact extensions of periodic tests. The output cutoff is fixed geometrically,
and is a contraction in L². The derivative order on tests is reversed.
-/

@[expose] public noncomputable section
open MeasureTheory LineDeriv Set
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff SchwartzMap
open JanetCartan.AmplitudeBound JanetCartan.PeriodicLocalL2

namespace JanetCartan.Pseudodifferential.DifferentialChart
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "L²" => EuclideanL2 d ℂ

/-- Transposition reverses the ordered word, with its exact sign
(`app:ch_background:eq:bg-commutator`). -/
theorem orderedTransferAction_pairing (is : List (Fin d)) (f : L²) (φ : 𝓢(E, ℂ)) :
    orderedTransferAction (fun i ↦ lineDerivOp (EuclideanSpace.single i 1 : E)) is
      (f : 𝓢'(E, ℂ)) φ = (-1 : ℂ) ^ is.length *
        ∫ x, euclideanCoordinateDerivList is.reverse (φ : E → ℂ) x * f x := by
  induction is generalizing φ with
  | nil => simp [orderedTransferAction, euclideanCoordinateDerivList,
      Lp.toTemperedDistribution_apply, smul_eq_mul]
  | cons i is ih =>
    simp only [orderedTransferAction, TemperedDistribution.lineDerivOp_apply_apply, map_neg]
    rw [ih]
    have he : (⇑(lineDerivOp (EuclideanSpace.single i 1 : E) φ)) =
        euclideanCoordinateDerivList [i] (φ : E → ℂ) := by
      funext x
      exact SchwartzMap.lineDerivOp_apply_eq_fderiv _ _ _
    rw [he]
    simp only [List.reverse_cons, euclideanCoordinateDerivList_append, List.length_cons, pow_succ]
    ring

namespace SourceCutoff
variable {r : ℝ} (χ : SourceCutoff d r)

/-- Multiplication by the fixed chart cutoff preserves L²
(`app:ch_background:eq:bg-commutator`). -/
theorem memLp_mul (f : L²) : MemLp (fun x ↦ (χ.toFun x : ℂ) * f x) 2 := by
  apply (Lp.memLp f).mono
    ((Complex.continuous_ofReal.comp χ.smooth.continuous).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable f))
  exact Filter.Eventually.of_forall fun x ↦ by
    change ‖(χ.toFun x : ℂ) * f x‖ ≤ ‖f x‖
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (χ.range x).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (χ.range x).2

/-- The localized L² representative used to transpose the compact identity
(`app:ch_background:eq:bg-commutator`). -/
def localize (f : L²) : L² := (χ.memLp_mul f).toLp _

/-- Localization is a contraction, independent of all amplitude budgets
(`app:ch_background:eq:bg-commutator`). -/
theorem norm_localize_le (f : L²) : ‖χ.localize f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [(χ.memLp_mul f).coeFn_toLp] with x hx
  rw [show χ.localize f x = (χ.toFun x : ℂ) * f x from hx, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (χ.range x).1]
  exact mul_le_of_le_one_left (norm_nonneg _) (χ.range x).2

/-- A compactly supported Euclidean pairing equals the normalized torus
pairing of its periodization (`app:ch_background:eq:bg-commutator`). -/
theorem integral_toTorus_mul (f : L²) (φ : Torus d → ℂ)
    (hf : ∀ᵐ x ∂volume, x ∉ halfOpenCell d → f x = 0) :
    (∫ z, φ z * toTorus (𝕜 := ℂ) f z) = ∫ x, periodicLift φ x * f x := by
  calc
    _ = ∫ z, φ z * f (centeredTorusRepresentative z) := by
      apply integral_congr_ae
      filter_upwards [toTorus_coe (𝕜 := ℂ) f] with z hz
      rw [hz, Function.comp_apply]
    _ = ∫ x in halfOpenCell d, periodicLift φ x * f x := by
      rw [← integral_representative]
      simp only [periodicLift, Function.comp_apply, torusQuotient_centeredTorusRepresentative]
    _ = _ := by
      rw [← integral_indicator measurableSet_halfOpenCell]
      apply integral_congr_ae
      filter_upwards [hf] with x hx
      by_cases hc : x ∈ halfOpenCell d
      · rw [indicator_of_mem hc]
      · simp [indicator_of_notMem hc, hx hc]

/-- Exact pairing with the localized residual: the artificial cutoff appears
only in the test extension (`app:ch_background:eq:bg-commutator`). -/
theorem integral_localize (f : L²) (φ : Torus d → ℂ) :
    (∫ z, φ z * toTorus (𝕜 := ℂ) (χ.localize f) z) =
      ∫ x, χ.extend φ x * f x := by
  rw [integral_toTorus_mul]
  · apply integral_congr_ae
    filter_upwards [(χ.memLp_mul f).coeFn_toLp] with x hx
    rw [show χ.localize f x = (χ.toFun x : ℂ) * f x from hx]
    simp only [extend]
    ring
  · filter_upwards [(χ.memLp_mul f).coeFn_toLp] with x hx hc
    rw [show χ.localize f x = (χ.toFun x : ℂ) * f x from hx]
    have hz : χ.toFun x = 0 := by
      by_contra h
      exact hc (subset_halfOpenCell_of_strict (fun y hy ↦ hy)
        (χ.support_cell (subset_tsupport _ h)))
    simp [hz]

/-- Localization is additive, as required to separate the two commutator
terms (`app:ch_background:eq:bg-commutator`). -/
theorem localize_add (f g : L²) : χ.localize (f + g) = χ.localize f + χ.localize g := by
  apply Lp.ext
  filter_upwards [(χ.memLp_mul (f + g)).coeFn_toLp, (χ.memLp_mul f).coeFn_toLp,
    (χ.memLp_mul g).coeFn_toLp, Lp.coeFn_add f g,
    Lp.coeFn_add (χ.localize f) (χ.localize g)] with x h h₁ h₂ h₃ h₄
  simp only [localize] at *
  simp only [Pi.add_apply] at h₃ h₄
  rw [h, h₄, h₁, h₂, h₃]
  exact mul_add _ _ _

/-- The fixed cutoff is exactly the identity on an output supported in the
physical box (`app:ch_background:eq:bg-commutator`). -/
theorem localize_eq (f : L²) (hf : ∀ᵐ x ∂volume, x ∉ chartBox r → f x = 0) :
    χ.localize f = f := by
  apply Lp.ext
  filter_upwards [(χ.memLp_mul f).coeFn_toLp, hf] with x hx hs
  rw [show χ.localize f x = (χ.toFun x : ℂ) * f x from hx]
  by_cases hb : x ∈ chartBox r
  · have hp : x ∈ {x | χ.toFun x = 1} := interior_subset (χ.plateau hb)
    change χ.toFun x = 1 at hp
    simp [hp]
  · simp [hs hb]

end SourceCutoff

/-- Transfer of an actual Euclidean ordered derivative to a normalized torus
pairing. Only the differentiated input needs support in the source box;
the residual is localized by a fixed contraction
(`app:ch_background:eq:bg-commutator`). -/
theorem orderedDerivative_torus_pairing {r : ℝ} (hr : r < 1 / 2)
    (χ : SourceCutoff d r) (is : List (Fin d)) (f g : L²)
    (hf : ∀ᵐ x ∂volume, x ∉ chartBox r → f x = 0)
    (hfg : orderedTransferAction (fun i ↦ lineDerivOp (EuclideanSpace.single i 1 : E))
      is (f : 𝓢'(E, ℂ)) = (g : 𝓢'(E, ℂ)))
    (φ : Torus d → ℂ) (hφ : IsSmoothPeriodic φ) :
    (∫ z, φ z * toTorus (𝕜 := ℂ) (χ.localize g) z) =
      (-1 : ℂ) ^ is.length *
        ∫ z, periodicCoordinateDerivList is.reverse φ z * toTorus (𝕜 := ℂ) f z := by
  let ψ : 𝓢(E, ℂ) := (χ.compact_extend φ).toSchwartzMap (χ.smooth_extend hφ)
  have h := congrArg (fun T : 𝓢'(E, ℂ) ↦ T ψ) hfg
  rw [orderedTransferAction_pairing, Lp.toTemperedDistribution_apply] at h
  rw [χ.integral_localize, SourceCutoff.integral_toTorus_mul f _
    (hf.mono (fun x hx hc ↦ hx (fun hb ↦ hc (chartBox_subset_cell hr hb))))]
  calc
    _ = (-1 : ℂ) ^ is.length *
        ∫ x, euclideanCoordinateDerivList is.reverse (χ.extend φ) x * f x := h.symm
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hf] with x hx
      by_cases hb : x ∈ chartBox r
      · rw [χ.derivative_extend_eq hφ is.reverse hb]
      · simp [hx hb]

/-- Complex bilinear periodic tests recover the project's real-inner-product
weak derivative, with the same ordered word and sign
(`app:ch_background:eq:bg-commutator`). -/
theorem hasPeriodicWeakDerivativeList_of_pairing (is : List (Fin d))
    (u v : PeriodicL2 d ℂ)
    (h : ∀ φ : Torus d → ℂ, IsSmoothPeriodic φ →
      (∫ z, φ z * v z) = (-1 : ℂ) ^ is.length *
        ∫ z, periodicCoordinateDerivList is.reverse φ z * u z) :
    HasPeriodicWeakDerivativeList is u v := by
  intro φ hφ
  have hc := h (fun z ↦ starRingEnd ℂ (φ z))
    (hφ.comp_clm Complex.conjCLE.toContinuousLinearMap)
  have hconj : periodicCoordinateDerivList is.reverse (fun z ↦ starRingEnd ℂ (φ z)) =
      fun z ↦ starRingEnd ℂ (periodicCoordinateDerivList is.reverse φ z) :=
    periodicCoordinateDerivList_comp_clm hφ Complex.conjCLE.toContinuousLinearMap _
  rw [hconj] at hc
  have hi (a : PeriodicL2 d ℂ) {ψ : Torus d → ℂ} (hψ : IsSmoothPeriodic ψ) :
      Integrable (fun z ↦ starRingEnd ℂ (ψ z) * a z) :=
    ((hψ.comp_clm Complex.conjCLE.toContinuousLinearMap).1.memLp_of_hasCompactSupport (p := 2)
      (HasCompactSupport.of_compactSpace _)).integrable_mul (Lp.memLp a)
  have hp (a : PeriodicL2 d ℂ) {ψ : Torus d → ℂ} (hψ : IsSmoothPeriodic ψ) :
      (∫ z, inner ℝ (a z) (ψ z)) = (∫ z, starRingEnd ℂ (ψ z) * a z).re := by
    calc
      _ = ∫ z, (starRingEnd ℂ (ψ z) * a z).re := by
        congr 1
        funext z
        rw [real_inner_comm, Complex.inner, mul_comm]
      _ = _ := integral_re (hi a hψ)
  rw [hp v hφ, hp u (hφ.coordinateDerivList is.reverse)]
  have hr := congrArg Complex.re hc
  rw [show (-1 : ℂ) ^ is.length = ((-1 : ℝ) ^ is.length : ℂ) by simp,
    ← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at hr
  exact hr

/-- Actual periodic weak derivatives follow from the Euclidean distribution
identity and geometric support, without assuming a commutator estimate
(`app:ch_background:eq:bg-commutator`). -/
theorem hasPeriodicWeakDerivativeList_of_chart {r : ℝ} (hr : r < 1 / 2)
    (χ : SourceCutoff d r) (is : List (Fin d)) (f g : L²)
    (hf : ∀ᵐ x ∂volume, x ∉ chartBox r → f x = 0)
    (hfg : orderedTransferAction (fun i ↦ lineDerivOp (EuclideanSpace.single i 1 : E))
      is (f : 𝓢'(E, ℂ)) = (g : 𝓢'(E, ℂ))) :
    HasPeriodicWeakDerivativeList is (toTorus (𝕜 := ℂ) f)
      (toTorus (𝕜 := ℂ) (χ.localize g)) :=
  hasPeriodicWeakDerivativeList_of_pairing is _ _
    (orderedDerivative_torus_pairing hr χ is f g hf hfg)

/-- A Euclidean commutator representative gives an actual periodic weak
commutator representative without any increase of its L² norm. This is the
scalar transfer consumed by the periodic and finite-row estimates
(`app:ch_background:eq:bg-commutator`). -/
theorem exists_periodic_commutator_of_chart {r : ℝ} (hr : r < 1 / 2)
    (χ : SourceCutoff d r) (is : List (Fin d)) (f g w : L²)
    (hf : ∀ᵐ x ∂volume, x ∉ chartBox r → f x = 0)
    (hg : ∀ᵐ x ∂volume, x ∉ chartBox r → g x = 0)
    (hw : orderedTransferAction (fun i ↦ lineDerivOp (EuclideanSpace.single i 1 : E))
      is (f : 𝓢'(E, ℂ)) - (g : 𝓢'(E, ℂ)) = (w : 𝓢'(E, ℂ))) :
    ∃ W : PeriodicL2 d ℂ,
      HasPeriodicWeakDerivativeList is (toTorus (𝕜 := ℂ) f)
        (toTorus (𝕜 := ℂ) g + W) ∧ ‖W‖ ≤ ‖w‖ := by
  refine ⟨toTorus (𝕜 := ℂ) (χ.localize w), ?_,
    (norm_toTorusFun_le (χ.localize w)).trans (χ.norm_localize_le w)⟩
  have he : orderedTransferAction (fun i ↦ lineDerivOp (EuclideanSpace.single i 1 : E))
      is (f : 𝓢'(E, ℂ)) = ((g + w : L²) : 𝓢'(E, ℂ)) := by
    rw [show ((g + w : L²) : 𝓢'(E, ℂ)) = (g : 𝓢'(E, ℂ)) + (w : 𝓢'(E, ℂ)) from
      (Lp.toTemperedDistributionCLM ℂ volume 2).map_add g w]
    simpa only [Lp.toTemperedDistributionCLM_apply, add_comm] using (sub_eq_iff_eq_add.mp hw)
  have h := hasPeriodicWeakDerivativeList_of_chart hr χ is f (g + w) hf he
  rwa [χ.localize_add, χ.localize_eq g hg, map_add] at h

end JanetCartan.Pseudodifferential.DifferentialChart
