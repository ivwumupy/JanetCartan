module

public import JanetCartan.Analysis.Microlocal.NormalComparison.KernelCalculus.Oscillatory
public import JanetCartan.Analysis.Microlocal.NormalComparison.KernelCalculus.FullKernel.Integrability
public import JanetCartan.Analysis.Microlocal.AmplitudeBound.FullNormalKernel.IntegralSeries

/-!
# Full kernels of actual compact normal compositions

The literal kernel action in `app:ch_osc:eq:osc-exact-normal-kernel` and
`app:ch_osc:prop:osc-normal`, before the change of parameter variable. The
cross formula also applies to the distinct kernels in the differentiated
product. Absolute convergence, the adjoint identity, and Fubini are proved
from continuity and compact support and the L²/L∞ input assumptions.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace JanetCartan.NormalComparison

open AmplitudeBound

variable {d m r q : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "U" => EuclideanSpace ℝ (Fin m)

/-- The actual cross composition has the full matrix kernel, in the displayed
integration order of `app:ch_osc:eq:osc-exact-normal-kernel`. The kernels and
their vector dimensions may differ, as needed in `app:ch_osc:prop:osc-normal`. -/
theorem compactVectorKernelOperator_cross_ae_integral
    (D : Set U) {s : Fin r → E → U → ℂ} {t : Fin q → E → U → ℂ}
    (hcS : ∀ i, Continuous (Function.uncurry (s i)))
    (hsS : ∀ i, HasCompactSupport (Function.uncurry (s i)))
    (hcT : ∀ j, Continuous (Function.uncurry (t j)))
    (hsT : ∀ j, HasCompactSupport (Function.uncurry (t j)))
    (g : Lp ℂ ∞ (volume.restrict D)) (f : NormalOutputL2 d q) (i : Fin r) :
    ((compactVectorKernelOperator D hcS hsS).comp
      ((multiplicationOperator g).comp
        (compactVectorKernelOperator D hcT hsT).adjoint) f) i =ᵐ[volume]
      fun x ↦ ∑ j, ∫ y, (∫ u in D, s i x u * star (t j y u) * g u) * f j y := by
  have hmul := multiplicationOperator_coeFn g
    ((compactVectorKernelOperator D hcT hsT).adjoint f)
  have hadj := compactVectorKernelOperator_adjoint_ae_integral D hcT hsT f
  filter_upwards [compactVectorKernelOperator_ae_integral D hcS hsS
    (multiplicationOperator g ((compactVectorKernelOperator D hcT hsT).adjoint f)) i]
    with x hx
  change (compactVectorKernelOperator D hcS hsS
    (multiplicationOperator g ((compactVectorKernelOperator D hcT hsT).adjoint f))) i x = _
  rw [hx]
  calc
    _ = ∫ u in D, ∑ j, s i x u * (g u * ∫ y, star (t j y u) * f j y) := by
      apply integral_congr_ae
      filter_upwards [hmul, hadj] with u hu ha
      rw [hu, ha, Finset.mul_sum, Finset.mul_sum]
    _ = ∑ j, ∫ u in D, s i x u * (g u * ∫ y, star (t j y u) * f j y) :=
      integral_finsetSum _ (fun j _ ↦ integrable_compactCrossKernel_adjoint_integral
        D (hcS i) (hsS i) (hcT j) (hsT j) g (f j) x)
    _ = _ := Finset.sum_congr rfl fun j _ ↦
      integral_compactCrossKernel_swap D (hcS i) (hsS i) (hcT j) (hsT j) g (f j) x

/-- The scalar actual normal composition agrees with the existing
`fullNormalAmplitudeKernel`, with coefficient one. Its integration order is
justified by the cross-kernel Fubini theorem
(`app:ch_osc:eq:osc-exact-normal-kernel`). -/
theorem compactKernelOperator_normal_ae_fullNormalAmplitudeKernel
    (D : Set U) {t : E → U → ℂ}
    (hc : Continuous (Function.uncurry t))
    (hs : HasCompactSupport (Function.uncurry t))
    (g : Lp ℂ ∞ (volume.restrict D)) (f : Lp (α := E) ℂ 2) :
    (compactKernelOperator (μ := volume.restrict D) (ν := volume) hc hs).comp
      ((multiplicationOperator g).comp
        (compactKernelOperator (μ := volume.restrict D) (ν := volume) hc hs).adjoint) f =ᵐ[volume]
      fullNormalAmplitudeKernel (μ := volume.restrict D) t (fun _ _ ↦ 1) g f := by
  have hmul := multiplicationOperator_coeFn g
    ((compactKernelOperator (μ := volume.restrict D) (ν := volume) hc hs).adjoint f)
  have hadj := compactKernelOperator_adjoint_ae_integral (μ := volume.restrict D) hc hs f
  filter_upwards [compactKernelOperator_ae_integral (ν := volume) hc hs
    (multiplicationOperator g ((compactKernelOperator (μ := volume.restrict D) (ν := volume) hc hs).adjoint f))]
    with x hx
  change compactKernelOperator (ν := volume) hc hs
    (multiplicationOperator g ((compactKernelOperator (μ := volume.restrict D) (ν := volume) hc hs).adjoint f)) x = _
  rw [hx]
  calc
    _ = ∫ u in D, t x u * (g u * ∫ y, star (t y u) * f y) := by
      apply integral_congr_ae
      filter_upwards [hmul, hadj] with u hu ha
      rw [hu, ha]
    _ = _ := by
      simpa only [fullNormalAmplitudeKernel, mul_one] using
        integral_compactCrossKernel_swap D hc hs hc hs g f x

/-- The exact full oscillatory kernel of the constructed masked normal
operator (`app:ch_osc:eq:osc-exact-normal-kernel`). Both physical positions
remain independent; the normalization is squared and the phase is their
difference. The parent supplies the paper's normalization and subsequent
change of variables. -/
theorem compactOscillatoryNormalOperator_ae_integral
    {n : ℕ} (D : Set (Euclidean n)) (scale K : ℝ)
    {φ : Euclidean n → Euclidean n → ℝ}
    {a : Euclidean n → Euclidean n → Fin r → ℂ}
    (hφ : Continuous (Function.uncurry φ))
    (ha : ∀ i, Continuous (fun p : Euclidean n × Euclidean n ↦ a p.1 p.2 i))
    (hs : ∀ i, HasCompactSupport (fun p : Euclidean n × Euclidean n ↦ a p.1 p.2 i))
    (g : Lp ℂ ∞ (volume.restrict D)) (f : NormalOutputL2 n r) (i : Fin r) :
    (compactOscillatoryNormalOperator D scale K hφ ha hs g f) i =ᵐ[volume]
      fun x ↦ ∑ j, ∫ y, (((scale ^ 2 : ℝ) : ℂ) *
        ∫ u in D, oscillatoryFactor K (φ x u - φ y u) *
          (a x u i * star (a y u j)) * g u) * f j y := by
  have h := compactVectorKernelOperator_cross_ae_integral D
    (fun i ↦ continuous_normalizedOscillatoryKernel scale K
      (a := fun x u ↦ a x u i) hφ (ha i))
    (fun i ↦ hasCompactSupport_normalizedOscillatoryKernel scale K φ
      (a := fun x u ↦ a x u i) (hs i))
    (fun j ↦ continuous_normalizedOscillatoryKernel scale K
      (a := fun y u ↦ a y u j) hφ (ha j))
    (fun j ↦ hasCompactSupport_normalizedOscillatoryKernel scale K φ
      (a := fun y u ↦ a y u j) (hs j)) g f i
  change (compactOscillatoryNormalOperator D scale K hφ ha hs g f) i =ᵐ[volume] _ at h
  refine h.trans (Eventually.of_forall fun x ↦ ?_)
  apply Finset.sum_congr rfl
  intro j _
  apply integral_congr_ae
  apply Eventually.of_forall
  intro y
  dsimp only
  rw [← integral_const_mul]
  congr 2
  funext u
  rw [normalizedOscillatoryKernel_mul_star]
  ring

end JanetCartan.NormalComparison
