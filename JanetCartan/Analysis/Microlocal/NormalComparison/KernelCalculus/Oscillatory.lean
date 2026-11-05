module

public import JanetCartan.Analysis.Microlocal.NormalComparison.KernelCalculus.Vector
public import JanetCartan.Analysis.Microlocal.NormalComparison.MaskSymbols

/-!
# Compact oscillatory operator calculus

Construction of the actual scalar-to-vector operator and its Hilbert adjoint
for `app:ch_osc:prop:osc-normal`. Parameter differentiation and the transport
channel identification are separate remaining steps.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal Topology ContDiff

namespace JanetCartan.NormalComparison

variable {n r : ℕ}

/-- The literal scalar kernel with generic real normalization in
`app:ch_osc:prop:osc-normal`. The parent supplies `(K/(2π))^(n/2)`. -/
def normalizedOscillatoryKernel (scale K : ℝ)
    (φ : Euclidean n → Euclidean n → ℝ)
    (a : Euclidean n → Euclidean n → ℂ) (x u : Euclidean n) : ℂ :=
  (scale : ℂ) * oscillatoryFactor K (φ x u) * a x u

/-- Joint continuity of each normalized kernel entry in
`app:ch_osc:prop:osc-normal`. -/
theorem continuous_normalizedOscillatoryKernel (scale K : ℝ)
    {φ : Euclidean n → Euclidean n → ℝ} {a : Euclidean n → Euclidean n → ℂ}
    (hφ : Continuous (Function.uncurry φ)) (ha : Continuous (Function.uncurry a)) :
    Continuous (Function.uncurry (normalizedOscillatoryKernel scale K φ a)) := by
  exact (continuous_const.mul
    ((continuous_const.mul (Complex.continuous_ofReal.comp (continuous_const.mul hφ))).cexp)).mul ha

/-- Multiplying by the phase and normalization preserves compact amplitude
support in `app:ch_osc:prop:osc-normal`. -/
theorem hasCompactSupport_normalizedOscillatoryKernel (scale K : ℝ)
    (φ : Euclidean n → Euclidean n → ℝ) {a : Euclidean n → Euclidean n → ℂ}
    (ha : HasCompactSupport (Function.uncurry a)) :
    HasCompactSupport (Function.uncurry (normalizedOscillatoryKernel scale K φ a)) :=
  ha.mul_left

/-- The exact phase-difference factor in the full normal kernel of
`app:ch_osc:eq:osc-exact-normal-kernel`. -/
theorem oscillatoryFactor_mul_star (K θ η : ℝ) :
    oscillatoryFactor K θ * star (oscillatoryFactor K η) =
      oscillatoryFactor K (θ - η) := by
  unfold oscillatoryFactor
  change Complex.exp _ * starRingEnd ℂ (Complex.exp _) = _
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_sub,
    Complex.ofReal_mul]
  ring

/-- The generic real normalization is squared exactly, with both physical
positions independent (`app:ch_osc:eq:osc-exact-normal-kernel`). -/
theorem normalizedOscillatoryKernel_mul_star (scale K : ℝ)
    (φ : Euclidean n → Euclidean n → ℝ)
    (a b : Euclidean n → Euclidean n → ℂ) (x y u : Euclidean n) :
    normalizedOscillatoryKernel scale K φ a x u *
        star (normalizedOscillatoryKernel scale K φ b y u) =
      ((scale ^ 2 : ℝ) : ℂ) * oscillatoryFactor K (φ x u - φ y u) *
        (a x u * star (b y u)) := by
  simp only [normalizedOscillatoryKernel, star_mul, Complex.star_def,
    Complex.conj_ofReal, Complex.ofReal_pow]
  rw [← oscillatoryFactor_mul_star]
  change _ = (scale : ℂ) ^ 2 *
    (oscillatoryFactor K (φ x u) * starRingEnd ℂ (oscillatoryFactor K (φ y u))) *
      (a x u * starRingEnd ℂ (b y u))
  ring

/-- The actual oscillatory operator of `app:ch_osc:prop:osc-normal`, defined
on all of the input L² space with full physical-space vector output. -/
def compactOscillatoryOperator (D : Set (Euclidean n)) (scale K : ℝ)
    {φ : Euclidean n → Euclidean n → ℝ}
    {a : Euclidean n → Euclidean n → Fin r → ℂ}
    (hφ : Continuous (Function.uncurry φ))
    (ha : ∀ i, Continuous (fun p : Euclidean n × Euclidean n ↦ a p.1 p.2 i))
    (hs : ∀ i, HasCompactSupport (fun p : Euclidean n × Euclidean n ↦ a p.1 p.2 i)) :
    Lp ℂ 2 (volume.restrict D) →L[ℂ] NormalOutputL2 n r :=
  compactVectorKernelOperator D
    (t := fun i ↦ normalizedOscillatoryKernel scale K φ (fun x u ↦ a x u i))
    (fun i ↦ continuous_normalizedOscillatoryKernel scale K
      (a := fun x u ↦ a x u i) hφ (ha i))
    (fun i ↦ hasCompactSupport_normalizedOscillatoryKernel scale K φ
      (a := fun x u ↦ a x u i) (hs i))

/-- The constructed operator has the literal input integral from
`app:ch_osc:prop:osc-normal`, with no operator-existence hypothesis. -/
theorem compactOscillatoryOperator_ae_integral (D : Set (Euclidean n)) (scale K : ℝ)
    {φ : Euclidean n → Euclidean n → ℝ}
    {a : Euclidean n → Euclidean n → Fin r → ℂ}
    (hφ : Continuous (Function.uncurry φ))
    (ha : ∀ i, Continuous (fun p : Euclidean n × Euclidean n ↦ a p.1 p.2 i))
    (hs : ∀ i, HasCompactSupport (fun p : Euclidean n × Euclidean n ↦ a p.1 p.2 i))
    (h : Lp ℂ 2 (volume.restrict D)) (i : Fin r) :
    (compactOscillatoryOperator D scale K hφ ha hs h) i =ᵐ[volume]
      fun x ↦ ∫ u in D, (scale : ℂ) * oscillatoryFactor K (φ x u) * a x u i * h u :=
  compactVectorKernelOperator_ae_integral D
    (t := fun i ↦ normalizedOscillatoryKernel scale K φ (fun x u ↦ a x u i))
    (fun i ↦ continuous_normalizedOscillatoryKernel scale K
      (a := fun x u ↦ a x u i) hφ (ha i))
    (fun i ↦ hasCompactSupport_normalizedOscillatoryKernel scale K φ
      (a := fun x u ↦ a x u i) (hs i)) h i

/-- The masked normal operator is composed with the actual Hilbert adjoint,
for `app:ch_osc:eq:osc-exact-normal-kernel`. -/
def compactOscillatoryNormalOperator (D : Set (Euclidean n)) (scale K : ℝ)
    {φ : Euclidean n → Euclidean n → ℝ}
    {a : Euclidean n → Euclidean n → Fin r → ℂ}
    (hφ : Continuous (Function.uncurry φ))
    (ha : ∀ i, Continuous (fun p : Euclidean n × Euclidean n ↦ a p.1 p.2 i))
    (hs : ∀ i, HasCompactSupport (fun p : Euclidean n × Euclidean n ↦ a p.1 p.2 i))
    (g : Lp ℂ ∞ (volume.restrict D)) : NormalOutputL2 n r →L[ℂ] NormalOutputL2 n r :=
  let T := compactOscillatoryOperator D scale K hφ ha hs
  T.comp ((AmplitudeBound.multiplicationOperator g).comp T.adjoint)

end JanetCartan.NormalComparison
