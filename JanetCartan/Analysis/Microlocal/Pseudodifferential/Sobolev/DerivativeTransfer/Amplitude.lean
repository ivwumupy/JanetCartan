module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Realization

/-!
# Physical derivatives of the full scalar amplitude

The amplitude algebra for `app:ch_regular_base:eq:graph-derivative-transfer`
and the order-minus-one reduction in `app:ch_regular_base:eq:fio-input`.
Every derivative acts on the entire amplitude, including its physical masks.
-/

@[expose] public noncomputable section
open Filter
open scoped ContDiff Topology RealInnerProductSpace
open JanetCartan.AmplitudeBound

namespace JanetCartan.Pseudodifferential
variable {n d : ℕ}

/-- `app:ch_regular_base:eq:graph-derivative-transfer`: ordered derivatives
compose by concatenation, with the outer derivatives first. -/
theorem euclideanCoordinateDerivList_append (is js : List (Fin n))
    (f : EuclideanSpace ℝ (Fin n) → ℂ) :
    euclideanCoordinateDerivList (is ++ js) f =
      euclideanCoordinateDerivList is (euclideanCoordinateDerivList js f) := by
  induction is with
  | nil => rfl
  | cons i is ih => simp only [List.cons_append, euclideanCoordinateDerivList, ih]

/-- `app:ch_regular_base:eq:graph-derivative-transfer`: differentiation of a
sum of smooth complete amplitudes. -/
theorem euclideanCoordinateDerivList_add
    {f g : EuclideanSpace ℝ (Fin n) → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (is : List (Fin n)) :
    euclideanCoordinateDerivList is (fun z ↦ f z + g z) =
      fun z ↦ euclideanCoordinateDerivList is f z + euclideanCoordinateDerivList is g z := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [euclideanCoordinateDerivList, ih]
    funext z
    exact congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℂ ↦ L (EuclideanSpace.single i 1))
      (fderiv_add ((contDiff_euclideanCoordinateDerivList hf is).differentiable (by simp) z)
        ((contDiff_euclideanCoordinateDerivList hg is).differentiable (by simp) z))

/-- `app:ch_regular_base:eq:fio-input`: frequency-only factors commute with
all physical derivatives. -/
theorem euclideanCoordinateDerivList_const_mul
    {f : EuclideanSpace ℝ (Fin n) → ℂ} (hf : ContDiff ℝ ∞ f)
    (a : ℂ) (is : List (Fin n)) :
    euclideanCoordinateDerivList is (fun z ↦ a * f z) =
      fun z ↦ a * euclideanCoordinateDerivList is f z := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [euclideanCoordinateDerivList, ih]
    funext z
    rw [fderiv_const_mul ((contDiff_euclideanCoordinateDerivList hf is).differentiable
      (by simp) z)]
    rfl

/-- `app:ch_regular_base:eq:graph-derivative-transfer`: derivatives preserve
the fixed physical box, including at its boundary. -/
theorem supportedInCenteredBox_coordinateDerivList
    {f : EuclideanSpace ℝ (Fin n) → ℂ} {R : ℝ} (hs : SupportedInCenteredBox R f)
    (is : List (Fin n)) : SupportedInCenteredBox R (euclideanCoordinateDerivList is f) := by
  induction is with
  | nil => exact hs
  | cons j js ih =>
    intro z hz i
    by_contra hn
    have hlt : R < |z i| := lt_of_not_ge hn
    have he : euclideanCoordinateDerivList js f =ᶠ[𝓝 z] (fun _ ↦ 0) := by
      filter_upwards [(isOpen_lt continuous_const ((EuclideanSpace.proj i).continuous.abs)).mem_nhds hlt] with w hw
      exact Classical.byContradiction (fun h ↦ (not_le_of_gt hw) (ih w h i))
    have hz0 := congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℂ ↦ L (EuclideanSpace.single j 1))
      (he.fderiv (𝕜 := ℝ)).self_of_nhds
    exact hz (by simpa [euclideanCoordinateDerivList] using hz0)

/-- `app:ch_regular_base:eq:graph-derivative-transfer`: output coordinate in
the paired physical position. -/
def physicalOutputIndex (i : Fin d) : Fin (2 * d) := ⟨i.val, by omega⟩

/-- `app:ch_regular_base:eq:graph-derivative-transfer`: source coordinate in
the paired physical position. -/
def physicalSourceIndex (i : Fin d) : Fin (2 * d) := ⟨d + i.val, by omega⟩

/-- `app:ch_regular_base:eq:graph-derivative-transfer`: the full amplitude
created by transferring one output derivative to the source. -/
def transferAmplitude
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (i : Fin d) (ξ : EuclideanSpace ℝ (Fin d)) (z : EuclideanSpace ℝ (Fin (2 * d))) : ℂ :=
  euclideanCoordinateDerivList [physicalOutputIndex i] (b ξ) z +
    euclideanCoordinateDerivList [physicalSourceIndex i] (b ξ) z

/-- `app:ch_regular_base:eq:fio-input`: the first output derivative amplitude
for the unit-period Fourier convention. -/
def outputDerivativeAmplitude
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (i : Fin d) (ξ : EuclideanSpace ℝ (Fin d)) (z : EuclideanSpace ℝ (Fin (2 * d))) : ℂ :=
  euclideanCoordinateDerivList [physicalOutputIndex i] (b ξ) z +
    (2 * Real.pi * Complex.I * (ξ i : ℝ)) * b ξ z

/-- `app:ch_regular_base:eq:graph-derivative-transfer`: the transferred
amplitude remains smooth in both physical positions. -/
theorem contDiff_transferAmplitude
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hb : ∀ ξ, ContDiff ℝ ∞ (b ξ)) (i : Fin d) (ξ : EuclideanSpace ℝ (Fin d)) :
    ContDiff ℝ ∞ (transferAmplitude b i ξ) :=
  (contDiff_euclideanCoordinateDerivList (hb ξ) _).add
    (contDiff_euclideanCoordinateDerivList (hb ξ) _)

/-- `app:ch_regular_base:eq:graph-derivative-transfer`: physical coordinate
derivatives preserve joint smoothness with the frequency parameter. -/
theorem contDiff_uncurry_euclideanCoordinateDerivList
    {b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin n) → ℂ}
    (hb : ContDiff ℝ ∞ (Function.uncurry b)) (is : List (Fin n)) :
    ContDiff ℝ ∞ (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n) ↦
      euclideanCoordinateDerivList is (b p.1) p.2) := by
  induction is with
  | nil => exact hb
  | cons i is ih =>
    have h := ih.comp (f := fun p :
      (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin n) ↦
        (p.1.1, p.2)) (by fun_prop)
    exact h.fderiv_apply contDiff_snd contDiff_const (by simp)

/-- `app:ch_regular_base:eq:graph-derivative-transfer`: joint smoothness of
the transferred full amplitude. -/
theorem contDiff_uncurry_transferAmplitude
    {b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ}
    (hb : ContDiff ℝ ∞ (Function.uncurry b)) (i : Fin d) :
    ContDiff ℝ ∞ (Function.uncurry (transferAmplitude b i)) :=
  (contDiff_uncurry_euclideanCoordinateDerivList hb _).add
    (contDiff_uncurry_euclideanCoordinateDerivList hb _)

/-- `app:ch_regular_base:eq:fio-input`: the gain-one amplitude is jointly
smooth, including at zero frequency. -/
theorem contDiff_uncurry_outputDerivativeAmplitude
    {b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ}
    (hb : ContDiff ℝ ∞ (Function.uncurry b)) (i : Fin d) :
    ContDiff ℝ ∞ (Function.uncurry (outputDerivativeAmplitude b i)) := by
  apply (contDiff_uncurry_euclideanCoordinateDerivList hb _).add
  exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
    ((EuclideanSpace.proj i).contDiff.comp contDiff_fst))).mul hb

/-- `app:ch_regular_base:eq:graph-derivative-transfer`: transfer preserves the
original physical box and every mask already included in the amplitude. -/
theorem supportedInCenteredBox_transferAmplitude
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (R : ℝ) (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (i : Fin d) (ξ) :
    SupportedInCenteredBox R (transferAmplitude b i ξ) := by
  intro z hz
  by_cases hx : euclideanCoordinateDerivList [physicalOutputIndex i] (b ξ) z = 0
  · exact supportedInCenteredBox_coordinateDerivList (hs ξ) [physicalSourceIndex i] z
      (by simpa [transferAmplitude, hx] using hz)
  · exact supportedInCenteredBox_coordinateDerivList (hs ξ) [physicalOutputIndex i] z hx

/-- `app:ch_regular_base:eq:fio-input`: the gain-one amplitude retains the
fixed physical support. -/
theorem supportedInCenteredBox_outputDerivativeAmplitude
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (R : ℝ) (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (i : Fin d) (ξ) :
    SupportedInCenteredBox R (outputDerivativeAmplitude b i ξ) := by
  intro z hz
  by_cases hx : euclideanCoordinateDerivList [physicalOutputIndex i] (b ξ) z = 0
  · exact hs ξ z (by intro h; exact hz (by simp [outputDerivativeAmplitude, hx, h]))
  · exact supportedInCenteredBox_coordinateDerivList (hs ξ) [physicalOutputIndex i] z hx

/-- `app:ch_regular_base:eq:graph-derivative-transfer`: one transfer consumes
exactly one additional primitive physical derivative. -/
theorem hasAmplitudeDerivativeBound_transferAmplitude
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hb : ∀ ξ, ContDiff ℝ ∞ (b ξ)) (i : Fin d) (N : ℕ) (A : ℝ)
    (hA : HasAmplitudeDerivativeBound b (N + 1) A) :
    HasAmplitudeDerivativeBound (transferAmplitude b i) N (2 * A) := by
  intro ξ is his z
  unfold transferAmplitude
  rw [euclideanCoordinateDerivList_add
    (contDiff_euclideanCoordinateDerivList (hb ξ) _)
    (contDiff_euclideanCoordinateDerivList (hb ξ) _)]
  simp only [← euclideanCoordinateDerivList_append]
  exact (norm_add_le _ _).trans (by
    have h₁ := hA ξ (is ++ [physicalOutputIndex i]) (by simpa using Nat.add_le_add_right his 1) z
    have h₂ := hA ξ (is ++ [physicalSourceIndex i]) (by simpa using Nat.add_le_add_right his 1) z
    linarith)

/-- `app:ch_regular_base:eq:fio-input`: the order-minus-one physical budget
implies an order-zero budget for the first output derivative amplitude. -/
theorem hasAmplitudeDerivativeBound_outputDerivativeAmplitude
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hb : ∀ ξ, ContDiff ℝ ∞ (b ξ)) (i : Fin d) (N : ℕ) (A : ℝ)
    (hA : ∀ ξ is, is.length ≤ N + 1 → ∀ z,
      (1 + ‖ξ‖) * ‖euclideanCoordinateDerivList is (b ξ) z‖ ≤ A) :
    HasAmplitudeDerivativeBound (outputDerivativeAmplitude b i) N
      ((1 + 2 * Real.pi) * A) := by
  intro ξ is his z
  unfold outputDerivativeAmplitude
  rw [euclideanCoordinateDerivList_add
    (contDiff_euclideanCoordinateDerivList (hb ξ) _) (contDiff_const.mul (hb ξ)),
    euclideanCoordinateDerivList_const_mul (hb ξ), ← euclideanCoordinateDerivList_append]
  have h₀ := hA ξ is (his.trans (Nat.le_succ _)) z
  have h₁ := hA ξ (is ++ [physicalOutputIndex i])
    (by simpa using Nat.add_le_add_right his 1) z
  have hn : ‖euclideanCoordinateDerivList (is ++ [physicalOutputIndex i]) (b ξ) z‖ ≤ A := by
    nlinarith [norm_nonneg ξ, norm_nonneg (euclideanCoordinateDerivList
      (is ++ [physicalOutputIndex i]) (b ξ) z)]
  have hξ : |ξ i| ≤ ‖ξ‖ := PiLp.norm_apply_le ξ i
  have hm : ‖(2 * (Real.pi : ℂ) * Complex.I * (ξ i : ℝ)) *
      euclideanCoordinateDerivList is (b ξ) z‖ ≤ 2 * Real.pi * A := by
    simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, Complex.norm_I, mul_one]
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    nlinarith [norm_nonneg (euclideanCoordinateDerivList is (b ξ) z)]
  exact (norm_add_le _ _).trans (by nlinarith)

end JanetCartan.Pseudodifferential
