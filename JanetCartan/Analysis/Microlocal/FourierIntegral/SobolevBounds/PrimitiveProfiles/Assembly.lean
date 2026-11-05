module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.PrimitiveProfiles.Profiles
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.PrimitiveProfiles.PhaseNormalization

/-!
# Primitive profiles on a normalized carrier

Step 3 of `app:ch_regular_base:thm:actual-calculus`. The low operator reserve is
`μ₀`; the phase-to-primitive shift is two, so the final fixed shift is `μ₀ + 2`.
The amplitude seminorm is `normalizedSeminorm` of the complete matrix amplitude,
including both physical masks. The phase seminorm is `cNorm` of
`fun p => S p.1.1 p.2` on the same normalized ball; degree-one homogeneity
identifies this with the phase divided by the dilation radius.

The geometric inputs describe a fixed buffered chart and its dilated physical
region. Symbol-class finiteness of the amplitude is explicit. Scalar finiteness,
interpolation, low bounds, and high inverse bounds are proved from the phase,
its fixed low seminorm, and its actual zeroth-order inverse gap. The parent
`jc-deduce-fio-strong-sobolev` must instantiate the geometry and low L² reserve.
-/

@[expose] public noncomputable section
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.PrimitiveProfiles
open FullAmplitudePrimitiveBudget FullAmplitudePrimitiveBudget.Local FirstOutputJets
variable {n r : ℕ}

/-- Ordinary smoothness on the dilated region gives normalized smoothness of
the complete field, including all masks. Source: Step 3 before
`app:ch_regular_base:eq:fio-input`. -/
theorem contDiffOn_normalizedField_of_dilations
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U V : Set (Point n)} {f : Point n → F}
    (hf : ContDiffOn ℝ ∞ f V)
    (hrad : ∀ R : ℝ, 1 ≤ R → ∀ p ∈ U, (p.1, R • p.2) ∈ V)
    {R : ℝ} (hR : 1 ≤ R) : ContDiffOn ℝ ∞ (normalizedField R f) U := by
  exact hf.comp (contDiff_fst.prodMk (contDiff_snd.const_smul R)).contDiffOn
    (hrad R hR)

/-- Pass from normalized radii to the frequency weight used by `StrongAssembly`.
The covering condition involves only the fixed carrier, chart, and weight.
Source: `app:ch_regular_base:eq:fio-input`. -/
theorem weighted_jet_le_normalizedSeminorm_on_carrier
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (z : Point n) {δ : ℝ} {U V T : Set (Point n)}
    (hU : IsOpen U) (hV : IsOpen V) (hball : Metric.closedBall z δ ⊆ U)
    (hrad : ∀ R : ℝ, 1 ≤ R → ∀ p ∈ U, (p.1, R • p.2) ∈ V)
    (weight : Euclidean n → ℝ) (hw : ∀ η, 0 ≤ weight η)
    (hcover : ∀ p ∈ T, ∃ R : ℝ, 1 ≤ R ∧ ∃ q ∈ Metric.closedBall z δ,
      p = (q.1, R • q.2) ∧ weight p.2 ≤ R)
    {f : Field n F} (hf : ContDiffOn ℝ ∞ (uncurry f) V)
    (hb : ∀ j, BoundedNormalizedSeminorm (Metric.closedBall z δ) j (uncurry f)) :
    ∀ p ∈ T, ∀ w : List (Coordinate n),
      weight p.2 ^ frequencyOrder w * ‖uncurry (jet w f) p‖ ≤
        normalizedSeminorm (Metric.closedBall z δ) w.length (uncurry f) := by
  intro p hp w
  obtain ⟨R, hR, q, hq, rfl, hweight⟩ := hcover p hp
  exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hw _) hweight _) (norm_nonneg _)).trans
    (weighted_jet_le_normalizedSeminorm z hU hV hball hf
      (fun _ hR ↦ contDiffOn_normalizedField_of_dilations hf hrad hR)
      w (hb _) hR q hq (hrad R hR q (hball hq)))

/-- A fixed baseline and a fixed shift supply every primitive input of
`exists_graph_sobolev_constant_of_weighted_primitives` and its literal-adjoint
counterpart. Constants precede the phase, amplitude, and all high seminorms.
The low bound `L` is chosen before `s`; the high endpoint uses the fixed shift
`μ₀ + 2`. No interpolation or high inverse-jet bound is assumed.
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`.

The carrier `T` can be either `(X₀ ×ˢ Y₀) ×ˢ F₀` or `K₀ ×ˢ F₀` in the two
consumers. The normalized covering condition and the open region `V` are
geometric inputs owed by the Hamilton phase and carrier producers. -/
theorem exists_primitiveProfile_inputs
    (z : Point n) {δ : ℝ} (hδ : 0 < δ) {U V : Set (Point n)}
    (hU : IsOpen U) (hV : IsOpen V) (hball : Metric.closedBall z δ ⊆ U)
    (hrad : ∀ R : ℝ, 1 ≤ R → ∀ p ∈ U, (p.1, R • p.2) ∈ V)
    {X D : Set (Euclidean n)} (hX : IsOpen X) (hD : IsOpen D)
    (hchart : ∀ p ∈ V, p.1.1 ∈ X ∧ p.2 ∈ D)
    (hcone : ∀ R : ℝ, 0 < R → ∀ η ∈ D, R • η ∈ D)
    (μ₀ : ℕ) {M : ℝ} (hM : 0 ≤ M) (B : ℝ) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ s : ℕ, ∃ C I : ℝ, 1 ≤ C ∧ 1 ≤ I ∧
      ∀ (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r),
      ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D) →
      (∀ R : ℝ, 0 < R → ∀ x ∈ X, ∀ η ∈ D, S x (R • η) = R * S x η) →
      (∀ p ∈ V, IsUnit (mixedPhaseMatrix S p.1.1 p.2).det) →
      (∀ p ∈ Metric.closedBall z δ, ‖(mixedPhaseMatrix S p.1.1 p.2)⁻¹‖ ≤ B) →
      ContDiffOn ℝ ∞ (uncurry A) V →
      (∀ j, BoundedNormalizedSeminorm (Metric.closedBall z δ) j (uncurry A)) →
      cNorm (Metric.closedBall z δ) (μ₀ + 2) (fun p : Point n ↦ S p.1.1 p.2) ≤ M →
      normalizedSeminorm (Metric.closedBall z δ) μ₀ (uncurry A) ≤ M →
      let q := primitiveProfile (Metric.closedBall z δ) S A
      let H := C * (1 + normalizedSeminorm (Metric.closedBall z δ) (s + (μ₀ + 2))
        (uncurry A) + cNorm (Metric.closedBall z δ) (s + (μ₀ + 2))
          (fun p : Point n ↦ S p.1.1 p.2))
      (∀ a j, 0 ≤ q a j) ∧ (∀ a, Monotone (q a)) ∧ 1 ≤ H ∧
      (∀ a, q a μ₀ ≤ L) ∧ (∀ a, q a (μ₀ + s) ≤ H) ∧
      (∀ a j, μ₀ < j → j < μ₀ + s →
        q a j ≤ I * q a μ₀ ^ (1 - ((j - μ₀ : ℕ) : ℝ) / s) *
          q a (μ₀ + s) ^ (((j - μ₀ : ℕ) : ℝ) / s)) ∧
      ∀ (T : Set (Point n)) (weight : Euclidean n → ℝ), (∀ η, 0 ≤ weight η) →
        (∀ p ∈ T, ∃ R : ℝ, 1 ≤ R ∧ ∃ v ∈ Metric.closedBall z δ,
          p = (v.1, R • v.2) ∧ weight p.2 ≤ R) →
        (∀ p ∈ T, ∀ w, weight p.2 ^ frequencyOrder w * ‖uncurry (jet w A) p‖ ≤
          q none w.length) ∧
        (∀ p ∈ T, ∀ a w,
          weight p.2 ^ frequencyOrder w * ‖uncurry (jet w (scalarPrimitive S a)) p‖ ≤
            q (some a) w.length) := by
  have hUV : U ⊆ V := by
    intro p hp
    simpa using hrad 1 le_rfl p hp
  have hchartU (p) (hp : p ∈ U) := hchart p (hUV hp)
  obtain ⟨C₀, hC₀, he₀⟩ := exists_normalizedSeminorm_scalarPrimitive_le_phase
    z hδ hU hball hX hD hchartU hcone μ₀ hM B
  refine ⟨1 + M + C₀ * (1 + M), by nlinarith, ?_⟩
  intro s
  obtain ⟨Cₛ, hCₛ, heₛ⟩ := exists_normalizedSeminorm_scalarPrimitive_le_phase
    z hδ hU hball hX hD hchartU hcone (μ₀ + s) hM B
  obtain ⟨I, hI, hi⟩ := exists_primitiveProfile_interpolation (r := r) z hδ hU hball μ₀ s
  refine ⟨1 + Cₛ, I, by linarith, hI, ?_⟩
  intro S A hS hhom hinv hgap hA hbA hlowS hlowA
  dsimp only
  have hlow₂ : cNorm (Metric.closedBall z δ) 2 (fun p : Point n ↦ S p.1.1 p.2) ≤ M :=
    (CNormInterpolation.cNorm_mono _ _ (by omega : 2 ≤ μ₀ + 2)).trans hlowS
  have hreg (a : ScalarIndex n) (j : ℕ) := normalized_scalarPrimitive_regular
    hX hD hcone hS hhom hU hball hchartU (fun p hp ↦ hinv p (hUV hp)) a j
  have hnA (R : ℝ) (hR : 1 ≤ R) := contDiffOn_normalizedField_of_dilations hA hrad hR
  have hn := normalizedSeminorm_nonneg (Metric.closedBall z δ) (s + (μ₀ + 2)) (uncurry A)
  have hp := cNorm_nonneg (Metric.closedBall z δ) (s + (μ₀ + 2))
    (fun p : Point n ↦ S p.1.1 p.2)
  refine ⟨primitiveProfile_nonneg _ S A,
    primitiveProfile_monotone hbA (fun a j ↦ (hreg a j).2.1), ?_, ?_, ?_, ?_, ?_⟩
  · nlinarith
  · intro a
    cases a with
    | none => exact hlowA.trans (by nlinarith)
    | some a =>
      have he := (he₀ S hS hhom hlow₂ (fun p hp ↦ hinv p (hUV hp)) hgap a).trans
        (mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) hlowS) hC₀.le)
      exact he.trans (by linarith)
  · intro a
    cases a with
    | none =>
      have he := normalizedSeminorm_mono (hbA (s + (μ₀ + 2)))
        (by omega : μ₀ + s ≤ s + (μ₀ + 2))
      change normalizedSeminorm _ _ _ ≤ _
      nlinarith
    | some a =>
      have he := heₛ S hS hhom hlow₂ (fun p hp ↦ hinv p (hUV hp)) hgap a
      have heq : μ₀ + s + 2 = s + (μ₀ + 2) := by omega
      rw [heq] at he
      change normalizedSeminorm _ _ _ ≤ _
      nlinarith
  · exact hi S A (fun R hR ↦ (hnA R hR).of_le (by simp))
      (fun a R hR ↦ ((hreg a (μ₀ + s)).1 R hR).of_le (by simp))
      (hbA _) (fun a ↦ (hreg a _).2.1)
  · intro T weight hw hcover
    refine ⟨weighted_jet_le_normalizedSeminorm_on_carrier z hU hV hball hrad
      weight hw hcover hA hbA, ?_⟩
    intro p hp a w
    exact weighted_jet_le_normalizedSeminorm_on_carrier z hU hV hball hrad
      weight hw hcover (contDiffOn_joint_scalarPrimitive hX hD hS hchart hinv a)
      (fun j ↦ (hreg a j).2.1) p hp w

end JanetCartan.FourierIntegral.PrimitiveProfiles
