module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.ComplexModulation.Coefficients
public import JanetCartan.Geometry.IsometricEmbedding.Waves.WKB.Amplitude

/-!
# Exact complex modulation of the actual leading reconstruction

Prove `app:ch_waves:eq:exact-W-amplitude` for the published zero-source complex
response, identified on both quadratures with the canonical real reconstruction.
The principal amplitude is the complex extension of the literal `principalNormal`
from `app:ch_waves:eq:arbitrary-b-amplitudes`. The same coefficients instantiate
`WKB.firstOrder_reconstruction_twoTermWave`, including complex correction amplitudes.

The product identities use only pointwise differentiability of the phase and
amplitude and a nonzero small parameter. The local family statement allows
application to the actual smooth phase and amplitude from the null-transport and
leading-wave constructions. Producing those objects, their gaps and their tame
bounds remains with those constructions; no such existence result is claimed here.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
open JanetCartan.AmbientResponse JanetCartan.ResponseTransfer

set_option backward.isDefEq.respectTransparency false

namespace JanetCartan.LeadingWave

/-- Exact modulation of the actual canonical complex reconstruction, before
inserting the small-parameter prefactor (`app:ch_waves:eq:exact-W-amplitude`).
Neither a characteristic equation nor transport is needed. -/
theorem completedVariationComplex_zero_modulated {n N : ℕ}
    (F : Euclidean n → Euclidean N) {ρ : ℝ} {S : Euclidean n → ℝ}
    {b : Euclidean n → EuclideanSpace ℂ (Fin n)} {x : Euclidean n}
    (hS : DifferentiableAt ℝ S x) (hb : DifferentiableAt ℝ b x) :
    completedVariationComplex F (modulatedWave ρ S b) 0 x =
      waveCarrier ρ S x • ((Complex.I * (ρ : ℂ)) •
        canonicalPrincipalNormalComplex F x (scalarDifferential S x) (b x) +
        completedVariationComplex F b 0 x) := by
  simpa only [Pi.zero_apply, zero_smul, smul_zero, ← Pi.zero_def,
    responseReconstructionAmplitude_zero] using
      completedVariationComplex_modulated F 0 0 hS hb

/-- Constant complex scaling of the actual zero-source operator, used for
the prefactor in `app:ch_waves:eq:exact-W-amplitude`. -/
theorem completedVariationComplex_zero_const_smul {n N : ℕ}
    (F : Euclidean n → Euclidean N) (c : ℂ)
    {b : Euclidean n → EuclideanSpace ℂ (Fin n)} {x : Euclidean n}
    (hb : DifferentiableAt ℝ b x) :
    completedVariationComplex F (fun y ↦ c • b y) 0 x =
      c • completedVariationComplex F b 0 x := by
  have hb' : DifferentiableAt ℝ (fun y ↦ c • b y) x := hb.const_smul c
  rw [completedVariationComplex_zero_eq_firstOrder F hb',
    completedVariationComplex_zero_eq_firstOrder F hb]
  have hd : fderiv ℝ (fun y ↦ c • b y) x = c • fderiv ℝ b x :=
    (hb.hasFDerivAt.const_smul c).fderiv
  simp only [WKB.firstOrderApply, partialDeriv, hd,
    _root_.smul_apply, map_smul, ← Finset.smul_sum, smul_add]

/-- The exact small-parameter product identity
`app:ch_waves:eq:exact-W-amplitude` for an arbitrary complex amplitude. Both
`i * τ * ν` and `τ² * V(b)` are retained, with physical frequency `τ⁻¹`. -/
theorem completedVariationComplex_zero_tau_modulated {n N : ℕ}
    (F : Euclidean n → Euclidean N) {τ : ℝ} (hτ : τ ≠ 0)
    {S : Euclidean n → ℝ} {b : Euclidean n → EuclideanSpace ℂ (Fin n)}
    {x : Euclidean n} (hS : DifferentiableAt ℝ S x) (hb : DifferentiableAt ℝ b x) :
    completedVariationComplex F
      (fun y ↦ (τ : ℂ) ^ 2 • modulatedWave τ⁻¹ S b y) 0 x =
      waveCarrier τ⁻¹ S x • ((Complex.I * (τ : ℂ)) •
        canonicalPrincipalNormalComplex F x (scalarDifferential S x) (b x) +
        (τ : ℂ) ^ 2 • completedVariationComplex F b 0 x) := by
  have hm : DifferentiableAt ℝ (modulatedWave τ⁻¹ S b) x :=
    (hasFDerivAt_waveCarrier hS).differentiableAt.smul hb
  rw [completedVariationComplex_zero_const_smul F _ hm,
    completedVariationComplex_zero_modulated F hS hb, smul_comm ((τ : ℂ) ^ 2), smul_add,
    smul_smul]
  have hc : (τ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hτ
  have he : (τ : ℂ) ^ 2 * (Complex.I * ((τ⁻¹ : ℝ) : ℂ)) = Complex.I * (τ : ℂ) := by
    push_cast
    field_simp
  rw [he]

/-- The real-amplitude specialization of `app:ch_waves:eq:exact-W-amplitude`,
using the shared inclusion and the literal `principalNormal` and `reconstruction`. -/
theorem completedVariationComplex_zero_tau_modulated_real {n N : ℕ}
    (F : Euclidean n → Euclidean N) {τ : ℝ} (hτ : τ ≠ 0)
    {S : Euclidean n → ℝ} {b : Euclidean n → Euclidean n}
    {x : Euclidean n} (hS : DifferentiableAt ℝ S x) (hb : DifferentiableAt ℝ b x) :
    completedVariationComplex F
      (fun y ↦ (τ : ℂ) ^ 2 • waveCarrier τ⁻¹ S y • euclideanComplexInclusion (b y)) 0 x =
      waveCarrier τ⁻¹ S x • ((Complex.I * (τ : ℂ)) • euclideanComplexInclusion
        (principalNormal (canonicalNormalCompletion F x) (scalarDifferential S x) (b x)) +
        (τ : ℂ) ^ 2 • euclideanComplexInclusion
          (reconstruction F (canonicalNormalCompletion F) b x)) := by
  have hc : DifferentiableAt ℝ (fun y ↦ euclideanComplexInclusion (b y)) x :=
    euclideanComplexInclusion.differentiableAt.comp x hb
  simpa only [modulatedWave, canonicalPrincipalNormalComplex_inclusion,
    completedVariationComplex_zero_inclusion F hb] using
      completedVariationComplex_zero_tau_modulated F hτ hS hc

/-- Pointwise WKB specialization of `app:ch_waves:eq:exact-W-amplitude`
for the actual canonical coefficients, retaining both quadratures of both
amplitudes. The phase and amplitudes need only be differentiable at this point. -/
theorem completedVariationComplex_zero_twoTermWave {n N : ℕ}
    (F : Euclidean n → Euclidean N) {lam : ℝ} (hlam : lam ≠ 0)
    {S : Euclidean n → ℝ} {a b : Euclidean n → EuclideanSpace ℂ (Fin n)}
    {x : Euclidean n} (hS : DifferentiableAt ℝ S x)
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x) :
    completedVariationComplex F (twoTermWave lam S a b) 0 x =
      modulatedWave lam S (WKB.reconstructionAmplitude lam
        (fun y ↦ canonicalPrincipalNormalComplex F y (scalarDifferential S y) (a y))
        (fun y ↦ canonicalPrincipalNormalComplex F y (scalarDifferential S y) (b y))
        (fun y ↦ completedVariationComplex F a 0 y)
        (fun y ↦ completedVariationComplex F b 0 y)) x := by
  have ht : DifferentiableAt ℝ (twoTermWave lam S a b) x :=
    (hasFDerivAt_waveCarrier hS).differentiableAt.smul
      ((ha.add (hb.const_smul ((lam : ℂ)⁻¹))).const_smul (((lam : ℂ)⁻¹) ^ 2))
  rw [completedVariationComplex_zero_eq_firstOrder F ht,
    WKB.firstOrder_twoTermWave_expansion _ _ hlam hS ha hb]
  simp only [canonicalReconstruction_principalSymbol,
    ← completedVariationComplex_zero_eq_firstOrder F ha,
    ← completedVariationComplex_zero_eq_firstOrder F hb,
    modulatedWave, WKB.reconstructionAmplitude, smul_smul]
  module

/-- The actual reconstruction instantiates
`WKB.firstOrder_reconstruction_twoTermWave` with its own coefficients. This is
the displacement polynomial from `app:ch_waves:eq:exact-W-amplitude`, without
any eikonal or transport premise. -/
theorem completedVariationComplex_zero_twoTermWave_family {n N : ℕ}
    (F : Euclidean n → Euclidean N) {lam : ℝ} (hlam : lam ≠ 0)
    {S : Euclidean n → ℝ} {a b : Euclidean n → EuclideanSpace ℂ (Fin n)}
    (hS : Differentiable ℝ S) (ha : Differentiable ℝ a) (hb : Differentiable ℝ b) :
    completedVariationComplex F (twoTermWave lam S a b) 0 =
      modulatedWave lam S (WKB.reconstructionAmplitude lam
        (fun y ↦ canonicalPrincipalNormalComplex F y (scalarDifferential S y) (a y))
        (fun y ↦ canonicalPrincipalNormalComplex F y (scalarDifferential S y) (b y))
        (fun y ↦ completedVariationComplex F a 0 y)
        (fun y ↦ completedVariationComplex F b 0 y)) := by
  have he {u : Euclidean n → EuclideanSpace ℂ (Fin n)} (hu : Differentiable ℝ u) :
      completedVariationComplex F u 0 =
        WKB.firstOrderApply (canonicalReconstructionDerivative F)
          (canonicalReconstructionValue F) u := by
    funext x
    exact completedVariationComplex_zero_eq_firstOrder F (hu x)
  have ht : Differentiable ℝ (twoTermWave lam S a b) := fun x ↦
    (hasFDerivAt_waveCarrier (hS x)).differentiableAt.smul
      (((ha x).add ((hb x).const_smul ((lam : ℂ)⁻¹))).const_smul (((lam : ℂ)⁻¹) ^ 2))
  rw [he ht, WKB.firstOrder_reconstruction_twoTermWave _ _ hlam hS ha hb,
    ← he ha, ← he hb]
  simp only [canonicalReconstruction_principalSymbol]

/-- The physical carrier at frequency `τ⁻¹` is exactly the exponential
in `app:ch_waves:eq:exact-W-amplitude`; no torus-frequency factor is inserted. -/
theorem waveCarrier_inv_eq_exp_div {n : ℕ} (τ : ℝ) (S : Euclidean n → ℝ)
    (x : Euclidean n) :
    waveCarrier τ⁻¹ S x = Complex.exp (Complex.I * (S x : ℂ) / (τ : ℂ)) := by
  unfold waveCarrier
  congr 1
  simp only [Complex.ofReal_inv, div_eq_mul_inv]
  ring

/-- The literal exponential form of `app:ch_waves:eq:exact-W-amplitude`
for the actual zero-source complex operator and the canonical real reconstruction.
The leading-wave construction supplies the differentiable phase and amplitude. -/
theorem completedVariationComplex_zero_exact_amplitude {n N : ℕ}
    (F : Euclidean n → Euclidean N) {τ : ℝ} (hτ : τ ≠ 0)
    {S : Euclidean n → ℝ} {b : Euclidean n → Euclidean n}
    {x : Euclidean n} (hS : DifferentiableAt ℝ S x) (hb : DifferentiableAt ℝ b x) :
    completedVariationComplex F
      (fun y ↦ (τ : ℂ) ^ 2 • Complex.exp (Complex.I * (S y : ℂ) / (τ : ℂ)) •
        euclideanComplexInclusion (b y)) 0 x =
      Complex.exp (Complex.I * (S x : ℂ) / (τ : ℂ)) •
        ((Complex.I * (τ : ℂ)) • euclideanComplexInclusion
          (principalNormal (canonicalNormalCompletion F x) (scalarDifferential S x) (b x)) +
        (τ : ℂ) ^ 2 • euclideanComplexInclusion
          (reconstruction F (canonicalNormalCompletion F) b x)) := by
  simpa only [waveCarrier_inv_eq_exp_div] using
    completedVariationComplex_zero_tau_modulated_real F hτ hS hb

/-- Local family form of `app:ch_waves:eq:exact-W-amplitude` on any open
domain. Local differentiability suffices, so local smooth phase and transport
outputs instantiate this identity without global extensions. -/
theorem completedVariationComplex_zero_exact_amplitude_on {n N : ℕ}
    (F : Euclidean n → Euclidean N) {τ : ℝ} (hτ : τ ≠ 0)
    {S : Euclidean n → ℝ} {b : Euclidean n → Euclidean n} {s : Set (Euclidean n)}
    (hs : IsOpen s) (hS : DifferentiableOn ℝ S s) (hb : DifferentiableOn ℝ b s) :
    Set.EqOn (completedVariationComplex F
      (fun y ↦ (τ : ℂ) ^ 2 • Complex.exp (Complex.I * (S y : ℂ) / (τ : ℂ)) •
        euclideanComplexInclusion (b y)) 0)
      (fun x ↦ Complex.exp (Complex.I * (S x : ℂ) / (τ : ℂ)) •
        ((Complex.I * (τ : ℂ)) • euclideanComplexInclusion
          (principalNormal (canonicalNormalCompletion F x) (scalarDifferential S x) (b x)) +
        (τ : ℂ) ^ 2 • euclideanComplexInclusion
          (reconstruction F (canonicalNormalCompletion F) b x))) s := by
  intro x hx
  exact completedVariationComplex_zero_exact_amplitude F hτ
    ((hS x hx).differentiableAt (hs.mem_nhds hx))
    ((hb x hx).differentiableAt (hs.mem_nhds hx))

end JanetCartan.LeadingWave
