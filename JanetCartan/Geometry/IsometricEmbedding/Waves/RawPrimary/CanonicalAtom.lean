module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.ComplexModulation
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.Representation

/-!
# Canonical two-term atoms for raw superposition

These formulas use the actual zero-source ambient reconstruction, rather than
an unspecified reconstruction operator. `canonicalAtom` is the integrand of
`app:ch_waves:eq:WKB-W`. Its displacement polynomial and differential matrix
are identified on the original open wave domain, with no global extension.

The phase and two covector amplitudes are still arguments: the full-modulation
transport and the restricted-symbol correction must supply the SAME arguments
in the final construction. The identities here do not assert their existence,
graded estimates, or the raw slice bound.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.RawPrimary
open LeadingWave ResponseTransfer

variable {n N : ℕ}

/-- The actual canonical reconstructed two-term atom, with `λ = τ⁻¹`
(`app:ch_waves:eq:WKB-u`, `app:ch_waves:eq:WKB-W`). -/
def canonicalAtom (F : Euclidean n → Euclidean N) (τ : ℝ)
    (S : Euclidean n × Euclidean (n - 1) → ℝ)
    (b₀ b₁ : Euclidean n × Euclidean (n - 1) → EuclideanSpace ℂ (Fin n))
    (p : Euclidean n × Euclidean (n - 1)) : EuclideanSpace ℂ (Fin N) :=
  completedVariationComplex F
    (twoTermWave τ⁻¹ (fun x ↦ S (x, p.2)) (fun x ↦ b₀ (x, p.2))
      (fun x ↦ b₁ (x, p.2))) 0 p.1

/-- The literal canonical displacement polynomial, retaining all three
inverse-frequency powers (`app:ch_waves:eq:exact-W-amplitude`). -/
def canonicalDisplacementAmplitude (F : Euclidean n → Euclidean N) (τ : ℝ)
    (S : Euclidean n × Euclidean (n - 1) → ℝ)
    (b₀ b₁ : Euclidean n × Euclidean (n - 1) → EuclideanSpace ℂ (Fin n))
    (p : Euclidean n × Euclidean (n - 1)) : EuclideanSpace ℂ (Fin N) :=
  WKB.reconstructionAmplitude τ⁻¹
    (fun x ↦ canonicalPrincipalNormalComplex F x
      (scalarDifferential (fun y ↦ S (y, p.2)) x) (b₀ (x, p.2)))
    (fun x ↦ canonicalPrincipalNormalComplex F x
      (scalarDifferential (fun y ↦ S (y, p.2)) x) (b₁ (x, p.2)))
    (fun x ↦ completedVariationComplex F (fun y ↦ b₀ (y, p.2)) 0 x)
    (fun x ↦ completedVariationComplex F (fun y ↦ b₁ (y, p.2)) 0 x) p.1

/-- The actual differential matrix of the canonical atom, with the chosen
Frobenius matrix norm (`app:ch_waves:eq:WKB-amplitude-difference`). -/
def canonicalAtomDerivative (F : Euclidean n → Euclidean N) (τ : ℝ)
    (S : Euclidean n × Euclidean (n - 1) → ℝ)
    (b₀ b₁ : Euclidean n × Euclidean (n - 1) → EuclideanSpace ℂ (Fin n))
    (p : Euclidean n × Euclidean (n - 1)) : Matrix (Fin N) (Fin n) ℂ :=
  fun i j ↦ partialDeriv (fun x ↦ canonicalAtom F τ S b₀ b₁ (x, p.2)) p.1 j i

/-- The demodulated derivative amplitude in
`app:ch_waves:eq:individual-representation`, as a Frobenius matrix. -/
def canonicalDerivativeAmplitude (F : Euclidean n → Euclidean N) (τ : ℝ)
    (S : Euclidean n × Euclidean (n - 1) → ℝ)
    (b₀ b₁ : Euclidean n × Euclidean (n - 1) → EuclideanSpace ℂ (Fin n))
    (p : Euclidean n × Euclidean (n - 1)) : Matrix (Fin N) (Fin n) ℂ :=
  fun i j ↦ waveFirstAmplitude τ⁻¹ (fun x ↦ S (x, p.2))
    (fun x ↦ canonicalDisplacementAmplitude F τ S b₀ b₁ (x, p.2)) p.1
      (EuclideanSpace.single j 1) i

/-- Canonical reconstruction yields the literal displacement polynomial at
each differentiability point (`app:ch_waves:eq:exact-W-amplitude`). -/
theorem canonicalAtom_eq (F : Euclidean n → Euclidean N) {τ : ℝ} (hτ : τ ≠ 0)
    {S : Euclidean n × Euclidean (n - 1) → ℝ}
    {b₀ b₁ : Euclidean n × Euclidean (n - 1) → EuclideanSpace ℂ (Fin n)}
    {x : Euclidean n} {ζ : Euclidean (n - 1)}
    (hS : DifferentiableAt ℝ (fun y ↦ S (y, ζ)) x)
    (hb₀ : DifferentiableAt ℝ (fun y ↦ b₀ (y, ζ)) x)
    (hb₁ : DifferentiableAt ℝ (fun y ↦ b₁ (y, ζ)) x) :
    canonicalAtom F τ S b₀ b₁ (x, ζ) =
      Complex.exp (Complex.I * (S (x, ζ) / τ : ℝ)) •
        canonicalDisplacementAmplitude F τ S b₀ b₁ (x, ζ) := by
  rw [canonicalAtom, completedVariationComplex_zero_twoTermWave F (inv_ne_zero hτ) hS hb₀ hb₁]
  simp only [modulatedWave, waveCarrier_inv_eq_exp_div, Complex.ofReal_div, mul_div_assoc]
  rfl

/-- The derivative matrix is the modulated canonical amplitude on the same
open physical domain (`app:ch_waves:eq:individual-representation`). -/
theorem fderiv_canonicalAtom (F : Euclidean n → Euclidean N)
    {τ : ℝ} (hτ : τ ≠ 0)
    {S : Euclidean n × Euclidean (n - 1) → ℝ}
    {b₀ b₁ : Euclidean n × Euclidean (n - 1) → EuclideanSpace ℂ (Fin n)}
    {U : Set (Euclidean n)} (hU : IsOpen U) {x : Euclidean n} (hx : x ∈ U)
    (ζ : Euclidean (n - 1))
    (hS : DifferentiableOn ℝ (fun y ↦ S (y, ζ)) U)
    (hb₀ : DifferentiableOn ℝ (fun y ↦ b₀ (y, ζ)) U)
    (hb₁ : DifferentiableOn ℝ (fun y ↦ b₁ (y, ζ)) U)
    (hA : DifferentiableAt ℝ
      (fun y ↦ canonicalDisplacementAmplitude F τ S b₀ b₁ (y, ζ)) x) (w : Euclidean n) :
    fderiv ℝ (fun y ↦ canonicalAtom F τ S b₀ b₁ (y, ζ)) x w =
      Complex.exp (Complex.I * (S (x, ζ) / τ : ℝ)) •
        waveFirstAmplitude τ⁻¹ (fun y ↦ S (y, ζ))
          (fun y ↦ canonicalDisplacementAmplitude F τ S b₀ b₁ (y, ζ)) x w := by
  have he : (fun y ↦ canonicalAtom F τ S b₀ b₁ (y, ζ)) =ᶠ[𝓝 x]
      modulatedWave τ⁻¹ (fun y ↦ S (y, ζ))
        (fun y ↦ canonicalDisplacementAmplitude F τ S b₀ b₁ (y, ζ)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    rw [canonicalAtom_eq F hτ ((hS y hy).differentiableAt (hU.mem_nhds hy))
      ((hb₀ y hy).differentiableAt (hU.mem_nhds hy))
      ((hb₁ y hy).differentiableAt (hU.mem_nhds hy))]
    simp only [modulatedWave, waveCarrier_inv_eq_exp_div, Complex.ofReal_div]
    congr 2
    ring
  rw [he.fderiv_eq, fderiv_modulatedWave ((hS x hx).differentiableAt (hU.mem_nhds hx)) hA]
  simp only [waveCarrier_inv_eq_exp_div, Complex.ofReal_div, mul_div_assoc]

/-- The derivative matrix is the modulated canonical amplitude on the same
open physical domain (`app:ch_waves:eq:individual-representation`). -/
theorem canonicalAtomDerivative_eq (F : Euclidean n → Euclidean N)
    {τ : ℝ} (hτ : τ ≠ 0)
    {S : Euclidean n × Euclidean (n - 1) → ℝ}
    {b₀ b₁ : Euclidean n × Euclidean (n - 1) → EuclideanSpace ℂ (Fin n)}
    {U : Set (Euclidean n)} (hU : IsOpen U) {x : Euclidean n} (hx : x ∈ U)
    (ζ : Euclidean (n - 1))
    (hS : DifferentiableOn ℝ (fun y ↦ S (y, ζ)) U)
    (hb₀ : DifferentiableOn ℝ (fun y ↦ b₀ (y, ζ)) U)
    (hb₁ : DifferentiableOn ℝ (fun y ↦ b₁ (y, ζ)) U)
    (hA : DifferentiableAt ℝ
      (fun y ↦ canonicalDisplacementAmplitude F τ S b₀ b₁ (y, ζ)) x) :
    canonicalAtomDerivative F τ S b₀ b₁ (x, ζ) =
      Complex.exp (Complex.I * (S (x, ζ) / τ : ℝ)) •
        canonicalDerivativeAmplitude F τ S b₀ b₁ (x, ζ) := by
  ext i j
  exact congrArg (fun v : EuclideanSpace ℂ (Fin N) ↦ v i)
    (fderiv_canonicalAtom F hτ hU hx ζ hS hb₀ hb₁ hA (EuclideanSpace.single j 1))

/-- Exact shifted demodulation of the canonical differentiated atom
(`app:ch_waves:eq:individual-representation`). This algebraic identity uses
the actual derivative matrix as the integrand. -/
theorem canonicalAtomDerivative_demodulated (F : Euclidean n → Euclidean N)
    {τ : ℝ} (hτ : τ ≠ 0)
    {S : Euclidean n × Euclidean (n - 1) → ℝ}
    {b₀ b₁ : Euclidean n × Euclidean (n - 1) → EuclideanSpace ℂ (Fin n)}
    {U : Set (Euclidean n)} (hU : IsOpen U) {x : Euclidean n} (hx : x ∈ U)
    (ζ η : Euclidean (n - 1))
    (hS : DifferentiableOn ℝ (fun y ↦ S (y, ζ + τ • η)) U)
    (hb₀ : DifferentiableOn ℝ (fun y ↦ b₀ (y, ζ + τ • η)) U)
    (hb₁ : DifferentiableOn ℝ (fun y ↦ b₁ (y, ζ + τ • η)) U)
    (hA : DifferentiableAt ℝ
      (fun y ↦ canonicalDisplacementAmplitude F τ S b₀ b₁ (y, ζ + τ • η)) x) :
    Complex.exp (-Complex.I * (S (x, ζ) / τ : ℝ)) •
        canonicalAtomDerivative F τ S b₀ b₁ (x, ζ + τ • η) =
      Complex.exp (Complex.I *
        (rawPrimaryPhaseDifference (fun y ξ ↦ S (y, ξ)) ζ τ x η : ℝ)) •
          canonicalDerivativeAmplitude F τ S b₀ b₁ (x, ζ + τ • η) := by
  rw [canonicalAtomDerivative_eq F hτ hU hx _ hS hb₀ hb₁ hA,
    smul_smul, ← Complex.exp_add]
  congr 2
  simp only [rawPrimaryPhaseDifference, sub_div, Complex.ofReal_sub]
  ring

end JanetCartan.RawPrimary
