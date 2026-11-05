module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.NormalAmplitude.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The literal spectator density of the transport normal

These definitions print `app:ch_background:eq:bg-full-complex-amplitude` in
physical Euclidean covectors. The spectator measure is two-dimensional Lebesgue
measure. They can be used while the kernel change-of-variables proof is pending;
identification with that kernel remains the kernel owner's obligation.

All coefficients are real, including the matrix of the complex channel normal.
The complex operator uses their canonical inclusion into complex matrices. The
normalized PDO amplitude is `(2π)^n` times this literal amplitude.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormalReduction.TransportSymbol

/-- The two physical positions and output covector in
`app:ch_background:eq:bg-full-complex-amplitude`. -/
abbrev Variables (n : ℕ) := FourierIntegral.NormalVariables n

/-- Original coordinates `(x,x',z,η)`, with `z=(s,v)`, in
`app:ch_background:eq:bg-Psi`. -/
abbrev InputVariables (n : ℕ) :=
  (Euclidean n × Euclidean n) × ((ℝ × Euclidean 2) × Euclidean (n - 1))

/-- Only the primitive coefficient functions in
`app:ch_background:eq:bg-full-complex-amplitude`. There are no regularity,
existence, or symbol estimates in this record. The reduced covector is the
actual function `q_G(x,ξ_a(x,z))`; its construction belongs to the geometry. -/
structure Coefficients (n N : ℕ) where
  measurement : Euclidean n → ℝ
  angular : (ℝ × Euclidean 2) × Euclidean (n - 1) → ℝ
  high : ℝ → ℝ
  normal : Euclidean n × (ℝ × Euclidean 2) → Euclidean N
  reduced : Euclidean n × (ℝ × Euclidean 2) → Fin n → ℝ

variable {n N : ℕ}

/-- The inverse substitution retains both positions and the spectator.
Source: `app:ch_background:eq:bg-full-complex-amplitude`. -/
def inverseCoordinates (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
    (p : Variables n × Euclidean 2) : InputVariables n :=
  ((p.1.1, p.1.2.1), ((u p).1, p.2), (u p).2)

/-- The explicit scalar weight, including both measurement masks, before
inverse substitution (`app:ch_background:eq:bg-full-complex-amplitude`). `J`
is the absolute Jacobian `|det D_(s,η) Ψ|`, whose identity and gap are inputs. -/
def inputWeight (a : Coefficients n N) (J : InputVariables n → ℝ)
    (p : InputVariables n) : ℝ :=
  a.measurement p.1.1 * a.measurement p.1.2 *
    a.angular (p.2.1, ‖p.2.2‖⁻¹ • p.2.2) ^ 2 * a.high ‖p.2.2‖ ^ 2 *
    ‖p.2.2‖ / J p * ‖a.normal (p.1.1, p.2.1)‖ ^ 2 *
    ‖a.normal (p.1.2, p.2.1)‖ ^ 2

/-- The full rank-one matrix density before substitution; no diagonal or
spectator is discarded (`app:ch_background:eq:bg-full-complex-amplitude`). -/
def inputDensity (a : Coefficients n N) (J : InputVariables n → ℝ)
    (p : InputVariables n) : Matrix (Fin n) (Fin n) ℝ :=
  inputWeight a J p • Matrix.vecMulVec (a.reduced (p.1.1, p.2.1))
    (a.reduced (p.1.2, p.2.1))

/-- Literal zero extension off the joint inverse chart, as required in Step 1
of `app:ch_background:prop:bg-frame`. -/
def extendedDensity (a : Coefficients n N) (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
    (Ω : Set (Variables n × Euclidean 2)) :
    Variables n × Euclidean 2 → Matrix (Fin n) (Fin n) ℝ :=
  Ω.indicator (fun p ↦ inputDensity a J (inverseCoordinates u p))

/-- The actual compact spectator integral. The integration measure remains
Lebesgue, as in `app:ch_background:eq:bg-full-complex-amplitude`. Equality to
the unrestricted integral follows once the spectator support lies in `K`. -/
def amplitude (a : Coefficients n N) (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
    (Ω : Set (Variables n × Euclidean 2)) (K : Set (Euclidean 2))
    (p : Variables n) : Matrix (Fin n) (Fin n) ℝ :=
  ∫ v in K, extendedDensity a J u Ω (p, v)

/-- Removing only the high cutoff defines the homogeneous coefficient in
`app:ch_background:eq:bg-symbol`; its domain is away from frequency zero. -/
def homogeneousCoefficients (a : Coefficients n N) : Coefficients n N :=
  { a with high := fun _ ↦ 1 }

/-- The diagonal formula of `app:ch_background:eq:bg-symbol`. Homogeneity
requires the actual inverse and Jacobian scaling identities proved separately. -/
def homogeneousDiagonal (a : Coefficients n N) (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
    (Ω : Set (Variables n × Euclidean 2)) (K : Set (Euclidean 2))
    (x k : Euclidean n) : Matrix (Fin n) (Fin n) ℝ :=
  amplitude (homogeneousCoefficients a) J u Ω K (x, x, k)

/-- Regularization of each carrier by `χ(|η|/R)`; the normal therefore contains
its square (`app:ch_background:prop:bg-frame`, Step 1). -/
def regularizedCoefficients (a : Coefficients n N) (χ : ℝ → ℝ) (R : ℝ) :
    Coefficients n N := { a with high := fun t ↦ a.high t * χ (t / R) }

/-- Exact cancellation of the two half-order weights in
`app:ch_background:eq:bg-full-complex-amplitude`. -/
theorem halfWeights_mul (η : Euclidean (n - 1)) :
    Real.sqrt ‖η‖ * Real.sqrt ‖η‖ = ‖η‖ := Real.mul_self_sqrt (norm_nonneg η)

/-- The radial regularization appears squared in the actual normal density.
Source: `app:ch_background:eq:bg-full-complex-amplitude`. -/
theorem inputDensity_regularized (a : Coefficients n N) (J : InputVariables n → ℝ)
    (χ : ℝ → ℝ) (R : ℝ) (p : InputVariables n) :
    inputDensity (regularizedCoefficients a χ R) J p =
      χ (‖p.2.2‖ / R) ^ 2 • inputDensity a J p := by
  ext i j
  simp only [inputDensity, inputWeight, regularizedCoefficients, Matrix.smul_apply,
    smul_eq_mul]
  ring

/-- The compact spectator integral is the full Lebesgue integral when its
literal density vanishes off `K`. This is a support obligation, not a change
of input measure (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem amplitude_eq_integral (a : Coefficients n N) (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
    (Ω : Set (Variables n × Euclidean 2)) (K : Set (Euclidean 2))
    (p : Variables n)
    (hs : ∀ v ∉ K, extendedDensity a J u Ω (p, v) = 0) :
    amplitude a J u Ω K p = ∫ v, extendedDensity a J u Ω (p, v) :=
  setIntegral_eq_integral_of_forall_compl_eq_zero hs

end JanetCartan.ContinuumNormalReduction.TransportSymbol
