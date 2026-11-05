module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.GradedPrimitives.Amplitude.Inverse

/-!
# Selected and literal inverse amplitude primitives

Finite local amplitude deductions for `app:ch_response:eq:direct-envelope-profile`
and the primitive inputs of
`NearCarrierSymbol.hasFullSourceSymbolBound_of_expression`.

`norm_jet_normalizedParameterAmplitude_le` proves the general selected-amplitude
profile from the unshifted normalized full amplitude, selector, and carrier jets.
`norm_jet_normalizedSelectedLiteralAmplitude_le` instantiates it with the literal
coordinate inverse, including `phaseJacobian`, the actual transport inverse, and
every source, target, frequency, and parameter-selector mask. All four joint
variables are retained. No adjoint replaces the coordinate inverse.

The response geometry producer supplies finite annular profiles for the actual
Jacobian and transport and a zeroth-order transport inverse gap; fixed cutoff
and carrier producers supply their finite jets. The proofs derive every
positive-order inverse and selected-amplitude jet. The constants are explicit
functions of these finite profiles, independent of frequency and `L`.

The reserve is natural subtraction. With `R = Rstar - 2` and `2 ≤ Rstar`,
`reserve_exponent` converts `k - R` to the exact `k + 2 - Rstar` consumed by the
parent's expression budget. The parent must still provide the actual profiles
from response geometry and assemble global smooth cutoff extensions; these local
deductions do not assert an unconditional graph estimate.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer.GradedPrimitives
open FourierIntegral

variable {n r : ℕ} {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

section Literal
variable {S : Euclidean n → Euclidean n → ℝ}
  {t : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ}
  {χs χt χg : Euclidean n → ℝ} {q : P × Euclidean n → ℂ}
  {ζ : P → Euclidean n} {ρ : ℝ} {N : ℕ}
  {U : Set (ParameterAmplitudePoint n P)}
  {V : Set (Euclidean n × Euclidean n × Euclidean n)}
  {W : Set (P × Euclidean n)} {C : Set P}
  (hmask : ContDiffOn ℝ N (normalizedReverseMask χs χt χg ρ) V)
  (hj : ContDiffOn ℝ N (fun v : Euclidean n × Euclidean n × Euclidean n ↦
    phaseJacobian S v.2.1 (ρ • v.2.2)) V)
  (ht : ContDiffOn ℝ N (fun v : Euclidean n × Euclidean n × Euclidean n ↦
    t v.2.1 (ρ • v.2.2)) V)
  (hu : ∀ v ∈ V, IsUnit (t v.2.1 (ρ • v.2.2)))
  (hq : ContDiffOn ℝ N q W) (hζ : ContDiffOn ℝ N ζ C)
  (hUV : MapsTo (carrierAmplitudeShift ζ) U V)
  (hUW : ∀ p ∈ U, (p.2, p.1.2.2) ∈ W) (hUC : ∀ p ∈ U, p.2 ∈ C)

include hmask hj ht hu hq hζ hUV hUW hUC

/-- Smoothness of the actual selected coordinate-inverse amplitude from its
primitive factors, with both physical positions and the parameter varying.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem normalizedSelectedLiteralAmplitude_contDiffOn :
    ContDiffOn ℝ N
      (normalizedParameterAmplitude (ReverseDerivative.literalAmplitude S t χs χt χg)
        q ζ ρ) U :=
  normalizedParameterAmplitude_contDiffOn
    (normalizedLiteralAmplitude_contDiffOn hmask hj ht hu) hq hζ hUV hUW hUC

/-- The complete selected literal coordinate-inverse amplitude profile from
primitive annular jets and the zeroth-order transport inverse gap. This closes
the local amplitude obligation of `app:ch_response:eq:direct-envelope-profile`.
The shared total order includes both positions, normalized covector, and all
parameter directions. The statement holds on the whole open buffer and hence
on each compact parameter box contained in it. -/
theorem norm_jet_normalizedSelectedLiteralAmplitude_le
    (hU : IsOpen U) (hV : IsOpen V) (hW : IsOpen W) (hC : IsOpen C)
    {k R : ℕ} {F J T Q : ℕ → ℝ} {M Z L : ℝ}
    (hF : ∀ i, 0 ≤ F i) (hJ : ∀ i, 0 ≤ J i) (hT : ∀ i, 0 ≤ T i)
    (hQ : ∀ i, 0 ≤ Q i) (hZ : 0 ≤ Z) (hL : 1 ≤ L)
    (hmaskjet : ∀ i ≤ N, ∀ v ∈ V,
      ‖iteratedFDeriv ℝ i (normalizedReverseMask χs χt χg ρ) v‖ ≤ F i)
    (hjjet : ∀ i ≤ N, ∀ v ∈ V,
      ‖iteratedFDeriv ℝ i
        (fun w : Euclidean n × Euclidean n × Euclidean n ↦
          phaseJacobian S w.2.1 (ρ • w.2.2)) v‖ ≤ J i * L ^ (i - R))
    (htjet : ∀ i, 1 ≤ i → i ≤ N → ∀ v ∈ V,
      ‖iteratedFDeriv ℝ i
        (fun w : Euclidean n × Euclidean n × Euclidean n ↦
          t w.2.1 (ρ • w.2.2)) v‖ ≤ T i * L ^ (i - R))
    (hgap : ∀ v ∈ V, ‖(t v.2.1 (ρ • v.2.2))⁻¹‖ ≤ M)
    (hqjet : ∀ i ≤ N, ∀ w ∈ W, ‖iteratedFDeriv ℝ i q w‖ ≤ Q i)
    (hζjet : ∀ i, 1 ≤ i → i ≤ N → ∀ c ∈ C, ‖iteratedFDeriv ℝ i ζ c‖ ≤ Z)
    (hk : k ≤ N) {p : ParameterAmplitudePoint n P} (hp : p ∈ U) :
    ‖iteratedFDeriv ℝ k
      (normalizedParameterAmplitude (ReverseDerivative.literalAmplitude S t χs χt χg)
        q ζ ρ) p‖ ≤
      selectedAmplitudeConstant (literalAmplitudeConstant r F J T M) Q Z k * L ^ (k - R) :=
  norm_jet_normalizedParameterAmplitude_le hU hV hW hC
    (normalizedLiteralAmplitude_contDiffOn hmask hj ht hu) hq hζ hUV hUW hUC
    (literalAmplitudeConstant_nonneg r hF hJ hT M) hQ hZ hL
    (fun _i hi v hv ↦ norm_jet_normalizedLiteralAmplitude_le hmask hj ht hu hV
      hF hJ hT hL hmaskjet hjjet htjet hi hv (hgap v hv)) hqjet hζjet hk hp

end Literal
end JanetCartan.ResponseTransfer.GradedPrimitives
