module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ParameterRealization.Source
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ParameterRealization.Frequency

/-!
# Signed scalar parameter kernel identities

The scalar specialization of `app:ch_response:eq:direct-envelope-profile`.
The phase is the fixed original `S`, the frequency is fixed, and only the
carrier and the full selected amplitude vary. The forward coefficient is `C`;
the reverse coefficient is `-C B⁻¹`. The latter's entire source divergence is
retained. These are pointwise identities feeding compact frequency integration,
not assumptions about derivatives of a realized operator.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff

namespace JanetCartan.ResponseTransfer.NearCarrierParameter
open FourierIntegral

variable {d : ℕ} {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Leibniz's rule in the form needed for source transfer of a parameter phase
derivative. The actual forward/reverse phase lemmas discharge `he` below.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem hasLineDerivAt_scalar_kernel_source
    (e A : P → E → ℂ) (q : Fin d → E → ℂ) (c v : P) (y : E) (Ac : ℂ)
    (he : HasLineDerivAt ℝ (fun a ↦ e a y)
      (-(∑ j, q j y * fderiv ℝ (e c) y (EuclideanSpace.single j 1))) c v)
    (ha : HasLineDerivAt ℝ (fun a ↦ A a y) Ac c v)
    (hes : DifferentiableAt ℝ (e c) y)
    (has : DifferentiableAt ℝ (A c) y)
    (hqs : ∀ j, DifferentiableAt ℝ (q j) y) :
    HasLineDerivAt ℝ (fun a ↦ e a y * A a y)
      (e c y * (Ac + ∑ j, fderiv ℝ (fun z ↦ q j z * A c z) y
          (EuclideanSpace.single j 1)) -
        ∑ j, fderiv ℝ (fun z ↦ e c z * (q j z * A c z)) y
          (EuclideanSpace.single j 1)) c v := by
  have hd (j : Fin d) := congrArg (fun L : E →L[ℝ] ℂ ↦ L (EuclideanSpace.single j 1))
    (fderiv_mul hes ((hqs j).mul has))
  simp only [Pi.mul_def, add_apply, smul_apply, smul_eq_mul] at hd
  have halg : e c y * (Ac + ∑ j, fderiv ℝ (fun z ↦ q j z * A c z) y
          (EuclideanSpace.single j 1)) -
        ∑ j, fderiv ℝ (fun z ↦ e c z * (q j z * A c z)) y
          (EuclideanSpace.single j 1) =
      (-(∑ j, q j y * fderiv ℝ (e c) y (EuclideanSpace.single j 1))) * A c y +
        e c y * Ac := by
    simp only [hd, Finset.sum_add_distrib, ← Finset.mul_sum]
    have hs : (∑ j, q j y * fderiv ℝ (e c) y (EuclideanSpace.single j 1) * A c y) =
        ∑ j, q j y * A c y * fderiv ℝ (e c) y (EuclideanSpace.single j 1) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [neg_mul, Finset.sum_mul, hs]
    ring
  rw [halg]
  simpa only [HasLineDerivAt, Pi.mul_def, zero_smul, add_zero] using HasDerivAt.mul he ha

/-- Full scalar forward kernel, before frequency integration, for
`app:ch_response:eq:direct-envelope-profile`. The scalar amplitude retains
both physical positions and may include the fixed Fourier normalization. -/
def forwardScalarKernel (S : E → E → ℝ) (ζ : P → E) (ρ : ℝ)
    (A : P → E × E → E → ℂ) (c : P) (z : E × E) (δ : E) : ℂ :=
  graphOscillation (phaseIncrement S (ζ c) ρ) z.1 z.2 δ * A c z δ

/-- Full scalar reverse kernel. In particular, `A` may be the scalar entry of
the selected literal `j_S U⁻¹` amplitude, with every cutoff retained.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
def reverseScalarKernel (S : E → E → ℝ) (ζ : P → E) (ρ : ℝ)
    (A : P → E × E → E → ℂ) (c : P) (z : E × E) (δ : E) : ℂ :=
  ReverseDerivative.oscillation S (ζ c) ρ z.1 z.2 δ * A c z δ

/-- The parameter datum amplitude for the forward phase, with the positive
coefficient `C_l` (`app:ch_response:eq:direct-envelope-profile`). -/
def forwardParameterDatum (S : E → E → ℝ) (ζ : P → E) (ρ : ℝ)
    (A : P → E × E → E → ℂ) (c v : P) (j : Fin d) (z : E × E) (δ : E) : ℂ :=
  (phaseCoefficient S ζ ρ c v z.1 δ j : ℂ) * A c z δ

/-- The parameter remainder of the forward full amplitude, with derivatives
in its second physical position (`app:ch_response:eq:direct-envelope-profile`). -/
def forwardParameterRemainder (S : E → E → ℝ) (ζ : P → E) (ρ : ℝ)
    (A : P → E × E → E → ℂ) (c v : P) (z : E × E) (δ : E) : ℂ :=
  fderiv ℝ (fun a ↦ A a z δ) c v +
    ∑ j, (phaseCoefficient S ζ ρ c v z.1 δ j : ℂ) *
      fderiv ℝ (fun y ↦ A c (z.1, y) δ) z.2 (EuclideanSpace.single j 1)

/-- The actual scalar forward phase gives the source-divergence kernel
identity. It yields datum amplitudes `C_l A` and remainder
`∂c A + Σ C_l ∂y_l A`, not an assumed operator derivative.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem hasLineDerivAt_forwardScalarKernel_source
    {S : E → E → ℝ} {ζ : P → E} {D : Set E}
  (hD : IsOpen D) (hcD : Convex ℝ D) (hD0 : (0 : E) ∉ D)
  {x : E} (hS : ContDiffOn ℝ ∞ (S x) D) (hhom : PosHomogeneousOne (S x))
  {c : P} (hζ : DifferentiableAt ℝ ζ c) (hζD : ζ c ∈ D)
  {ρ : ℝ} (hρ : 0 < ρ) {δ : E} (hend : ζ c + ρ⁻¹ • δ ∈ D)
    (A : P → E × E → E → ℂ) (v : P) (y : E)
    (ha : DifferentiableAt ℝ (fun a ↦ A a (x, y) δ) c)
    (has : DifferentiableAt ℝ (fun z ↦ A c (x, z) δ) y) :
    HasLineDerivAt ℝ (fun a ↦ forwardScalarKernel S ζ ρ A a (x, y) δ)
      (graphOscillation (phaseIncrement S (ζ c) ρ) x y δ *
          forwardParameterRemainder S ζ ρ A c v (x, y) δ -
        ∑ j, fderiv ℝ (fun z ↦ graphOscillation (phaseIncrement S (ζ c) ρ) x z δ *
          forwardParameterDatum S ζ ρ A c v j (x, z) δ) y
            (EuclideanSpace.single j 1)) c v := by
  let e := fun a z ↦ graphOscillation (phaseIncrement S (ζ a) ρ) x z δ
  let q := fun j (_ : E) ↦ (phaseCoefficient S ζ ρ c v x δ j : ℂ)
  have hes : DifferentiableAt ℝ (e c) y := by
    exact ((Complex.ofRealCLM.differentiableAt.comp y
      ((differentiableAt_const _).sub (differentiableAt_id.inner ℝ
        (differentiableAt_const δ)))).const_mul Complex.I).cexp
  have hphase : -(∑ j, q j y * fderiv ℝ (e c) y (EuclideanSpace.single j 1)) =
      (Complex.I * ((∑ j, phaseCoefficient S ζ ρ c v x δ j * δ j : ℝ) : ℂ)) * e c y := by
    change -(∑ j, q j y * partialDeriv (e c) y j) = _
    simp only [e, partialDeriv_graphOscillation_source, q, Complex.ofReal_sum,
      Complex.ofReal_mul, Finset.mul_sum, Finset.sum_mul, neg_mul, mul_neg, Finset.sum_neg_distrib,
      neg_neg]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have he : HasLineDerivAt ℝ (fun a ↦ e a y)
      (-(∑ j, q j y * fderiv ℝ (e c) y (EuclideanSpace.single j 1))) c v := by
    rw [hphase]
    exact hasLineDerivAt_forwardOscillation hD hcD hD0 hS hhom hζ hζD hρ hend y v
  have h := hasLineDerivAt_scalar_kernel_source e (fun a z ↦ A a (x, z) δ) q c v y _
    he (ha.hasFDerivAt.hasLineDerivAt v) hes has (fun _ ↦ differentiableAt_const _)
  have hd (j : Fin d) : fderiv ℝ (fun z ↦ q j z * A c (x, z) δ) y
      (EuclideanSpace.single j 1) =
      q j y * fderiv ℝ (fun z ↦ A c (x, z) δ) y (EuclideanSpace.single j 1) := by
    simp only [q, fderiv_const_mul has, smul_apply, smul_eq_mul]
  simpa only [hd, e, q, forwardScalarKernel, forwardParameterRemainder,
    forwardParameterDatum] using h


/-- The signed reverse parameter coefficient is `-C B⁻¹`, with `J` the
supplied inverse of the averaged mixed matrix. Source:
`app:ch_response:eq:direct-envelope-profile`. -/
def reverseParameterRow (S : E → E → ℝ) (ζ : P → E) (ρ : ℝ)
    (J : E → E → Matrix (Fin d) (Fin d) ℝ) (c v : P) (x δ : E) (j : Fin d) : ℂ :=
  -(reverseCoefficient (fun z ↦ phaseCoefficient S ζ ρ c v z δ) (fun z ↦ J z δ) x j : ℂ)

/-- The signed reverse datum amplitude, retaining both amplitude positions
and the literal inverse weight (`app:ch_response:eq:direct-envelope-profile`). -/
def reverseParameterDatum (S : E → E → ℝ) (ζ : P → E) (ρ : ℝ)
    (J : E → E → Matrix (Fin d) (Fin d) ℝ)
    (A : P → E × E → E → ℂ) (c v : P) (j : Fin d) (z : E × E) (δ : E) : ℂ :=
  reverseParameterRow S ζ ρ J c v z.2 δ j * A c z δ

/-- The full reverse remainder is the parameter amplitude derivative plus
source divergence of the signed datum amplitude, hence minus the divergence
of `(C B⁻¹) A`. Source: `app:ch_response:eq:direct-envelope-profile`. -/
def reverseParameterRemainder (S : E → E → ℝ) (ζ : P → E) (ρ : ℝ)
    (J : E → E → Matrix (Fin d) (Fin d) ℝ)
    (A : P → E × E → E → ℂ) (c v : P) (z : E × E) (δ : E) : ℂ :=
  fderiv ℝ (fun a ↦ A a z δ) c v +
    ∑ j, fderiv ℝ (fun x ↦ reverseParameterDatum S ζ ρ J A c v j (z.1, x) δ)
      z.2 (EuclideanSpace.single j 1)

/-- Explicit negative divergence form of the reverse remainder. Derivatives
of the inverse matrix, the full weight, and all source cutoffs remain inside
the differentiated product (`app:ch_response:eq:direct-envelope-profile`). -/
theorem reverseParameterRemainder_eq_sub_divergence
    (S : E → E → ℝ) (ζ : P → E) (ρ : ℝ)
    (J : E → E → Matrix (Fin d) (Fin d) ℝ)
    (A : P → E × E → E → ℂ) (c v : P) (z : E × E) (δ : E) :
    reverseParameterRemainder S ζ ρ J A c v z δ =
      fderiv ℝ (fun a ↦ A a z δ) c v -
        ∑ j, fderiv ℝ (fun x ↦
          (reverseCoefficient (fun u ↦ phaseCoefficient S ζ ρ c v u δ)
            (fun u ↦ J u δ) x j : ℂ) * A c (z.1, x) δ) z.2
              (EuclideanSpace.single j 1) := by
  simp only [reverseParameterRemainder, reverseParameterDatum, reverseParameterRow,
    neg_mul, fderiv_fun_neg, neg_apply, Finset.sum_neg_distrib, sub_eq_add_neg]

/-- The actual reverse phase gives the signed scalar source-divergence
identity. The parameter phase trade is derived from homogeneity and the chart,
then the proved matrix cancellation produces `-C B⁻¹`. Source:
`app:ch_response:eq:direct-envelope-profile`. -/
theorem hasLineDerivAt_reverseScalarKernel_source
    {S : E → E → ℝ} {ζ : P → E} {D : Set E}
    (hD : IsOpen D) (hcD : Convex ℝ D) (hD0 : (0 : E) ∉ D)
    {x : E} (hS : ContDiffOn ℝ ∞ (S x) D) (hhom : PosHomogeneousOne (S x))
    {c : P} (hζ : DifferentiableAt ℝ ζ c) (hζD : ζ c ∈ D)
    {ρ : ℝ} (hρ : 0 < ρ) {δ : E} (hend : ζ c + ρ⁻¹ • δ ∈ D)
    (A : P → E × E → E → ℂ) (v : P) (y : E)
    (B J : E → E → Matrix (Fin d) (Fin d) ℝ)
    (hJB : J x δ * B x δ = 1)
    (hsp : DifferentiableAt ℝ (fun z ↦ phaseIncrement S (ζ c) ρ z δ) x)
    (hgrad : ∀ l, partialDeriv (fun z ↦ phaseIncrement S (ζ c) ρ z δ) x l =
      (B x δ).mulVec (fun k ↦ δ k) l)
    (ha : DifferentiableAt ℝ (fun a ↦ A a (y, x) δ) c)
    (has : DifferentiableAt ℝ (fun z ↦ A c (y, z) δ) x)
    (hq : ∀ j, DifferentiableAt ℝ (fun z ↦ reverseParameterRow S ζ ρ J c v z δ j) x) :
    HasLineDerivAt ℝ (fun a ↦ reverseScalarKernel S ζ ρ A a (y, x) δ)
      (ReverseDerivative.oscillation S (ζ c) ρ y x δ *
          reverseParameterRemainder S ζ ρ J A c v (y, x) δ -
        ∑ j, fderiv ℝ (fun z ↦ ReverseDerivative.oscillation S (ζ c) ρ y z δ *
          reverseParameterDatum S ζ ρ J A c v j (y, z) δ) x
            (EuclideanSpace.single j 1)) c v := by
  let e := fun a z ↦ ReverseDerivative.oscillation S (ζ a) ρ y z δ
  let q := fun j z ↦ reverseParameterRow S ζ ρ J c v z δ j
  have hes : DifferentiableAt ℝ (e c) x := by
    exact ((Complex.ofRealCLM.differentiableAt.comp x
      ((differentiableAt_const _).sub hsp)).const_mul Complex.I).cexp
  have ht := reverse_parameter_phase_trade S (ζ c) ρ y x δ
    (fun z ↦ phaseCoefficient S ζ ρ c v z δ) (fun z ↦ B z δ) (fun z ↦ J z δ)
    hJB hsp hgrad
  have he : HasLineDerivAt ℝ (fun a ↦ e a x)
      (-(∑ j, q j x * fderiv ℝ (e c) x (EuclideanSpace.single j 1))) c v := by
    have hh := hasLineDerivAt_reverseOscillation hD hcD hD0 hS hhom hζ hζD hρ hend y v
    rw [ht] at hh
    simpa only [q, reverseParameterRow, neg_mul, Finset.sum_neg_distrib, neg_neg,
      partialDeriv, e] using hh
  exact hasLineDerivAt_scalar_kernel_source e (fun a z ↦ A a (y, z) δ) q c v x _
    he (ha.hasFDerivAt.hasLineDerivAt v) hes has hq

end JanetCartan.ResponseTransfer.NearCarrierParameter
