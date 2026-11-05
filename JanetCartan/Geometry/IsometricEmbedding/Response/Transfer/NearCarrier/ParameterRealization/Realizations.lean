module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ParameterRealization.ScalarKernels
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ParameterRealization.KernelJets

/-!
# Literal scalar graph realizations and their parameter derivatives

Actual first parameter derivatives for `app:ch_response:eq:direct-envelope-profile`.
The fixed operator phase and fixed frequency appear literally in the kernels.
Only primitive smooth selected-kernel/amplitude/coefficient jets, common compact
supports, and bounded realizations on Schwartz tests are inputs. Neither the
output derivative nor the signed kernel identity is assumed. The compact box
may be any subset of the open parameter domain.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

namespace JanetCartan.ResponseTransfer.NearCarrierParameter
open FourierIntegral Pseudodifferential
variable {d p : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "P" => EuclideanSpace ℝ (Fin p)
local notation "L²" => Lp ℂ 2 (volume : Measure E)

private theorem kernel_parameter_differentiable
    {U : Set P} (hU : IsOpen U) {k : P → E × E → E → ℂ}
    (hk : ContDiffOn ℝ ∞ (fun z : (P × (E × E)) × E ↦ k z.1.1 z.1.2 z.2)
      ((U ×ˢ univ) ×ˢ univ)) {c : P} (hc : c ∈ U) (z : E × E) (δ : E) :
    DifferentiableAt ℝ (fun a ↦ k a z δ) c := by
  have ht := hk.contDiffAt (x := ((c, z), δ)) (((hU.prod isOpen_univ).prod isOpen_univ).mem_nhds
    ⟨⟨hc, mem_univ z⟩, mem_univ δ⟩)
  exact (ht.comp c ((contDiffAt_id.prodMk contDiffAt_const).prodMk contDiffAt_const)).differentiableAt (by simp)

/-- The actual forward derivative on arbitrary L² data, including the datum's
parameter derivative. `Q` is a smooth extension of the phase coefficient from
the compact selected frequency carrier; its values elsewhere are immaterial.
The remainder is literally `∂c A + Σ C_l ∂y_l A`. All modified-kernel support
and smoothness obligations are proved, not assumed. Source:
`app:ch_response:eq:direct-envelope-profile`. -/
theorem hasLineDerivAt_forward_realization
    {U : Set P} (hU : IsOpen U) {X Y F : Set E}
    (hX : IsCompact X) (hY : IsCompact Y) (hF : IsCompact F)
    {S : E → E → ℝ} {ζ : P → E} {ρ : ℝ}
    {D : Set E} (hD : IsOpen D) (hcD : Convex ℝ D) (hD0 : (0 : E) ∉ D)
    (hS : ∀ x, ContDiffOn ℝ ∞ (S x) D) (hhom : ∀ x, PosHomogeneousOne (S x))
    (hρ : 0 < ρ) {c : P} (hc : c ∈ U) (v : P)
    (hζ : DifferentiableAt ℝ ζ c) (hζD : ζ c ∈ D)
    (hend : ∀ δ ∈ F, ζ c + ρ⁻¹ • δ ∈ D)
    (A : P → E × E → E → ℂ)
    (hk : ContDiffOn ℝ ∞ (fun z : (P × (E × E)) × E ↦
      forwardScalarKernel S ζ ρ A z.1.1 z.1.2 z.2) ((U ×ˢ univ) ×ˢ univ))
    (hs : ∀ a ∈ U, ∀ δ ∈ F, tsupport (fun z ↦ A a z δ) ⊆ X ×ˢ Y)
    (ha : ∀ x y δ, δ ∈ F → DifferentiableAt ℝ (fun a ↦ A a (x, y) δ) c)
    (has : ∀ x y δ, δ ∈ F → DifferentiableAt ℝ (fun z ↦ A c (x, z) δ) y)
    (Q : Fin d → E × E → E → ℂ)
    (hQ : ∀ j, ContDiff ℝ ∞ (Function.uncurry (Q j)))
    (hQC : ∀ j x y δ, δ ∈ F → Q j (x, y) δ = (phaseCoefficient S ζ ρ c v x δ j : ℂ))
    (T : P → L² →L[ℂ] L²) (R : L² →L[ℂ] L²) (B : Fin d → L² →L[ℂ] L²)
    (hT : ∀ a ∈ U, ∀ g : SchwartzMap E ℂ, T a (g.toLp 2 volume) =ᵐ[volume]
      fun x ↦ ∫ y, frequencyKernel F (forwardScalarKernel S ζ ρ A a) (x, y) * g y)
    (hR : ∀ g : SchwartzMap E ℂ, R (g.toLp 2 volume) =ᵐ[volume]
      fun x ↦ ∫ y, frequencyKernel F (fun z δ ↦
        graphOscillation (phaseIncrement S (ζ c) ρ) z.1 z.2 δ *
          forwardParameterRemainder S ζ ρ A c v z δ) (x, y) * g y)
    (hB : ∀ j, ∀ g : SchwartzMap E ℂ, B j (g.toLp 2 volume) =ᵐ[volume]
      fun x ↦ ∫ y, frequencyKernel F (fun z δ ↦
        graphOscillation (phaseIncrement S (ζ c) ρ) z.1 z.2 δ *
          forwardParameterDatum S ζ ρ A c v j z δ) (x, y) * g y)
    {f : P → L²} {df : Fin d → L²} {pf : L²}
    (hdf : ∀ j, HasEuclideanL2CoordinateDerivative j (f c) (df j))
    (hpf : HasLineDerivAt ℝ f pf c v) :
    HasLineDerivAt ℝ (fun a ↦ T a (f a))
      (R (f c) + ∑ j, B j (df j) + T c pf) c v := by
  let k := forwardScalarKernel S ζ ρ A
  have hsK (a : P) (ha : a ∈ U) (δ : E) (hδ : δ ∈ F) :
      tsupport (fun z ↦ k a z δ) ⊆ X ×ˢ Y :=
    tsupport_mul_subset_right.trans (hs a ha δ hδ)
  have hdatum (j : Fin d) (z : E × E) (δ : E) (hδ : δ ∈ F) :
      Q j z δ * k c z δ = graphOscillation (phaseIncrement S (ζ c) ρ) z.1 z.2 δ *
        forwardParameterDatum S ζ ρ A c v j z δ := by
    rw [show Q j z δ = (phaseCoefficient S ζ ρ c v z.1 δ j : ℂ) from hQC j _ _ δ hδ]
    dsimp [k, forwardScalarKernel, forwardParameterDatum]
    ring
  apply hasLineDerivAt_frequency_transfer_of_coefficients hU hX hY hF hk hsK hc v Q hQ
    (fun z δ ↦ graphOscillation (phaseIncrement S (ζ c) ρ) z.1 z.2 δ *
      forwardParameterRemainder S ζ ρ A c v z δ) _ T R B hT hR _ hdf hpf
  · intro x y δ hδ
    have hd := ((kernel_parameter_differentiable hU hk hc (x, y) δ).hasFDerivAt.hasLineDerivAt v).unique
      (hasLineDerivAt_forwardScalarKernel_source hD hcD hD0 (hS x) (hhom x)
        hζ hζD hρ (hend δ hδ) A v y (ha x y δ hδ) (has x y δ hδ))
    have he (j : Fin d) :
        (fun z ↦ Q j (x, z) δ * forwardScalarKernel S ζ ρ A c (x, z) δ) =
        (fun z ↦ graphOscillation (phaseIncrement S (ζ c) ρ) x z δ *
          forwardParameterDatum S ζ ρ A c v j (x, z) δ) :=
      funext fun z ↦ hdatum j (x, z) δ hδ
    simpa only [he] using hd
  · intro j g
    apply (hB j g).trans
    apply Filter.Eventually.of_forall
    intro x
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro y
    dsimp only
    apply congrArg (fun t : ℂ ↦ t * g y)
    exact setIntegral_congr_fun hF.measurableSet (fun δ hδ ↦ (hdatum j (x, y) δ hδ).symm)


/-- The actual reverse derivative on arbitrary L² data. The fixed phase has
its negative parameter sign; the datum amplitudes are `-(C B⁻¹)_j A`, and the
remainder includes the negative full source divergence. Every analytic
interchange and all support/smoothness fields are derived from primitive jets.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem hasLineDerivAt_reverse_realization
    {U : Set P} (hU : IsOpen U) {X Y F : Set E}
    (hX : IsCompact X) (hY : IsCompact Y) (hF : IsCompact F)
    {S : E → E → ℝ} {ζ : P → E} {ρ : ℝ}
    {D : Set E} (hD : IsOpen D) (hcD : Convex ℝ D) (hD0 : (0 : E) ∉ D)
    (hS : ∀ x, ContDiffOn ℝ ∞ (S x) D) (hhom : ∀ x, PosHomogeneousOne (S x))
    (hρ : 0 < ρ) {c : P} (hc : c ∈ U) (v : P)
    (hζ : DifferentiableAt ℝ ζ c) (hζD : ζ c ∈ D)
    (hend : ∀ δ ∈ F, ζ c + ρ⁻¹ • δ ∈ D)
    (B0 J : E → E → Matrix (Fin d) (Fin d) ℝ)
    (hJB : ∀ x δ, δ ∈ F → J x δ * B0 x δ = 1)
    (hsp : ∀ x δ, δ ∈ F → DifferentiableAt ℝ (fun z ↦ phaseIncrement S (ζ c) ρ z δ) x)
    (hgrad : ∀ x δ, δ ∈ F → ∀ l,
      partialDeriv (fun z ↦ phaseIncrement S (ζ c) ρ z δ) x l =
        (B0 x δ).mulVec (fun k ↦ δ k) l)
    (A : P → E × E → E → ℂ)
    (hk : ContDiffOn ℝ ∞ (fun z : (P × (E × E)) × E ↦
      reverseScalarKernel S ζ ρ A z.1.1 z.1.2 z.2) ((U ×ˢ univ) ×ˢ univ))
    (hs : ∀ a ∈ U, ∀ δ ∈ F, tsupport (fun z ↦ A a z δ) ⊆ X ×ˢ Y)
    (ha : ∀ x y δ, δ ∈ F → DifferentiableAt ℝ (fun a ↦ A a (x, y) δ) c)
    (has : ∀ x y δ, δ ∈ F → DifferentiableAt ℝ (fun z ↦ A c (x, z) δ) y)
    (Q : Fin d → E × E → E → ℂ)
    (hQ : ∀ j, ContDiff ℝ ∞ (Function.uncurry (Q j)))
    (hQC : ∀ j x y δ, δ ∈ F → Q j (x, y) δ = reverseParameterRow S ζ ρ J c v y δ j)
    (T : P → L² →L[ℂ] L²) (R : L² →L[ℂ] L²) (B : Fin d → L² →L[ℂ] L²)
    (hT : ∀ a ∈ U, ∀ g : SchwartzMap E ℂ, T a (g.toLp 2 volume) =ᵐ[volume]
      fun x ↦ ∫ y, frequencyKernel F (reverseScalarKernel S ζ ρ A a) (x, y) * g y)
    (hR : ∀ g : SchwartzMap E ℂ, R (g.toLp 2 volume) =ᵐ[volume]
      fun x ↦ ∫ y, frequencyKernel F (fun z δ ↦
        ReverseDerivative.oscillation S (ζ c) ρ z.1 z.2 δ *
          reverseParameterRemainder S ζ ρ J A c v z δ) (x, y) * g y)
    (hB : ∀ j, ∀ g : SchwartzMap E ℂ, B j (g.toLp 2 volume) =ᵐ[volume]
      fun x ↦ ∫ y, frequencyKernel F (fun z δ ↦
        ReverseDerivative.oscillation S (ζ c) ρ z.1 z.2 δ *
          reverseParameterDatum S ζ ρ J A c v j z δ) (x, y) * g y)
    {f : P → L²} {df : Fin d → L²} {pf : L²}
    (hdf : ∀ j, HasEuclideanL2CoordinateDerivative j (f c) (df j))
    (hpf : HasLineDerivAt ℝ f pf c v) :
    HasLineDerivAt ℝ (fun a ↦ T a (f a))
      (R (f c) + ∑ j, B j (df j) + T c pf) c v := by
  let k := reverseScalarKernel S ζ ρ A
  have hsK (a : P) (ha : a ∈ U) (δ : E) (hδ : δ ∈ F) :
      tsupport (fun z ↦ k a z δ) ⊆ X ×ˢ Y :=
    tsupport_mul_subset_right.trans (hs a ha δ hδ)
  have hdatum (j : Fin d) (z : E × E) (δ : E) (hδ : δ ∈ F) :
      Q j z δ * k c z δ = ReverseDerivative.oscillation S (ζ c) ρ z.1 z.2 δ *
        reverseParameterDatum S ζ ρ J A c v j z δ := by
    rw [show Q j z δ = reverseParameterRow S ζ ρ J c v z.2 δ j from hQC j _ _ δ hδ]
    dsimp [k, reverseScalarKernel, reverseParameterDatum]
    ring
  apply hasLineDerivAt_frequency_transfer_of_coefficients hU hX hY hF hk hsK hc v Q hQ
    (fun z δ ↦ ReverseDerivative.oscillation S (ζ c) ρ z.1 z.2 δ *
      reverseParameterRemainder S ζ ρ J A c v z δ) _ T R B hT hR _ hdf hpf
  · intro x y δ hδ
    have hqs (j : Fin d) : DifferentiableAt ℝ
        (fun z ↦ reverseParameterRow S ζ ρ J c v z δ j) y := by
      have he : (fun z ↦ reverseParameterRow S ζ ρ J c v z δ j) =
          fun z ↦ Q j (x, z) δ := funext fun z ↦ (hQC j x z δ hδ).symm
      rw [he]
      exact ((hQ j).comp ((contDiff_const.prodMk contDiff_id).prodMk contDiff_const)).differentiable (by simp) y
    have hd := ((kernel_parameter_differentiable hU hk hc (x, y) δ).hasFDerivAt.hasLineDerivAt v).unique
      (hasLineDerivAt_reverseScalarKernel_source hD hcD hD0 (hS y) (hhom y)
        hζ hζD hρ (hend δ hδ) A v x B0 J (hJB y δ hδ) (hsp y δ hδ)
        (hgrad y δ hδ) (ha x y δ hδ) (has x y δ hδ) hqs)
    have he (j : Fin d) :
        (fun z ↦ Q j (x, z) δ * reverseScalarKernel S ζ ρ A c (x, z) δ) =
        (fun z ↦ ReverseDerivative.oscillation S (ζ c) ρ x z δ *
          reverseParameterDatum S ζ ρ J A c v j (x, z) δ) :=
      funext fun z ↦ hdatum j (x, z) δ hδ
    simpa only [he] using hd
  · intro j g
    apply (hB j g).trans
    apply Filter.Eventually.of_forall
    intro x
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro y
    dsimp only
    apply congrArg (fun t : ℂ ↦ t * g y)
    exact setIntegral_congr_fun hF.measurableSet (fun δ hδ ↦ (hdatum j (x, y) δ hδ).symm)

end JanetCartan.ResponseTransfer.NearCarrierParameter
