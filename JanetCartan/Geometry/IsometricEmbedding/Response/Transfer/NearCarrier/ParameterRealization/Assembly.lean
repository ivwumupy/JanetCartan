module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ParameterRealization.LocalKernels

/-!
# Actual parameter amplitude transfer

Construct `HasParameterAmplitudeTransfer` for the literal selected scalar
forward and reverse graphs in `app:ch_response:eq:direct-envelope-profile`.
The interpretation of the expression operations, their smoothness/support,
operator differentiation, and source integration by parts are all proved.
The remaining inputs are primitive phase/carrier geometry and jets, smooth
extensions of the actual phase coefficients, and bounded realizations
identified with the literal test kernels. The fixed Fourier normalization
belongs to the initial joint amplitude, as in `normalizedScalarAmplitude`.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
namespace JanetCartan.ResponseTransfer.NearCarrierParameter
open FourierIntegral IsometricEmbedding.Response.NearCarrier
variable {d p m : ℕ} {ι : Type*}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "P" => EuclideanSpace ℝ (Fin p)
local notation "Z" => JointAmplitudePoint d p
local notation "L²" => Lp ℂ 2 (volume : Measure E)

private theorem coefficient_frozen_smooth
    {U : Set P} {q : Z → ℂ} (hq : ContDiffOn ℝ ∞ q ((U ×ˢ univ) ×ˢ univ))
    {c : P} (hc : c ∈ U) :
    ContDiff ℝ ∞ (fun z : (E × E) × E ↦ q ((c, z.1), z.2)) :=
  contDiffOn_univ.mp (hq.comp
    ((contDiff_const.prodMk contDiff_fst).prodMk contDiff_snd).contDiffOn
    (fun _ _ ↦ ⟨⟨hc, mem_univ _⟩, mem_univ _⟩))

private theorem parameter_slice_differentiable {U : Set P} (hU : IsOpen U)
    {X Y F : Set E} {b : Z → ℂ} (hb : ParameterAmplitudeAdmissible U X Y F b)
    {c : P} (hc : c ∈ U) (z : E × E) (δ : E) :
    DifferentiableAt ℝ (fun a ↦ b ((a, z), δ)) c :=
  (hb.differentiableAt hU hc z δ).comp c
    ((differentiableAt_id.prodMk (differentiableAt_const z)).prodMk (differentiableAt_const δ))

private theorem source_slice_differentiable {U : Set P} (hU : IsOpen U)
    {X Y F : Set E} {b : Z → ℂ} (hb : ParameterAmplitudeAdmissible U X Y F b)
    {c : P} (hc : c ∈ U) (x y δ : E) :
    DifferentiableAt ℝ (fun y ↦ b ((c, (x, y)), δ)) y :=
  (hb.differentiableAt hU hc (x, y) δ).comp y
    (((differentiableAt_const c).prodMk
      ((differentiableAt_const x).prodMk differentiableAt_id)).prodMk (differentiableAt_const δ))

/-- Interpretation of the actual expression remainder in parameter/source
slices. This closes the amplitude-expression premise of the transfer interface
from ordinary chain rules (`app:ch_response:eq:direct-envelope-profile`). -/
theorem evaluate_parameterSourceTerms_slice
    {U : Set P} (hU : IsOpen U) {X Y F : Set E}
    (a : ι → Z → ℂ) (b : AmplitudeExpression Z ℂ ι) (v : P) (idx : Fin d → ι)
    (hb : ParameterAmplitudeAdmissible U X Y F (b.evaluate a))
    (ha : ∀ j, ContDiffOn ℝ ∞ (a (idx j)) ((U ×ˢ univ) ×ˢ univ))
    {c : P} (hc : c ∈ U) (z : E × E) (δ : E) :
    (b.divergenceTransfer (parameterAmplitudeDirection v) (parameterSourceTerms idx)).evaluate a
        ((c, z), δ) =
      fderiv ℝ (fun t ↦ b.evaluate a ((t, z), δ)) c v +
        ∑ j, fderiv ℝ (fun y ↦ a (idx j) ((c, (z.1, y)), δ) *
          b.evaluate a ((c, (z.1, y)), δ)) z.2 (EuclideanSpace.single j 1) := by
  rw [evaluate_parameterSourceTerms,
    fderiv_parameterAmplitudeDirection (hb.differentiableAt hU hc z δ)]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact fderiv_sourceAmplitudeDirection ((hb.mul (ha j)).differentiableAt hU hc z δ) j

/-- The forward literal realization supplies the parameter-transfer interface.
The remainder and datum expressions are identified here, and their support and
smoothness are proved. No output derivative or Sobolev bound is an input.
The phase and frequency stay fixed; `a (idx i j)` is a smooth extension of
`C_j` on the selected carrier. Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem hasParameterAmplitudeTransfer_forward
    {U : Set P} (hU : IsOpen U) {X Y F : Set E}
    (hX : IsCompact X) (hY : IsCompact Y) (hF : IsCompact F)
    {V : Set E} (hV : IsOpen V) (hFV : F ⊆ V)
    {S : E → E → ℝ} {ζ : P → E} {ρ : ℝ}
    {D : Set E} (hD : IsOpen D) (hcD : Convex ℝ D) (hD0 : (0 : E) ∉ D)
    (hS : ∀ x, ContDiffOn ℝ ∞ (S x) D) (hhom : ∀ x, PosHomogeneousOne (S x))
    (hρ : 0 < ρ) (hζ : ∀ c ∈ U, DifferentiableAt ℝ ζ c)
    (hζD : ∀ c ∈ U, ζ c ∈ D)
    (hend : ∀ c ∈ U, ∀ δ ∈ F, ζ c + ρ⁻¹ • δ ∈ D)
    (hΦ : ContDiffOn ℝ ∞ (fun z : (P × E) × E ↦
      phaseIncrement S (ζ z.1.1) ρ z.1.2 z.2) ((U ×ˢ univ) ×ˢ V))
    (w : Fin m → P) (idx : Fin m → Fin d → ι) (a : ι → Z → ℂ)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (a (idx i j)) ((U ×ˢ univ) ×ˢ univ))
    (hC : ∀ i j c, c ∈ U → ∀ x y δ, δ ∈ F →
      a (idx i j) ((c, (x, y)), δ) = (phaseCoefficient S ζ ρ c (w i) x δ j : ℂ))
    (T : P → (Z → ℂ) → L² →L[ℂ] L²)
    (hT : ∀ b, ParameterAmplitudeAdmissible U X Y F b → ∀ c ∈ U,
      ∀ g : SchwartzMap E ℂ, T c b (g.toLp 2 volume) =ᵐ[volume]
        fun x ↦ ∫ y, frequencyKernel F
          (forwardScalarKernel S ζ ρ (fun t z δ ↦ b ((t, z), δ)) c) (x, y) * g y) :
    HasParameterAmplitudeTransfer U w (fun i ↦ parameterAmplitudeDirection (w i))
      (fun i ↦ parameterSourceTerms (idx i)) (fun _ _ ↦ ContinuousLinearMap.mul ℝ ℂ)
      idx a T (ParameterAmplitudeAdmissible U X Y F) := by
  intro b hb f df pf i c hc hdf hpf
  let A := fun t z δ ↦ b.evaluate a ((t, z), δ)
  have hrem := admissible_parameterSourceTerms hU hX.isClosed hY.isClosed a b (w i) (idx i) hb (ha i)
  have hremEq (z : E × E) (δ : E) (hδ : δ ∈ F) :
      (b.divergenceTransfer (parameterAmplitudeDirection (w i))
        (parameterSourceTerms (idx i))).evaluate a ((c, z), δ) =
        forwardParameterRemainder S ζ ρ A c (w i) z δ := by
    rw [evaluate_parameterSourceTerms_slice hU a b (w i) (idx i) hb (ha i) hc]
    unfold forwardParameterRemainder
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    have he : (fun y ↦ a (idx i j) ((c, (z.1, y)), δ) * b.evaluate a ((c, (z.1, y)), δ)) =
        fun y ↦ (phaseCoefficient S ζ ρ c (w i) z.1 δ j : ℂ) * b.evaluate a ((c, (z.1, y)), δ) :=
      funext fun y ↦ congrArg (fun q : ℂ ↦ q * b.evaluate a ((c, (z.1, y)), δ))
        (hC i j c hc z.1 y δ hδ)
    rw [he, fderiv_const_mul (source_slice_differentiable hU hb hc z.1 z.2 δ)]
    rfl
  apply hasLineDerivAt_forward_realization hU hX hY hF hD hcD hD0 hS hhom hρ hc
    (w i) (hζ c hc) (hζD c hc) (hend c hc) A (contDiffOn_forwardScalarKernel_of_chart hU hF.isClosed hV hFV hΦ hb) hb.2.1
    (fun x y δ _ ↦ parameter_slice_differentiable hU hb hc (x, y) δ)
    (fun x y δ _ ↦ source_slice_differentiable hU hb hc x y δ)
    (fun j z δ ↦ a (idx i j) ((c, z), δ))
    (fun j ↦ coefficient_frozen_smooth (ha i j) hc) (fun j x y δ hδ ↦ hC i j c hc x y δ hδ)
    (fun t ↦ T t (b.evaluate a))
    (T c ((b.divergenceTransfer (parameterAmplitudeDirection (w i)) (parameterSourceTerms (idx i))).evaluate a))
    (fun j ↦ T c ((b.coefficientProduct (ContinuousLinearMap.mul ℝ ℂ) (idx i j)).evaluate a))
    (hT _ hb) _ _ hdf hpf
  · intro g
    apply (hT _ hrem c hc g).trans
    apply Filter.Eventually.of_forall
    intro x
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro y
    dsimp only
    congr 1
    exact setIntegral_congr_fun hF.measurableSet (fun δ hδ ↦
      congrArg (fun t : ℂ ↦ graphOscillation (phaseIncrement S (ζ c) ρ) x y δ * t)
        (hremEq (x, y) δ hδ))
  · intro j g
    apply (hT _ (hb.mul (ha i j)) c hc g).trans
    apply Filter.Eventually.of_forall
    intro x
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro y
    dsimp only
    congr 1
    apply setIntegral_congr_fun hF.measurableSet
    intro δ hδ
    change _ * (a (idx i j) ((c, (x, y)), δ) * A c (x, y) δ) = _
    rw [hC i j c hc x y δ hδ]
    rfl

/-- The reverse literal realization supplies the parameter-transfer interface
with coefficient `-C B⁻¹`. The whole signed source product is differentiated,
retaining derivatives of the inverse matrix and the full `j_S U⁻¹` amplitude.
Smoothness/support and expression identities are proved; only primitive phase
geometry, jets, and literal bounded realizations are inputs. Source:
`app:ch_response:eq:direct-envelope-profile`. -/
theorem hasParameterAmplitudeTransfer_reverse
    {U : Set P} (hU : IsOpen U) {X Y F : Set E}
    (hX : IsCompact X) (hY : IsCompact Y) (hF : IsCompact F)
    {V : Set E} (hV : IsOpen V) (hFV : F ⊆ V)
    {S : E → E → ℝ} {ζ : P → E} {ρ : ℝ}
    {D : Set E} (hD : IsOpen D) (hcD : Convex ℝ D) (hD0 : (0 : E) ∉ D)
    (hS : ∀ x, ContDiffOn ℝ ∞ (S x) D) (hhom : ∀ x, PosHomogeneousOne (S x))
    (hρ : 0 < ρ) (hζ : ∀ c ∈ U, DifferentiableAt ℝ ζ c)
    (hζD : ∀ c ∈ U, ζ c ∈ D)
    (hend : ∀ c ∈ U, ∀ δ ∈ F, ζ c + ρ⁻¹ • δ ∈ D)
    (hΦ : ContDiffOn ℝ ∞ (fun z : (P × E) × E ↦
      phaseIncrement S (ζ z.1.1) ρ z.1.2 z.2) ((U ×ˢ univ) ×ˢ V))
    (B0 J : P → E → E → Matrix (Fin d) (Fin d) ℝ)
    (hJB : ∀ c ∈ U, ∀ x δ, δ ∈ F → J c x δ * B0 c x δ = 1)
    (hgrad : ∀ c ∈ U, ∀ x δ, δ ∈ F → ∀ l,
      partialDeriv (fun z ↦ phaseIncrement S (ζ c) ρ z δ) x l =
        (B0 c x δ).mulVec (fun k ↦ δ k) l)
    (w : Fin m → P) (idx : Fin m → Fin d → ι) (a : ι → Z → ℂ)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (a (idx i j)) ((U ×ˢ univ) ×ˢ univ))
    (hC : ∀ i j c, c ∈ U → ∀ x y δ, δ ∈ F →
      a (idx i j) ((c, (x, y)), δ) = reverseParameterRow S ζ ρ (J c) c (w i) y δ j)
    (T : P → (Z → ℂ) → L² →L[ℂ] L²)
    (hT : ∀ b, ParameterAmplitudeAdmissible U X Y F b → ∀ c ∈ U,
      ∀ g : SchwartzMap E ℂ, T c b (g.toLp 2 volume) =ᵐ[volume]
        fun x ↦ ∫ y, frequencyKernel F
          (reverseScalarKernel S ζ ρ (fun t z δ ↦ b ((t, z), δ)) c) (x, y) * g y) :
    HasParameterAmplitudeTransfer U w (fun i ↦ parameterAmplitudeDirection (w i))
      (fun i ↦ parameterSourceTerms (idx i)) (fun _ _ ↦ ContinuousLinearMap.mul ℝ ℂ)
      idx a T (ParameterAmplitudeAdmissible U X Y F) := by
  intro b hb f df pf i c hc hdf hpf
  let A := fun t z δ ↦ b.evaluate a ((t, z), δ)
  have hsp (x δ : E) (hδ : δ ∈ F) : DifferentiableAt ℝ (fun z ↦ phaseIncrement S (ζ c) ρ z δ) x := by
    have h := hΦ.contDiffAt (x := ((c, x), δ)) (((hU.prod isOpen_univ).prod hV).mem_nhds
      ⟨⟨hc, mem_univ x⟩, hFV hδ⟩)
    exact (h.comp x ((contDiffAt_const.prodMk contDiffAt_id).prodMk contDiffAt_const)).differentiableAt (by simp)
  have hrem := admissible_parameterSourceTerms hU hX.isClosed hY.isClosed a b (w i) (idx i) hb (ha i)
  have hremEq (z : E × E) (δ : E) (hδ : δ ∈ F) :
      (b.divergenceTransfer (parameterAmplitudeDirection (w i))
        (parameterSourceTerms (idx i))).evaluate a ((c, z), δ) =
        reverseParameterRemainder S ζ ρ (J c) A c (w i) z δ := by
    rw [evaluate_parameterSourceTerms_slice hU a b (w i) (idx i) hb (ha i) hc]
    unfold reverseParameterRemainder
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    have he : (fun y ↦ a (idx i j) ((c, (z.1, y)), δ) * b.evaluate a ((c, (z.1, y)), δ)) =
        fun y ↦ reverseParameterDatum S ζ ρ (J c) A c (w i) j (z.1, y) δ :=
      funext fun y ↦ congrArg (fun q : ℂ ↦ q * b.evaluate a ((c, (z.1, y)), δ))
        (hC i j c hc z.1 y δ hδ)
    rw [he]
  apply hasLineDerivAt_reverse_realization hU hX hY hF hD hcD hD0 hS hhom hρ hc
    (w i) (hζ c hc) (hζD c hc) (hend c hc) (B0 c) (J c) (hJB c hc)
    (fun x δ hδ ↦ hsp x δ hδ) (hgrad c hc) A (contDiffOn_reverseScalarKernel_of_chart hU hF.isClosed hV hFV hΦ hb) hb.2.1
    (fun x y δ _ ↦ parameter_slice_differentiable hU hb hc (x, y) δ)
    (fun x y δ _ ↦ source_slice_differentiable hU hb hc x y δ)
    (fun j z δ ↦ a (idx i j) ((c, z), δ))
    (fun j ↦ coefficient_frozen_smooth (ha i j) hc) (fun j x y δ hδ ↦ hC i j c hc x y δ hδ)
    (fun t ↦ T t (b.evaluate a))
    (T c ((b.divergenceTransfer (parameterAmplitudeDirection (w i)) (parameterSourceTerms (idx i))).evaluate a))
    (fun j ↦ T c ((b.coefficientProduct (ContinuousLinearMap.mul ℝ ℂ) (idx i j)).evaluate a))
    (hT _ hb) _ _ hdf hpf
  · intro g
    apply (hT _ hrem c hc g).trans
    apply Filter.Eventually.of_forall
    intro x
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro y
    dsimp only
    congr 1
    exact setIntegral_congr_fun hF.measurableSet (fun δ hδ ↦
      congrArg (fun t : ℂ ↦ ReverseDerivative.oscillation S (ζ c) ρ x y δ * t)
        (hremEq (x, y) δ hδ))
  · intro j g
    apply (hT _ (hb.mul (ha i j)) c hc g).trans
    apply Filter.Eventually.of_forall
    intro x
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro y
    dsimp only
    congr 1
    apply setIntegral_congr_fun hF.measurableSet
    intro δ hδ
    change _ * (a (idx i j) ((c, (x, y)), δ) * A c (x, y) δ) = _
    rw [hC i j c hc x y δ hδ]
    rfl

end JanetCartan.ResponseTransfer.NearCarrierParameter
