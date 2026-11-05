module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.NormalizedTransfer.SupportedParameter

/-!
# Parameter realization from coefficient agreement on the original support

The coefficient producer `GradedPrimitives.exists_global_selected_primitives`
gives agreement on a neighborhood of the complete selected support. Only this
agreement is used here. The signed phase identities are proved from the actual
phase and inverse, then the checked compact-kernel realization leaf supplies
`HasParameterAmplitudeTransfer`. Consumer: `DerivativeBounds.ParameterAssembly`,
for `app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
namespace JanetCartan.ResponseTransfer.NormalizedTransfer
open FourierIntegral IsometricEmbedding.Response.NearCarrier NearCarrierParameter
variable {n p m : ℕ} {ι : Type*}
local notation "E" => Euclidean n
local notation "P" => Euclidean p
local notation "Z" => JointAmplitudePoint n p
local notation "L²" => Lp ℂ 2 (volume : Measure E)

private theorem kernel_derivative_of_weighted_phase
    (e A : P → E → ℂ) (q : Fin n → E → ℂ) (c v : P) (y : E)
    (hep : DifferentiableAt ℝ (fun t ↦ e t y) c)
    (hap : DifferentiableAt ℝ (fun t ↦ A t y) c)
    (hes : DifferentiableAt ℝ (e c) y) (has : DifferentiableAt ℝ (A c) y)
    (hqs : ∀ j, DifferentiableAt ℝ (q j) y)
    (he : fderiv ℝ (fun t ↦ e t y) c v * A c y =
      (-(∑ j, q j y * fderiv ℝ (e c) y (EuclideanSpace.single j 1))) * A c y) :
    fderiv ℝ (fun t ↦ e t y * A t y) c v =
      e c y * (fderiv ℝ (fun t ↦ A t y) c v +
        ∑ j, fderiv ℝ (fun z ↦ q j z * A c z) y (EuclideanSpace.single j 1)) -
      ∑ j, fderiv ℝ (fun z ↦ q j z * (e c z * A c z)) y (EuclideanSpace.single j 1) := by
  have hd (j : Fin n) := congrArg (fun L : E →L[ℝ] ℂ ↦ L (EuclideanSpace.single j 1))
    (fderiv_mul hes ((hqs j).mul has))
  simp only [Pi.mul_def, add_apply, smul_apply, smul_eq_mul] at hd
  have hs (j : Fin n) : (fun z ↦ q j z * (e c z * A c z)) =
      fun z ↦ e c z * (q j z * A c z) := funext fun z ↦ mul_left_comm _ _ _
  have hdp := congrArg (fun L : P →L[ℝ] ℂ ↦ L v) (fderiv_mul hep hap)
  simp only [Pi.mul_def, add_apply, smul_apply, smul_eq_mul] at hdp
  rw [hdp]
  simp only [hs, hd]
  rw [mul_comm (A c y), he]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, neg_mul, Finset.sum_mul]
  have hh : (∑ j, q j y * fderiv ℝ (e c) y (EuclideanSpace.single j 1) * A c y) =
      ∑ j, q j y * A c y * fderiv ℝ (e c) y (EuclideanSpace.single j 1) := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hh]
  ring

private theorem parameter_transfer_of_supported_phase
    {ρ : ℝ} (hρ : ρ ≠ 0) {U : Set P} (hU : IsOpen U) {X Y F : Set E}
    (hX : IsCompact X) (hY : IsCompact Y) (hF : IsCompact F) {K : Set Z}
    {V : Set E} (hV : IsOpen V) (hFV : (fun ε ↦ ρ • ε) '' F ⊆ V)
    (osc : Z → ℂ) (ho : ContDiffOn ℝ ∞ osc ((U ×ˢ univ) ×ˢ V))
    (w : Fin m → P) (idx : Fin m → Fin n → ι) (a : ι → Z → ℂ)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (a (idx i j)) ((U ×ˢ univ) ×ˢ univ))
    (hphase : ∀ i c, c ∈ U → ∀ x y δ, δ ∈ (fun ε ↦ ρ • ε) '' F →
      ((c, (x, y)), ρ⁻¹ • δ) ∈ K →
      fderiv ℝ (fun t ↦ osc ((t, (x, y)), δ)) c (w i) =
        -(∑ j, physicalField ρ (a (idx i j)) ((c, (x, y)), δ) *
          fderiv ℝ (fun z ↦ osc ((c, (x, z)), δ)) y (EuclideanSpace.single j 1)))
    (T : P → (Z → ℂ) → L² →L[ℂ] L²)
    (hT : ∀ b, SupportedJointAmplitude U X Y F K b → ∀ c ∈ U,
      ∀ g : SchwartzMap E ℂ, T c b (g.toLp 2 volume) =ᵐ[volume]
        fun x ↦ ∫ y, frequencyKernel ((fun ε ↦ ρ • ε) '' F)
          (fun z δ ↦ osc ((c, z), δ) * physicalField ρ b ((c, z), δ)) (x, y) * g y) :
    HasParameterAmplitudeTransfer U w (fun i ↦ parameterAmplitudeDirection (w i))
      (fun i ↦ parameterSourceTerms (idx i)) (fun _ _ ↦ ContinuousLinearMap.mul ℝ ℂ)
      idx a T (SupportedJointAmplitude U X Y F K) := by
  intro b hb f df pf i c hc hdf hpf
  let A := fun t z δ ↦ physicalField ρ (b.evaluate a) ((t, z), δ)
  let Q := fun j z δ ↦ physicalField ρ (a (idx i j)) ((c, z), δ)
  let k := fun t z δ ↦ osc ((t, z), δ) * A t z δ
  let rem := (b.divergenceTransfer (parameterAmplitudeDirection (w i)) (parameterSourceTerms (idx i))).evaluate a
  have hb' := admissible_physicalField_parameter hρ hb.1
  have hrem := supportedJointAmplitude_parameter hU hX.isClosed hY.isClosed a b (w i) (idx i) hb (ha i)
  have hk : ContDiffOn ℝ ∞ (fun z : Z ↦ k z.1.1 z.1.2 z.2) ((U ×ˢ univ) ×ˢ univ) :=
    contDiffOn_selectedProduct hU (hF.image (continuous_const_smul ρ)).isClosed hV hFV hb'.1 hb'.2.2 ho
  apply hasLineDerivAt_frequency_transfer_of_coefficients hU hX hY
    (hF.image (continuous_const_smul ρ)) hk
    (fun t ht δ hδ ↦ tsupport_mul_subset_right.trans (hb'.2.1 t ht δ hδ)) hc (w i) Q
    (fun j ↦ contDiff_frozenField (contDiffOn_physicalField_parameter ρ (ha i j)) hc)
    (fun z δ ↦ osc ((c, z), δ) * physicalField ρ rem ((c, z), δ)) _
    (fun t ↦ T t (b.evaluate a)) (T c rem)
    (fun j ↦ T c ((b.coefficientProduct (ContinuousLinearMap.mul ℝ ℂ) (idx i j)).evaluate a))
    (hT _ hb) (hT _ hrem c hc) _ hdf hpf
  · intro x y δ hδ
    have hoa : DifferentiableAt ℝ osc ((c, (x, y)), δ) :=
      (ho.contDiffAt (((hU.prod isOpen_univ).prod hV).mem_nhds
        ⟨⟨hc, mem_univ _⟩, hFV hδ⟩)).differentiableAt (by simp)
    have hop : DifferentiableAt ℝ (fun t : P ↦ osc ((t, (x, y)), δ)) c :=
      hoa.comp c ((differentiableAt_id.prodMk (differentiableAt_const (x, y))).prodMk
      (differentiableAt_const δ))
    have hos : DifferentiableAt ℝ (fun z : E ↦ osc ((c, (x, z)), δ)) y :=
      hoa.comp y (((differentiableAt_const c).prodMk
      ((differentiableAt_const x).prodMk differentiableAt_id)).prodMk (differentiableAt_const δ))
    have hap : DifferentiableAt ℝ (fun t : P ↦ A t (x, y) δ) c :=
      (hb.1.differentiableAt hU hc (x, y) (ρ⁻¹ • δ)).comp c
      (show DifferentiableAt ℝ (fun t : P ↦ ((t, (x, y)), ρ⁻¹ • δ)) c from
        (differentiableAt_id.prodMk (differentiableAt_const (x, y))).prodMk (differentiableAt_const (ρ⁻¹ • δ)))
    have has : DifferentiableAt ℝ (fun z : E ↦ A c (x, z) δ) y :=
      (hb.1.differentiableAt hU hc (x, y) (ρ⁻¹ • δ)).comp y
      (show DifferentiableAt ℝ (fun z : E ↦ ((c, (x, z)), ρ⁻¹ • δ)) y from
        ((differentiableAt_const c).prodMk ((differentiableAt_const x).prodMk differentiableAt_id)).prodMk
          (differentiableAt_const (ρ⁻¹ • δ)))
    have hqs (j : Fin n) : DifferentiableAt ℝ (fun z ↦ Q j (x, z) δ) y :=
      ((contDiff_frozenField (contDiffOn_physicalField_parameter ρ (ha i j)) hc).comp
        ((contDiff_const.prodMk contDiff_id).prodMk contDiff_const)).differentiable (by simp) y
    have hp : fderiv ℝ (fun t ↦ osc ((t, (x, y)), δ)) c (w i) * A c (x, y) δ =
        (-(∑ j, Q j (x, y) δ * fderiv ℝ (fun z ↦ osc ((c, (x, z)), δ)) y
          (EuclideanSpace.single j 1))) * A c (x, y) δ := by
      by_cases hz : A c (x, y) δ = 0
      · simp only [hz, mul_zero]
      · rw [hphase i c hc x y δ hδ (hb.2 (subset_tsupport _ hz))]
    have hid := kernel_derivative_of_weighted_phase
      (fun t z ↦ osc ((t, (x, z)), δ)) (fun t z ↦ A t (x, z) δ)
      (fun j z ↦ Q j (x, z) δ) c (w i) y hop hap hos has hqs hp
    dsimp only [rem]
    rw [physical_parameterSourceTerms_slice hρ hU a b (w i) (idx i) hb.1 (ha i) hc]
    exact hid
  · intro j g
    apply (hT _ (supportedJointAmplitude_coefficientProduct a b (idx i j) hb (ha i j)) c hc g).trans
    apply Filter.Eventually.of_forall
    intro x
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro y
    dsimp only
    apply congrArg (fun t : ℂ ↦ t * g y)
    apply setIntegral_congr_fun (hF.image (continuous_const_smul ρ)).measurableSet
    intro δ _
    dsimp only
    rw [physical_parameterDatum]
    exact mul_left_comm _ _ _

/-- The normalized forward parameter transfer with coefficient agreement only
on the complete original joint support. Smooth extensions are produced by
`GradedPrimitives.exists_global_selected_primitives`; no literal transfer
identity or graph estimate is an input. The bounded literal realizations are
supplied by FullLow/BranchRealization. Source:
`app:ch_response:eq:direct-envelope-profile`. -/
theorem hasParameterAmplitudeTransfer_forward_supported
    {ρ : ℝ} (hρ : 0 < ρ) {U : Set P} (hU : IsOpen U) {X Y F : Set E} {K : Set Z}
    (hX : IsCompact X) (hY : IsCompact Y) (hF : IsCompact F)
    {V : Set E} (hV : IsOpen V) (hFV : (fun ε ↦ ρ • ε) '' F ⊆ V)
    {S : E → E → ℝ} {ζ : P → E}
    {D : Set E} (hD : IsOpen D) (hcD : Convex ℝ D) (hD0 : (0 : E) ∉ D)
    (hS : ∀ x, ContDiffOn ℝ ∞ (S x) D) (hhom : ∀ x, PosHomogeneousOne (S x))
    (hζ : ∀ c ∈ U, DifferentiableAt ℝ ζ c) (hζD : ∀ c ∈ U, ζ c ∈ D)
    (hend : ∀ c ∈ U, ∀ ε ∈ F, ζ c + ε ∈ D)
    (hΦ : ContDiffOn ℝ ∞ (fun z : (P × E) × E ↦
      phaseIncrement S (ζ z.1.1) ρ z.1.2 z.2) ((U ×ˢ univ) ×ˢ V))
    (w : Fin m → P) (idx : Fin m → Fin n → ι) (a : ι → Z → ℂ)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (a (idx i j)) ((U ×ˢ univ) ×ˢ univ))
    (hC : ∀ i j z, z ∈ K →
      a (idx i j) z = (phaseCoefficient S ζ ρ z.1.1 (w i) z.1.2.1 (ρ • z.2) j : ℂ))
    (T : P → (Z → ℂ) → L² →L[ℂ] L²)
    (hT : ∀ b, SupportedJointAmplitude U X Y F K b →
      ∀ c ∈ U, ∀ g : SchwartzMap E ℂ, T c b (g.toLp 2 volume) =ᵐ[volume]
        fun x ↦ ∫ y, frequencyKernel ((fun ε ↦ ρ • ε) '' F)
          (forwardScalarKernel S ζ ρ (fun t z δ ↦ physicalField ρ b ((t, z), δ)) c) (x, y) * g y) :
    HasParameterAmplitudeTransfer U w (fun i ↦ parameterAmplitudeDirection (w i))
      (fun i ↦ parameterSourceTerms (idx i)) (fun _ _ ↦ ContinuousLinearMap.mul ℝ ℂ)
      idx a T (SupportedJointAmplitude U X Y F K) := by
  let osc : Z → ℂ := fun z ↦ graphOscillation (phaseIncrement S (ζ z.1.1) ρ)
    z.1.2.1 z.1.2.2 z.2
  have ho : ContDiffOn ℝ ∞ osc ((U ×ˢ univ) ×ˢ V) := by
    apply (contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn _)).cexp
    exact (hΦ.comp
      ((contDiff_fst.fst.prodMk contDiff_fst.snd.fst).prodMk contDiff_snd).contDiffOn
      (fun z hz ↦ ⟨⟨hz.1.1, mem_univ _⟩, hz.2⟩)).sub
        (contDiff_fst.snd.snd.inner ℝ contDiff_snd).contDiffOn
  apply parameter_transfer_of_supported_phase hρ.ne' hU hX hY hF hV hFV osc ho w idx a ha _ T hT
  intro i c hc x y δ hδ hK
  have hend' : ζ c + ρ⁻¹ • δ ∈ D := by
    obtain ⟨ε, hε, rfl⟩ := hδ
    simpa only [smul_smul, inv_mul_cancel₀ hρ.ne', one_smul] using hend c hc ε hε
  have hod : DifferentiableAt ℝ (fun t : P ↦ osc ((t, (x, y)), δ)) c :=
    ((ho.contDiffAt (((hU.prod isOpen_univ).prod hV).mem_nhds
      ⟨⟨hc, mem_univ _⟩, hFV hδ⟩)).differentiableAt (by simp)).comp c
        ((differentiableAt_id.prodMk (differentiableAt_const (x, y))).prodMk (differentiableAt_const δ))
  have hd := (hod.hasFDerivAt.hasLineDerivAt (w i)).unique
    (hasLineDerivAt_forwardOscillation hD hcD hD0 (hS x) (hhom x)
      (hζ c hc) (hζD c hc) hρ hend' y (w i))
  have hq (j : Fin n) : physicalField ρ (a (idx i j)) ((c, (x, y)), δ) =
      (phaseCoefficient S ζ ρ c (w i) x δ j : ℂ) := by
    simpa only [physicalField, smul_smul, mul_inv_cancel₀ hρ.ne', one_smul] using hC i j _ hK
  rw [hd]
  simp_rw [hq]
  change _ = -(∑ j, (phaseCoefficient S ζ ρ c (w i) x δ j : ℂ) *
    partialDeriv (fun z ↦ graphOscillation (phaseIncrement S (ζ c) ρ) x z δ) y j)
  simp only [partialDeriv_graphOscillation_source, Complex.ofReal_sum,
    Complex.ofReal_mul, Finset.mul_sum, Finset.sum_mul, neg_mul, mul_neg, Finset.sum_neg_distrib, neg_neg]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The normalized reverse parameter transfer with coefficient agreement only
on the complete original joint support. Smooth extensions are produced by
`GradedPrimitives.exists_global_selected_primitives`; no literal transfer
identity or graph estimate is an input. The bounded literal realizations are
supplied by FullLow/BranchRealization. Source:
`app:ch_response:eq:direct-envelope-profile`. -/
theorem hasParameterAmplitudeTransfer_reverse_supported
    {ρ : ℝ} (hρ : 0 < ρ) {U : Set P} (hU : IsOpen U) {X Y F : Set E} {K : Set Z}
    (hX : IsCompact X) (hY : IsCompact Y) (hF : IsCompact F)
    {V : Set E} (hV : IsOpen V) (hFV : (fun ε ↦ ρ • ε) '' F ⊆ V)
    {S : E → E → ℝ} {ζ : P → E}
    {D : Set E} (hD : IsOpen D) (hcD : Convex ℝ D) (hD0 : (0 : E) ∉ D)
    (hS : ∀ x, ContDiffOn ℝ ∞ (S x) D) (hhom : ∀ x, PosHomogeneousOne (S x))
    (hζ : ∀ c ∈ U, DifferentiableAt ℝ ζ c) (hζD : ∀ c ∈ U, ζ c ∈ D)
    (hend : ∀ c ∈ U, ∀ ε ∈ F, ζ c + ε ∈ D)
    (hΦ : ContDiffOn ℝ ∞ (fun z : (P × E) × E ↦
      phaseIncrement S (ζ z.1.1) ρ z.1.2 z.2) ((U ×ˢ univ) ×ˢ V))
    (B J : P → E → E → Matrix (Fin n) (Fin n) ℝ)
    (hJB : ∀ z ∈ K, J z.1.1 z.1.2.2 (ρ • z.2) * B z.1.1 z.1.2.2 (ρ • z.2) = 1)
    (hgrad : ∀ z ∈ K, ∀ l,
      partialDeriv (fun x ↦ phaseIncrement S (ζ z.1.1) ρ x (ρ • z.2)) z.1.2.2 l =
        (B z.1.1 z.1.2.2 (ρ • z.2)).mulVec (fun k ↦ (ρ • z.2) k) l)
    (w : Fin m → P) (idx : Fin m → Fin n → ι) (a : ι → Z → ℂ)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (a (idx i j)) ((U ×ˢ univ) ×ˢ univ))
    (hC : ∀ i j z, z ∈ K →
      a (idx i j) z = reverseParameterRow S ζ ρ (J z.1.1) z.1.1 (w i) z.1.2.2 (ρ • z.2) j)
    (T : P → (Z → ℂ) → L² →L[ℂ] L²)
    (hT : ∀ b, SupportedJointAmplitude U X Y F K b →
      ∀ c ∈ U, ∀ g : SchwartzMap E ℂ, T c b (g.toLp 2 volume) =ᵐ[volume]
        fun x ↦ ∫ y, frequencyKernel ((fun ε ↦ ρ • ε) '' F)
          (reverseScalarKernel S ζ ρ (fun t z δ ↦ physicalField ρ b ((t, z), δ)) c) (x, y) * g y) :
    HasParameterAmplitudeTransfer U w (fun i ↦ parameterAmplitudeDirection (w i))
      (fun i ↦ parameterSourceTerms (idx i)) (fun _ _ ↦ ContinuousLinearMap.mul ℝ ℂ)
      idx a T (SupportedJointAmplitude U X Y F K) := by
  let osc : Z → ℂ := fun z ↦ ReverseDerivative.oscillation S (ζ z.1.1) ρ
    z.1.2.1 z.1.2.2 z.2
  have ho : ContDiffOn ℝ ∞ osc ((U ×ˢ univ) ×ˢ V) := by
    apply (contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn _)).cexp
    exact (contDiff_fst.snd.fst.inner ℝ contDiff_snd).contDiffOn.sub
      (hΦ.comp ((contDiff_fst.fst.prodMk contDiff_fst.snd.snd).prodMk contDiff_snd).contDiffOn
        (fun z hz ↦ ⟨⟨hz.1.1, mem_univ _⟩, hz.2⟩))
  apply parameter_transfer_of_supported_phase hρ.ne' hU hX hY hF hV hFV osc ho w idx a ha _ T hT
  intro i c hc x y δ hδ hK
  have hend' : ζ c + ρ⁻¹ • δ ∈ D := by
    obtain ⟨ε, hε, rfl⟩ := hδ
    simpa only [smul_smul, inv_mul_cancel₀ hρ.ne', one_smul] using hend c hc ε hε
  have hod : DifferentiableAt ℝ (fun t : P ↦ osc ((t, (x, y)), δ)) c :=
    ((ho.contDiffAt (((hU.prod isOpen_univ).prod hV).mem_nhds
      ⟨⟨hc, mem_univ _⟩, hFV hδ⟩)).differentiableAt (by simp)).comp c
        ((differentiableAt_id.prodMk (differentiableAt_const (x, y))).prodMk (differentiableAt_const δ))
  have hd := (hod.hasFDerivAt.hasLineDerivAt (w i)).unique
    (hasLineDerivAt_reverseOscillation hD hcD hD0 (hS y) (hhom y)
      (hζ c hc) (hζD c hc) hρ hend' x (w i))
  have hq (j : Fin n) : physicalField ρ (a (idx i j)) ((c, (x, y)), δ) =
      reverseParameterRow S ζ ρ (J c) c (w i) y δ j := by
    simpa only [physicalField, smul_smul, mul_inv_cancel₀ hρ.ne', one_smul] using hC i j _ hK
  have hinv : J c y δ * B c y δ = 1 := by
    simpa only [smul_smul, mul_inv_cancel₀ hρ.ne', one_smul] using hJB _ hK
  have hg (l : Fin n) : partialDeriv (fun z ↦ phaseIncrement S (ζ c) ρ z δ) y l =
      (B c y δ).mulVec (fun k ↦ δ k) l := by
    simpa only [smul_smul, mul_inv_cancel₀ hρ.ne', one_smul] using hgrad _ hK l
  have hsp : DifferentiableAt ℝ (fun z ↦ phaseIncrement S (ζ c) ρ z δ) y := by
    have hdΦ := (hΦ.contDiffAt (x := ((c, y), δ)) (((hU.prod isOpen_univ).prod hV).mem_nhds
      ⟨⟨hc, mem_univ y⟩, hFV hδ⟩)).differentiableAt (by simp)
    have hm : DifferentiableAt ℝ (fun z : E ↦ ((c, z), δ)) y :=
      ((differentiableAt_const c).prodMk differentiableAt_id).prodMk (differentiableAt_const δ)
    exact hdΦ.comp y hm
  rw [hd, reverse_parameter_phase_trade S (ζ c) ρ x y δ
    (fun z ↦ phaseCoefficient S ζ ρ c (w i) z δ) (fun z ↦ B c z δ) (fun z ↦ J c z δ) hinv hsp hg]
  simp only [hq, reverseParameterRow, neg_mul, Finset.sum_neg_distrib, neg_neg, partialDeriv, osc]

/-- Insert the existing physical Fourier normalization exactly once after
the scalar parameter-kernel realization. The resulting family has the same
normalization as `scalarGraphOperator` in the joint spatial assembly, by
`normalizedScalarAmplitude_frozenField`. The factor is fixed during every
parameter derivative (`app:ch_response:eq:direct-envelope-profile`). -/
theorem hasParameterAmplitudeTransfer_fourierNormalization
    {U : Set P} {X Y F : Set E} {K : Set Z}
    (w : Fin m → P) (idx : Fin m → Fin n → ι) (a : ι → Z → ℂ)
    (T : P → (Z → ℂ) → L² →L[ℂ] L²)
    (h : HasParameterAmplitudeTransfer U w (fun i ↦ parameterAmplitudeDirection (w i))
      (fun i ↦ parameterSourceTerms (idx i)) (fun _ _ ↦ ContinuousLinearMap.mul ℝ ℂ)
      idx a T (SupportedJointAmplitude U X Y F K)) :
    HasParameterAmplitudeTransfer U w (fun i ↦ parameterAmplitudeDirection (w i))
      (fun i ↦ parameterSourceTerms (idx i)) (fun _ _ ↦ ContinuousLinearMap.mul ℝ ℂ)
      idx a (fun c b ↦ (((2 * Real.pi) ^ n : ℂ)⁻¹) • T c b)
      (SupportedJointAmplitude U X Y F K) := by
  intro b hb f df pf i c hc hdf hpf
  have hd := HasDerivAt.const_smul (((2 * Real.pi) ^ n : ℂ)⁻¹)
    (h b hb f df pf i c hc hdf hpf)
  simpa only [HasLineDerivAt, smul_add, Finset.smul_sum, smul_apply, Pi.smul_def] using hd

end JanetCartan.ResponseTransfer.NormalizedTransfer
