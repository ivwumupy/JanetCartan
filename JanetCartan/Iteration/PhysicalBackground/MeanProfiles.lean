module

public import JanetCartan.Iteration.PhysicalBackground.BaseProfiles
public import JanetCartan.Analysis.Operator.MeasureEnvelopes.Derivatives
public import JanetCartan.Analysis.Calculus.CompactParameterIntegral
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.PhysicalBounds.CompactJets
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmplitudeGrades.PhaseJets
public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.PhysicalMean
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.NullFlowDependence.CompactComposition

/-!
# The actual weighted current mean from the retained principal matrices

Fixed carrier integration preserves physical derivative profiles. Its jets
are justified by dominated differentiation on the original compact weight
support, not assumed as an analytic input. The principal Gram tensor is the
literal constant-initial physical mean. These are source-profile operations
for `app:ch_background:prop:bg-current`, not a new carrier selection.
-/

@[expose] public noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff Matrix Matrix.Norms.Frobenius Topology
set_option backward.isDefEq.respectTransparency false

namespace JanetCartan.PhysicalBackground
open ContinuumRow PositiveBackground DerivativeBounds ResponseTransfer.GradedPrimitives

private theorem cNorm_weighted_integral_le_joint
    {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K U W : Set (Euclidean n)} (hU : IsOpen U) (hW : IsOpen W)
    (hKU : K ⊆ U) (hUW : U ⊆ W)
    {V L : Set CarrierParameter} (hV : IsOpen V) (hL : IsCompact L) (hLV : L ⊆ V)
    {J : Set (Euclidean n × CarrierParameter)} (hJ : IsCompact J)
    (hJW : J ⊆ W ×ˢ V) (hUL : U ×ˢ L ⊆ J)
    (w : CarrierParameter → ℝ) (hw : ContDiff ℝ ∞ w)
    (hsupp : ∀ z, z ∉ L → w z = 0)
    (f : Euclidean n × CarrierParameter → E) (hf : ContDiffOn ℝ ∞ f (W ×ˢ V)) (s : ℕ) :
    cNorm K s (fun x ↦ ∫ z, w z • f (x, z) ∂(volume.prod volume)) ≤
      (s + 1 : ℝ) * (∫ z in L, ‖w z‖ ∂(volume.prod volume)) * cNorm J s f := by
  let μ : Measure CarrierParameter := volume.prod volume
  let : IsFiniteMeasure (μ.restrict L) := isFiniteMeasure_restrict.mpr hL.measure_lt_top.ne
  let A := cNorm J s f
  have hA : 0 ≤ A := cNorm_nonneg ..
  let B : Euclidean n × CarrierParameter → E := fun p ↦ w p.2 • f p
  have hB : ContDiffOn ℝ ∞ B (W ×ˢ V) := (hw.comp contDiff_snd).contDiffOn.smul hf
  have he : (fun x ↦ ∫ z, w z • f (x, z) ∂μ) =
      (fun x ↦ ∫ z in L, w z • f (x, z) ∂μ) := by
    funext x
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    rw [hsupp z hz, zero_smul]
  rw [he]
  have hpart (z) (hz : z ∈ L) (x) (hx : x ∈ U) :
      ContDiffAt ℝ ∞ (fun y ↦ f (y, z)) x :=
    (hf.contDiffAt ((hW.prod hV).mem_nhds ⟨hUW hx, hLV hz⟩)).comp x
      (contDiffAt_id.prodMk contDiffAt_const)
  have hm (j : ℕ) (x) (hx : x ∈ U) : AEStronglyMeasurable
      (fun z ↦ iteratedFDeriv ℝ j (fun y ↦ B (y, z)) x) (μ.restrict L) :=
    (integrableOn_compactParameter hL hLV
      (RawPrimary.contDiffOn_atomPhysicalJet hW hV hB j).continuousOn (hUW hx)).aestronglyMeasurable
  have hi : Integrable (fun z ↦ ‖w z‖ * A) (μ.restrict L) :=
    ((hw.continuous.norm.continuousOn).integrableOn_compact' hL hL.measurableSet).mul_const A
  have hb (j : ℕ) (hj : j ≤ s) : ∀ᵐ z ∂μ.restrict L, ∀ x ∈ U,
      ‖iteratedFDeriv ℝ j (fun y ↦ B (y, z)) x‖ ≤ ‖w z‖ * A := by
    filter_upwards [ae_restrict_mem hL.measurableSet] with z hz x hx
    rw [show (fun y ↦ B (y, z)) = (fun y ↦ w z • f (y, z)) from rfl,
      iteratedFDeriv_const_smul_apply' ((hpart z hz x hx).of_le (by simp)), norm_smul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact (RawPrimary.AmplitudeGrades.norm_iteratedFDeriv_physical_slice_le (hW.prod hV) hf
      ⟨hUW hx, hLV hz⟩ j).trans (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hJ
        (fun p hp ↦ (hf.contDiffAt ((hW.prod hV).mem_nhds (hJW hp))).of_le (by simp))
        (hUL ⟨hx, hz⟩) hj)
  have hh := MeasureEnvelopes.cNorm_integral_le (μ := μ.restrict L)
    (A := fun z x ↦ B (x, z)) (b := fun _ z ↦ ‖w z‖ * A) (r := s) hU
    (by
      filter_upwards [ae_restrict_mem hL.measurableSet] with z hz x hx
      exact ((hpart z hz x hx).const_smul (w z)).of_le (by simp))
    (fun j _ x hx ↦ hm j x hx) (fun _ _ ↦ hi) hb
    (fun _ _ ↦ ae_of_all _ (fun z ↦ mul_nonneg (norm_nonneg _) hA)) hKU
  simpa only [B, integral_mul_const, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one, mul_assoc] using hh

private def principalGram {n N : ℕ} (D : Matrix (Fin N) (Fin n) ℝ) : MetricTensor n := Dᵀ * D

private theorem contDiff_principalGram {n N : ℕ} : ContDiff ℝ ∞ (@principalGram n N) := by
  let L := (Matrix.transposeLinearEquiv (Fin N) (Fin n) ℝ ℝ).toLinearMap.toContinuousLinearMap
  exact (matrixMulBilinear (Fin n) (Fin N) (Fin n)).contDiff.comp L.contDiff |>.clm_apply contDiff_id

private theorem exists_principalGram_profile {n N : ℕ}
    {J : Set (Euclidean n × CarrierParameter)} (hJ : IsCompact J)
    (A : ℕ → ℝ) (hA : ∀ s, 0 ≤ A s) :
    ∃ C : ℕ → ℝ, (∀ s, 0 ≤ C s) ∧
      ∀ D : Euclidean n × CarrierParameter → Matrix (Fin N) (Fin n) ℝ,
      (∀ p ∈ J, ContDiffAt ℝ ∞ D p) →
      ∀ (r₀ : ℕ) (T : ℝ), 1 ≤ T → HasDerivativeProfile J D r₀ T A →
      HasDerivativeProfile J (fun p ↦ principalGram (D p)) r₀ T C := by
  let S := closedBall (0 : Matrix (Fin N) (Fin n) ℝ) (A 0)
  let B := fun s ↦ cNorm S s (@principalGram n N)
  have hB (s) : 0 ≤ B s := cNorm_nonneg ..
  refine ⟨fun s ↦ ∑ j ∈ Finset.range (s + 1), compositionConstant B A j,
    fun s ↦ Finset.sum_nonneg (fun j _ ↦ compositionConstant_nonneg hB hA j), ?_⟩
  intro D hD r₀ T hT hp
  have hrange (p) (hpJ : p ∈ J) : D p ∈ S := by
    have h := (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hJ
      (fun q hq ↦ (hD q hq).of_le (by simp : (0 : ℕ∞ω) ≤ ∞)) hpJ (Nat.zero_le 0)).trans (hp 0)
    simpa only [S, mem_closedBall, dist_zero_right, norm_iteratedFDeriv_zero,
      Nat.zero_sub, pow_zero, mul_one] using h
  exact hasDerivativeProfile_fixed_smooth_comp hJ hD (fun _ _ ↦ contDiff_principalGram.contDiffAt)
    B A hB hA hT r₀ hp (fun j p hpJ ↦
      norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall _ _)
        (fun _ _ ↦ contDiff_principalGram.contDiffAt.of_le (by simp : (j : ℕ∞ω) ≤ ∞))
        (hrange p hpJ) le_rfl)

private def tensorCoordinate {n : ℕ} (i j : Fin n) : MetricTensor n →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ ℝ) j).comp
      (LinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ Fin n → ℝ) i))

/-- The literal uncorrected physical mean is the fixed weighted Gram integral
of the SAME retained real principal matrices. No sample, frozen field, or new
mean is selected (`app:ch_background:eq:bg-affine-mean`). -/
theorem physicalDensityMean_zero_eqOn_principalGram
    {n N : ℕ} {ι : Type*} [Fintype ι]
    (d : ι → CarrierData n N) (χ : ι → CarrierParameter → ℝ)
    (hχ : ∀ a, ContDiff ℝ ∞ (χ a)) (hχc : ∀ a, HasCompactSupport (χ a))
    {W : Set (Euclidean n)} (V : ι → Set CarrierParameter)
    (hχV : ∀ a, tsupport (χ a) ⊆ V a)
    (hD : ∀ a, ContinuousOn
      (fun p : Euclidean n × CarrierParameter ↦ LeadingWave.principalMatrix
        ((d a).normalField p.1 p.2) ((d a).covector p.1 p.2)) (W ×ˢ V a)) :
    EqOn (physicalDensityMean d χ 0)
      (fun x ↦ ∑ a, ∫ z, (χ a z ^ 2) •
        ((LeadingWave.principalMatrix ((d a).normalField x z) ((d a).covector x z))ᵀ *
          LeadingWave.principalMatrix ((d a).normalField x z) ((d a).covector x z))
        ∂(volume.prod volume)) W := by
  intro x hx
  apply Finset.sum_congr rfl
  intro a _
  let D := fun z ↦ LeadingWave.principalMatrix ((d a).normalField x z) ((d a).covector x z)
  let f := fun z ↦ χ a z ^ 2 • principalGram (D z)
  have hc : ContinuousOn f (tsupport (χ a)) :=
    ((hχ a).continuous.continuousOn.pow 2).smul
      (contDiff_principalGram.continuous.comp_continuousOn
        ((hD a).comp (continuousOn_const.prodMk continuousOn_id) (fun _ hz ↦ ⟨hx, hχV a hz⟩)))
  have hi : Integrable f (volume.prod volume) := by
    apply (integrableOn_iff_integrable_of_support_subset ?_).mp
      (hc.integrableOn_compact' (hχc a) (isClosed_tsupport _).measurableSet)
    intro z hz
    by_contra h
    exact hz (by simp [f, image_eq_zero_of_notMem_tsupport h])
  ext i j
  have he := (tensorCoordinate i j).integral_comp_comm hi
  change (∫ z, f z i j ∂(volume.prod volume)) = (∫ z, f z ∂(volume.prod volume)) i j at he
  calc
    _ = ∫ z, f z i j ∂(volume.prod volume) := by
      apply integral_congr_ae
      filter_upwards [] with z
      simp only [Pi.zero_apply, add_zero, mul_one, f, principalGram, D,
        LeadingWave.principalMatrix_transpose_mul, Matrix.smul_apply, smul_eq_mul]
      ring
    _ = _ := he

/-- The SAME constant-initial current physical mean inherits the retained
principal-matrix profile, with no derivative loss under the original weighted
carrier integral. The constants are fixed before current carrier data, scale
and reserve. The principal-matrix input is the checked joint leading bound of
`PhysicalPrimary.exists_history_retained_leading_data`, not a mean-profile
success assumption (`app:ch_background:eq:bg-current-profile`). -/
theorem exists_physicalDensityMean_zero_profile
    {n N : ℕ} {ι : Type*} [Fintype ι]
    {K U W : Set (Euclidean n)} (hK : IsCompact K) (hU : IsOpen U) (hW : IsOpen W)
    (hKU : K ⊆ U) (hUW : U ⊆ W)
    (χ : ι → CarrierParameter → ℝ) (hχ : ∀ a, ContDiff ℝ ∞ (χ a))
    (hχc : ∀ a, HasCompactSupport (χ a))
    (V : ι → Set CarrierParameter) (hV : ∀ a, IsOpen (V a))
    (hχV : ∀ a, tsupport (χ a) ⊆ V a)
    (J : ι → Set (Euclidean n × CarrierParameter)) (hJ : ∀ a, IsCompact (J a))
    (hJW : ∀ a, J a ⊆ W ×ˢ V a) (hUJ : ∀ a, U ×ˢ tsupport (χ a) ⊆ J a)
    (A : ι → ℕ → ℝ) (hA : ∀ a s, 0 ≤ A a s) :
    ∃ C : ℕ → ℝ, (∀ s, 0 ≤ C s) ∧
      ∀ d : ι → CarrierData n N,
      (∀ a, ContDiffOn ℝ ∞
        (fun p : Euclidean n × CarrierParameter ↦ LeadingWave.principalMatrix
          ((d a).normalField p.1 p.2) ((d a).covector p.1 p.2)) (W ×ˢ V a)) →
      ∀ (r₀ : ℕ) (T : ℝ), 1 ≤ T →
      (∀ a, HasDerivativeProfile (J a)
        (fun p : Euclidean n × CarrierParameter ↦ LeadingWave.principalMatrix
          ((d a).normalField p.1 p.2) ((d a).covector p.1 p.2)) r₀ T (A a)) →
      HasDerivativeProfile K (physicalDensityMean d χ 0) r₀ T C := by
  classical
  choose B hB hgram using fun a ↦ exists_principalGram_profile (N := N) (hJ a) (A a) (hA a)
  let mass := fun a ↦ ∫ z in tsupport (χ a), ‖χ a z ^ 2‖ ∂(volume.prod volume)
  have hmass (a) : 0 ≤ mass a := integral_nonneg (fun _ ↦ norm_nonneg _)
  let C := fun s : ℕ ↦ ∑ a, (s + 1 : ℝ) * mass a * B a s
  have hC (s) : 0 ≤ C s := Finset.sum_nonneg (fun a _ ↦
    mul_nonneg (mul_nonneg (by positivity) (hmass a)) (hB a s))
  refine ⟨C, hC, ?_⟩
  intro d hD r₀ T hT hDp s
  let D := fun a (p : Euclidean n × CarrierParameter) ↦
    LeadingWave.principalMatrix ((d a).normalField p.1 p.2) ((d a).covector p.1 p.2)
  let G := fun a (x : Euclidean n) ↦ ∫ z, χ a z ^ 2 • principalGram (D a (x, z)) ∂(volume.prod volume)
  have hg (a) : ContDiffOn ℝ ∞ (fun p ↦ principalGram (D a p)) (W ×ˢ V a) :=
    contDiff_principalGram.comp_contDiffOn (hD a)
  have hGs (a) : ContDiffOn ℝ ∞ (G a) W := by
    let : IsFiniteMeasure ((volume.prod volume : Measure CarrierParameter).restrict (tsupport (χ a))) :=
      isFiniteMeasure_restrict.mpr (hχc a).measure_lt_top.ne
    have he : G a = fun x ↦ ∫ z in tsupport (χ a),
        χ a z ^ 2 • principalGram (D a (x, z)) ∂(volume.prod volume) := by
      funext x
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      simp only [image_eq_zero_of_notMem_tsupport hz, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, zero_smul]
    rw [he]
    exact contDiffOn_compactParameterIntegral hW (hV a) (hχc a) (hχV a)
      (((hχ a).pow 2 |>.comp contDiff_snd).contDiffOn.smul (hg a))
  have heq := physicalDensityMean_zero_eqOn_principalGram d χ hχ hχc V hχV
    (fun a ↦ (hD a).continuousOn)
  have hnorm : cNorm K s (physicalDensityMean d χ 0) = cNorm K s (fun x ↦ ∑ a, G a x) := by
    apply GeometricProfile.cNorm_eq_of_eventuallyEq
    intro x hx
    filter_upwards [hW.mem_nhds (hUW (hKU hx))] with y hy
    exact heq hy
  rw [hnorm]
  have hsum := cNorm_sum_le_of_contDiffAt Finset.univ hK
    (fun a _ x hx ↦ ((hGs a).contDiffAt (hW.mem_nhds (hUW (hKU hx)))).of_le (by simp : (s : ℕ∞ω) ≤ ∞))
  apply hsum.trans
  have each (a) : cNorm K s (G a) ≤ ((s + 1 : ℝ) * mass a * B a s) * T ^ (s - r₀) := by
    have hp := hgram a (D a)
      (fun p hp ↦ (hD a).contDiffAt ((hW.prod (hV a)).mem_nhds (hJW a hp))) r₀ T hT (hDp a) s
    have hi := cNorm_weighted_integral_le_joint hU hW hKU hUW (hV a) (hχc a) (hχV a)
      (hJ a) (hJW a) (hUJ a) (fun z ↦ χ a z ^ 2) ((hχ a).pow 2)
      (fun z hz ↦ by rw [image_eq_zero_of_notMem_tsupport hz]; norm_num)
      (fun p ↦ principalGram (D a p)) (hg a) s
    exact hi.trans ((mul_le_mul_of_nonneg_left hp
      (mul_nonneg (by positivity) (hmass a))).trans_eq (by ring))
  simpa only [C, Finset.sum_mul] using Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) ↦ each a)

private theorem contDiff_principalMatrix_pair {n N : ℕ} :
    ContDiff ℝ ∞ (fun p : Euclidean N × Euclidean n ↦ LeadingWave.principalMatrix p.1 p.2) := by
  let C : (Fin N → Fin n → ℝ) →L[ℝ] Matrix (Fin N) (Fin n) ℝ :=
    LinearMap.toContinuousLinearMap (LinearMap.id : (Fin N → Fin n → ℝ) →ₗ[ℝ] Matrix (Fin N) (Fin n) ℝ)
  apply C.contDiff.comp
  apply contDiff_pi.mpr
  intro a
  apply contDiff_pi.mpr
  intro i
  exact ((((EuclideanSpace.proj a : Euclidean N →L[ℝ] ℝ)).contDiff.comp contDiff_fst).mul
    (((EuclideanSpace.proj i : Euclidean n →L[ℝ] ℝ)).contDiff.comp contDiff_snd)).neg

/-- Finite-low continuity of the literal current mean follows from the actual
normal and phase-covector differences on the original support. The normal
input is produced by retained leading `RetainedDataComparison`; the covector
input is produced by `exists_originalCoefficient_carrier_immersion_tolerance`.
Neither a small current mean nor a successful source is a premise. The weights
and reference fields are fixed before the varying current data
(`app:ch_background:prop:bg-current`, fixed-neighborhood step). -/
theorem exists_physicalDensityMean_zero_sub_tolerance
    {n N : ℕ} {ι : Type*} [Fintype ι]
    {K U W : Set (Euclidean n)} (hK : IsCompact K) (hU : IsOpen U) (hW : IsOpen W)
    (hKU : K ⊆ U) (hUW : U ⊆ W)
    (χ : ι → CarrierParameter → ℝ) (hχ : ∀ a, ContDiff ℝ ∞ (χ a))
    (hχc : ∀ a, HasCompactSupport (χ a))
    (V : ι → Set CarrierParameter) (hV : ∀ a, IsOpen (V a))
    (hχV : ∀ a, tsupport (χ a) ⊆ V a)
    (J : ι → Set (Euclidean n × CarrierParameter)) (hJ : ∀ a, IsCompact (J a))
    (hJW : ∀ a, J a ⊆ W ×ˢ V a) (hUJ : ∀ a, U ×ˢ tsupport (χ a) ⊆ J a)
    (d₀ : ι → CarrierData n N)
    (hν₀ : ∀ a, ContDiffOn ℝ ∞ (Function.uncurry (d₀ a).normalField) (W ×ˢ V a))
    (hξ₀ : ∀ a, ContDiffOn ℝ ∞ (Function.uncurry (d₀ a).covector) (W ×ˢ V a))
    (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ι → ℝ, (∀ a, 0 < δ a) ∧
      ∀ d : ι → CarrierData n N,
      (∀ a, ContDiffOn ℝ ∞ (Function.uncurry (d a).normalField) (W ×ˢ V a)) →
      (∀ a, ContDiffOn ℝ ∞ (Function.uncurry (d a).covector) (W ×ˢ V a)) →
      (∀ a, cNorm (J a) m (Function.uncurry (d a).normalField - Function.uncurry (d₀ a).normalField) +
        cNorm (J a) m (Function.uncurry (d a).covector - Function.uncurry (d₀ a).covector) < δ a) →
      cNorm K m (physicalDensityMean d χ 0 - physicalDensityMean d₀ χ 0) < ε := by
  classical
  let cost := fun a ↦ (m + 1 : ℝ) * ∫ z in tsupport (χ a), ‖χ a z ^ 2‖ ∂(volume.prod volume)
  have hcost (a) : 0 ≤ cost a := mul_nonneg (by positivity) (integral_nonneg (fun _ ↦ norm_nonneg _))
  let total := ∑ a, cost a
  have htotal : 0 ≤ total := Finset.sum_nonneg (fun a _ ↦ hcost a)
  let η := ε / (1 + total)
  have hη : 0 < η := div_pos hε (by linarith)
  let Φ : Euclidean N × Euclidean n → MetricTensor n := fun p ↦
    principalGram (LeadingWave.principalMatrix p.1 p.2)
  have hΦ : ContDiff ℝ ∞ Φ := contDiff_principalGram.comp contDiff_principalMatrix_pair
  let f₀ := fun a (p : Euclidean n × CarrierParameter) ↦ ((d₀ a).normalField p.1 p.2, (d₀ a).covector p.1 p.2)
  have hf₀ (a) (p) (hp : p ∈ J a) : ContDiffAt ℝ ∞ (f₀ a) p :=
    ((hν₀ a).prodMk (hξ₀ a)).contDiffAt ((hW.prod (hV a)).mem_nhds (hJW a hp))
  have hchoice (a) : ∃ δ > (0 : ℝ),
      ∀ f : Euclidean n × CarrierParameter → Euclidean N × Euclidean n,
        (∀ p ∈ J a, ContDiffAt ℝ ∞ f p) → cNorm (J a) m (f - f₀ a) < δ →
          cNorm (J a) m (Φ ∘ f - Φ ∘ f₀ a) < η := by
    obtain ⟨L, _hL, _hLU, δ, hδ, hb⟩ :=
      ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.NullFlowDependence.exists_cNorm_comp_sub_lt_with_buffer
        (hJ a) isOpen_univ hΦ.contDiffOn (hf₀ a) (mapsTo_univ _ _) m hη
    refine ⟨δ, hδ, ?_⟩
    intro f hf hsmall
    exact hb Φ f hΦ.contDiffOn hf (by simpa only [sub_self, cNorm_zero] using hδ) hsmall
  choose δ hδ hcompare using hchoice
  refine ⟨δ, hδ, ?_⟩
  intro d hν hξ hsmall
  let f := fun a (p : Euclidean n × CarrierParameter) ↦ ((d a).normalField p.1 p.2, (d a).covector p.1 p.2)
  let diff := fun a ↦ Φ ∘ f a - Φ ∘ f₀ a
  let G := fun a (x : Euclidean n) ↦ ∫ z, χ a z ^ 2 • diff a (x, z) ∂(volume.prod volume)
  have hf (a) : ContDiffOn ℝ ∞ (f a) (W ×ˢ V a) := (hν a).prodMk (hξ a)
  have hdiff (a) : ContDiffOn ℝ ∞ (diff a) (W ×ˢ V a) :=
    (hΦ.comp_contDiffOn (hf a)).sub (hΦ.comp_contDiffOn ((hν₀ a).prodMk (hξ₀ a)))
  have hdifference (a) : cNorm (J a) m (diff a) < η := by
    apply hcompare a (f a) (fun p hp ↦ (hf a).contDiffAt ((hW.prod (hV a)).mem_nhds (hJW a hp)))
    have hp := FullPhaseCharts.InverseEstimates.cNorm_prodMk_le_on (J a) (hJ a) m
      (fun p hp ↦ ((hν a).sub (hν₀ a)).contDiffAt ((hW.prod (hV a)).mem_nhds (hJW a hp)) |>.of_le (by simp))
      (fun p hp ↦ ((hξ a).sub (hξ₀ a)).contDiffAt ((hW.prod (hV a)).mem_nhds (hJW a hp)) |>.of_le (by simp))
    exact hp.trans_lt (hsmall a)
  have hint (a) (g : Euclidean n × CarrierParameter → MetricTensor n)
      (hg : ContinuousOn g (W ×ˢ V a)) (x) (hx : x ∈ W) :
      Integrable (fun z ↦ χ a z ^ 2 • g (x, z)) (volume.prod volume) := by
    have hc := ((hχ a).continuous.continuousOn.pow 2).smul
      (hg.comp (continuousOn_const.prodMk continuousOn_id) (fun _ hz ↦ ⟨hx, hχV a hz⟩))
    apply (integrableOn_iff_integrable_of_support_subset ?_).mp
      (hc.integrableOn_compact' (hχc a) (isClosed_tsupport _).measurableSet)
    intro z hz
    by_contra h
    exact hz (by simp [image_eq_zero_of_notMem_tsupport h])
  have hGs (a) : ContDiffOn ℝ ∞ (G a) W := by
    let : IsFiniteMeasure ((volume.prod volume : Measure CarrierParameter).restrict (tsupport (χ a))) :=
      isFiniteMeasure_restrict.mpr (hχc a).measure_lt_top.ne
    have he : G a = fun x ↦ ∫ z in tsupport (χ a), χ a z ^ 2 • diff a (x, z) ∂(volume.prod volume) := by
      funext x
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      simp [image_eq_zero_of_notMem_tsupport hz]
    rw [he]
    exact contDiffOn_compactParameterIntegral hW (hV a) (hχc a) (hχV a)
      (((hχ a).pow 2 |>.comp contDiff_snd).contDiffOn.smul (hdiff a))
  have heq : EqOn (physicalDensityMean d χ 0 - physicalDensityMean d₀ χ 0)
      (fun x ↦ ∑ a, G a x) W := by
    intro x hx
    have he := physicalDensityMean_zero_eqOn_principalGram d χ hχ hχc V hχV
      (fun a ↦ (contDiff_principalMatrix_pair.comp_contDiffOn (hf a)).continuousOn) hx
    have he₀ := physicalDensityMean_zero_eqOn_principalGram d₀ χ hχ hχc V hχV
      (fun a ↦ (contDiff_principalMatrix_pair.comp_contDiffOn ((hν₀ a).prodMk (hξ₀ a))).continuousOn) hx
    change physicalDensityMean d χ 0 x - physicalDensityMean d₀ χ 0 x = _
    rw [he, he₀, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    have hi := hint a (Φ ∘ f a) (hΦ.comp_contDiffOn (hf a)).continuousOn x hx
    have hi₀ := hint a (Φ ∘ f₀ a) (hΦ.comp_contDiffOn ((hν₀ a).prodMk (hξ₀ a))).continuousOn x hx
    change (∫ z, χ a z ^ 2 • (Φ ∘ f a) (x, z) ∂(volume.prod volume)) -
      (∫ z, χ a z ^ 2 • (Φ ∘ f₀ a) (x, z) ∂(volume.prod volume)) = _
    rw [← integral_sub hi hi₀]
    apply integral_congr_ae
    filter_upwards [] with z
    exact (smul_sub (χ a z ^ 2) _ _).symm
  have hnorm : cNorm K m (physicalDensityMean d χ 0 - physicalDensityMean d₀ χ 0) =
      cNorm K m (fun x ↦ ∑ a, G a x) := by
    apply GeometricProfile.cNorm_eq_of_eventuallyEq
    intro x hx
    filter_upwards [hW.mem_nhds (hUW (hKU hx))] with y hy
    exact heq hy
  rw [hnorm]
  have hsum := cNorm_sum_le_of_contDiffAt Finset.univ hK
    (fun a _ x hx ↦ ((hGs a).contDiffAt (hW.mem_nhds (hUW (hKU hx)))).of_le (by simp : (m : ℕ∞ω) ≤ ∞))
  have each (a) : cNorm K m (G a) ≤ cost a * η := by
    have hi := cNorm_weighted_integral_le_joint hU hW hKU hUW (hV a) (hχc a) (hχV a)
      (hJ a) (hJW a) (hUJ a) (fun z ↦ χ a z ^ 2) ((hχ a).pow 2)
      (fun z hz ↦ by rw [image_eq_zero_of_notMem_tsupport hz]; norm_num) (diff a) (hdiff a) m
    exact hi.trans (mul_le_mul_of_nonneg_left (hdifference a).le (hcost a))
  have hall : cNorm K m (fun x ↦ ∑ a, G a x) ≤ total * η :=
    hsum.trans (by simpa only [total, Finset.sum_mul] using Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) ↦ each a))
  apply hall.trans_lt
  have hηeq : (1 + total) * η = ε := mul_div_cancel₀ _ (by linarith : (1 + total) ≠ 0)
  nlinarith

end JanetCartan.PhysicalBackground
