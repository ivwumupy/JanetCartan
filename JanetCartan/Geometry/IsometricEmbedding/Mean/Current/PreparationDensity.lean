module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.DensityRepresentative
public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.Preparation

/-!+# The smooth signed update from the same original inverse

For `app:ch_mean_pairs:eq:mean-density-recursion`, restrict the SAME
corrected-positive `Q₀` and augmented adjoint to smooth sources. Full raw
membership, supplied by the actual inverse/initial-adjoint producers, now
constructs a jointly smooth supported density. Its transported mean is
exactly the literal uncut density mean, pointwise on the output torus.
Consequently the previously proved complete cancellation applies to this
smooth representative, retaining the exterior component globally.

These are actual density functions, not a record assuming successful
preparation. The row and its raw regularity still require instantiation;
finite-reserve bounds and the finite preparation remain separate obligations.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff

namespace JanetCartan.CurrentMean
open ContinuumRow CarrierSobolev UncutDensity

variable {n N : ℕ} {ι : Type*} [Fintype ι]

omit [Fintype ι] in
/-- Uniqueness on the original density space is pointwise in both sets of
variables. This promotes the actual synthesis linearity to smooth updates
(`app:ch_mean_pairs:eq:mean-density-recursion`). -/
theorem smoothSupportedDensity_ext_of_ae_all_positions
    {K : ι → Set CarrierParameter} (v w : smoothSupportedDensity n ι K)
    (hvw : ∀ a, ∀ᵐ z ∂(volume.prod volume : Measure CarrierParameter), ∀ y,
      v.val a (z,y) = w.val a (z,y)) : v = w := by
  apply Subtype.ext
  funext a p
  have he := Measure.eq_of_ae_eq ((hvw a).mono fun _ hz ↦ hz p.2)
    (((v.property a).1.continuous).comp (continuous_id.prodMk continuous_const))
    (((w.property a).1.continuous).comp (continuous_id.prodMk continuous_const))
  exact congrFun he p.1

section FixedRow

variable (d : ι → CarrierData n N)
    (hρsmooth : ∀ a, ContDiff ℝ ∞
      (fun p : CarrierVariable n ↦ ((d a).angularCutoff p.1 p.2 : ℂ)))
    (hcρ : ∀ a, HasCompactSupport
      (fun p : CarrierVariable n ↦ ((d a).angularCutoff p.1 p.2 : ℂ)))
    (hχsmooth : ∀ a, ContDiff ℝ ∞ (d a).highCutoff)
    (hlow : ∀ a r, r ≤ 1 → (d a).highCutoff r = 0)
    (hχ : ∀ a r, |(d a).highCutoff r| ≤ 1)
    (A : ι → ℝ) (hA : ∀ a, 0 ≤ A a)
    (hρ : ∀ a z θ, |(d a).angularCutoff z θ| ≤ A a)
    (K : ι → Set CarrierParameter) (hK : ∀ a, IsCompact (K a))
    (hsupp : ∀ a z, z ∉ K a → ∀ θ, (d a).angularCutoff z θ = 0)
    (image : OutputL2 n →L[ℝ] OutputL2 n)
    (U : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n) (ψ : C(Torus n, ℝ))
    (Q₀ : OutputL2 n →L[ℝ] OutputL2 n)
    (hreg : ∀ (e : SmoothResidual n) (s : ℕ),
      (augmentedRow image U ψ).adjoint (Q₀ (smoothResidualToL2 n e)) ∈
        augmentedInputLevel n ι s)

include hreg in
/-- The actual smooth source supplies all mixed raw orders of each of the
SAME canonical carrier slots, before any cutoff
(`app:ch_mean_pairs:eq:mean-density-recursion`). -/
private theorem preparation_carrier_mem (e : SmoothResidual n) (a : ι) (s : ℕ) :
    MemRawSobolev s
      (((augmentedRow image U ψ).adjoint (Q₀ (smoothResidualToL2 n e))).fst.snd a) :=
  ((mem_augmentedInputLevel_iff s _).mp (hreg e s)).2.1 a

include hρsmooth hcρ hχsmooth hlow hχ hA hρ hK hsupp hreg in
/-- Existence of the smooth supported update, proved from the actual
half-order synthesis on the original adjoint. The equality refers to
`preparationDensity` with this same `Q₀` and source
(`app:ch_mean_pairs:eq:mean-density-recursion`). -/
theorem exists_preparationDensityRepresentative (e : SmoothResidual n) :
    ∃ v : smoothSupportedDensity n ι K, ∀ a,
      v.val a =ᵐ[carrierMeasure n]
        preparationDensity d image U ψ Q₀ (smoothResidualToL2 n e) a := by
  choose f hf he using fun a ↦ exists_smooth_initialDensity (d a)
    (hρsmooth a) (hcρ a) (hχsmooth a) (hlow a) (hχ a) (hA a) (hρ a) (-2)
    (((augmentedRow image U ψ).adjoint (Q₀ (smoothResidualToL2 n e))).fst.snd a)
    (preparation_carrier_mem image U ψ Q₀ hreg e a)
  refine ⟨⟨f, fun a ↦ ⟨hf a, ?_⟩⟩, he⟩
  exact initialDensityRepresentative_zero_off_carrier (d a) (-2) _
    (hK a).isClosed (hsupp a) (f a) (hf a).continuous (he a)

/-- One smooth signed density on the original supported space. The choice
is independent of derivative order and will be unique by continuity
(`app:ch_mean_pairs:eq:mean-density-recursion`). -/
def preparationDensityRepresentative (e : SmoothResidual n) :
    smoothSupportedDensity n ι K :=
  (exists_preparationDensityRepresentative d hρsmooth hcρ hχsmooth hlow hχ
    A hA hρ K hK hsupp image U ψ Q₀ hreg e).choose

/-- The smooth signed update represents precisely the literal uncut density
of the fixed row (`app:ch_mean_pairs:eq:mean-density-recursion`). -/
theorem preparationDensityRepresentative_ae (e : SmoothResidual n) (a : ι) :
    (preparationDensityRepresentative d hρsmooth hcρ hχsmooth hlow hχ
      A hA hρ K hK hsupp image U ψ Q₀ hreg e).val a =ᵐ[carrierMeasure n]
        preparationDensity d image U ψ Q₀ (smoothResidualToL2 n e) a :=
  (exists_preparationDensityRepresentative d hρsmooth hcρ hχsmooth hlow hχ
    A hA hρ K hK hsupp image U ψ Q₀ hreg e).choose_spec a

/-- The unique continuous representative is fixed at every initial position
for almost every carrier parameter. This is the identity used before
substitution of the physical footpoint
(`app:ch_mean_pairs:eq:mean-density-recursion`). -/
theorem preparationDensityRepresentative_ae_all_positions
    (e : SmoothResidual n) (a : ι) :
    ∀ᵐ z ∂(volume.prod volume : Measure CarrierParameter), ∀ y,
      (preparationDensityRepresentative d hρsmooth hcρ hχsmooth hlow hχ
        A hA hρ K hK hsupp image U ψ Q₀ hreg e).val a (z,y) =
      preparationDensity d image U ψ Q₀ (smoothResidualToL2 n e) a (z,y) :=
  initialDensity_ae_all_positions (d a) (n + 1) (by omega)
    (hρsmooth a).continuous.measurable (hχsmooth a).continuous.measurable
    (hA a) zero_le_one (hρ a) (hχ a) (-2) _
    (preparation_carrier_mem image U ψ Q₀ hreg e a _)
    _ (((preparationDensityRepresentative d hρsmooth hcρ hχsmooth hlow hχ
      A hA hρ K hK hsupp image U ψ Q₀ hreg e).property a).1.continuous)
    (preparationDensityRepresentative_ae d hρsmooth hcρ hχsmooth hlow hχ
      A hA hρ K hK hsupp image U ψ Q₀ hreg e a)

/-- The measured transported increment of the SAME smooth update equals
the literal uncut increment at every output point. The external weight is
unchanged (`app:ch_mean_pairs:eq:mean-density-recursion`). -/
theorem preparationDensityRepresentative_measured
    (e : SmoothResidual n) (a : ι) (w : CarrierParameter → ℝ) :
    measuredIncrement (d a) w
      ((preparationDensityRepresentative d hρsmooth hcρ hχsmooth hlow hχ
        A hA hρ K hK hsupp image U ψ Q₀ hreg e).val a) =
    measuredIncrement (d a) w
      (preparationDensity d image U ψ Q₀ (smoothResidualToL2 n e) a) :=
  measuredIncrement_eq_of_ae_all_positions (d a) w
    (preparationDensityRepresentative_ae_all_positions d hρsmooth hcρ hχsmooth hlow hχ
      A hA hρ K hK hsupp image U ψ Q₀ hreg e a)

/-- The actual smooth density correction is linear on smooth full-output
sources, with the original `Q₀` retained. The linear laws follow from the
literal uncut integrals and uniqueness, not from choosing a new output at
each derivative order (`app:ch_mean_pairs:eq:mean-density-recursion`). -/
def preparationDensityCorrection : SmoothResidual n →ₗ[ℝ] smoothSupportedDensity n ι K where
  toFun := preparationDensityRepresentative d hρsmooth hcρ hχsmooth hlow hχ
    A hA hρ K hK hsupp image U ψ Q₀ hreg
  map_add' e f := by
    apply smoothSupportedDensity_ext_of_ae_all_positions
    intro a
    have he := preparationDensityRepresentative_ae_all_positions d hρsmooth hcρ hχsmooth hlow hχ
      A hA hρ K hK hsupp image U ψ Q₀ hreg e a
    have hf := preparationDensityRepresentative_ae_all_positions d hρsmooth hcρ hχsmooth hlow hχ
      A hA hρ K hK hsupp image U ψ Q₀ hreg f a
    have hef := preparationDensityRepresentative_ae_all_positions d hρsmooth hcρ hχsmooth hlow hχ
      A hA hρ K hK hsupp image U ψ Q₀ hreg (e + f) a
    have hadd := initialDensity_add_ae_all_positions (d a) (n + 1) (by omega)
      (hρsmooth a).continuous.measurable (hχsmooth a).continuous.measurable
      (hA a) zero_le_one (hρ a) (hχ a) (-2) _ _
      (preparation_carrier_mem image U ψ Q₀ hreg e a _)
      (preparation_carrier_mem image U ψ Q₀ hreg f a _)
    filter_upwards [he, hf, hef, hadd] with z he hf hef hadd
    intro y
    change _ = (_ : ℝ) + _
    rw [he, hf, hef]
    simpa only [preparationDensity, map_add, WithLp.add_fst, WithLp.add_snd,
      PiLp.add_apply] using hadd y
  map_smul' b e := by
    apply smoothSupportedDensity_ext_of_ae_all_positions
    intro a
    have he := preparationDensityRepresentative_ae_all_positions d hρsmooth hcρ hχsmooth hlow hχ
      A hA hρ K hK hsupp image U ψ Q₀ hreg e a
    have hbe := preparationDensityRepresentative_ae_all_positions d hρsmooth hcρ hχsmooth hlow hχ
      A hA hρ K hK hsupp image U ψ Q₀ hreg (b • e) a
    have hsmul := initialDensity_smul_ae_all_positions (d a) (-2) b
      (((augmentedRow image U ψ).adjoint (Q₀ (smoothResidualToL2 n e))).fst.snd a)
    filter_upwards [he, hbe, hsmul] with z he hbe hsmul
    intro y
    change _ = b * _
    rw [he, hbe]
    simpa only [preparationDensity, map_smul, RingHom.id_apply, WithLp.smul_fst,
      WithLp.smul_snd, PiLp.smul_apply] using hsmul y

/-- Global cancellation for the constructed smooth densities. The original
normal inverse equation and raw regularity are the precise remaining
producer inputs; cancellation is derived and the exterior auxiliary normal
is retained (`app:ch_mean_pairs:eq:mean-density-recursion`). -/
theorem preparationDensityRepresentative_cancellation
    (χ : ι → CarrierParameter → ℝ)
    (hplateau : ∀ a z θ, (d a).angularCutoff z θ ≠ 0 → χ a z = 1)
    (hU : ∀ a (u : carrierInitialTestSpace n),
      U a (carrierInitialTestToLp u) =ᵐ[volume] carrierTestIntegral (d a) u.val)
    (hk : ∀ a x, AEStronglyMeasurable (carrierKernel (d a) x) (carrierMeasure n))
    (hst : ∀ a x, ContinuousOn (measuredStress (d a) x) (K a))
    (e : SmoothResidual n)
    (hinverse : augmentedNormal image U ψ (Q₀ (smoothResidualToL2 n e)) =
      smoothResidualToL2 n e) :
    (fun x ↦ (∑ a, measuredIncrement (d a) (fun z ↦ χ a z ^ 2)
      ((preparationDensityRepresentative d hρsmooth hcρ hχsmooth hlow hχ
        A hA hρ K hK hsupp image U ψ Q₀ hreg e).val a) x) -
      preparationAuxiliaryOutput image ψ (Q₀ (smoothResidualToL2 n e)) x) =ᵐ[volume]
        fun x ↦ -e.val x () := by
  simp_rw [preparationDensityRepresentative_measured]
  have he := preparationCancellation_ae d (n + 1) (by omega) χ hplateau U hU hk hK hsupp hst
    hA (fun _ ↦ zero_le_one) hρ hχ image ψ Q₀ (smoothResidualToL2 n e) (hreg e _) hinverse
  filter_upwards [he, SmoothPeriodicFamily.componentL2_coe_ae () e] with x hx hy
  exact hx.trans (congrArg Neg.neg hy)

end FixedRow
end JanetCartan.CurrentMean
