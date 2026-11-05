module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ParameterRealization.CompactKernelL2
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ParameterRealization.WeakSource

/-!
# L² parameter transfer from compact kernel identities

The analytic assembly in `app:ch_response:eq:direct-envelope-profile`.
The input identity is an identity of smooth, scalar kernels before applying
them to data. Operator differentiation, weak source integration, and the
independent parameter derivative of the datum are consequences. The literal
selected phase calculations supply the kernel identity; no Sobolev estimate
or derivative of a realized operator is an input.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace JanetCartan.ResponseTransfer.NearCarrierParameter
open Pseudodifferential CompactKernelL2
open JanetCartan.ResponseTransfer.ParameterRealization.L2Family

variable {d p : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "P" => EuclideanSpace ℝ (Fin p)
local notation "L²" => Lp ℂ 2 (volume : Measure E)

/-- A bounded realization identified only on Schwartz tests acts by its literal
compact kernel on every L² datum. Consumer: the parameter source transfer in
`app:ch_response:eq:direct-envelope-profile`. -/
theorem compact_realization_ae
    {Kx Ky : Set E} (hKx : IsCompact Kx) (hKy : IsCompact Ky)
    {k : E × E → ℂ} (hk : Continuous k) (hs : tsupport k ⊆ Kx ×ˢ Ky)
    (T : L² →L[ℂ] L²)
    (hT : ∀ f : SchwartzMap E ℂ,
      T (f.toLp 2 volume) =ᵐ[volume] fun x ↦ ∫ y, k (x, y) * f y)
    (f : L²) : T f =ᵐ[volume] fun x ↦ ∫ y, k (x, y) * f y := by
  let : CompactSpace Kx := isCompact_iff_compactSpace.mp hKx
  let : CompactSpace Ky := isCompact_iff_compactSpace.mp hKy
  let : CompactSpace (Kx ×ˢ Ky) := isCompact_iff_compactSpace.mp (hKx.prod hKy)
  let g : C(Kx ×ˢ Ky, ℂ) := ⟨fun z ↦ k z, hk.comp continuous_subtype_val⟩
  have hz (z : E × E) (hz : z ∉ Kx ×ˢ Ky) : k z = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h ↦ hz (hs h))
  rw [eq_kernelOperator_of_schwartz hKx hKy g k (fun _ ↦ rfl) hz T hT]
  exact kernelOperator_ae hKx hKy g k (fun _ ↦ rfl) hz f

/-- The source row of a kernel with common compact physical support is a
compact test function, as required by the weak source identity in
`app:ch_response:eq:direct-envelope-profile`. -/
theorem compactSupport_kernel_row
    {Kx Ky : Set E} (hKy : IsCompact Ky) {k : E × E → ℂ}
    (hs : tsupport k ⊆ Kx ×ˢ Ky) (x : E) :
    HasCompactSupport (fun y ↦ k (x, y)) := by
  apply hKy.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ hKy.isClosed
  intro y hy
  exact (hs (subset_tsupport _ hy)).2

/-- Transfer a finite source divergence from compact kernels to actual weak
L² derivatives. The kernel equality is pointwise and contains no operator or
datum. It is produced by the signed forward/reverse phase calculation in
`app:ch_response:eq:direct-envelope-profile`. -/
theorem integral_kernel_source_transfer
    (dk r : E → ℂ) (b : Fin d → E → ℂ)
    (hr : ContDiff ℝ ∞ r) (hrc : HasCompactSupport r)
    (hb : ∀ j, ContDiff ℝ ∞ (b j)) (hbc : ∀ j, HasCompactSupport (b j))
    (hid : ∀ y, dk y = r y -
      ∑ j, fderiv ℝ (b j) y (EuclideanSpace.single j 1))
    (f : L²) (df : Fin d → L²)
    (hdf : ∀ j, HasEuclideanL2CoordinateDerivative j f (df j)) :
    (∫ y, dk y * f y) = (∫ y, r y * f y) + ∑ j, ∫ y, b j y * df j y := by
  have hi := integrable_compactTest_mul_l2 f r hr hrc
  have hdi (j : Fin d) := integrable_compactTest_fderiv_mul_l2 f j (b j) (hb j) (hbc j)
  simp_rw [hid, sub_mul, Finset.sum_mul]
  rw [integral_sub hi (integrable_finsetSum _ (fun j _ ↦ hdi j)),
    integral_finsetSum _ (fun j _ ↦ hdi j)]
  simp only [integral_compactTest_fderiv_mul_l2 (hdf _) _ (hb _) (hbc _),
    Finset.sum_neg_distrib, sub_neg_eq_add]

/-- Actual parameter derivative of a compact scalar kernel realization,
including the datum derivative. Smoothness and common support imply operator
norm differentiation; the pointwise source identity implies the displayed L²
formula via the distributional derivative of the datum. This is the analytic
step consumed by the literal selected graph assembly for
`app:ch_response:eq:direct-envelope-profile`. -/
theorem hasLineDerivAt_compact_kernel_transfer
    {U : Set P} (hU : IsOpen U) {Kx Ky : Set E}
    (hKx : IsCompact Kx) (hKy : IsCompact Ky)
    {k : P → E × E → ℂ}
    (hk : ContDiffOn ℝ ∞ (Function.uncurry k) (U ×ˢ univ))
    (hs : ∀ a ∈ U, tsupport (k a) ⊆ Kx ×ˢ Ky)
    (T : P → L² →L[ℂ] L²)
    (hT : ∀ a ∈ U, ∀ g : SchwartzMap E ℂ,
      T a (g.toLp 2 volume) =ᵐ[volume] fun x ↦ ∫ y, k a (x, y) * g y)
    {c : P} (hc : c ∈ U) (v : P)
    (r : E × E → ℂ) (b : Fin d → E × E → ℂ)
    (hr : ContDiff ℝ ∞ r) (hrs : tsupport r ⊆ Kx ×ˢ Ky)
    (hb : ∀ j, ContDiff ℝ ∞ (b j)) (hbs : ∀ j, tsupport (b j) ⊆ Kx ×ˢ Ky)
    (R : L² →L[ℂ] L²) (B : Fin d → L² →L[ℂ] L²)
    (hR : ∀ g : SchwartzMap E ℂ,
      R (g.toLp 2 volume) =ᵐ[volume] fun x ↦ ∫ y, r (x, y) * g y)
    (hB : ∀ j, ∀ g : SchwartzMap E ℂ,
      B j (g.toLp 2 volume) =ᵐ[volume] fun x ↦ ∫ y, b j (x, y) * g y)
    (hid : ∀ x y, fderiv ℝ (fun a ↦ k a (x, y)) c v = r (x, y) -
      ∑ j, fderiv ℝ (fun z ↦ b j (x, z)) y (EuclideanSpace.single j 1))
    {f : P → L²} {df : Fin d → L²} {pf : L²}
    (hdf : ∀ j, HasEuclideanL2CoordinateDerivative j (f c) (df j))
    (hpf : HasLineDerivAt ℝ f pf c v) :
    HasLineDerivAt ℝ (fun a ↦ T a (f a))
      (R (f c) + ∑ j, B j (df j) + T c pf) c v := by
  have he : fderiv ℝ T c v (f c) = R (f c) + ∑ j, B j (df j) := by
    apply Lp.ext
    have hbsum : ∀ᵐ x ∂volume, ∀ j, B j (df j) x = ∫ y, b j (x, y) * df j y :=
      ae_all_iff.mpr fun j ↦ compact_realization_ae hKx hKy (hb j).continuous (hbs j)
        (B j) (hB j) (df j)
    filter_upwards [fderiv_realization_ae hU hKx hKy hk hs T hT hc v (f c),
      compact_realization_ae hKx hKy hr.continuous hrs R hR (f c), hbsum,
      Lp.coeFn_add (R (f c)) (∑ j, B j (df j)),
      Lp.coeFn_fun_finsetSum Finset.univ (fun j ↦ B j (df j))] with x hx hrx hbx hadd hsum
    rw [hadd, Pi.add_apply, hsum, hx, hrx]
    simp only [hbx]
    exact integral_kernel_source_transfer _ _ _
      (hr.comp (contDiff_const.prodMk contDiff_id))
      (compactSupport_kernel_row hKy hrs x)
      (fun j ↦ (hb j).comp (contDiff_const.prodMk contDiff_id))
      (fun j ↦ compactSupport_kernel_row hKy (hbs j) x)
      (hid x) (f c) df hdf
  simpa only [he] using hasLineDerivAt_realization_apply hU hKx hKy hk hs T hT hc v hpf

end JanetCartan.ResponseTransfer.NearCarrierParameter
