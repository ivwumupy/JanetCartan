module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Retarded.ParameterRealization.L2Family.CompactFamily
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# Compact scalar kernels as bounded L² operators

The bounded linear passage from the uniform norm on a compact product to the
operator norm, used to differentiate the realizations in
`app:ch_response:eq:direct-envelope-profile`. All measures are Lebesgue measures.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace JanetCartan.ResponseTransfer.NearCarrierParameter.CompactKernelL2

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "L²" => Lp ℂ 2 (volume : Measure E)

/-- Zero extension of a continuous function on the compact physical carrier,
used in `app:ch_response:eq:direct-envelope-profile`. -/
def zeroExtension {K : Set E} (f : C(K, ℂ)) : E → ℂ :=
  Function.extend Subtype.val f 0

/-- Zero extension agrees with the carrier restriction used in
`app:ch_response:eq:direct-envelope-profile`. -/
lemma zeroExtension_mem {K : Set E} (f : C(K, ℂ)) {x : E} (hx : x ∈ K) :
    zeroExtension f x = f ⟨x, hx⟩ :=
  Subtype.coe_injective.extend_apply _ _ ⟨x, hx⟩

/-- Zero extension vanishes off the carrier in
`app:ch_response:eq:direct-envelope-profile`. -/
lemma zeroExtension_notMem {K : Set E} (f : C(K, ℂ)) {x : E} (hx : x ∉ K) :
    zeroExtension f x = 0 :=
  Function.extend_apply' _ _ _ (by simpa using hx)

/-- Compact uniform bounds put the zero extension in actual Lebesgue L²;
this is the spatial extension step of `app:ch_response:eq:direct-envelope-profile`. -/
lemma zeroExtension_memLp {K : Set E} [CompactSpace K] (hK : IsCompact K)
    (f : C(K, ℂ)) : MemLp (zeroExtension f) 2 volume := by
  have hm : StronglyMeasurable (zeroExtension f) :=
    (MeasurableEmbedding.subtype_coe hK.measurableSet).stronglyMeasurable_extend
      f.continuous.stronglyMeasurable stronglyMeasurable_zero
  have hs : HasCompactSupport (zeroExtension f) := by
    apply hK.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hn
    exact hx (zeroExtension_notMem f hn)
  apply hs.memLp_of_bound hm.aestronglyMeasurable ‖f‖
  apply Eventually.of_forall
  intro x
  by_cases hx : x ∈ K
  · rw [zeroExtension_mem f hx]
    exact f.norm_coe_le_norm _
  · rw [zeroExtension_notMem f hx, norm_zero]
    exact norm_nonneg _

/-- Bounded complex-linear zero extension, used for both kernel variables in
`app:ch_response:eq:direct-envelope-profile`. -/
def zeroExtensionL2 {K : Set E} [CompactSpace K] (hK : IsCompact K) : C(K, ℂ) →L[ℂ] L² :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ (zeroExtension_memLp hK f).toLp (zeroExtension f)
      map_add' := by
        intro f g
        rw [← MemLp.toLp_add]
        apply MemLp.toLp_congr
        apply Eventually.of_forall
        intro x
        by_cases hx : x ∈ K
        · simp [zeroExtension_mem _ hx]
        · simp [zeroExtension_notMem _ hx]
      map_smul' := by
        intro a f
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        apply MemLp.toLp_congr
        apply Eventually.of_forall
        intro x
        by_cases hx : x ∈ K
        · simp [zeroExtension_mem _ hx]
        · simp [zeroExtension_notMem _ hx] }
    ‖indicatorConstLp (μ := (volume : Measure E)) 2 hK.measurableSet
      hK.measure_lt_top.ne (1 : ℝ)‖
    (fun f ↦ by
      rw [mul_comm]
      change ‖(zeroExtension_memLp hK f).toLp (zeroExtension f)‖ ≤ _
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [(zeroExtension_memLp hK f).coeFn_toLp,
        indicatorConstLp_coeFn (μ := (volume : Measure E)) (p := 2)
          (hs := hK.measurableSet) (hμs := hK.measure_lt_top.ne) (c := (1 : ℝ))]
        with x hx hy
      rw [hx, hy]
      by_cases hxK : x ∈ K
      · simp only [zeroExtension_mem _ hxK, indicator_of_mem hxK, norm_one, mul_one]
        exact f.norm_coe_le_norm _
      · simp [zeroExtension_notMem _ hxK, indicator_of_notMem hxK])

/-- The zero-extension operator has its literal representative, for
`app:ch_response:eq:direct-envelope-profile`. -/
lemma zeroExtensionL2_ae {K : Set E} [CompactSpace K] (hK : IsCompact K)
    (f : C(K, ℂ)) : zeroExtensionL2 hK f =ᵐ[volume] zeroExtension f :=
  (zeroExtension_memLp hK f).coeFn_toLp

/-- The bounded bilinear Lebesgue L² pairing used by `kernelOperator` in
`app:ch_response:eq:direct-envelope-profile`. -/
def kernelPairing : L² →L[ℂ] L² →L[ℂ] ℂ :=
  (ContinuousLinearMap.mul ℂ ℂ).lpPairing volume 2 2

/-- The bilinear L² pairing is the literal integral used in
`app:ch_response:eq:direct-envelope-profile`. -/
lemma kernelPairing_eq (f g : L²) : kernelPairing f g = ∫ y, f y * g y :=
  (ContinuousLinearMap.mul ℂ ℂ).lpPairing_eq_integral f g

variable {Kx Ky : Set (EuclideanSpace ℝ (Fin d))} [CompactSpace Kx] [CompactSpace Ky]
  [CompactSpace (Kx ×ˢ Ky)]

/-- Continuous rows of the compact kernel, used by `kernelOperator` in
`app:ch_response:eq:direct-envelope-profile`. -/
def kernelRows (k : C(Kx ×ˢ Ky, ℂ)) : C(Kx, C(Ky, ℂ)) :=
  (k.comp ⟨fun z : Kx × Ky ↦ ⟨(z.1.val, z.2.val), z.1.property, z.2.property⟩,
    (continuous_subtype_val.prodMap continuous_subtype_val).subtype_mk _⟩).curry

omit [CompactSpace Kx] in
/-- The uniform row bound for the operator-norm lifting in
`app:ch_response:eq:direct-envelope-profile`. -/
lemma kernelRows_norm_le (k : C(Kx ×ˢ Ky, ℂ)) (x : Kx) : ‖kernelRows k x‖ ≤ ‖k‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro y
  exact k.norm_coe_le_norm ⟨(x.val, y.val), x.property, y.property⟩

/-- Integrate a compact kernel in the source variable, before zero extension
in the output variable in `app:ch_response:eq:direct-envelope-profile`. -/
def kernelAction (hKy : IsCompact Ky) (k : C(Kx ×ˢ Ky, ℂ)) : L² →L[ℂ] C(Kx, ℂ) :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ ⟨fun x ↦ kernelPairing (zeroExtensionL2 hKy (kernelRows k x)) f,
        ((kernelPairing.flip f).continuous.comp (zeroExtensionL2 hKy).continuous).comp
          (kernelRows k).continuous⟩
      map_add' := by intros; ext; simp only [map_add, ContinuousMap.add_apply]; rfl
      map_smul' := by intros; ext; simp only [map_smul, ContinuousMap.smul_apply]; rfl }
    (‖kernelPairing (d := d)‖ * ‖zeroExtensionL2 hKy‖ * ‖k‖)
    (fun f ↦ by
      apply (ContinuousMap.norm_le _ (by positivity)).mpr
      intro x
      calc
        ‖kernelPairing (zeroExtensionL2 hKy (kernelRows k x)) f‖ ≤
            ‖kernelPairing (d := d)‖ * ‖zeroExtensionL2 hKy (kernelRows k x)‖ * ‖f‖ :=
          ContinuousLinearMap.le_opNorm₂ _ _ _
        _ ≤ ‖kernelPairing (d := d)‖ * (‖zeroExtensionL2 hKy‖ * ‖k‖) * ‖f‖ := by
          gcongr
          exact ((zeroExtensionL2 hKy).le_opNorm _).trans
            (mul_le_mul_of_nonneg_left (kernelRows_norm_le k x) (norm_nonneg _))
        _ = _ := by ring)

/-- A continuous compact kernel gives a bounded L² operator, continuously and
linearly in the uniform kernel norm. This is the operator-norm lifting used by
`app:ch_response:eq:direct-envelope-profile`. -/
def kernelOperator (hKx : IsCompact Kx) (hKy : IsCompact Ky) :
    C(Kx ×ˢ Ky, ℂ) →L[ℂ] (L² →L[ℂ] L²) :=
  LinearMap.mkContinuous
    { toFun := fun k ↦ (zeroExtensionL2 hKx).comp (kernelAction hKy k)
      map_add' := by
        intro k l
        apply ContinuousLinearMap.ext
        intro f
        change zeroExtensionL2 hKx (kernelAction hKy (k + l) f) =
          zeroExtensionL2 hKx (kernelAction hKy k f) + zeroExtensionL2 hKx (kernelAction hKy l f)
        rw [← map_add]
        congr 1
        ext x
        change kernelPairing (zeroExtensionL2 hKy (kernelRows (k + l) x)) f = _
        have hr : kernelRows (k + l) x = kernelRows k x + kernelRows l x := rfl
        simp only [hr, map_add, add_apply, ContinuousMap.add_apply]
        rfl
      map_smul' := by
        intro a k
        apply ContinuousLinearMap.ext
        intro f
        change zeroExtensionL2 hKx (kernelAction hKy (a • k) f) =
          a • zeroExtensionL2 hKx (kernelAction hKy k f)
        rw [← map_smul]
        congr 1
        ext x
        change kernelPairing (zeroExtensionL2 hKy (kernelRows (a • k) x)) f = _
        have hr : kernelRows (a • k) x = a • kernelRows k x := rfl
        simp only [hr, map_smul, smul_apply, ContinuousMap.smul_apply]
        rfl }
    (‖zeroExtensionL2 hKx‖ * (‖kernelPairing (d := d)‖ * ‖zeroExtensionL2 hKy‖))
    (fun k ↦ by
      change ‖(zeroExtensionL2 hKx).comp (kernelAction hKy k)‖ ≤ _
      apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
      calc
        ‖zeroExtensionL2 hKx‖ * ‖kernelAction hKy k‖ ≤
            ‖zeroExtensionL2 hKx‖ * (‖kernelPairing (d := d)‖ * ‖zeroExtensionL2 hKy‖ * ‖k‖) := by
          gcongr
          exact LinearMap.mkContinuous_norm_le _ (by positivity) _
        _ = _ := by ring)

/-- The constructed operator has the literal integral on every L² datum.
This supplies the differentiated-kernel realization in
`app:ch_response:eq:direct-envelope-profile`. -/
theorem kernelOperator_ae (hKx : IsCompact Kx) (hKy : IsCompact Ky)
    (k : C(Kx ×ˢ Ky, ℂ)) (g : E × E → ℂ)
    (hk : ∀ z : Kx ×ˢ Ky, k z = g z)
    (hs : ∀ z ∉ Kx ×ˢ Ky, g z = 0) (f : L²) :
    kernelOperator hKx hKy k f =ᵐ[volume] fun x ↦ ∫ y, g (x, y) * f y := by
  filter_upwards [zeroExtensionL2_ae hKx (kernelAction hKy k f)] with x hx
  change zeroExtensionL2 hKx (kernelAction hKy k f) x = _
  rw [hx]
  by_cases hxK : x ∈ Kx
  · rw [zeroExtension_mem _ hxK]
    change kernelPairing (zeroExtensionL2 hKy (kernelRows k ⟨x, hxK⟩)) f = _
    rw [kernelPairing_eq]
    apply integral_congr_ae
    filter_upwards [zeroExtensionL2_ae hKy (kernelRows k ⟨x, hxK⟩)] with y hy
    rw [hy]
    congr 1
    by_cases hyK : y ∈ Ky
    · rw [zeroExtension_mem _ hyK]
      exact hk ⟨(x, y), hxK, hyK⟩
    · rw [zeroExtension_notMem _ hyK, hs (x, y) (fun h ↦ hyK h.2)]
  · rw [zeroExtension_notMem _ hxK]
    have hz (y : E) : g (x, y) = 0 := hs (x, y) (fun h ↦ hxK h.1)
    simp [hz]

/-- Agreement on Schwartz tests identifies a supplied bounded realization with
the constructed compact-kernel operator. The density argument also applies in
dimension zero (`app:ch_response:eq:direct-envelope-profile`). -/
theorem eq_kernelOperator_of_schwartz (hKx : IsCompact Kx) (hKy : IsCompact Ky)
    (k : C(Kx ×ˢ Ky, ℂ)) (g : E × E → ℂ)
    (hk : ∀ z : Kx ×ˢ Ky, k z = g z)
    (hs : ∀ z ∉ Kx ×ˢ Ky, g z = 0) (T : L² →L[ℂ] L²)
    (hT : ∀ f : SchwartzMap E ℂ,
      T (f.toLp 2 volume) =ᵐ[volume] fun x ↦ ∫ y, g (x, y) * f y) :
    T = kernelOperator hKx hKy k := by
  apply DFunLike.coe_injective
  apply (SchwartzMap.denseRange_toLpCLM (F := ℂ) (p := 2)
    (μ := (volume : Measure E)) ENNReal.ofNat_ne_top).equalizer T.continuous
      (kernelOperator hKx hKy k).continuous
  funext f
  apply Lp.ext
  apply (hT f).trans
  apply EventuallyEq.symm
  apply (kernelOperator_ae hKx hKy k g hk hs (f.toLp 2 volume)).trans
  apply Eventually.of_forall
  intro x
  apply integral_congr_ae
  filter_upwards [f.coeFn_toLp 2 volume] with y hy
  rw [hy]

end JanetCartan.ResponseTransfer.NearCarrierParameter.CompactKernelL2
