module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.RetainedBackground.CompactTensor.Extension
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Retarded.ParameterRealization.L2Family.CompactFamily

/-!
# Smooth compact tensor families in physical L2

Classical joint smoothness and a common compact physical support produce the
literal L2 classes and all their parameter derivatives. The consumer is
`app:ch_waves:eq:background-quadrature`; no L2 regularity is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.Sampling.RetainedBackground.CompactTensor
open ResponseTransfer.ParameterRealization.L2Family

variable {n : ℕ} {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
variable {K : Set (Euclidean n)} (hK : IsCompact K)
variable {g : P → Euclidean n → Matrix (Fin n) (Fin n) ℝ}
variable (hg : ContDiff ℝ ∞ (Function.uncurry g))
variable (hs : ∀ a x, x ∉ K → g a x = 0)

include hK hg hs in
/-- Every classical slice belongs to physical Lebesgue L2
(`app:ch_waves:eq:background-quadrature`). -/
theorem family_memLp (a : P) : MemLp (g a) 2 volume := by
  apply Continuous.memLp_of_hasCompactSupport
  · exact (hg.comp (contDiff_const.prodMk contDiff_id)).continuous
  · apply hK.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hn
    exact hx (hs a x hn)

/-- The literal Lebesgue L2 class of the tensor, with the original physical
measure (`app:ch_waves:eq:background-quadrature`). -/
def family (a : P) : Lp (Matrix (Fin n) (Fin n) ℝ) 2 (volume : Measure (Euclidean n)) :=
  (family_memLp hK hg hs a).toLp (g a)

/-- The L2 representative is the original tensor almost everywhere
(`app:ch_waves:eq:background-quadrature`). -/
theorem family_ae (a : P) : family hK hg hs a =ᵐ[volume] g a :=
  (family_memLp hK hg hs a).coeFn_toLp

include hg in
private lemma compact_apply [CompactSpace K] (a : P) (x : K) :
    compactFamily (K := K) g a x = g a x :=
  compactFamily_apply hg.contDiffOn (mem_univ a) x

include hg in
private lemma compact_smooth [CompactSpace K] (k : ℕ) (a : P) :
    ContDiffAt ℝ k (compactFamily (K := K) g) a :=
  compactFamily_contDiffAt k isOpen_univ hg.contDiffOn (mem_univ a)

include hg in
private lemma compact_iterated_apply [CompactSpace K]
    (k : ℕ) (v : Fin k → P) (a : P) (x : K) :
    (iteratedFDeriv ℝ k (compactFamily (K := K) g) a v) x =
      iteratedFDeriv ℝ k (fun b ↦ g b x) a v := by
  have hh := (ContinuousMap.evalCLM ℝ x (M := Matrix (Fin n) (Fin n) ℝ)).iteratedFDeriv_comp_left
    (compact_smooth hg k a) (le_refl (k : ℕ∞ω))
  have he : ((ContinuousMap.evalCLM ℝ x (M := Matrix (Fin n) (Fin n) ℝ)) ∘
      compactFamily (K := K) g) = (fun b ↦ g b x) := by
    funext b
    exact compact_apply hg b x
  rw [he] at hh
  exact (congrArg (fun m ↦ m v) hh).symm

include hs in
private lemma differential_zero (k : ℕ) (v : Fin k → P) (a : P)
    {x : Euclidean n} (hx : x ∉ K) :
    iteratedFDeriv ℝ k (fun b ↦ g b x) a v = 0 := by
  have he : (fun b ↦ g b x) = (fun _ ↦ (0 : Matrix (Fin n) (Fin n) ℝ)) :=
    funext fun b ↦ hs b x hx
  rw [he]
  cases k with
  | zero => exact iteratedFDeriv_zero_apply _
  | succ k => simp

include hg hs in
private lemma extension_differential [CompactSpace K]
    (k : ℕ) (v : Fin k → P) (a : P) :
    extendZero (iteratedFDeriv ℝ k (compactFamily (K := K) g) a v) =
      fun x ↦ iteratedFDeriv ℝ k (fun b ↦ g b x) a v := by
  funext x
  by_cases hx : x ∈ K
  · rw [extendZero_mem _ hx]
    exact compact_iterated_apply hg k v a ⟨x, hx⟩
  · rw [extendZero_notMem _ hx, differential_zero hs k v a hx]

include hK hg hs in
/-- Every evaluated pointwise parameter derivative is in physical L2
(`app:ch_waves:eq:background-quadrature`). -/
theorem iteratedParameterDeriv_memLp (k : ℕ) (v : Fin k → P) (a : P) :
    MemLp (fun x ↦ iteratedFDeriv ℝ k (fun b ↦ g b x) a v) 2 volume := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  rw [← extension_differential hg hs k v a]
  exact extendZero_memLp hK _

private lemma family_eq_compact [CompactSpace K] :
    family hK hg hs = compactToL2 hK ∘ compactFamily (K := K) g := by
  funext a
  change (family_memLp hK hg hs a).toLp _ = (extendZero_memLp hK _).toLp _
  apply MemLp.toLp_congr
  apply Filter.Eventually.of_forall
  intro x
  by_cases hx : x ∈ K
  · rw [extendZero_mem _ hx, compact_apply hg a ⟨x, hx⟩]
  · rw [extendZero_notMem _ hx, hs a x hx]

/-- The tensor's literal L2 family is smooth at every finite order, by the
compact-family calculus and bounded zero extension
(`app:ch_waves:eq:background-quadrature`). -/
theorem contDiff_family (k : ℕ) : ContDiff ℝ k (family hK hg hs) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  rw [family_eq_compact hK hg hs]
  apply (compactToL2 hK).contDiff.comp
  exact contDiff_iff_contDiffAt.mpr (compact_smooth hg k)

/-- Evaluating an actual L2 derivative gives the L2 class of the pointwise
classical derivative (`app:ch_waves:eq:background-quadrature`). -/
theorem iteratedFDeriv_family (k : ℕ) (v : Fin k → P) (a : P) :
    iteratedFDeriv ℝ k (family hK hg hs) a v =
      (iteratedParameterDeriv_memLp hK hg hs k v a).toLp
        (fun x ↦ iteratedFDeriv ℝ k (fun b ↦ g b x) a v) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  rw [family_eq_compact hK hg hs,
    (compactToL2 hK).iteratedFDeriv_comp_left (compact_smooth hg k a)
      (le_refl (k : ℕ∞ω))]
  change (extendZero_memLp hK _).toLp _ = _
  apply MemLp.toLp_congr
  exact Filter.Eventually.of_forall (congrFun (extension_differential hg hs k v a))

/-- Uniform classical parameter jets give the actual L2 operator-norm bound.
This supplies Taylor's remainder constant in the background quadrature.
Source: `app:ch_waves:eq:background-quadrature`. -/
theorem norm_iteratedFDeriv_family_le (k : ℕ) (a : P) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ x ∈ K, ‖iteratedFDeriv ℝ k (fun b ↦ g b x) a‖ ≤ B) :
    ‖iteratedFDeriv ℝ k (family hK hg hs) a‖ ≤ physicalL2Constant hK * B := by
  apply ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg (physicalL2Constant_nonneg hK) hB)
  intro v
  rw [iteratedFDeriv_family hK hg hs k v a]
  calc
    _ ≤ physicalL2Constant hK * (B * ∏ i, ‖v i‖) :=
      norm_toLp_le hK _ (fun x hx ↦ differential_zero hs k v a hx)
        (mul_nonneg hB (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _))
        (fun x hx ↦ ((iteratedFDeriv ℝ k (fun b ↦ g b x) a).le_opNorm v).trans
          (mul_le_mul_of_nonneg_right (hb x hx) (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _)))
    _ = (physicalL2Constant hK * B) * ∏ i, ‖v i‖ := by ring

/-- A uniform pointwise bound controls the tensor's literal L2 norm; used in
the adjacent transport comparison (`app:ch_waves:eq:background-quadrature`). -/
theorem norm_family_le (a : P) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ x ∈ K, ‖g a x‖ ≤ B) :
    ‖family hK hg hs a‖ ≤ physicalL2Constant hK * B :=
  norm_toLp_le hK _ (hs a) hB hb

end JanetCartan.Sampling.RetainedBackground.CompactTensor
