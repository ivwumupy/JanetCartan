module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenImageComparison.PeriodicEnergy.Channel
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenImageComparison.KernelEnergy

/-!
# The explicit kernel for the full frozen periodic normal correction

These concrete integrals are the kernels for `B D*`, its adjoint `D B*`,
and `D D*`, where `B` and `D` are the actual fixed operators in `Channel`.
For the mixed term the constant differential factor is transferred to the
smooth source section, leaving the integrable Euclidean Bessel kernel
undifferentiated. The original source multiplier remains inside that section.

This module proves the section's smoothness and compact support, and the
compact support of the full kernel. Joint smoothness of the intermediate
integrals and their identification with the bounded normal are separate
obligations of `PeriodicEnergy` (`paper-v2.tex`, `app:ch_background:prop:bg-frame`).
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set
open scoped ContDiff
open JanetCartan.ContinuumRow
open JanetCartan.ContinuumNormalReduction.ImageNormal

namespace JanetCartan.ContinuumNormal.FrozenImageComparison

variable {n : ℕ} {R : ℝ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The source section in `B D*`: source multiplication precedes convolution,
and the one-factor kernel is spatially reversed and transposed. The two
source masks remain in this product (`app:ch_background:prop:bg-frame`). -/
def fixedMixedSourceKernel (hR : 0 < R)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (j k : Fin n) (q : E × E) : ℝ :=
  FixedCutoffs.physical hR 2 q.1 * fixedLatticeKernel hR A j k q.swap

/-- Smoothness of the actual section to which the mixed-term differential
factor is transferred (`app:ch_background:prop:bg-frame`). -/
theorem contDiff_fixedMixedSourceKernel (hR : 0 < R) (hcell : 4 * R < 1 / 2)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (j k : Fin n) :
    ContDiff ℝ ∞ (fixedMixedSourceKernel hR A j k) :=
  ((FixedCutoffs.physical hR 2).contDiff.comp contDiff_fst).mul
    ((contDiff_fixedLatticeKernel hR hcell A j k).comp
      (contDiff_snd.prodMk contDiff_fst))

/-- The mixed section is supported on source times measurement, so all its
source derivatives vanish outside the original measurement support in the
second variable (`app:ch_background:prop:bg-frame`). -/
theorem tsupport_fixedMixedSourceKernel_subset (hR : 0 < R)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (j k : Fin n) :
    tsupport (fixedMixedSourceKernel hR A j k) ⊆
      tsupport (FixedCutoffs.physical hR 2) ×ˢ
        tsupport (FixedCutoffs.physical hR 1) := by
  apply closure_minimal _ ((isClosed_tsupport _).prod (isClosed_tsupport _))
  intro q hq
  have hK : fixedLatticeKernel hR A j k q.swap ≠ 0 := by
    intro hk
    exact hq (by simp [fixedMixedSourceKernel, hk])
  have hs := tsupport_fixedLatticeKernel_subset hR A j k (subset_tsupport _ hK)
  exact ⟨hs.2, hs.1⟩

/-- Compact support of the actual mixed source section
(`app:ch_background:prop:bg-frame`, frozen image comparison). -/
theorem hasCompactSupport_fixedMixedSourceKernel (hR : 0 < R)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (j k : Fin n) :
    HasCompactSupport (fixedMixedSourceKernel hR A j k) :=
  ((FixedCutoffs.physical hR 2).hasCompactSupport.isCompact.prod
    (FixedCutoffs.physical hR 1).hasCompactSupport.isCompact).of_isClosed_subset
      (isClosed_tsupport _) (tsupport_fixedMixedSourceKernel_subset hR A j k)

/-- The proposed literal kernel entry of `B D*`, after moving the constant
derivative onto the smooth source section. Translation fixes the Bessel
factor, which has integral one. Identifying this expression with the actual
operator requires the integration-by-parts and Fubini proofs; the definition
does not assert that identity (`app:ch_background:prop:bg-frame`). -/
def fixedMixedKernelEntry (hR : 0 < R)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) (p : E × E) : ℝ :=
  FixedCutoffs.physical hR 1 p.1 * ∑ a, ∑ k, A a i k *
    ∫ t : E, imageBesselKernel t *
      fderiv ℝ (fixedMixedSourceKernel hR A j k) (p.1 - t, p.2)
        (EuclideanSpace.single a 1, 0)

/-- The literal product-kernel candidate for `D D*`, retaining the common
intermediate source variable (`app:ch_background:prop:bg-frame`). -/
def fixedLatticeProductKernelEntry (hR : 0 < R)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) (p : E × E) : ℝ :=
  ∑ k, ∫ z : E, fixedLatticeKernel hR A i k (p.1, z) *
    fixedLatticeKernel hR A j k (p.2, z)

/-- All three entries of the normal correction, with the mixed term's
spatial transpose explicitly present (`app:ch_background:prop:bg-frame`). -/
def fixedNormalCorrectionKernelEntry (hR : 0 < R)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) (p : E × E) : ℝ :=
  fixedMixedKernelEntry hR A i j p + fixedMixedKernelEntry hR A j i p.swap +
    fixedLatticeProductKernelEntry hR A i j p

/-- The full matrix kernel as a continuous linear map on the real Euclidean
fiber, in the format required by `exists_compactKernel_energy_bound`.
This is an explicit integral construction, with no comparison premise
(`app:ch_background:prop:bg-frame`, frozen image comparison). -/
def fixedNormalCorrectionKernel (hR : 0 < R)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (p : E × E) : E →L[ℝ] E :=
  ∑ i, ∑ j, fixedNormalCorrectionKernelEntry hR A i j p •
    (EuclideanSpace.proj j).smulRight (EuclideanSpace.single i 1)

/-- Coordinate action of the full kernel, for its identification with the
finite matrix of scalar bounded integral operators
(`app:ch_background:prop:bg-frame`, frozen image comparison). -/
theorem fixedNormalCorrectionKernel_apply (hR : 0 < R)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (p : E × E) (v : E) (i : Fin n) :
    fixedNormalCorrectionKernel hR A p v i =
      ∑ j, fixedNormalCorrectionKernelEntry hR A i j p * v j := by
  simp [fixedNormalCorrectionKernel, ContinuousLinearMap.smulRight_apply,
    EuclideanSpace.single, EuclideanSpace.proj, Pi.single_apply, mul_ite,
    Finset.sum_ite_irrel]

/-- The mixed kernel vanishes when either measurement variable is outside
its fixed support. Differentiation of the source section does not enlarge
the second-variable support (`app:ch_background:prop:bg-frame`). -/
theorem fixedMixedKernelEntry_eq_zero_off_support (hR : 0 < R)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) (p : E × E)
    (hp : p ∉ tsupport (FixedCutoffs.physical hR 1) ×ˢ
      tsupport (FixedCutoffs.physical hR 1)) :
    fixedMixedKernelEntry hR A i j p = 0 := by
  by_cases hx : p.1 ∈ tsupport (FixedCutoffs.physical hR 1)
  · have hy : p.2 ∉ tsupport (FixedCutoffs.physical hR 1) := fun hy ↦ hp ⟨hx, hy⟩
    have hd (k : Fin n) (t : E) :
        fderiv ℝ (fixedMixedSourceKernel hR A j k) (p.1 - t, p.2) = 0 :=
      fderiv_of_notMem_tsupport ℝ (fun h ↦
        hy ((tsupport_fixedMixedSourceKernel_subset hR A j k h).2))
    simp [fixedMixedKernelEntry, hd]
  · simp [fixedMixedKernelEntry, image_eq_zero_of_notMem_tsupport hx]

/-- Both outer variables of the `D D*` kernel retain the measurement support
(`app:ch_background:prop:bg-frame`, frozen image comparison). -/
theorem fixedLatticeProductKernelEntry_eq_zero_off_support (hR : 0 < R)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) (p : E × E)
    (hp : p ∉ tsupport (FixedCutoffs.physical hR 1) ×ˢ
      tsupport (FixedCutoffs.physical hR 1)) :
    fixedLatticeProductKernelEntry hR A i j p = 0 := by
  by_cases hx : p.1 ∈ tsupport (FixedCutoffs.physical hR 1)
  · have hy : p.2 ∉ tsupport (FixedCutoffs.physical hR 1) := fun hy ↦ hp ⟨hx, hy⟩
    have hk (k : Fin n) (z : E) : fixedLatticeKernel hR A j k (p.2, z) = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h ↦
        hy ((tsupport_fixedLatticeKernel_subset hR A j k h).1))
    simp [fixedLatticeProductKernelEntry, hk]
  · have hk (k : Fin n) (z : E) : fixedLatticeKernel hR A i k (p.1, z) = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h ↦
        hx ((tsupport_fixedLatticeKernel_subset hR A i k h).1))
    simp [fixedLatticeProductKernelEntry, hk]

/-- Every scalar entry of the full normal correction retains the original
measurement supports (`app:ch_background:prop:bg-frame`). -/
theorem fixedNormalCorrectionKernelEntry_eq_zero_off_support (hR : 0 < R)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) (p : E × E)
    (hp : p ∉ tsupport (FixedCutoffs.physical hR 1) ×ˢ
      tsupport (FixedCutoffs.physical hR 1)) :
    fixedNormalCorrectionKernelEntry hR A i j p = 0 := by
  have hs : p.swap ∉ tsupport (FixedCutoffs.physical hR 1) ×ˢ
      tsupport (FixedCutoffs.physical hR 1) := fun hs ↦ hp ⟨hs.2, hs.1⟩
  simp only [fixedNormalCorrectionKernelEntry,
    fixedMixedKernelEntry_eq_zero_off_support hR A i j p hp,
    fixedMixedKernelEntry_eq_zero_off_support hR A j i p.swap hs,
    fixedLatticeProductKernelEntry_eq_zero_off_support hR A i j p hp, add_zero]

/-- Compactness of every scalar block, needed by the actual bounded
matrix-kernel realization (`app:ch_background:prop:bg-frame`). -/
theorem hasCompactSupport_fixedNormalCorrectionKernelEntry (hR : 0 < R)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    HasCompactSupport (fixedNormalCorrectionKernelEntry hR A i j) := by
  apply HasCompactSupport.intro
    ((FixedCutoffs.physical hR 1).hasCompactSupport.isCompact.prod
      (FixedCutoffs.physical hR 1).hasCompactSupport.isCompact)
  exact fun p hp ↦ fixedNormalCorrectionKernelEntry_eq_zero_off_support hR A i j p hp

/-- The full normal-kernel candidate has the original measurement support
in both variables, with no inner support radius (`app:ch_background:prop:bg-frame`). -/
theorem tsupport_fixedNormalCorrectionKernel_subset (hR : 0 < R)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    tsupport (fixedNormalCorrectionKernel hR A) ⊆
      tsupport (FixedCutoffs.physical hR 1) ×ˢ
        tsupport (FixedCutoffs.physical hR 1) := by
  apply closure_minimal _ ((isClosed_tsupport _).prod (isClosed_tsupport _))
  intro p hp
  by_contra hn
  apply hp
  unfold fixedNormalCorrectionKernel
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  rw [fixedNormalCorrectionKernelEntry_eq_zero_off_support hR A i j p hn]
  exact zero_smul ℝ
    ((EuclideanSpace.proj j).smulRight (EuclideanSpace.single i 1) : E →L[ℝ] E)

/-- Compactness of the explicit full normal-kernel candidate, at the fixed
outer radius (`app:ch_background:prop:bg-frame`, frozen image comparison).
Joint smoothness and operator identification remain separate proof targets. -/
theorem hasCompactSupport_fixedNormalCorrectionKernel (hR : 0 < R)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    HasCompactSupport (fixedNormalCorrectionKernel hR A) :=
  ((FixedCutoffs.physical hR 1).hasCompactSupport.isCompact.prod
    (FixedCutoffs.physical hR 1).hasCompactSupport.isCompact).of_isClosed_subset
      (isClosed_tsupport _) (tsupport_fixedNormalCorrectionKernel_subset hR A)

end JanetCartan.ContinuumNormal.FrozenImageComparison
