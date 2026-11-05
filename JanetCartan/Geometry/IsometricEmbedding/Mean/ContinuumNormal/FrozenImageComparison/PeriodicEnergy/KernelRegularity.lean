module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenImageComparison.PeriodicEnergy.Kernel
public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.KernelDecay.OutputDerivatives.CompactIntegral

/-!
# Joint smoothness of the explicit frozen normal kernel

For `paper-v2.tex`, `app:ch_background:prop:bg-frame`, the mixed normal
term is integrated against the fixed integrable Euclidean Bessel kernel.
All parameter derivatives act on the translated compact source section;
its compact derivative bounds provide integrable majorants at every order.
The lattice product has a fixed compact source carrier, so the existing
compact-parameter integration theorem supplies its joint smoothness.

These results produce the regularity of the concrete kernels in `Kernel`
for the full frozen periodic energy comparison and its bounded matrix-kernel
realization. Identification with the actual normal operator is separate.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Filter Set
open scoped ContDiff Topology
open JanetCartan.ContinuumRow
open JanetCartan.ContinuumNormalReduction.ImageNormal
open JanetCartan.FiniteChain.Retarded.KernelDecay

namespace JanetCartan.ContinuumNormal.FrozenImageComparison

variable {n : ℕ} {R : ℝ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The mixed normal integral in `app:ch_background:prop:bg-frame` is smooth
when its compact section is translated in the first variable. The Bessel
factor remains fixed in every derivative. -/
private theorem contDiff_bessel_first_translate
    {F : E × E → ℝ} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    ContDiff ℝ ∞ (fun p : E × E ↦
      ∫ t : E, imageBesselKernel t * F (p + (-t, 0))) := by
  have hb (m : ℕ) : ∃ C : ℝ, ∀ p, ‖iteratedFDeriv ℝ m F p‖ ≤ C := by
    obtain ⟨C, _, hC⟩ := hc.exists_bound_iteratedFDeriv hF m
    exact ⟨C, hC m le_rfl⟩
  choose C hC using hb
  let G : E → E × E → ℝ := fun t p ↦ imageBesselKernel t • F (p + (-t, 0))
  have hG (t : E) : ContDiff ℝ ∞ (G t) :=
    (hF.comp (contDiff_id.add contDiff_const)).const_smul _
  have he (m : ℕ) (t : E) (p : E × E) :
      iteratedFDeriv ℝ m (G t) p =
        imageBesselKernel t • iteratedFDeriv ℝ m F (p + (-t, 0)) := by
    rw [show G t = fun p ↦ imageBesselKernel t • F (p + (-t, 0)) from rfl,
      iteratedFDeriv_const_smul_apply' (f := fun p : E × E ↦ F (p + (-t, 0)))
        ((hF.comp (contDiff_id.add contDiff_const)).contDiffAt.of_le (by simp)),
      iteratedFDeriv_comp_add_right]
  have hm (m : ℕ) (p : E × E) : AEStronglyMeasurable
      (fun t ↦ iteratedFDeriv ℝ m (G t) p) volume := by
    simp_rw [he]
    exact measurable_imageBesselKernel.aestronglyMeasurable.smul
      (((hF.continuous_iteratedFDeriv (by simp)).comp
        (continuous_const.add (continuous_neg.prodMk continuous_const))).aestronglyMeasurable)
  have hbound (m : ℕ) (t : E) (p : E × E) :
      ‖iteratedFDeriv ℝ m (G t) p‖ ≤ imageBesselKernel t * C m := by
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (imageBesselKernel_nonneg t)]
    exact mul_le_mul_of_nonneg_left (hC m _) (imageBesselKernel_nonneg t)
  have hi (m : ℕ) (p : E × E) : Integrable (fun t ↦ iteratedFDeriv ℝ m (G t) p) :=
    (integrable_imageBesselKernel.mul_const (C m)).mono' (hm m p)
      (ae_of_all _ fun t ↦ hbound m t p)
  have hid (m : ℕ) : iteratedFDeriv ℝ m (fun p ↦ ∫ t, G t p) =
      fun p ↦ ∫ t, iteratedFDeriv ℝ m (G t) p := by
    funext p
    exact MeasureEnvelopes.iteratedFDeriv_integral_of_dominated (r := m)
      (b := fun j t ↦ imageBesselKernel t * C j) isOpen_univ
      (ae_of_all _ fun t q _ ↦ (hG t).contDiffAt.of_le (by simp))
      (fun j _ q _ ↦ hm j q) (fun j _ ↦ integrable_imageBesselKernel.mul_const (C j))
      (fun j _ ↦ ae_of_all _ fun t q _ ↦ hbound j t q) le_rfl (mem_univ p)
  have hd (m : ℕ) (p : E × E) : HasFDerivAt
      (fun q ↦ ∫ t, iteratedFDeriv ℝ m (G t) q)
      (∫ t, fderiv ℝ (iteratedFDeriv ℝ m (G t)) p) p := by
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le
      (F' := fun q t ↦ fderiv ℝ (iteratedFDeriv ℝ m (G t)) q)
      (s := univ) (bound := fun t ↦ imageBesselKernel t * C (m + 1)) univ_mem
    · exact Eventually.of_forall (hm m)
    · exact hi m p
    · exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) ↦ E × E) ℝ).continuous.comp_aestronglyMeasurable
        (hm (m + 1) p)
    · exact ae_of_all _ fun t q _ ↦ by
        simpa only [norm_fderiv_iteratedFDeriv] using hbound (m + 1) t q
    · exact integrable_imageBesselKernel.mul_const (C (m + 1))
    · exact ae_of_all _ fun t q _ ↦
        ((hG t).contDiffAt.differentiableAt_iteratedFDeriv
          (m := m) (by exact_mod_cast ENat.natCast_lt_top m)).hasFDerivAt
  change ContDiff ℝ ∞ (fun p ↦ ∫ t, G t p)
  apply contDiff_of_differentiable_iteratedFDeriv
  intro m _
  rw [hid]
  exact fun p ↦ (hd m p).differentiableAt

/-- Joint smoothness of the concrete mixed normal entry, with the constant
first-order factor already transferred to the smooth compact source section.
All domination comes from its compact derivative bounds and the Bessel mass
(`app:ch_background:prop:bg-frame`, frozen periodic energy comparison). -/
theorem contDiff_fixedMixedKernelEntry (hR : 0 < R) (hcell : 4 * R < 1 / 2)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    ContDiff ℝ ∞ (fixedMixedKernelEntry hR A i j) := by
  unfold fixedMixedKernelEntry
  apply ((FixedCutoffs.physical hR 1).contDiff.comp contDiff_fst).mul
  apply ContDiff.sum
  intro a _
  apply ContDiff.sum
  intro k _
  apply contDiff_const.mul
  have hs := contDiff_fixedMixedSourceKernel hR hcell A j k
  have hd : ContDiff ℝ ∞ (fun q ↦
      fderiv ℝ (fixedMixedSourceKernel hR A j k) q
        (EuclideanSpace.single a 1, 0)) :=
    (hs.fderiv_right (by simp)).clm_apply contDiff_const
  have hc := (hasCompactSupport_fixedMixedSourceKernel hR A j k).fderiv_apply ℝ
    (EuclideanSpace.single a 1, 0)
  simpa [Prod.add_def, sub_eq_add_neg] using contDiff_bessel_first_translate hd hc

/-- Joint smoothness of the concrete `D D*` entry: both lattice factors
share the original fixed compact source support
(`app:ch_background:prop:bg-frame`, frozen periodic energy comparison). -/
theorem contDiff_fixedLatticeProductKernelEntry (hR : 0 < R) (hcell : 4 * R < 1 / 2)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    ContDiff ℝ ∞ (fixedLatticeProductKernelEntry hR A i j) := by
  unfold fixedLatticeProductKernelEntry
  apply ContDiff.sum
  intro k _
  have hf : ContDiff ℝ ∞ (fun q : (E × E) × E ↦
      fixedLatticeKernel hR A i k (q.1.1, q.2) *
        fixedLatticeKernel hR A j k (q.1.2, q.2)) :=
    ((contDiff_fixedLatticeKernel hR hcell A i k).comp
      (contDiff_fst.fst.prodMk contDiff_snd)).mul
      ((contDiff_fixedLatticeKernel hR hcell A j k).comp
        (contDiff_fst.snd.prodMk contDiff_snd))
  apply contDiff_integral_commonCarrier hf
    (FixedCutoffs.physical hR 2).hasCompactSupport.isCompact
  intro p z hz
  have hk : fixedLatticeKernel hR A i k (p.1, z) = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h ↦
      hz ((tsupport_fixedLatticeKernel_subset hR A i k h).2))
  simp only [hk, zero_mul]

/-- Every scalar entry of the full three-term normal correction is jointly
smooth. This supplies the continuity used by the bounded matrix-kernel
identification (`app:ch_background:prop:bg-frame`). -/
theorem contDiff_fixedNormalCorrectionKernelEntry (hR : 0 < R)
    (hcell : 4 * R < 1 / 2) (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    ContDiff ℝ ∞ (fixedNormalCorrectionKernelEntry hR A i j) :=
  ((contDiff_fixedMixedKernelEntry hR hcell A i j).add
    ((contDiff_fixedMixedKernelEntry hR hcell A j i).comp
      (contDiff_snd.prodMk contDiff_fst))).add
    (contDiff_fixedLatticeProductKernelEntry hR hcell A i j)

/-- The explicit full frozen normal correction is jointly smooth as a
continuous-linear-map-valued kernel. Together with its compact support this
supplies the regularity input of `exists_compactKernel_energy_bound`
(`app:ch_background:prop:bg-frame`, frozen periodic energy comparison). -/
theorem contDiff_fixedNormalCorrectionKernel (hR : 0 < R) (hcell : 4 * R < 1 / 2)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    ContDiff ℝ ∞ (fixedNormalCorrectionKernel hR A) := by
  unfold fixedNormalCorrectionKernel
  exact ContDiff.sum fun i _ ↦ ContDiff.sum fun j _ ↦
    (contDiff_fixedNormalCorrectionKernelEntry hR hcell A i j).smul contDiff_const

end JanetCartan.ContinuumNormal.FrozenImageComparison
