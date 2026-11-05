module

public import JanetCartan.Iteration.PhysicalMean.CanonicalSource
public import JanetCartan.Iteration.PhysicalMean.FixedSourceFourierMass
public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.CanonicalPrefixData

/-!
# The literal fixed-source input before external sample weights

Consumer: the actual fixed-K physical mean and the sharp Fourier-mass estimate
in `main:eq:primary-fixed-scales`. The physical sample synthesis applies sqrt μ
ONCE outside the complete background-plus-correction wave. Consequently each
input here is the UNWEIGHTED component adjoint. The weighted native row is used
only to reassemble the aggregate input; no sample weight is divided.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalMean.OriginalCanonicalInput
open RawInputPartition RawInputRealization PhysicalSamplingShells
open CurrentMean ContinuumRow FixedSourceFourierMass

variable {n J : ℕ} {ι : Type*}

/-- The unweighted original component adjoint, using the same smooth source
and global inverse (`app:ch_mean_pairs:defn:mean-canonical`). -/
def rawInput (A : ι → RefinedInput n J →L[ℝ] OutputL2 n)
    (Q0 : OutputL2 n →L[ℝ] OutputL2 n) (r : SmoothResidual n) (i : ι) : RefinedInput n J :=
  (A i).adjoint (Q0 (smoothResidualToL2 n r))

/-- Its literal original annular representative, not a weighted input divided
by a possibly zero sample weight (`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
def nativeInput (A : ι → RefinedInput n J →L[ℝ] OutputL2 n)
    (Q0 : OutputL2 n →L[ℝ] OutputL2 n) (r : SmoothResidual n) (i : ι) :
    Lp ℂ 2 (annularShellMeasure (n := n) (refinedRadius (J := J))) :=
  (annularShellEquiv (refinedRadius (J := J))).symm (rawInput A Q0 r i)

/-- The SAME fixed prefix used by Gprefix; no extra Fourier scalar or sqrt μ
enters this physical datum (`app:ch_mean_pairs:defn:mean-canonical`). -/
def wideInput (A : ι → RefinedInput n J →L[ℝ] OutputL2 n)
    (Q0 : OutputL2 n →L[ℝ] OutputL2 n) (L : ℕ) (r : SmoothResidual n) (i : ι) : WideInput n J :=
  widePrefix n J L ((realWideRefinement n J).symm (rawInput A Q0 r i))

/-- The sampled derivative and its physical wide datum have exactly the same
input, before any external sample weight (`main:eq:old-canonical`). -/
theorem wideInput_realization {m : Type*} [Fintype m]
    (A : ι → RefinedInput n J →L[ℝ] OutputL2 n)
    (Q0 : OutputL2 n →L[ℝ] OutputL2 n) (L : ℕ) (r : SmoothResidual n) (i : ι)
    (G : WideInput n J →ₗ[ℝ] SmoothPeriodicFamily n Unit (Matrix m (Fin n) ℂ)) :
    canonicalWidePrefixRawMap G L (rawInput A Q0 r i) = G (wideInput A Q0 L r i) := rfl

/-- The additional fixed prefix only deletes original band coordinates, so
it cannot increase the radial moment used by92's sharp Fourier-mass estimate.
There is no prefix, sample-cardinality or band-count factor. -/
theorem refinedMomentNorm_prefix_le (L : ℕ) (v : RefinedInput n J) :
    refinedMomentNorm (refinedPrefix n J L v) ≤ refinedMomentNorm v := by
  unfold refinedMomentNorm
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  rw [refinedPrefix_apply]
  split_ifs
  · exact le_rfl
  · simpa using sq_nonneg (refinedRadius i ^ n * ‖v i‖)

/-- The fixed physical wide datum is controlled by the same native HALF moment
as92's unprojected datum. Its actual producer is the individual adjoint moment
on the SAME Q0 source; this lemma adds no mass or solver hypothesis. -/
theorem wideInput_fourierMass_le_halfMoment (hn : 1 ≤ n)
    (A : ι → RefinedInput n J →L[ℝ] OutputL2 n)
    (Q0 : OutputL2 n →L[ℝ] OutputL2 n) (L : ℕ) (r : SmoothResidual n) (i : ι)
    {d : Euclidean (n - 1) → ℂ} {M : ℝ}
    (hd : Measurable d) (hM : 0 ≤ M) (hbound : ∀ η, ‖d η‖ ≤ M)
    (hf : MemLp (fun u ↦ ((‖u.2‖ ^ ((n : ℝ) + 1 / 2) : ℝ) : ℂ) * nativeInput A Q0 r i u)
      2 (annularShellMeasure (n := n) (refinedRadius (J := J)))) :
    (∫ η, ‖weightedWideDensity d (wideInput A Q0 L r i) η‖) ≤
      ((2 * M * Real.sqrt (unitBallVolume n)) * 2 ^ (n + 1)) *
        lpNorm (fun u ↦ ((‖u.2‖ ^ ((n : ℝ) + 1 / 2) : ℝ) : ℂ) * nativeInput A Q0 r i u)
          2 (annularShellMeasure (n := n) (refinedRadius (J := J))) := by
  have hm := integral_norm_weightedWideDensity_le_moment hn hd hM hbound (wideInput A Q0 L r i)
  have he : wideRefinement n J (wideInput A Q0 L r i) =
      refinedPrefix n J L (rawInput A Q0 r i) := by
    change wideRefinement n J (widePrefix n J L ((wideRefinement n J).symm _)) = _
    rw [wideRefinement_prefix, LinearIsometryEquiv.apply_symm_apply]
  rw [he] at hm
  have hn := refinedMomentNorm_le_halfMoment (nativeInput A Q0 r i) hf
  have hraw : (annularShellEquiv (refinedRadius (J := J))) (nativeInput A Q0 r i) = rawInput A Q0 r i :=
    (annularShellEquiv (refinedRadius (J := J))).apply_symm_apply _
  rw [hraw] at hn
  exact hm.trans ((mul_le_mul_of_nonneg_left
    ((refinedMomentNorm_prefix_le L _).trans hn) (by positivity)).trans_eq (by ring))

/-- A real version of the existing annular isometry, with unchanged pointwise
values and measure (`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
def realAnnularEquiv (n J : ℕ) :
    Lp ℂ 2 (annularShellMeasure (n := n) (refinedRadius (J := J))) ≃ₗᵢ[ℝ] RefinedInput n J :=
  { toLinearEquiv := (annularShellEquiv (V := ℂ) (n := n) (refinedRadius (J := J))).toLinearEquiv.restrictScalars ℝ
    norm_map' := (annularShellEquiv (V := ℂ) (n := n) (refinedRadius (J := J))).norm_map }

/-- Exact unweighted annular transport of the original component adjoint.
The hArep producer is93's actual A/An equality, not an analytic estimate; it
holds also at zero outer weights (`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem nativeInput_eq_adjoint
    (A : ι → RefinedInput n J →L[ℝ] OutputL2 n)
    (Q0 : OutputL2 n →L[ℝ] OutputL2 n) (r : SmoothResidual n) (i : ι)
    (T : Lp ℂ 2 (annularShellMeasure (n := n) (refinedRadius (J := J))) →L[ℝ] OutputL2 n)
    (hA : ∀ v, A i v = T ((annularShellEquiv (refinedRadius (J := J))).symm v)) :
    nativeInput A Q0 r i = T.adjoint (Q0 (smoothResidualToL2 n r)) := by
  let e := realAnnularEquiv n J
  have hT : T = (A i).comp e.toContinuousLinearEquiv.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro f
    change T f = A i ((annularShellEquiv (refinedRadius (J := J))) f)
    simpa only [LinearIsometryEquiv.symm_apply_apply] using
      (hA ((annularShellEquiv (refinedRadius (J := J))) f)).symm
  rw [hT, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply, e.adjoint_eq_symm]
  rfl

end JanetCartan.PhysicalMean.OriginalCanonicalInput
end
