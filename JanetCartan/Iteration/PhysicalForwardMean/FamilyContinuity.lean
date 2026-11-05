module

public import JanetCartan.Iteration.PhysicalForwardMean.KernelIdentity
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.DifferentiatedAmplitudes.Integral

/-!
# Qualitative native sampled-family physical jet continuity

The ORIGINAL fixed-sample families are jointly smooth in physical space and
frequency. Only this qualitative fact is used for compact integration; no
frequency derivatives or their norms enter the estimate. The sample type is
arbitrary discrete and never differentiated. This leaf discharges the computed
branch continuity and physical-kernel-jet continuity needed by the forward
construction, rather than postulating those analytic output properties.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff
namespace JanetCartan.PhysicalForwardMean
open RawPrimary RawPrimary.SliceBounds PhysicalMean NormalComparison

variable {n : ℕ} {ι : Type*} [TopologicalSpace ι] [DiscreteTopology ι]
  {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
local notation "E" => Euclidean n

/-- The explicitly differentiated original branch is jointly continuous on the
native discrete-sample/frequency space, without any quantitative frequency jets
(`app:ch_mean_pairs:eq:block-normal`). -/
theorem continuous_discrete_forwardBranchAmplitude
    (θ : ι → P → E → ℝ) (A : ι → P → E → ℂ)
    (hθ : ∀ i, ContDiff ℝ ∞ (Function.uncurry (θ i)))
    (hA : ∀ i, ContDiff ℝ ∞ (Function.uncurry (A i)))
    {s : ℕ} (v : Fin s → E) (b : SliceDerivativeBranch s) :
    Continuous (fun q : (ι × P) × E ↦
      sliceDerivativeAmplitude (θ q.1.1 q.1.2) (A q.1.1 q.1.2) v b q.2) := by
  have hc : Continuous (fun q : ι × (E × P) ↦
      sliceDerivativeAmplitude (θ q.1 q.2.2) (A q.1 q.2.2) v b q.2.1) := by
    apply continuous_prod_of_discrete_left.mpr
    intro i
    have hh := contDiffOn_jointSliceDerivativeAmplitude isOpen_univ isOpen_univ
      (((hθ i).comp (contDiff_snd.prodMk contDiff_fst)).contDiffOn (s := univ ×ˢ univ))
      (((hA i).comp (contDiff_snd.prodMk contDiff_fst)).contDiffOn (s := univ ×ˢ univ)) v b
    exact (contDiffOn_univ.mp (by simpa only [univ_prod_univ,
      Function.comp_def, Function.uncurry_apply_pair] using hh)).continuous
  exact hc.comp (continuous_fst.fst.prodMk (continuous_snd.prodMk continuous_fst.snd))

/-- All physical jets of the actual original forward kernel are jointly
continuous on its literal native sampled domain. The original input mask needs
only continuity, and is not differentiated. No regularity in the discrete index
or quantitative initial-frequency jet is introduced
(`app:ch_mean_pairs:eq:block-normal`, `app:ch_mean_pairs:eq:block-fields`). -/
theorem continuous_discrete_physicalForwardKernel_jets
    (φ : ι → P → E → ℝ) (A : ι → P → E → ℂ) (m : ι × P → ℝ)
    (hφ : ∀ i, ContDiff ℝ ∞ (Function.uncurry (φ i)))
    (hA : ∀ i, ContDiff ℝ ∞ (Function.uncurry (A i))) (hm : Continuous m)
    (j : ℕ) :
    Continuous (fun q : E × (ι × P) ↦ iteratedFDeriv ℝ j
      (fun x ↦ physicalForwardKernel (fun u ↦ φ u.1 u.2) m (fun u ↦ A u.1 u.2) x q.2) q.1) := by
  let atom := fun i (q : E × P) ↦
    Complex.exp (Complex.I * (φ i q.2 q.1 : ℂ)) • A i q.2 q.1
  have ha (i : ι) : ContDiff ℝ ∞ (atom i) :=
    ((contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
      ((hφ i).comp (contDiff_snd.prodMk contDiff_fst)))).cexp).smul ((hA i).comp (contDiff_snd.prodMk contDiff_fst))
  have hc : Continuous (fun q : ι × (E × P) ↦
      iteratedFDeriv ℝ j (fun x ↦ atom q.1 (x, q.2.2)) q.2.1) := by
    apply continuous_prod_of_discrete_left.mpr
    intro i
    have hh := contDiffOn_atomPhysicalJet isOpen_univ isOpen_univ
      ((ha i).contDiffOn (s := univ ×ˢ univ)) j
    exact (contDiffOn_univ.mp (by simpa only [univ_prod_univ,
      Function.comp_def, Function.uncurry_apply_pair] using hh)).continuous
  have hscaled : Continuous (fun q : E × (ι × P) ↦
      (m q.2 : ℂ) • iteratedFDeriv ℝ j (fun x ↦ atom q.2.1 (x, q.2.2)) q.1) :=
    (Complex.continuous_ofReal.comp (hm.comp continuous_snd)).smul
      (hc.comp (continuous_snd.fst.prodMk (continuous_fst.prodMk continuous_snd.snd)))
  apply hscaled.congr
  intro q
  have he : (fun x ↦ physicalForwardKernel (fun u ↦ φ u.1 u.2) m
      (fun u ↦ A u.1 u.2) x q.2) = fun x ↦ (m q.2 : ℂ) • atom q.2.1 (x,q.2.2) := by
    funext x
    simp only [physicalForwardKernel, sampledMomentKernel, oscillatoryFactor, one_mul,
      star_star, atom, smul_eq_mul, mul_assoc]
  rw [he]
  have has : ContDiff ℝ ∞ (fun x : E ↦ atom q.2.1 (x,q.2.2)) :=
    (ha q.2.1).comp (contDiff_id.prodMk (contDiff_const (c := q.2.2)))
  exact (iteratedFDeriv_const_smul_apply' (a := (m q.2 : ℂ))
    (has.contDiffAt.of_le (by simp : (j : ℕ∞ω) ≤ ∞))).symm

end JanetCartan.PhysicalForwardMean
