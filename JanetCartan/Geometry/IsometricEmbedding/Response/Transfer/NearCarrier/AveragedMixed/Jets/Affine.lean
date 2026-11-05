module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.AveragedMixed.Basic
public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.InputJets.AveragedGradient.Integral

/-!
# Affine pullback of the primitive mixed jets

The normalized segment in `app:ch_response:eq:direct-envelope-profile` is
`(x, ε) ↦ (x, ζ + t • ε)`. Its linear part is a contraction for `0 ≤ t ≤ 1`.
These estimates supply the integrand bounds for the actual averaged matrix.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer

local instance averagedMixedAffineMatrixTopology (n : ℕ) : TopologicalSpace (Matrix (Fin n) (Fin n) ℝ) :=
  (Matrix.frobeniusNormedAddCommGroup (m := Fin n) (n := Fin n)
    (α := ℝ)).toUniformSpace.toTopologicalSpace

/-- Linear part of the normalized segment in
`app:ch_response:eq:direct-envelope-profile`. -/
def mixedSegmentLinear (n : ℕ) (t : ℝ) :
    (Euclidean n × Euclidean n) →L[ℝ] (Euclidean n × Euclidean n) :=
  (ContinuousLinearMap.fst ℝ (Euclidean n) (Euclidean n)).prod
    (t • ContinuousLinearMap.snd ℝ (Euclidean n) (Euclidean n))

/-- The segment pullback loses no derivative constant in the product norm
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem norm_mixedSegmentLinear_le (n : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖mixedSegmentLinear n t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro p
  change ‖(p.1, t • p.2)‖ ≤ 1 * ‖p‖
  rw [one_mul, Prod.norm_def, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
  exact max_le (norm_fst_le p)
    ((mul_le_of_le_one_left (norm_nonneg _) ht.2).trans (norm_snd_le p))

/-- Primitive mixed jets control the affine segment integrand, before any
integration (`app:ch_response:eq:direct-envelope-profile`). -/
theorem norm_iteratedFDeriv_mixedPhase_segment_le {n : ℕ}
    {S : Euclidean n → Euclidean n → ℝ} {ζ : Euclidean n}
    {X D : Set (Euclidean n)} (hX : IsOpen X) (hD : IsOpen D)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry (FourierIntegral.mixedPhaseMatrix S)) (X ×ˢ D))
    {k : ℕ} {B : ℝ}
    (hb : ∀ q ∈ X ×ˢ D,
      ‖iteratedFDeriv ℝ k (Function.uncurry (FourierIntegral.mixedPhaseMatrix S)) q‖ ≤ B)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    {p : Euclidean n × Euclidean n} (hp : (p.1, ζ + t • p.2) ∈ X ×ˢ D) :
    ‖iteratedFDeriv ℝ k
      (fun q : Euclidean n × Euclidean n ↦ FourierIntegral.mixedPhaseMatrix S q.1
        (ζ + t • q.2)) p‖ ≤ B := by
  let a : Euclidean n × Euclidean n := (0, ζ)
  let f := Function.uncurry (FourierIntegral.mixedPhaseMatrix S)
  let g := fun q ↦ f (a + q)
  let U := (fun q ↦ a + q) ⁻¹' (X ×ˢ D)
  have hU : IsOpen U := (hX.prod hD).preimage (continuous_const.add continuous_id)
  have hg : ContDiffOn ℝ ∞ g U := hS.comp
    (contDiff_const.add contDiff_id).contDiffOn (fun _ h ↦ h)
  have hp' : mixedSegmentLinear n t p ∈ U := by
    simpa [U, a, mixedSegmentLinear] using hp
  have he : (fun q : Euclidean n × Euclidean n ↦
      FourierIntegral.mixedPhaseMatrix S q.1 (ζ + t • q.2)) =
      g ∘ mixedSegmentLinear n t := by
    ext q i j
    simp [g, f, a, mixedSegmentLinear]
  rw [he]
  calc
    _ ≤ ‖iteratedFDeriv ℝ k g (mixedSegmentLinear n t p)‖ *
        ‖mixedSegmentLinear n t‖ ^ k :=
      NormalComparison.norm_iteratedFDeriv_comp_linear_on_open_le _ hU hg hp' k
    _ ≤ ‖iteratedFDeriv ℝ k g (mixedSegmentLinear n t p)‖ :=
      mul_le_of_le_one_right (norm_nonneg _)
        (pow_le_one₀ (norm_nonneg _) (norm_mixedSegmentLinear_le n ht))
    _ ≤ B := by
      rw [show g = (fun q ↦ f (a + q)) from rfl, iteratedFDeriv_comp_add_left]
      simpa [a, f, mixedSegmentLinear] using hb _ hp

/-- Joint smoothness of the segment follows from the primitive mixed matrix
on the buffered chart (`app:ch_response:eq:direct-envelope-profile`). -/
theorem mixedPhase_segment_contDiffAt {n : ℕ}
    {S : Euclidean n → Euclidean n → ℝ} {ζ : Euclidean n}
    {X D : Set (Euclidean n)} (hX : IsOpen X) (hD : IsOpen D)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry (FourierIntegral.mixedPhaseMatrix S)) (X ×ˢ D))
    {z : ℝ × (Euclidean n × Euclidean n)}
    (hz : (z.2.1, ζ + z.1 • z.2.2) ∈ X ×ˢ D) :
    ContDiffAt ℝ ∞ (fun w : ℝ × (Euclidean n × Euclidean n) ↦
      FourierIntegral.mixedPhaseMatrix S w.2.1 (ζ + w.1 • w.2.2)) z :=
  (hS.contDiffAt ((hX.prod hD).mem_nhds hz)).comp z
    (contDiffAt_snd.fst.prodMk
      (contDiffAt_const.add (contDiffAt_fst.smul contDiffAt_snd.snd)))

end JanetCartan.ResponseTransfer
