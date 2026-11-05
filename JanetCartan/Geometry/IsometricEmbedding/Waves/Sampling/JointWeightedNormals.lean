module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.JointWeightedPartition

/-!
# Weighted normal reassembly for the actual joint refinement

The subset carrier weights and the angular masks are the concrete functions
constructed in `JointWeightedPartition`. Their exact partition reassembles the
original annular and grouped-prefix normals on the original Lebesgue spaces.
The geometric covering premise concerns the support of the ORIGINAL kernel;
no normal identity or successful sampling event is assumed.
-/

@[expose] public noncomputable section
open Set Metric NormedSpace

namespace JanetCartan.Sampling
open SamplingKernelBounds SeparatedSampling ContinuumRow.CanonicalConic

variable {I P : Type*} [Fintype I] [DecidableEq I]
    [TopologicalSpace P] [FirstCountableTopology P] [LocallyCompactSpace P]
    {n : ℕ}
    (ηb : I → Euclidean (n - 1)) (r : I → ℝ)
    (hηb : ∀ i, ηb i ≠ 0) (hr : ∀ i, 0 < r i)

/-- The actual kernel on each subset chart changes only the original angular
detector. The original phase, amplitude, radial mask, physical output and
Fourier scalar are retained (`app:ch_waves:eq:sampling-prefix-normal`). -/
def jointSubsetKernel (D : BandKernelData P n)
    (hfloor : ∀ η, ‖η‖ ≤ 1 → D.mask η = 0) (s : Finset I) (i : s) :
    BandKernelData P n :=
  angularLocalizedKernel D hfloor (subsetAngularMask ηb r hηb hr s i)
    (canonicalAngularSquareMask_continuousOn _ _ _ _ i)
    (canonicalAngularSquareMask_abs_le _ _ _ _ i)

/-- The original carrier-weighted annular normal is exactly the sum of the
constructed local normals. The covering requirement is used only at nonzero
original weight and detector values (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem sum_carrierSubsetWeight_jointSubsetKernel_normal
    (D : BandKernelData P n) (hfloor : ∀ η, ‖η‖ ≤ 1 → D.mask η = 0)
    (ψ : Point → ℝ) (b : I → Point → ℝ) (z : Point)
    (hcover : ψ z ≠ 0 → ∀ η, D.mask η ≠ 0 → ∃ i, b i z = 1 ∧
      normalize η ∈ ball (normalize (ηb i)) (angularWidth (ηb i) (r i) / 4))
    (R : ℝ) (p : P) :
    ∑ s : Finset I, ∑ i : s, carrierSubsetWeight ψ b s z •
      atomNormal ((jointSubsetKernel ηb r hηb hr D hfloor s i).operator R p) =
        ψ z • atomNormal (D.operator R p) := by
  classical
  calc
    _ = ∑ s : Finset I, carrierSubsetWeight ψ b s z • atomNormal (D.operator R p) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [← Finset.smul_sum]
      by_cases hs : carrierSubsetWeight ψ b s z = 0
      · simp [hs]
      · congr 1
        apply sum_angularLocalizedKernel_normal
        intro η hη
        exact subsetAngularMask_sum_sq ηb r hηb hr ψ b s hs
          (hcover (carrierSubsetWeight_support ψ b s hs).1 η hη)
    _ = _ := by rw [← Finset.sum_smul, sum_carrierSubsetWeight]

/-- Every grouped prefix has the same weighted reassembly. Both sharp
pieces stay under the original smooth-band label, and no indicator enters
the smooth calculus (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem sum_carrierSubsetWeight_jointSubsetKernel_prefix_normal {J : ℕ}
    (D : BandKernelData (Fin J × P) n) (hfloor : ∀ η, ‖η‖ ≤ 1 → D.mask η = 0)
    (ψ : Point → ℝ) (b : I → Point → ℝ) (z : Point)
    (hcover : ψ z ≠ 0 → ∀ η, D.mask η ≠ 0 → ∃ i, b i z = 1 ∧
      normalize η ∈ ball (normalize (ηb i)) (angularWidth (ηb i) (r i) / 4))
    (L : ℕ) (p : P) :
    ∑ s : Finset I, ∑ i : s, carrierSubsetWeight ψ b s z •
      atomNormal (refinedKernelPrefix (jointSubsetKernel ηb r hηb hr D hfloor s i) L p) =
        ψ z • atomNormal (refinedKernelPrefix D L p) := by
  classical
  calc
    _ = ∑ s : Finset I, carrierSubsetWeight ψ b s z •
        atomNormal (refinedKernelPrefix D L p) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [← Finset.smul_sum]
      by_cases hs : carrierSubsetWeight ψ b s z = 0
      · simp [hs]
      · congr 1
        apply sum_angularLocalizedKernel_prefix_normal
        intro η hη
        exact subsetAngularMask_sum_sq ηb r hηb hr ψ b s hs
          (hcover (carrierSubsetWeight_support ψ b s hs).1 η hη)
    _ = _ := by rw [← Finset.sum_smul, sum_carrierSubsetWeight]

/-- Weighted reassembly preserves both physical real quadratures and the
literal factor four on the full real output (`app:ch_waves:eq:real-normal`). -/
theorem sum_carrierSubsetWeight_jointSubsetKernel_realPrefix_normal {J : ℕ}
    (D : BandKernelData (Fin J × P) n) (hfloor : ∀ η, ‖η‖ ≤ 1 → D.mask η = 0)
    (ψ : Point → ℝ) (b : I → Point → ℝ) (z : Point)
    (hcover : ψ z ≠ 0 → ∀ η, D.mask η ≠ 0 → ∃ i, b i z = 1 ∧
      normalize η ∈ ball (normalize (ηb i)) (angularWidth (ηb i) (r i) / 4))
    (L : ℕ) (p : P) :
    ∑ s : Finset I, ∑ i : s, carrierSubsetWeight ψ b s z •
      ((realQuadratureChannel (refinedKernelPrefix
        (jointSubsetKernel ηb r hηb hr D hfloor s i) L p)) ∘L
       (realQuadratureChannel (refinedKernelPrefix
        (jointSubsetKernel ηb r hηb hr D hfloor s i) L p)).adjoint) =
      (4 : ℝ) • realOutputCompression (ψ z • atomNormal (refinedKernelPrefix D L p)) := by
  classical
  simp_rw [realQuadratureChannel_normal_eq_four_realPart]
  rw [← sum_carrierSubsetWeight_jointSubsetKernel_prefix_normal
    ηb r hηb hr D hfloor ψ b z hcover L p]
  ext1 v
  simp [realOutputCompression, atomNormal, Finset.smul_sum, smul_smul, mul_comm]

end JanetCartan.Sampling
