module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalRowComparison.BandIdentification

/-!
# Continuity of the corrected cross kernel

The original sampling family varies continuously in the node and discretely
in the color. Apply its literal complexified real measurement to the two
extended derivative amplitudes (`main:eq:canonical-identity`).
-/

@[expose] public noncomputable section
open Set
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.CanonicalAtomRealization
open CanonicalRowComparison CurrentMean

/-- Continuity of the literal complex measurement used in the corrected
sampling kernel (`app:ch_mean_pairs:defn:mean-canonical`). -/
private theorem continuous_appliedCrossMeasurement {X : Type*} [TopologicalSpace X] {n N : ℕ}
    {C : X → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n}
    {B V : X → Matrix (Fin N) (Fin n) ℂ} (hC : Continuous C) (hB : Continuous B)
    (hV : Continuous V) : Continuous (fun t ↦ complexCrossMeasurement (C t) (B t) (V t)) := by
  let L := hermitianContinuousBilinear (m := Fin N) (n := Fin n)
  change Continuous (fun t ↦ euclideanComplexInclusion (C t (L (B t) (V t))) -
    Complex.I • euclideanComplexInclusion (C t (L (B t) (Complex.I • V t))))
  have hL := L.continuous.comp hB
  exact (euclideanComplexInclusion.continuous.comp (hC.clm_apply (hL.clm_apply hV))).sub
    ((euclideanComplexInclusion.continuous.comp
      (hC.clm_apply (hL.clm_apply (hV.const_smul Complex.I)))).const_smul Complex.I)

/-- The extended corrected amplitude gives the continuous joint cross kernel
required by the original sampling constructor. Inverse frequencies are fixed
per color, and the original node and extended carrier vary continuously
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem continuous_coloredCanonicalCrossKernel {ι γ : Type*} [TopologicalSpace ι]
    [TopologicalSpace γ] [DiscreteTopology γ] {n N : ℕ}
    (A : γ → (Euclidean n × (Euclidean 3 × Euclidean (n - 1))) → Matrix (Fin N) (Fin n) ℂ)
    (hA : ∀ c, Continuous (A c)) (C : Euclidean n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n)
    (hC : Continuous C) (color : ι → γ) (hcolor : Continuous color)
    (node : ι → Euclidean 3) (hnode : Continuous node)
    (carrier : ι → Euclidean (n - 1)) (hcarrier : Continuous carrier) :
    Continuous (fun q : (ι × Euclidean n) × Euclidean (n - 1) ↦
      complexCrossMeasurement (C q.1.2) (A (color q.1.1) (q.1.2, node q.1.1, carrier q.1.1))
        (A (color q.1.1) (q.1.2, node q.1.1, q.2))) := by
  have hu : Continuous (Function.uncurry A) := continuous_prod_of_discrete_left.mpr hA
  apply continuous_appliedCrossMeasurement (hC.comp (continuous_snd.comp continuous_fst))
  · exact hu.comp (f := fun q : (ι × Euclidean n) × Euclidean (n - 1) ↦
      (color q.1.1, q.1.2, node q.1.1, carrier q.1.1)) (by fun_prop)
  · exact hu.comp (f := fun q : (ι × Euclidean n) × Euclidean (n - 1) ↦
      (color q.1.1, q.1.2, node q.1.1, q.2)) (by fun_prop)

/-- On a fixed geometry the finitely many colored amplitudes have one
cross-kernel bound before the raw data or sampled labels. Compactness here
gives only the qualitative bound needed to form the operator, not the
history-uniform estimates (`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem exists_coloredCanonicalCrossKernel_bound {γ : Type*} [Finite γ] {n N : ℕ}
    (A : γ → (Euclidean n × (Euclidean 3 × Euclidean (n - 1))) → Matrix (Fin N) (Fin n) ℂ)
    (hA : ∀ c, Continuous (A c)) (hc : ∀ c, HasCompactSupport (A c))
    (C : Euclidean n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n) (hC : Continuous C)
    {K : Set (Euclidean n)} (hK : IsCompact K)
    (hs : ∀ c x z ξ, x ∉ K → A c (x, z, ξ) = 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ c x z ξ ξ',
      ‖complexCrossMeasurement (C x) (A c (x, z, ξ)) (A c (x, z, ξ'))‖ ≤ M := by
  let R := ⋃ c : γ, Set.range (A c)
  have hr : IsCompact R := isCompact_iUnion (fun c ↦ (hc c).isCompact_range (hA c))
  let B := fun q : Euclidean n × (Matrix (Fin N) (Fin n) ℂ × Matrix (Fin N) (Fin n) ℂ) ↦
    complexCrossMeasurement (C q.1) q.2.1 q.2.2
  have hb : Continuous B := continuous_appliedCrossMeasurement (hC.comp continuous_fst)
    (continuous_fst.comp continuous_snd) (continuous_snd.comp continuous_snd)
  obtain ⟨M, hM⟩ := (hK.prod (hr.prod hr)).exists_bound_of_continuousOn hb.continuousOn
  refine ⟨max 0 M, le_max_left _ _, fun c x z ξ ξ' ↦ ?_⟩
  by_cases hx : x ∈ K
  · exact (hM (x, A c (x, z, ξ), A c (x, z, ξ')) ⟨hx,
      mem_iUnion.mpr ⟨c, ⟨_, rfl⟩⟩, mem_iUnion.mpr ⟨c, ⟨_, rfl⟩⟩⟩).trans (le_max_right _ _)
  · simp only [hs c x z ξ' hx, map_zero, norm_zero, le_max_iff, le_refl, true_or]

open Sampling SamplingKernelBounds
variable {ι γ : Type*} [TopologicalSpace ι] [FirstCountableTopology ι] [LocallyCompactSpace ι]
    [TopologicalSpace γ] [DiscreteTopology γ] {n N : ℕ}

/-- Instantiate the existing sampling band constructor with the literal
colored cross amplitude. It uses the same extended matrix amplitude at
zero and at the shifted covector, and keeps the supplied support, mask,
Lebesgue measure and bounds (`app:ch_waves:eq:sampling-prefix-normal`). -/
def coloredCanonicalCrossBandData (J : ℕ)
    (S : ι → Euclidean n → Euclidean (n - 1) → ℝ)
    (hS : Continuous (fun q : (ι × Euclidean n) × Euclidean (n - 1) ↦ S q.1.1 q.1.2 q.2))
    (A : γ → (Euclidean n × (Euclidean 3 × Euclidean (n - 1))) → Matrix (Fin N) (Fin n) ℂ)
    (hA : ∀ c, Continuous (A c)) (C : Euclidean n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n)
    (hC : Continuous C) (color : ι → γ) (hcolor : Continuous color)
    (node : ι → Euclidean 3) (hnode : Continuous node)
    (carrier : ι → Euclidean (n - 1)) (hcarrier : Continuous carrier)
    (rate : γ → ℝ) (hnz : ∀ c, rate c ≠ 0) (mask : Euclidean (n - 1) → ℂ) (hd : Continuous mask)
    (K : Set (Euclidean n)) (hK : IsCompact K)
    (hs : ∀ c x z ξ, x ∉ K → A c (x, z, ξ) = 0)
    (M Md : ℝ) (hM : 0 ≤ M) (hMd : 0 ≤ Md)
    (hb : ∀ i x ξ, ‖complexCrossMeasurement (C x) (A (color i) (x, node i, carrier i))
      (A (color i) (x, node i, ξ))‖ ≤ M) (hdb : ∀ ξ, ‖mask ξ‖ ≤ Md) :
    BandKernelData (Fin J × ι) n :=
  RawKernel.bandKernelData S (fun i x ξ ↦ complexCrossMeasurement (C x) (A (color i) (x, node i, carrier i))
      (A (color i) (x, node i, ξ))) carrier (fun i ↦ rate (color i)) mask hS
    (continuous_coloredCanonicalCrossKernel A hA C hC color hcolor node hnode carrier hcarrier)
    hcarrier ((continuous_of_discreteTopology (f := rate)).comp hcolor) (fun i ↦ hnz (color i)) hd K hK
    (fun i x ξ hx ↦ by rw [hs (color i) x (node i) ξ hx, map_zero]) M Md hM hMd hb hdb
end JanetCartan.CanonicalAtomRealization
