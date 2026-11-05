module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalAtomRealization.InitializedRealization.FourierClassical

/-!
# Joint reduced-solution jets from the actual scalar L² components

The normalized inverse returns `PiLp` scalar Fourier envelopes. Assemble those
exact classes with the existing L² isometry, then use spatial Sobolev embedding
on every ordered parameter jet. This supplies the reduced-solution input of
`completedVariationComplex_joint_response_graded`, with total Fourier reserve
`m+n+1` for a joint jet of order `m`, hence `m+n+3` for the physical response.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped ContDiff Topology

namespace JanetCartan.CanonicalAtomRealization

open Pseudodifferential

/-- The SAME scalar Fourier representatives control the full joint jet and
each of its coordinates. The constant precedes the original parameter set,
field, smallness amplitude and frequency. Arbitrary size expressions are
retained verbatim, including a tame high/low scalar split
(`app:ch_response:eq:response-graded-derivative`). -/
theorem exists_reducedParameterJet_fourier_constant (n d N m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (V : Set (Euclidean 3 × Euclidean d)), IsOpen V →
      ∀ (f : Euclidean n × (Euclidean 3 × Euclidean d) → EuclideanSpace ℂ (Fin N)),
        ContDiffOn ℝ ∞ f (univ ×ˢ V) →
      ∀ A : ℝ, 0 ≤ A →
        (∀ c ∈ V, ∀ k ≤ m, ∀ w : Fin k → (Euclidean 3 × Euclidean d),
          (∀ l, ‖w l‖ ≤ 1) →
          ∃ u : PiLp 2 (fun _ : Fin N ↦ Lp ℂ 2 (volume : Measure (Euclidean n))),
            (∀ i, u i =ᵐ[volume]
              (fun x ↦ (iteratedFDeriv ℝ k (fun b ↦ f (x,b)) c w) i)) ∧
            MemMatrixFourierSobolev ((m-k+n+1 : ℕ) : ℝ) u ∧
            matrixFourierSobolevNorm ((m-k+n+1 : ℕ) : ℝ) u ≤ A) →
      ∀ p ∈ univ ×ˢ V,
        ‖iteratedFDeriv ℝ m f p‖ ≤ C*A ∧
        ∀ i, ‖iteratedFDeriv ℝ m (fun q ↦ f q i) p‖ ≤ C*A := by
  obtain ⟨C,hC,hclassical⟩ := exists_fullParameterResponse_cNorm_constant n d N m
  refine ⟨C,hC,?_⟩
  intro V hV f hf A hA hfourier
  have hvec (c) (hc : c ∈ V) (k : ℕ) (hk : k ≤ m)
      (w : Fin k → (Euclidean 3 × Euclidean d)) (hw : ∀ l, ‖w l‖ ≤ 1) :
      ∃ u : Lp (EuclideanSpace ℂ (Fin N)) 2 (volume : Measure (Euclidean n)),
        u =ᵐ[volume] (fun x ↦ iteratedFDeriv ℝ k (fun b ↦ f (x,b)) c w) ∧
        MemVectorFourierSobolev ((m-k+n+1 : ℕ) : ℝ) u ∧
        vectorFourierSobolevNorm ((m-k+n+1 : ℕ) : ℝ) u ≤ A := by
    obtain ⟨u,hrep,hu,hbound⟩ := hfourier c hc k hk w hw
    let v : Lp (EuclideanSpace ℂ (Fin N)) 2 (volume : Measure (Euclidean n)) :=
      (finiteL2CoordinateIsometry volume).symm u
    have hcoord : finiteL2CoordinateIsometry volume v = u :=
      (finiteL2CoordinateIsometry volume).apply_symm_apply u
    refine ⟨v,?_,?_,?_⟩
    · have hcAE := ae_all_iff.mpr (fun i : Fin N ↦ finiteL2Coordinates_apply_ae volume v i)
      have hrAE := ae_all_iff.mpr hrep
      filter_upwards [hcAE,hrAE] with x hx hy
      apply PiLp.ext
      intro i
      have h := hx i
      change (finiteL2CoordinateIsometry volume v i) x = v x i at h
      rw [hcoord] at h
      exact h.symm.trans (hy i)
    · simpa only [MemVectorFourierSobolev, hcoord] using hu
    · simpa only [vectorFourierSobolevNorm, hcoord] using hbound
  intro p hp
  have hat : ContDiffAt ℝ ∞ f p := hf.contDiffAt ((isOpen_univ.prod hV).mem_nhds hp)
  have hsingle : ({p} : Set (Euclidean n × (Euclidean 3 × Euclidean d))) ⊆ univ ×ˢ V :=
    singleton_subset_iff.mpr hp
  have hbound : ‖iteratedFDeriv ℝ m f p‖ ≤ C*A :=
    (norm_iteratedFDeriv_le_cNorm_of_contDiffAt isCompact_singleton
      (fun q hq ↦ by rcases mem_singleton_iff.mp hq with rfl; exact hat.of_le (by simp))
      (mem_singleton p) le_rfl).trans
        (hclassical V hV f hf A hA hvec {p} hsingle)
  refine ⟨hbound,?_⟩
  intro i
  let P : EuclideanSpace ℂ (Fin N) →L[ℝ] ℂ := PiLp.proj 2 (fun _ : Fin N ↦ ℂ) i
  have hP : ‖P‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    change ‖v i‖ ≤ 1 * ‖v‖
    simpa only [one_mul] using PiLp.norm_apply_le v i
  apply (P.norm_iteratedFDeriv_comp_left hat (by simp : (m : ℕ∞ω) ≤ ∞)).trans
  exact (mul_le_of_le_one_left (norm_nonneg _) hP).trans hbound

/-- The full reduced Fourier profile yields the joint classical profile
with exactly `n+1` reserve consumed by spatial Sobolev embedding. The
constants precede the source profile, scalar size, frequency and parameter
domain. This is the precise Fourier input used before the two further
reconstruction derivatives in `fullPrimaryResponse_fixedSolver_joint_graded`
(`app:ch_response:eq:response-graded-reduced`). -/
theorem exists_reducedParameterJoint_profile_constants (n d N : ℕ) :
    ∃ C : ℕ → ℝ, (∀ m, 0 ≤ C m) ∧
      ∀ (V : Set (Euclidean 3 × Euclidean d)), IsOpen V →
      ∀ (f : Euclidean n × (Euclidean 3 × Euclidean d) → EuclideanSpace ℂ (Fin N)),
        ContDiffOn ℝ ∞ f (univ ×ˢ V) →
      ∀ B : ℕ → ℝ, (∀ m, 0 ≤ B m) →
      ∀ A K : ℝ, 0 ≤ A → 1 ≤ K → ∀ reserve : ℕ,
        (∀ c ∈ V, ∀ k p : ℕ, ∀ w : Fin k → (Euclidean 3 × Euclidean d),
          (∀ l, ‖w l‖ ≤ 1) →
          ∃ u : PiLp 2 (fun _ : Fin N ↦ Lp ℂ 2 (volume : Measure (Euclidean n))),
            (∀ i, u i =ᵐ[volume]
              (fun x ↦ (iteratedFDeriv ℝ k (fun b ↦ f (x,b)) c w) i)) ∧
            MemMatrixFourierSobolev (p : ℝ) u ∧
            matrixFourierSobolevNorm (p : ℝ) u ≤
              B (p+k) * A * K^(p+k-(reserve+n+1))) →
      ∀ m q, q ∈ univ ×ˢ V →
        ‖iteratedFDeriv ℝ m f q‖ ≤ C m * B (m+n+1) * A * K^(m-reserve) ∧
        ∀ i, ‖iteratedFDeriv ℝ m (fun p ↦ f p i) q‖ ≤
          C m * B (m+n+1) * A * K^(m-reserve) := by
  classical
  choose C hC hjet using exists_reducedParameterJet_fourier_constant n d N
  refine ⟨C,hC,?_⟩
  intro V hV f hf B hB A K hA hK reserve hfourier m q hq
  have hsize : 0 ≤ B (m+n+1)*A*K^(m-reserve) :=
    mul_nonneg (mul_nonneg (hB _) hA) (pow_nonneg (zero_le_one.trans hK) _)
  have h := hjet m V hV f hf (B (m+n+1)*A*K^(m-reserve)) hsize ?_ q hq
  · simpa only [mul_assoc] using h
  · intro c hc k hk w hw
    obtain ⟨u,hrep,hu,hbound⟩ := hfourier c hc k (m-k+n+1) w hw
    refine ⟨u,hrep,hu,?_⟩
    have ht : m-k+n+1+k = m+n+1 := by omega
    have he : m+n+1-(reserve+n+1) = m-reserve := by omega
    simpa only [ht,he] using hbound

end JanetCartan.CanonicalAtomRealization
