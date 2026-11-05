module

public import JanetCartan.Geometry.IsometricEmbedding.Response.FullSourceEnvelopes.SourceJets
public import JanetCartan.Geometry.IsometricEmbedding.Response.PrimarySources.Envelopes.Sobolev.LocalJets
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ParameterDerivatives.InactiveDerivatives.CompactSobolev
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ParameterDerivatives.InactiveDerivatives.SobolevMembership

/-!
# Same-order reserved Fourier profiles for the physical source

The literal compact source is unchanged. Contract mixed parameter jets and
apply the existing compact-vector Fourier bound at exactly the spatial order.
Natural subtraction survives below the reserve; no negative slow-scale factor
is extracted. Consumer: the initial datum of the actual finite residual words,
`app:ch_response:eq:response-graded-source`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set MeasureTheory
open scoped ContDiff
namespace JanetCartan.PhysicalPrimary
open Pseudodifferential ResponseTransfer ResponseTransfer.Complement
open ResponseTransfer.FullSourceEnvelopes ResponsePrimarySources
open FourierIntegral FourierIntegral.LowBounds
variable {n d r : ℕ}
local notation "E" => Euclidean n
local notation "Par" => Euclidean 3 × Euclidean d
local notation "F" => EuclideanSpace ℂ (Fin r)

/-- Compact joint jets give the literal Fourier profile with the SAME source
reserve and parameter directions. Constants precede all source functions,
scales and reserves (`app:ch_response:eq:response-graded-source`). -/
theorem exists_reserved_source_fourier_constants
    {S : Set E} (hS : IsCompact S) (J : ℕ → ℝ) (hJ : ∀ j, 0 ≤ J j) :
    ∃ C : ℕ → ℕ → ℝ, (∀ k s, 0 ≤ C k s) ∧
    ∀ (a : E × Par → F) (_ha : ContDiff ℝ ∞ a)
      (_has : ∀ w, w.1 ∉ S → a w = 0) (A K : ℝ) (reserve : ℕ),
      0 ≤ A → 1 ≤ K →
      (∀ w j, ‖iteratedFDeriv ℝ j a w‖ ≤ J j * A * K^(j-reserve)) →
      ∀ c k (v : Fin k → Par), (∀ j, ‖v j‖ ≤ 1) → ∀ s : ℕ,
        let f := fun x ↦ iteratedFDeriv ℝ k (fun b ↦ a (x,b)) c v
        ∃ hm : MemLp f 2 volume, MemVectorFourierSobolev (s : ℝ) (hm.toLp f) ∧
          vectorFourierSobolevNorm (s : ℝ) (hm.toLp f) ≤ C k s * A * K^(s+k-reserve) := by
  let C := fun k s ↦ ((r : ℝ)*(1+(n : ℝ))^s*Real.sqrt (volume.real S)) *
    ∑ j ∈ Finset.range (s+1), J (j+k)
  have hC k s : 0 ≤ C k s := mul_nonneg
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by positivity) _))
      (Real.sqrt_nonneg _)) (Finset.sum_nonneg (fun j _ ↦ hJ _))
  refine ⟨C,hC,?_⟩
  intro a ha has A K reserve hA hK hjet c k v hv s f
  have haj : ContDiffOn ℝ ∞ (Function.uncurry (fun b x ↦ a (x,b))) (univ ×ˢ univ) :=
    (ha.comp (contDiff_snd.prodMk contDiff_fst)).contDiffOn
  have hs : ∀ b ∈ (univ : Set Par), tsupport (fun x ↦ a (x,b)) ⊆ S := by
    intro b _
    exact closure_minimal (fun x hx ↦ by by_contra h; exact hx (has (x,b) h)) hS.isClosed
  let hm := fullSource_parameterJet_memLp hS isOpen_univ haj hs k v (mem_univ c)
  have hf : ContDiff ℝ ∞ f := fullSource_parameterJet_contDiff isOpen_univ haj k v (mem_univ c)
  have hfs : tsupport f ⊆ S := by
    apply closure_minimal ?_ hS.isClosed
    intro x hx
    by_contra hxs
    have he : (fun b ↦ a (x,b)) = fun _ ↦ (0 : F) := funext fun b ↦ has (x,b) hxs
    apply hx
    dsimp only [f]
    rw [he]
    cases k <;> simp
  have hfc : HasCompactSupport f := hS.of_isClosed_subset (isClosed_tsupport _) hfs
  have hmem : MemVectorFourierSobolev (s : ℝ) (hm.toLp f) :=
    graphTest_memVectorFourierSobolev (s : ℝ) ⟨f,hf,hfc⟩
  have hsp := primary_carrier_derivative_spatial_bounds isOpen_univ isOpen_univ
    ha.contDiffOn k v hv (c := c) (mem_univ c)
  let B := (∑ j ∈ Finset.range (s+1), J (j+k)) * A * K^(s+k-reserve)
  have hB : 0 ≤ B := mul_nonneg
    (mul_nonneg (Finset.sum_nonneg (fun j _ ↦ hJ _)) hA)
    (pow_nonneg (zero_le_one.trans hK) _)
  refine ⟨hm,hmem,?_⟩
  apply (ParameterDerivatives.vectorSobolev_le_compactJets hS s f hf hfs hm hB ?_).trans_eq
    (by dsimp only [B,C]; ring)
  intro j hj x
  apply ((hsp.2 x (mem_univ x) j).trans (hjet (x,c) (j+k))).trans
  exact mul_le_mul
    (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun t _ ↦ hJ (t+k))
      (Finset.mem_range_succ_iff.mpr hj)) hA)
    (pow_le_pow_right₀ hK (Nat.sub_le_sub_right (Nat.add_le_add_right hj k) reserve))
    (pow_nonneg (zero_le_one.trans hK) _)
    (mul_nonneg (Finset.sum_nonneg (fun j _ ↦ hJ _)) hA)

end JanetCartan.PhysicalPrimary
