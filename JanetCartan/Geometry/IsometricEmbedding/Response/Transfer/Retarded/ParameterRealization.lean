module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Retarded.JetBounds
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Retarded.ParameterRealization.L2Family
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Retarded.ParameterRealization.JetCommutation
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Topology.Algebra.Module.Equiv.Submodule

/-!
# Classical parameter families in the retarded jet completion

For the parameter paragraph of `app:ch_response:thm:response-literal-transfer`,
classical joint smoothness and one fixed compact spatial support imply
smoothness in the actual Lebesgue Sobolev jet completion at every finite order.
The evaluated derivative is the inclusion of the actual pointwise parameter
derivative field, with its smoothness and compact support supplied by
`ClassicalFields`. No differentiability in a completed norm is assumed.

The final corollary discharges the smoothness premise of
`RetardedCutoffs.demodulated_parameter_jet_profile` on any parameter box inside
the open neighborhood. Its quantitative input bounds are independent of this
realization; no comparison with the local Sobolev scale is asserted here.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace JanetCartan.ResponseTransfer.ParameterRealization
open RetardedSobolev.Spaces

/-- A finite product of L² spaces admits a continuous linear retraction onto
the closed jet subspace. This auxiliary Hilbert product is used only to lift
smoothness; the target retains the original Sobolev norm. -/
private theorem contDiffAt_sobolev_of_coe {p d s k : ℕ} {F : Euclidean p → Sobolev s
    (volume : Measure ((Fin d → ℝ) × ℝ))} {c : Euclidean p}
    (hF : ContDiffAt ℝ k (fun a ↦ (F a).val) c) : ContDiffAt ℝ k F c := by
  let J := JetIndex d s → Lp ℂ 2 (volume : Measure ((Fin d → ℝ) × ℝ))
  let H := PiLp 2 (fun _ : JetIndex d s ↦
    Lp ℂ 2 (volume : Measure ((Fin d → ℝ) × ℝ)))
  let e : J ≃L[ℂ] H := (PiLp.continuousLinearEquiv 2 ℂ _).symm
  let S := sobolevSubmodule s (volume : Measure ((Fin d → ℝ) × ℝ))
  let T := S.map e.toLinearEquiv.toLinearMap
  have hT : IsClosed (T : Set H) := by
    rw [show (T : Set H) = e '' (S : Set J) from Submodule.map_coe _ _]
    exact e.toHomeomorph.isClosedMap _ (Submodule.isClosed_topologicalClosure _)
  let : IsClosed (T : Set H) := hT
  let : CompleteSpace T := IsClosed.completeSpace_coe
  let r : J →L[ℂ] Sobolev s volume :=
    (e.submoduleMap S).symm.toContinuousLinearMap.comp
      (T.orthogonalProjectionOnto.comp e.toContinuousLinearMap)
  have hr (a : Euclidean p) : r (F a).val = F a := by
    change (e.submoduleMap S).symm (T.orthogonalProjectionOnto
      ((e.submoduleMap S (F a) : T) : PiLp 2 _)) = _
    rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
    exact (e.submoduleMap S).symm_apply_apply _
  have hh := (r.restrictScalars ℝ).contDiff.contDiffAt.comp c hF
  change ContDiffAt ℝ k (fun a ↦ r (F a).val) c at hh
  simpa only [hr] using hh

/-- Classical joint smoothness and one fixed compact support imply smoothness
in the actual completed jet norm, at every finite parameter order
(`app:ch_response:thm:response-literal-transfer`). This supplies the smoothness
premise of `RetardedCutoffs.demodulated_parameter_jet_profile`. -/
theorem contDiffAt_ofTest_of_commonCompactSupport
    {p d : ℕ} {U : Set (Euclidean p)} (hU : IsOpen U)
    {K : Set (ℝ × (Fin d → ℝ))} (hK : IsCompact K)
    (f : Euclidean p → Test d)
    (hf : ContDiffOn ℝ ∞ (fun z ↦ (f z.1).val z.2) (U ×ˢ univ))
    (hs : ∀ c ∈ U, tsupport (f c).val ⊆ K)
    (s k : ℕ) {c : Euclidean p} (hc : c ∈ U) :
    ContDiffAt ℝ k (fun a ↦ ofTest s volume (f a)) c := by
  apply contDiffAt_sobolev_of_coe
  apply contDiffAt_pi.mpr
  intro i
  exact contDiffAt_toLp_of_contDiffOn_commonCompactSupport (g := fun a ↦ jet i (f a).val) hU
    ((Homeomorph.prodComm _ _).isCompact_preimage.mpr hK)
    (contDiffOn_jet hU f hf i) (fun a ha ↦ tsupport_jet_subset hK f hs i ha)
    (fun a ↦ jet_memLp volume i (f a)) k hc

/-- Every evaluated parameter derivative in the completed jet norm is the
canonical inclusion of its actual smooth compactly supported pointwise
parameter derivative (`app:ch_response:thm:response-literal-transfer`). The
spatial order `s` and parameter order `k` are unchanged. -/
theorem iteratedFDeriv_ofTest_eq_ofTest_parameterTest
    {p d : ℕ} {U : Set (Euclidean p)} (hU : IsOpen U)
    {K : Set (ℝ × (Fin d → ℝ))} (hK : IsCompact K)
    (f : Euclidean p → Test d)
    (hf : ContDiffOn ℝ ∞ (fun z ↦ (f z.1).val z.2) (U ×ˢ univ))
    (hs : ∀ c ∈ U, tsupport (f c).val ⊆ K)
    (s k : ℕ) (v : Fin k → Euclidean p) (c : Euclidean p) (hc : c ∈ U) :
    iteratedFDeriv ℝ k (fun a ↦ ofTest s volume (f a)) c v =
      ofTest s volume (parameterTest hU hK (fun a ↦ (f a).val) hf hs k v c hc) := by
  apply Subtype.ext
  funext i
  let ev : Sobolev s (volume : Measure ((Fin d → ℝ) × ℝ)) →L[ℝ]
      Lp ℂ 2 volume :=
    (ContinuousLinearMap.proj i).comp
      ((sobolevSubmodule s volume).subtypeL.restrictScalars ℝ)
  have he := congrArg (fun m ↦ m v) (ev.iteratedFDeriv_comp_left
    (contDiffAt_ofTest_of_commonCompactSupport hU hK f hf hs s k hc) le_rfl)
  change iteratedFDeriv ℝ k (fun a ↦ (jet_memLp volume i (f a)).toLp
    (jet i (f a).val)) c v =
    (iteratedFDeriv ℝ k (fun a ↦ ofTest s volume (f a)) c v).val i at he
  rw [← he]
  rw [iteratedFDeriv_toLp_eq_toLp_parameterDeriv (g := fun a ↦ jet i (f a).val) hU
    ((Homeomorph.prodComm _ _).isCompact_preimage.mpr hK)
    (contDiffOn_jet hU f hf i) (fun a ha ↦ tsupport_jet_subset hK f hs i ha)
    (fun a ↦ jet_memLp volume i (f a)) k v hc]
  apply MemLp.toLp_congr _ (jet_memLp volume i
    (parameterTest hU hK (fun a ↦ (f a).val) hf hs k v c hc))
  exact Filter.Eventually.of_forall
    (iteratedFDeriv_jet_eq_jet_parameterTest hU hK f hf hs i k v c hc)

end JanetCartan.ResponseTransfer.ParameterRealization

namespace JanetCartan.ResponseTransfer.RetardedCutoffs
open RetardedSobolev.Spaces

/-- The parameter profile for the fixed literal retarded factors follows from
classical joint smoothness and common compact support, without assuming
smoothness in a completed norm
(`app:ch_response:thm:response-literal-transfer`). The set `B` may be any fixed
compact parameter box inside `U`. Quantitative input bounds are the separate
norm-comparison obligation; total grade remains `s + k`. -/
theorem demodulated_parameter_jet_profile_of_classical
    {d p : ℕ} (W : RetardedCutoffs d) {ι : Type*}
    {U : Set (Euclidean p)} (hU : IsOpen U)
    {S : Set (ℝ × (Fin d → ℝ))} (hS : IsCompact S)
    (q : ℕ) (B : Set (Euclidean p)) (hB : B ⊆ U)
    (f : ι → Euclidean p → Test d)
    (hsmooth : ∀ i, ContDiffOn ℝ ∞ (fun z ↦ (f i z.1).val z.2) (U ×ˢ univ))
    (hsupport : ∀ i c, c ∈ U → tsupport (f i c).val ⊆ S)
    (ρ : ι → ℝ) (ζ : Euclidean p → Euclidean d) (A K : ι → ℝ)
    (hf : ∀ s k, k ≤ q → ∃ C : ℝ, 0 ≤ C ∧ ∀ i c, c ∈ B →
      ‖iteratedFDeriv ℝ k (fun c ↦ ofTest s volume (f i c)) c‖ ≤
        C * A i * K i ^ (s + k)) :
    ∀ s k, k ≤ q → ∃ C : ℝ, 0 ≤ C ∧ ∀ i c, c ∈ B →
      ‖iteratedFDeriv ℝ k
        (fun c ↦ ofTest s volume (W.demodulatedLower (ρ i) (ζ c) (f i c))) c‖ ≤
          C * A i * K i ^ (s + k) ∧
      ‖iteratedFDeriv ℝ k
        (fun c ↦ ofTest s volume (W.demodulatedUpper (ρ i) (ζ c) (f i c))) c‖ ≤
          C * A i * K i ^ (s + k) := by
  exact W.demodulated_parameter_jet_profile q B f ρ ζ A K
    (fun s i c hc ↦ ParameterRealization.contDiffAt_ofTest_of_commonCompactSupport
      hU hS (f i) (hsmooth i) (hsupport i) s q (hB hc)) hf

end JanetCartan.ResponseTransfer.RetardedCutoffs
