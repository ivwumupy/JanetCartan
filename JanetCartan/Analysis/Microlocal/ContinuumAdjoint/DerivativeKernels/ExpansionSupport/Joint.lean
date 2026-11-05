module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.Expansion
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.Iteration
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.SymbolBounds.RescaledSymbols
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.LowBounds

/-!
# Joint smoothness and support of the actual expansion

For `app:ch_background:prop:bg-adjoint`, the consumer is the primitive
regularity and support input of `exists_modifiedAdjoint_L2_bound` for each
term of `adjointDerivativeExpansion`. Support is contained in the original
joint **topological** support, including in the carrier and frequency variables.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff
namespace JanetCartan.ContinuumAdjoint.DerivativeKernels
open ContinuumRow NormalComparison ModifiedNormalSymbol
variable {n : ℕ}

private theorem contDiff_joint_measurement_partial {a : AdjointAmplitude n}
    (ha : ContDiff ℝ ∞ (fun p : AmplitudeVariables n ↦ a p.1 p.2.1 p.2.2))
    (j : Fin n) : ContDiff ℝ ∞ (fun p : AmplitudeVariables n ↦
      partialDeriv (fun y ↦ a p.1 y p.2.2) p.2.1 j) := by
  exact (ha.comp (contDiff_fst.fst.prodMk
    (contDiff_snd.prodMk contDiff_fst.snd.snd))).fderiv_apply
    contDiff_snd.fst contDiff_const (by simp)

/-- Full joint smoothness survives the zero branch of
`app:ch_background:eq:bg-derivative-trade`, including frequency derivatives. -/
theorem contDiff_zeroBranchAmplitude {a : AdjointAmplitude n}
    (ha : ContDiff ℝ ∞ (fun p : AmplitudeVariables n ↦ a p.1 p.2.1 p.2.2))
    {L : CarrierParameter → Euclidean n → Euclidean (n - 1) → Euclidean n}
    {V : CarrierParameter → Euclidean n → CarrierParameter → Euclidean n}
    (hL : ∀ h, ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean n ↦ L p.1 p.2 h))
    (hV : ∀ h, ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean n ↦ V p.1 p.2 h))
    (d : InitialCarrierDerivative n) : ContDiff ℝ ∞ (fun p : AmplitudeVariables n ↦
      zeroBranchAmplitude L V d a p.1 p.2.1 p.2.2) := by
  have hs (W : CarrierParameter → Euclidean n → Euclidean n)
      (hW : ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean n ↦ W p.1 p.2)) (j) :
      ContDiff ℝ ∞ (fun p : AmplitudeVariables n ↦
        partialDeriv (fun y ↦ W p.1 y j • a p.1 y p.2.2) p.2.1 j) :=
    contDiff_joint_measurement_partial (a := fun z x η ↦ W z x j • a z x η)
      (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n ↦ ℝ) j).contDiff.comp
        (hW.comp (contDiff_fst.prodMk contDiff_snd.fst))).smul ha) j
  cases d with
  | initial h => exact ContDiff.sum (s := Finset.univ) (fun j _ ↦ hs (fun z x ↦ L z x h) (hL h) j)
  | carrier h =>
    apply ContDiff.sub
    · exact (ha.comp (contDiff_snd.prodMk contDiff_fst.snd)).fderiv_apply
        contDiff_fst contDiff_const (by simp)
    · exact ContDiff.sum (s := Finset.univ) (fun j _ ↦ hs (fun z x ↦ V z x h) (hV h) j)

/-- Full joint smoothness survives the first branch of
`app:ch_background:eq:bg-derivative-trade`. -/
theorem contDiff_firstBranchAmplitude {a : AdjointAmplitude n}
    (ha : ContDiff ℝ ∞ (fun p : AmplitudeVariables n ↦ a p.1 p.2.1 p.2.2))
    {L : CarrierParameter → Euclidean n → Euclidean (n - 1) → Euclidean n}
    {V : CarrierParameter → Euclidean n → CarrierParameter → Euclidean n}
    (hL : ∀ h, ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean n ↦ L p.1 p.2 h))
    (hV : ∀ h, ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean n ↦ V p.1 p.2 h))
    (d : InitialCarrierDerivative n) (j : Fin n) : ContDiff ℝ ∞
      (fun p : AmplitudeVariables n ↦ firstBranchAmplitude L V d a j p.1 p.2.1 p.2.2) := by
  cases d with
  | initial h => exact ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n ↦ ℝ) j).contDiff.comp
      ((hL h).comp (contDiff_fst.prodMk contDiff_snd.fst))).smul ha
  | carrier h => exact (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n ↦ ℝ) j).contDiff.comp
      ((hV h).comp (contDiff_fst.prodMk contDiff_snd.fst))).smul ha).neg

/-- The zero branch stays in the original joint topological support
(`app:ch_background:prop:bg-adjoint`). No nonvanishing of the original
amplitude at a point of the differentiated support is asserted. -/
theorem tsupport_zeroBranchAmplitude_subset (L V) (d : InitialCarrierDerivative n)
    (a : AdjointAmplitude n) :
    tsupport (fun p : AmplitudeVariables n ↦ zeroBranchAmplitude L V d a p.1 p.2.1 p.2.2) ⊆
      tsupport (fun p : AmplitudeVariables n ↦ a p.1 p.2.1 p.2.2) := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro p hp
  by_contra hn
  have hx : p.2.1 ∉ tsupport (fun y ↦ a p.1 y p.2.2) :=
    fun hx ↦ hn (tsupport_comp_subset_preimage
      (fun p : AmplitudeVariables n ↦ a p.1 p.2.1 p.2.2)
      (continuous_const.prodMk (continuous_id.prodMk continuous_const)) hx)
  have hz : p.1 ∉ tsupport (fun z ↦ a z p.2.1 p.2.2) :=
    fun hz ↦ hn (tsupport_comp_subset_preimage
      (fun p : AmplitudeVariables n ↦ a p.1 p.2.1 p.2.2)
      (continuous_id.prodMk continuous_const) hz)
  have hzero (W : Euclidean n → Euclidean n) (j : Fin n) :
      partialDeriv (fun y ↦ W y j • a p.1 y p.2.2) p.2.1 j = 0 := by
    unfold partialDeriv
    rw [fderiv_of_notMem_tsupport (𝕜 := ℝ)
      (fun hm ↦ hx (tsupport_smul_subset_right _ _ hm))]
    rfl
  apply hp
  cases d with
  | initial h => exact Finset.sum_eq_zero (s := Finset.univ) (fun j _ ↦ hzero (fun y ↦ L p.1 y h) j)
  | carrier h =>
    simp only [zeroBranchAmplitude, carrierZeroAmplitude, transportCoefficient,
      fderiv_of_notMem_tsupport (𝕜 := ℝ) hz]
    rw [Finset.sum_eq_zero (fun j _ ↦ hzero (fun y ↦ V p.1 y h) j)]
    simp

/-- The first branch preserves the original joint topological support
(`app:ch_background:prop:bg-adjoint`). -/
theorem tsupport_firstBranchAmplitude_subset (L V) (d : InitialCarrierDerivative n)
    (a : AdjointAmplitude n) (j : Fin n) :
    tsupport (fun p : AmplitudeVariables n ↦ firstBranchAmplitude L V d a j p.1 p.2.1 p.2.2) ⊆
      tsupport (fun p : AmplitudeVariables n ↦ a p.1 p.2.1 p.2.2) := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro p hp
  apply subset_tsupport _
  intro hz
  apply hp
  cases d <;> simp [firstBranchAmplitude, initialFirstAmplitude, carrierFirstAmplitude, hz]

/-- Every actual generated amplitude is smooth jointly in all variables,
from the original full amplitude and eta-independent smooth fields
(`app:ch_background:prop:bg-adjoint`). -/
theorem contDiff_adjointDerivativeExpansion {a : AdjointAmplitude n}
    (ha : ContDiff ℝ ∞ (fun p : AmplitudeVariables n ↦ a p.1 p.2.1 p.2.2))
    {L : CarrierParameter → Euclidean n → Euclidean (n - 1) → Euclidean n}
    {V : CarrierParameter → Euclidean n → CarrierParameter → Euclidean n}
    (hL : ∀ h, ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean n ↦ L p.1 p.2 h))
    (hV : ∀ h, ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean n ↦ V p.1 p.2 h))
    (ds : List (InitialCarrierDerivative n)) (t : AdjointDerivativeTerm n)
    (ht : t ∈ adjointDerivativeExpansion L V ds a) :
    ContDiff ℝ ∞ (fun p : AmplitudeVariables n ↦ t.amplitude p.1 p.2.1 p.2.2) := by
  induction ds generalizing t with
  | nil =>
    simp only [adjointDerivativeExpansion, List.mem_singleton] at ht
    subst t
    exact ha
  | cons d ds ih =>
    obtain ⟨q, hq, ht⟩ := List.mem_flatMap.mp ht
    simp only [differentiateAdjointTerm, List.mem_cons, List.mem_ofFn] at ht
    rcases ht with rfl | ⟨j, rfl⟩
    · exact contDiff_zeroBranchAmplitude (ih q hq) hL hV d
    · exact contDiff_firstBranchAmplitude (ih q hq) hL hV d j

/-- All generated amplitudes retain the original joint topological support,
hence every closed carrier, measurement and frequency buffer, in
`app:ch_background:prop:bg-adjoint`. This support result needs no smoothness. -/
theorem tsupport_adjointDerivativeExpansion_subset (L V)
    (ds : List (InitialCarrierDerivative n)) (a : AdjointAmplitude n)
    (t : AdjointDerivativeTerm n) (ht : t ∈ adjointDerivativeExpansion L V ds a) :
    tsupport (fun p : AmplitudeVariables n ↦ t.amplitude p.1 p.2.1 p.2.2) ⊆
      tsupport (fun p : AmplitudeVariables n ↦ a p.1 p.2.1 p.2.2) := by
  induction ds generalizing t with
  | nil =>
    simp only [adjointDerivativeExpansion, List.mem_singleton] at ht
    subst t
    exact Subset.rfl
  | cons d ds ih =>
    obtain ⟨q, hq, ht⟩ := List.mem_flatMap.mp ht
    simp only [differentiateAdjointTerm, List.mem_cons, List.mem_ofFn] at ht
    rcases ht with rfl | ⟨j, rfl⟩
    · exact (tsupport_zeroBranchAmplitude_subset L V d q.amplitude).trans (ih q hq)
    · exact (tsupport_firstBranchAmplitude_subset L V d q.amplitude j).trans (ih q hq)

/-- Reassociation of product variables is an isometry, so the mixed symbol
reserve transfers with constant one to `scaledOriginalAmplitude`, the input
of `PrimitiveAmplitudeReserve.mixed_jets` in `app:ch_background:prop:bg-adjoint`.
No smoothness premise is needed for this exact norm identity. -/
theorem norm_iteratedFDeriv_scaledOriginalAmplitude (a : AdjointAmplitude n)
    (r : ℝ) (j : ℕ) (p : AmplitudeVariables n) :
    ‖iteratedFDeriv ℝ j (scaledOriginalAmplitude a r) p‖ =
      ‖iteratedFDeriv ℝ j (fun q : AdjointSymbolPoint n ↦
        a q.1.1 q.1.2 (r • q.2)) ((p.1, p.2.1), p.2.2)‖ := by
  exact (LinearIsometryEquiv.prodAssoc ℝ CarrierParameter (Euclidean n)
    (Euclidean (n - 1))).symm.norm_iteratedFDeriv_comp_right
      (fun q : AdjointSymbolPoint n ↦ a q.1.1 q.1.2 (r • q.2)) p j

end JanetCartan.ContinuumAdjoint.DerivativeKernels
