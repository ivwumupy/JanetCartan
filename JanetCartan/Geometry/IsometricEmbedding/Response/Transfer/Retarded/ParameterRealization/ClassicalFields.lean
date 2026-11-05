module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Retarded.Basic

/-!
# Classical parameter derivative fields

For the parameter paragraph of `app:ch_response:thm:response-literal-transfer`,
construct actual pointwise parameter derivatives of a jointly smooth family on
an open parameter neighborhood. Every finite derivative retains the same fixed
compact spatial support. These are the classical fields to be identified with
completed-norm derivatives in `RetardedCutoffs.demodulated_parameter_jet_profile`;
this module does not assert differentiability into the completion.
-/

@[expose] public noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace JanetCartan.ResponseTransfer.ParameterRealization
variable {p d : ℕ}

/-- Joint smoothness of the actual multilinear parameter differential, at every
finite order (`app:ch_response:thm:response-literal-transfer`). This supplies the
classical derivatives needed by the completed jet-norm parameter realization. -/
theorem contDiffOn_parameterDifferential {U : Set (Euclidean p)} (hU : IsOpen U)
    {f : Euclidean p → (ℝ × (Fin d → ℝ)) → ℂ}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ univ)) (k : ℕ) :
    ContDiffOn ℝ ∞
      (fun z : Euclidean p × (ℝ × (Fin d → ℝ)) ↦
        iteratedFDeriv ℝ k (fun c ↦ f c z.2) z.1) (U ×ˢ univ) := by
  induction k with
  | zero =>
    exact (continuousMultilinearCurryFin0 ℝ (Euclidean p) ℂ).symm.contDiff.comp_contDiffOn hf
  | succ k ih =>
    intro z hz
    have hi := ih.contDiffAt ((hU.prod isOpen_univ).mem_nhds hz)
    have hh : ContDiffAt ℝ ∞
        (fun w : (Euclidean p × (ℝ × (Fin d → ℝ))) × Euclidean p ↦
          iteratedFDeriv ℝ k (fun c ↦ f c w.1.2) w.2) (z, z.1) :=
      hi.comp (z, z.1) (contDiffAt_snd.prodMk (contDiffAt_snd.comp (z, z.1) contDiffAt_fst))
    have hd := hh.fderiv
      (f := fun (w : Euclidean p × (ℝ × (Fin d → ℝ))) c ↦
        iteratedFDeriv ℝ k (fun a ↦ f a w.2) c)
      (g := Prod.fst) (x₀ := z) contDiffAt_fst (m := ∞) (by simp)
    exact ((continuousMultilinearCurryLeftEquiv ℝ
      (fun _ : Fin (k + 1) ↦ Euclidean p) ℂ).symm.contDiff.contDiffAt.comp z hd).contDiffWithinAt

/-- The actual pointwise parameter derivative in fixed directions for
`app:ch_response:thm:response-literal-transfer`. Order zero is the original field. -/
def parameterField (f : Euclidean p → (ℝ × (Fin d → ℝ)) → ℂ)
    (k : ℕ) (v : Fin k → Euclidean p) (c : Euclidean p)
    (x : ℝ × (Fin d → ℝ)) : ℂ :=
  iteratedFDeriv ℝ k (fun a ↦ f a x) c v

/-- A common spatial support is retained by parameter differentiation on the
open parameter neighborhood (`app:ch_response:thm:response-literal-transfer`).
This uses local equality to zero, without assuming norm differentiability. -/
theorem parameterField_eq_zero_of_notMem {U : Set (Euclidean p)} (hU : IsOpen U)
    {K : Set (ℝ × (Fin d → ℝ))}
    {f : Euclidean p → (ℝ × (Fin d → ℝ)) → ℂ}
    (hs : ∀ c ∈ U, tsupport (f c) ⊆ K)
    (k : ℕ) (v : Fin k → Euclidean p) {c : Euclidean p} (hc : c ∈ U)
    {x : ℝ × (Fin d → ℝ)} (hx : x ∉ K) : parameterField f k v c x = 0 := by
  have he : (fun a ↦ f a x) =ᶠ[𝓝 c] (fun _ ↦ (0 : ℂ)) := by
    filter_upwards [hU.mem_nhds hc] with a ha
    exact image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hs a ha h))
  have hd := (he.iteratedFDeriv ℝ k).eq_of_nhds
  unfold parameterField
  rw [hd]
  cases k with
  | zero => exact iteratedFDeriv_zero_apply _
  | succ k => simp only [iteratedFDeriv_succ_const, Pi.zero_apply,
      zero_apply]

/-- The actual parameter derivative field is jointly smooth on the original
open neighborhood (`app:ch_response:thm:response-literal-transfer`). -/
theorem contDiffOn_parameterField {U : Set (Euclidean p)} (hU : IsOpen U)
    {f : Euclidean p → (ℝ × (Fin d → ℝ)) → ℂ}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ univ))
    (k : ℕ) (v : Fin k → Euclidean p) :
    ContDiffOn ℝ ∞ (Function.uncurry (parameterField f k v)) (U ×ˢ univ) :=
  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k ↦ Euclidean p) ℂ v).contDiff.comp_contDiffOn
    (contDiffOn_parameterDifferential hU hf k)

/-- Spatial smoothness of the actual parameter derivative field at each allowed
parameter (`app:ch_response:thm:response-literal-transfer`). -/
theorem contDiff_parameterField {U : Set (Euclidean p)} (hU : IsOpen U)
    {f : Euclidean p → (ℝ × (Fin d → ℝ)) → ℂ}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ univ))
    (k : ℕ) (v : Fin k → Euclidean p) {c : Euclidean p} (hc : c ∈ U) :
    ContDiff ℝ ∞ (parameterField f k v c) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  exact ((contDiffOn_parameterField hU hf k v).contDiffAt
    ((hU.prod isOpen_univ).mem_nhds ⟨hc, mem_univ x⟩)).comp x
      (contDiffAt_const.prodMk contDiffAt_id)

/-- Parameter derivatives keep the fixed closed spatial support, uniformly in
all directions and orders (`app:ch_response:thm:response-literal-transfer`). -/
theorem tsupport_parameterField_subset {U : Set (Euclidean p)} (hU : IsOpen U)
    {K : Set (ℝ × (Fin d → ℝ))} (hK : IsClosed K)
    {f : Euclidean p → (ℝ × (Fin d → ℝ)) → ℂ}
    (hs : ∀ c ∈ U, tsupport (f c) ⊆ K)
    (k : ℕ) (v : Fin k → Euclidean p) {c : Euclidean p} (hc : c ∈ U) :
    tsupport (parameterField f k v c) ⊆ K := by
  apply closure_minimal _ hK
  intro x hx
  by_contra h
  exact hx (parameterField_eq_zero_of_notMem hU hs k v hc h)

/-- Compact support of each actual parameter derivative, used to construct the
`Test d` representative (`app:ch_response:thm:response-literal-transfer`). -/
theorem hasCompactSupport_parameterField {U : Set (Euclidean p)} (hU : IsOpen U)
    {K : Set (ℝ × (Fin d → ℝ))} (hK : IsCompact K)
    {f : Euclidean p → (ℝ × (Fin d → ℝ)) → ℂ}
    (hs : ∀ c ∈ U, tsupport (f c) ⊆ K)
    (k : ℕ) (v : Fin k → Euclidean p) {c : Euclidean p} (hc : c ∈ U) :
    HasCompactSupport (parameterField f k v c) :=
  hK.of_isClosed_subset (isClosed_tsupport _) (tsupport_parameterField_subset hU hK.isClosed hs k v hc)

/-- The actual pointwise parameter derivative as a smooth compactly supported
field (`app:ch_response:thm:response-literal-transfer`). The hypotheses are solely
classical joint smoothness and a common compact support on an open neighborhood. -/
def parameterTest {U : Set (Euclidean p)} (hU : IsOpen U)
    {K : Set (ℝ × (Fin d → ℝ))} (hK : IsCompact K)
    (f : Euclidean p → (ℝ × (Fin d → ℝ)) → ℂ)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ univ))
    (hs : ∀ c ∈ U, tsupport (f c) ⊆ K)
    (k : ℕ) (v : Fin k → Euclidean p) (c : Euclidean p) (hc : c ∈ U) :
    RetardedSobolev.Spaces.Test d :=
  ⟨parameterField f k v c, contDiff_parameterField hU hf k v hc,
    hasCompactSupport_parameterField hU hK hs k v hc⟩

/-- The constructed test field evaluates to the actual classical derivative
(`app:ch_response:thm:response-literal-transfer`). -/
@[simp] theorem parameterTest_apply {U : Set (Euclidean p)} (hU : IsOpen U)
    {K : Set (ℝ × (Fin d → ℝ))} (hK : IsCompact K)
    (f : Euclidean p → (ℝ × (Fin d → ℝ)) → ℂ)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ univ))
    (hs : ∀ c ∈ U, tsupport (f c) ⊆ K)
    (k : ℕ) (v : Fin k → Euclidean p) (c : Euclidean p) (hc : c ∈ U)
    (x : ℝ × (Fin d → ℝ)) :
    (parameterTest hU hK f hf hs k v c hc).val x =
      iteratedFDeriv ℝ k (fun a ↦ f a x) c v := rfl

/-- The order-zero representative is the original test field, so the realization
also covers `k = 0` (`app:ch_response:thm:response-literal-transfer`). -/
@[simp] theorem parameterTest_zero {U : Set (Euclidean p)} (hU : IsOpen U)
    {K : Set (ℝ × (Fin d → ℝ))} (hK : IsCompact K)
    (f : Euclidean p → RetardedSobolev.Spaces.Test d)
    (hf : ContDiffOn ℝ ∞ (fun z ↦ (f z.1).val z.2) (U ×ˢ univ))
    (hs : ∀ c ∈ U, tsupport (f c).val ⊆ K)
    (v : Fin 0 → Euclidean p) (c : Euclidean p) (hc : c ∈ U) :
    parameterTest hU hK (fun a ↦ (f a).val) hf hs 0 v c hc = f c := by
  apply Subtype.ext
  funext x
  exact iteratedFDeriv_zero_apply v

end JanetCartan.ResponseTransfer.ParameterRealization
