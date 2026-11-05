module
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Retarded.ParameterRealization.ClassicalFields
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
/-!
# Parameter derivatives commute with classical mixed jets

The parameter paragraph of `app:ch_response:thm:response-literal-transfer`
uses the actual derivatives of the envelope, with spatial and parameter orders
counted together. We prove joint smoothness, common spatial support, and the
identity with `parameterTest` for every finite parameter order.

The proof writes each spatial jet as its ordered list of full spatial
directional derivatives. Symmetry of the second differential commutes one
parameter derivative past one spatial derivative; induction gives the exact
identity for the original word. The parent `ParameterRealization` consumes this
identity to lift the classical fields through L² into the closed jet completion.
-/

@[expose] public noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace JanetCartan.ResponseTransfer.ParameterRealization
open RetardedSobolev RetardedSobolev.Spaces
variable {p d : ℕ} {U : Set (Euclidean p)}
local notation "X" => ℝ × (Fin d → ℝ)

private theorem spatial_smooth (hU : IsOpen U) {f : Euclidean p → X → ℂ}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ univ)) (w : X) :
    ContDiffOn ℝ ∞ (fun z : Euclidean p × X ↦ fderiv ℝ (f z.1) z.2 w)
      (U ×ˢ univ) := by
  intro z hz
  have hi := hf.contDiffAt ((hU.prod isOpen_univ).mem_nhds hz)
  have hh : ContDiffAt ℝ ∞
      (fun q : (Euclidean p × X) × X ↦ f q.1.1 q.2) (z, z.2) :=
    hi.comp (z, z.2) ((contDiffAt_fst.comp _ contDiffAt_fst).prodMk contDiffAt_snd)
  exact ((hh.fderiv (f := fun q : Euclidean p × X ↦ f q.1)
    (g := Prod.snd) contDiffAt_snd (m := ∞) (by simp)).clm_apply
      contDiffAt_const).contDiffWithinAt

private theorem mixed_first (hU : IsOpen U) {f : Euclidean p → X → ℂ}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ univ))
    {c : Euclidean p} (hc : c ∈ U) (x w : X) (v : Euclidean p) :
    fderiv ℝ (fun a ↦ fderiv ℝ (f a) x w) c v =
      fderiv ℝ (fun y ↦ fderiv ℝ (fun a ↦ f a y) c v) x w := by
  let F := Function.uncurry f
  have hat (a : Euclidean p) (ha : a ∈ U) (y : X) : ContDiffAt ℝ ∞ F (a, y) :=
    hf.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨ha, mem_univ y⟩)
  have hx (a : Euclidean p) (ha : a ∈ U) (y : X) :
      fderiv ℝ (f a) y w = fderiv ℝ F (a, y) (0, w) := by
    exact congrArg (fun L ↦ L w) (((hat a ha y).differentiableAt (by simp)).hasFDerivAt.comp y
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) a y)).fderiv
  have hc' (y : X) : fderiv ℝ (fun a ↦ f a y) c v = fderiv ℝ F (c, y) (v, 0) := by
    exact congrArg (fun L ↦ L v) (((hat c hc y).differentiableAt (by simp)).hasFDerivAt.comp c
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) c y)).fderiv
  have he : (fun a ↦ fderiv ℝ (f a) x w) =ᶠ[𝓝 c]
      (fun a ↦ fderiv ℝ F (a, x) (0, w)) := by
    filter_upwards [hU.mem_nhds hc] with a ha using hx a ha x
  rw [he.fderiv_eq]
  simp_rw [hc']
  have hD := ((hat c hc x).fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have h₁ := ((hD.hasFDerivAt.comp c (hasFDerivAt_prodMk_left (𝕜 := ℝ) c x)).clm_apply
    (hasFDerivAt_const (𝕜 := ℝ) ((0 : Euclidean p), w) c)).fderiv
  have h₂ := ((hD.hasFDerivAt.comp x (hasFDerivAt_prodMk_right (𝕜 := ℝ) c x)).clm_apply
    (hasFDerivAt_const (𝕜 := ℝ) (v, (0 : X)) x)).fderiv
  simp only [Function.comp_def] at h₁ h₂
  rw [h₁, h₂]
  simpa using (hat c hc x).isSymmSndFDerivAt (by simp) (v, 0) (0, w)

private theorem parameter_succ (hU : IsOpen U) {f : Euclidean p → X → ℂ}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ univ))
    (k : ℕ) (v : Fin (k + 1) → Euclidean p) {c : Euclidean p} (hc : c ∈ U) (x : X) :
    parameterField f (k + 1) v c x =
      fderiv ℝ (fun a ↦ parameterField f k (Fin.tail v) a x) c (v 0) := by
  have hat : ContDiffAt ℝ ∞ (fun a ↦ f a x) c :=
    (hf.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hc, mem_univ x⟩)).comp c
      (contDiffAt_id.prodMk contDiffAt_const)
  exact (hat.differentiableAt_iteratedFDeriv (m := k) (by
    exact_mod_cast (WithTop.coe_lt_top (a := k)))).iteratedFDeriv_succ_apply_left'

private theorem parameter_spatial (hU : IsOpen U) {f : Euclidean p → X → ℂ}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ univ))
    (w : X) (k : ℕ) (v : Fin k → Euclidean p) {c : Euclidean p} (hc : c ∈ U) (x : X) :
    parameterField (fun a y ↦ fderiv ℝ (f a) y w) k v c x =
      fderiv ℝ (parameterField f k v c) x w := by
  induction k generalizing c with
  | zero =>
    unfold parameterField
    simp only [iteratedFDeriv_zero_apply]
  | succ k ih =>
    rw [parameter_succ hU (spatial_smooth hU hf w) k v hc x]
    have he : (fun a ↦ parameterField (fun a y ↦ fderiv ℝ (f a) y w) k
        (Fin.tail v) a x) =ᶠ[𝓝 c]
        (fun a ↦ fderiv ℝ (parameterField f k (Fin.tail v) a) x w) := by
      filter_upwards [hU.mem_nhds hc] with a ha using ih (Fin.tail v) ha
    rw [he.fderiv_eq, mixed_first hU (contDiffOn_parameterField hU hf k (Fin.tail v)) hc]
    congr 2
    funext y
    exact (parameter_succ hU hf k v hc y).symm

private def spatialWord : List X → (X → ℂ) → X → ℂ
  | [], f => f
  | w :: ws, f => fun x ↦ fderiv ℝ (spatialWord ws f) x w

private theorem word_smooth (hU : IsOpen U) {f : Euclidean p → X → ℂ}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ univ)) (ws : List X) :
    ContDiffOn ℝ ∞ (fun z : Euclidean p × X ↦ spatialWord ws (f z.1) z.2)
      (U ×ˢ univ) := by
  induction ws with
  | nil => exact hf
  | cons w ws ih => exact spatial_smooth hU (f := fun a ↦ spatialWord ws (f a)) ih w

private theorem parameter_word (hU : IsOpen U) {f : Euclidean p → X → ℂ}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ univ))
    (ws : List X) (k : ℕ) (v : Fin k → Euclidean p) {c : Euclidean p} (hc : c ∈ U) :
    parameterField (fun a ↦ spatialWord ws (f a)) k v c =
      spatialWord ws (parameterField f k v c) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    funext x
    exact (parameter_spatial hU (f := fun a ↦ spatialWord ws (f a))
      (word_smooth hU hf ws) w k v hc x).trans
      (congrArg (fun g ↦ fderiv ℝ g x w) ih)

private theorem word_append (ws zs : List X) (f : X → ℂ) :
    spatialWord (ws ++ zs) f = spatialWord ws (spatialWord zs f) := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp only [List.cons_append, spatialWord, ih]

private theorem transverse_eq_word {f : X → ℂ} (hf : ContDiff ℝ ∞ f)
    (ws : List (Fin d → ℝ)) :
    transverseJet ws f = spatialWord (ws.map (fun w ↦ (0, w))) f := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    rw [transverseJet, transverseDeriv_eq_fderiv w
      ((contDiff_transverseJet hf ws).differentiable (by simp)), ih]
    rfl

private theorem time_eq_word {f : X → ℂ} (hf : ContDiff ℝ ∞ f) (j : ℕ) :
    timeJet j f = spatialWord (List.replicate j (1, 0)) f := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [timeJet_succ, timeDeriv_eq_fderiv
      ((contDiff_timeJet hf j).differentiable (by simp)), ih]
    rfl

private def jetWord {s : ℕ} (i : JetIndex d s) : List X :=
  List.replicate i.2.2.val (1, 0) ++
    (List.ofFn (fun j ↦ Pi.single (i.2.1 j) 1)).map (fun w ↦ (0, w))

private theorem jet_eq_word {s : ℕ} (i : JetIndex d s) {f : X → ℂ}
    (hf : ContDiff ℝ ∞ f) (x : (Fin d → ℝ) × ℝ) :
    jet i f x = spatialWord (jetWord i) f x.swap := by
  unfold jet jetWord
  rw [time_eq_word (contDiff_transverseJet hf _), transverse_eq_word hf, word_append]
  rfl

/-- Joint smoothness of every actual mixed spatial jet, for the parameter
paragraph of `app:ch_response:thm:response-literal-transfer`. This supplies the
classical input to the parent's L² and closed jet-completion realization. -/
theorem contDiffOn_jet {s : ℕ} (hU : IsOpen U)
    (f : Euclidean p → Test d)
    (hf : ContDiffOn ℝ ∞ (fun z ↦ (f z.1).val z.2) (U ×ˢ univ))
    (i : JetIndex d s) :
    ContDiffOn ℝ ∞ (fun z : Euclidean p × ((Fin d → ℝ) × ℝ) ↦
      jet i (f z.1).val z.2) (U ×ˢ univ) := by
  have hw := word_smooth hU (f := fun a ↦ (f a).val) hf (jetWord i)
  have hg : ContDiff ℝ ∞ (fun z : Euclidean p × ((Fin d → ℝ) × ℝ) ↦
      (z.1, z.2.swap)) :=
    contDiff_fst.prodMk ((contDiff_snd.prodMk contDiff_fst).comp contDiff_snd)
  exact (hw.comp hg.contDiffOn (fun _ hz ↦ ⟨hz.1, mem_univ _⟩)).congr
    (fun z _ ↦ jet_eq_word i (f z.1).property.1 z.2)

/-- The spatial support of every actual jet stays in the original compact set
(with the coordinate swap used by `Spaces.jet`), as required for the L² family
in `app:ch_response:thm:response-literal-transfer`. -/
theorem tsupport_jet_subset {s : ℕ} {K : Set X} (hK : IsCompact K)
    (f : Euclidean p → Test d) (hs : ∀ c ∈ U, tsupport (f c).val ⊆ K)
    (i : JetIndex d s) {c : Euclidean p} (hc : c ∈ U) :
    tsupport (jet i (f c).val) ⊆ {x | x.swap ∈ K} := by
  apply closure_minimal _ (hK.isClosed.preimage continuous_swap)
  intro x hx
  by_contra h
  exact hx (jet_eq_zero_off_tsupport i (f c).property.1 x
    (fun ht ↦ h (hs c hc ht)))

/-- Parameter differentiation commutes with the actual mixed time/transverse
jet at every finite order (`app:ch_response:thm:response-literal-transfer`).
Both sides retain the same spatial word and the same `k` parameter directions,
hence total order `i.1.val + i.2.2.val + k`;
this is the classical identity consumed by the closed jet-completion lift. -/
theorem iteratedFDeriv_jet_eq_jet_parameterTest {s : ℕ}
    (hU : IsOpen U) {K : Set X} (hK : IsCompact K)
    (f : Euclidean p → Test d)
    (hf : ContDiffOn ℝ ∞ (fun z ↦ (f z.1).val z.2) (U ×ˢ univ))
    (hs : ∀ c ∈ U, tsupport (f c).val ⊆ K)
    (i : JetIndex d s) (k : ℕ) (v : Fin k → Euclidean p)
    (c : Euclidean p) (hc : c ∈ U) (x : (Fin d → ℝ) × ℝ) :
    iteratedFDeriv ℝ k (fun a ↦ jet i (f a).val x) c v =
      jet i (parameterTest hU hK (fun a ↦ (f a).val) hf hs k v c hc).val x := by
  simp_rw [jet_eq_word i (f _).property.1]
  rw [jet_eq_word i (parameterTest hU hK (fun a ↦ (f a).val) hf hs k v c hc).property.1]
  exact congrFun (parameter_word hU hf (jetWord i) k v hc) x.swap
end JanetCartan.ResponseTransfer.ParameterRealization
