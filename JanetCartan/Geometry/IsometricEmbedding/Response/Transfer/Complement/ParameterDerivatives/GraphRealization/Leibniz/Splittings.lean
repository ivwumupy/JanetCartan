module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ParameterDerivatives.GraphRealization.Compact
public import Mathlib.Data.List.OfFn

/-!
# Finite direction splittings for the complementary kernel

The combinatorial Leibniz rule consumed by `iteratedFDeriv_parameterGraphIntegrand_leibniz`
in the final parameter paragraph of `app:ch_response:thm:response-literal-transfer`.
The recursion splits directions, not derivatives of the graph output.
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology ContDiff

namespace JanetCartan.ResponseTransfer.Complement.ParameterDerivatives

variable {P F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- All ordered choices of which directions differentiate the kernel and which
differentiate the original source. Multiplicities are retained, as required by
`app:ch_response:thm:response-literal-transfer`. -/
def parameterLeibnizSplittings : List P → List (List P × List P)
  | [] => [([], [])]
  | v :: vs =>
    (parameterLeibnizSplittings vs).map (fun s ↦ (v :: s.1, s.2)) ++
      (parameterLeibnizSplittings vs).map (fun s ↦ (s.1, v :: s.2))

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
/-- Every term uses exactly the original total derivative order
(`app:ch_response:thm:response-literal-transfer`). -/
theorem parameterLeibnizSplittings_orders {vs : List P} {s : List P × List P}
    (hs : s ∈ parameterLeibnizSplittings vs) : s.1.length + s.2.length = vs.length := by
  induction vs generalizing s with
  | nil =>
    simp only [parameterLeibnizSplittings, List.mem_singleton] at hs
    subst s
    rfl
  | cons v vs ih =>
    simp only [parameterLeibnizSplittings, List.mem_append, List.mem_map] at hs
    rcases hs with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩ <;>
      simp only [List.length_cons] <;> have := ih ht <;> omega

/-- The actual Fréchet jet evaluated on a list of arbitrary directions. This
notation is used only to state the finite kernel/source expansion from
`app:ch_response:thm:response-literal-transfer`. -/
def parameterListJet (f : P → F) (vs : List P) (c : P) : F :=
  iteratedFDeriv ℝ vs.length f c vs.get

/-- List notation preserves arbitrary ordered Fréchet directions exactly
(`app:ch_response:thm:response-literal-transfer`). -/
theorem parameterListJet_ofFn (f : P → F) (k : ℕ) (v : Fin k → P) (c : P) :
    parameterListJet f (List.ofFn v) c = iteratedFDeriv ℝ k f c v := by
  unfold parameterListJet
  generalize hd : List.ofFn v = vs
  have hlen : vs.length = k := hd ▸ List.length_ofFn
  subst k
  congr 1
  apply List.ofFn_injective
  rw [List.ofFn_get]
  exact hd.symm

private theorem parameterListJet_cons (f : P → F) (v : P) (vs : List P) {c : P}
    (hf : ContDiffAt ℝ ∞ f c) :
    parameterListJet f (v :: vs) c =
      fderiv ℝ (parameterListJet f vs) c v := by
  have hd := hf.differentiableAt_iteratedFDeriv (m := vs.length) (ENat.natCast_lt_of_coe_top_le_withTop le_rfl _)
  have ht : Fin.tail (v :: vs).get = vs.get := by
    funext i
    change (v :: vs).get i.succ = vs.get i
    exact List.get_cons_succ
  change iteratedFDeriv ℝ (vs.length + 1) f c (v :: vs).get =
    fderiv ℝ (fun b ↦ iteratedFDeriv ℝ vs.length f b vs.get) c v
  simpa only [ht, List.get_cons_zero] using
    hd.iteratedFDeriv_succ_apply_left' (m := (v :: vs).get)

private theorem differentiableAt_parameterListJet (f : P → F) (vs : List P) {c : P}
    (hf : ContDiffAt ℝ ∞ f c) : DifferentiableAt ℝ (parameterListJet f vs) c :=
  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin vs.length ↦ P) F vs.get).differentiableAt.comp c
    (hf.differentiableAt_iteratedFDeriv (ENat.natCast_lt_of_coe_top_le_withTop le_rfl _))

private theorem differentiableAt_list_sum {ι : Type*} (l : List ι) (f : ι → P → F) {c : P}
    (hf : ∀ i ∈ l, DifferentiableAt ℝ (f i) c) :
    DifferentiableAt ℝ (fun b ↦ (l.map (fun i ↦ f i b)).sum) c := by
  induction l with
  | nil => simp
  | cons i l ih =>
    exact (hf i (by simp)).add (ih (fun j hj ↦ hf j (by simp [hj])))

private theorem fderiv_list_sum {ι : Type*} (l : List ι) (f : ι → P → F) {c : P}
    (hf : ∀ i ∈ l, DifferentiableAt ℝ (f i) c) (v : P) :
    fderiv ℝ (fun b ↦ (l.map (fun i ↦ f i b)).sum) c v =
      (l.map (fun i ↦ fderiv ℝ (f i) c v)).sum := by
  induction l with
  | nil => simp
  | cons i l ih =>
    have hsum := differentiableAt_list_sum l f (fun j hj ↦ hf j (by simp [hj]))
    simp only [List.map_cons, List.sum_cons]
    rw [fderiv_fun_add (hf i (by simp)) hsum, add_apply,
      ih (fun j hj ↦ hf j (by simp [hj]))]

variable [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]

/-- A checked finite Leibniz rule for the scalar kernel coefficient and
vector source. Each summand consists of actual jets of the two original
factors (`app:ch_response:thm:response-literal-transfer`). -/
theorem parameterListJet_smul (f : P → ℂ) (g : P → F) {U : Set P}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (vs : List P) {c : P} (hc : c ∈ U) :
    parameterListJet (fun b ↦ f b • g b) vs c =
      ((parameterLeibnizSplittings vs).map (fun s ↦
        parameterListJet f s.1 c • parameterListJet g s.2 c)).sum := by
  induction vs generalizing c with
  | nil => simp [parameterListJet, parameterLeibnizSplittings]
  | cons v vs ih =>
    have hf' := hf.contDiffAt (hU.mem_nhds hc)
    have hg' := hg.contDiffAt (hU.mem_nhds hc)
    rw [parameterListJet_cons (fun b ↦ f b • g b) _ _ (hf'.smul hg')]
    have he : parameterListJet (fun b ↦ f b • g b) vs =ᶠ[𝓝 c]
        fun b ↦ ((parameterLeibnizSplittings vs).map (fun s ↦
          parameterListJet f s.1 b • parameterListJet g s.2 b)).sum :=
      Filter.mem_of_superset (hU.mem_nhds hc) fun b hb ↦ ih hb
    rw [he.fderiv_eq, fderiv_list_sum _ _ (fun s _ ↦
      (differentiableAt_parameterListJet f s.1 hf').smul
        (differentiableAt_parameterListJet g s.2 hg'))]
    simp only [parameterLeibnizSplittings, List.map_append, List.sum_append, List.map_map,
      Function.comp_def]
    rw [← List.sum_map_add]
    apply congrArg List.sum
    apply List.map_congr_left
    intro s _
    rw [fderiv_fun_smul (differentiableAt_parameterListJet f s.1 hf')
      (differentiableAt_parameterListJet g s.2 hg')]
    simp only [add_apply, ContinuousLinearMap.smulRight_apply,
      smul_apply, parameterListJet_cons _ _ _ hf',
      parameterListJet_cons _ _ _ hg']
    exact add_comm _ _

end JanetCartan.ResponseTransfer.Complement.ParameterDerivatives
