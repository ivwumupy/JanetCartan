module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.IntegratedEnvelope.Assembly.Words
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ParameterDerivatives.GraphRealization.Leibniz.Splittings
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Cartesian words of the full source jet

For `app:ch_response:eq:direct-envelope-profile` the independent covector gives
a third Cartesian block, in addition to position and label. The norm on the two
parameter blocks is the product norm. Expand in their product basis, and commute
only derivatives of the smooth original datum to put the spatial derivatives
outside. This is used by `exists_fullSource_mixedL2_profile`.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff
namespace JanetCartan.ResponseTransfer.FullSourceEnvelopes
open Pseudodifferential DirectEvolution.IntegratedEnvelope
open Complement.ParameterDerivatives

variable {n d r : ℕ}
local notation "E" => Euclidean n
local notation "P" => Euclidean 3 × Euclidean d
local notation "F" => EuclideanSpace ℂ (Fin r)
local notation "Indices" => Fin n ⊕ (Fin 3 ⊕ Fin d)

variable (d) in
/-- Product basis of the two independent source blocks in
`app:ch_response:thm:response-literal-transfer`. -/
def fullSourceParameterBasis : Module.Basis (Fin 3 ⊕ Fin d) ℝ P :=
  (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.prod (EuclideanSpace.basisFun (Fin d) ℝ).toBasis

variable (n d) in
/-- Physical space times the original source parameter basis, in
`app:ch_response:eq:direct-envelope-profile`. -/
def fullSourceMixedBasis : Module.Basis Indices ℝ (E × P) :=
  (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.prod (fullSourceParameterBasis d)

/-- A Euclidean coordinate is bounded by the block norm
(`app:ch_response:eq:direct-envelope-profile`). -/
private theorem basis_coordinate_le {m : ℕ} (x : Euclidean m) (i : Fin m) :
    ‖(EuclideanSpace.basisFun (Fin m) ℝ).toBasis.repr x i‖ ≤ ‖x‖ := by
  rw [OrthonormalBasis.coe_toBasis_repr_apply]
  exact (PiLp.norm_apply_le _ i).trans_eq (LinearIsometryEquiv.norm_map _ _)

/-- Each of the three Cartesian blocks is contractive for the actual product norm
(`app:ch_response:eq:direct-envelope-profile`). -/
private theorem mixed_coordinate_le (x : E × P) (i : Indices) :
    ‖(fullSourceMixedBasis n d).repr x i‖ ≤ ‖x‖ := by
  rcases i with i | i | i
  · exact (basis_coordinate_le x.1 i).trans (norm_fst_le x)
  · exact (basis_coordinate_le x.2.1 i).trans ((norm_fst_le x.2).trans (norm_snd_le x))
  · exact (basis_coordinate_le x.2.2 i).trans ((norm_snd_le x.2).trans (norm_snd_le x))

/-- The exact product-norm tensor is bounded by its finite Cartesian evaluations;
there is no pointwise estimate on the source in `app:ch_response:eq:direct-envelope-profile`. -/
theorem norm_fullSource_mixedTensor_le_sum {j : ℕ} (T : (E × P) [×j]→L[ℝ] F) :
    ‖T‖ ≤ ∑ v : Fin j → Indices, ‖T (fun k ↦ fullSourceMixedBasis n d (v k))‖ := by
  classical
  let b := fullSourceMixedBasis n d
  apply T.opNorm_le_bound (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
  intro u
  have hu : u = fun k ↦ ∑ i, b.repr (u k) i • b i := funext fun k ↦ (b.sum_repr (u k)).symm
  calc
    ‖T u‖ = ‖∑ a : Fin j → Indices, (∏ k, b.repr (u k) (a k)) • T (fun k ↦ b (a k))‖ := by
      conv_lhs => rw [hu, T.map_sum]
      simp only [T.map_smul_univ]
    _ ≤ _ := (norm_sum_le _ _).trans (by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro a _
      rw [norm_smul, norm_prod, mul_comm]
      exact mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
        (fun k _ ↦ mixed_coordinate_le (u k) (a k))) (norm_nonneg _))

section Word
variable {X Y Z : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- The ordered parameter action specialized to directional differentiation
(`app:ch_response:eq:direct-envelope-profile`). -/
private abbrev word (vs : List X) (f : X → Y) := orderedTransferAction (fun v g x ↦ fderiv ℝ g x v) vs f

/-- Each intermediate directional derivative of the original smooth datum is smooth
(`app:ch_response:eq:direct-envelope-profile`). -/
private theorem word_smooth {f : X → Y} (hf : ContDiff ℝ ∞ f) (vs : List X) :
    ContDiff ℝ ∞ (word vs f) :=
  contDiffOn_univ.mp (Parameter.contDiffOn_orderedParameterWord isOpen_univ hf.contDiffOn vs)

/-- Schwarz symmetry permits sorting the mixed directions of the original datum
(`app:ch_response:eq:direct-envelope-profile`). -/
private theorem word_perm {f : X → Y} (hf : ContDiff ℝ ∞ f) {vs ws : List X}
    (hp : vs.Perm ws) : word vs f = word ws f := by
  induction hp with
  | nil => rfl
  | cons v h ih => exact congrArg (fun g : X → Y ↦ fun x ↦ fderiv ℝ g x v) ih
  | trans _ _ ih ih' => exact ih.trans ih'
  | swap v w vs =>
    let g := word vs f
    have hg := word_smooth hf vs
    have hd := (hg.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
    funext x
    change fderiv ℝ (fun y ↦ fderiv ℝ g y v) x w = fderiv ℝ (fun y ↦ fderiv ℝ g y w) x v
    rw [fderiv_clm_apply (hd x) (differentiableAt_const _), fderiv_clm_apply (hd x) (differentiableAt_const _)]
    simpa using (hg.contDiffAt.isSymmSndFDerivAt (by simp)) w v

/-- A concatenated word acts first by its inner parameter word
(`app:ch_response:eq:direct-envelope-profile`). -/
private theorem word_append (us vs : List X) (f : X → Y) : word (us ++ vs) f = word us (word vs f) := by
  induction us with
  | nil => rfl
  | cons v us ih => change (fun x ↦ fderiv ℝ (word (us ++ vs) f) x v) = _; rw [ih]; rfl

/-- An affine slice applies its linear part to each ordered direction
(`app:ch_response:eq:direct-envelope-profile`). -/
private theorem word_affine (L : X →L[ℝ] Y) (b : Y) {f : Y → Z} (hf : ContDiff ℝ ∞ f)
    (vs : List X) : word vs (fun x ↦ f (L x + b)) = fun x ↦ word (vs.map L) f (L x + b) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    funext x
    change fderiv ℝ (word vs _) x v = _
    rw [ih]
    exact congrArg (fun D : X →L[ℝ] Z ↦ D v)
      (((word_smooth hf (vs.map L)).differentiable (by simp) _).hasFDerivAt.comp x (L.hasFDerivAt.add_const b)).fderiv

/-- Evaluate the actual Fréchet tensor on the ordered list
(`app:ch_response:eq:direct-envelope-profile`). -/
private theorem word_eq_jet {f : X → Y} (hf : ContDiff ℝ ∞ f) (vs : List X) :
    word vs f = parameterListJet f vs :=
  funext fun x ↦ Assembly.orderedParameterWord_eq_iteratedFDeriv isOpen_univ hf.contDiffOn vs (mem_univ x)
end Word

/-- Sort coordinate indices by physical versus full-parameter block
(`app:ch_response:eq:direct-envelope-profile`). -/
private theorem split_word {A B : Type} (vs : List (A ⊕ B)) :
    ∃ xs : List A, ∃ ws : List B, vs.Perm (xs.map Sum.inl ++ ws.map Sum.inr) := by
  induction vs with
  | nil => exact ⟨[], [], .refl []⟩
  | cons v vs ih =>
    obtain ⟨xs, ws, h⟩ := ih
    cases v with
    | inl x => exact ⟨x :: xs, ws, h.cons _⟩
    | inr w => exact ⟨xs, w :: ws, (h.cons _).trans List.perm_middle.symm⟩

/-- Each Cartesian evaluation is a unit spatial word of a unit full-parameter word
of exactly the same total length (`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_fullSource_mixedBasisJet_spatial_parameter {j : ℕ} (v : Fin j → Indices) :
    ∃ xs : List E, ∃ ws : List P, xs.length + ws.length = j ∧
      (∀ x ∈ xs, ‖x‖ ≤ 1) ∧ (∀ w ∈ ws, ‖w‖ ≤ 1) ∧
      ∀ (f : E × P → F), ContDiff ℝ ∞ f → ∀ x c,
        iteratedFDeriv ℝ j f (x, c) (fun k ↦ fullSourceMixedBasis n d (v k)) =
          parameterListJet (fun y ↦ parameterListJet (fun b ↦ f (y, b)) ws c) xs x := by
  obtain ⟨is, ks, hp⟩ := split_word (List.ofFn v)
  let xs := is.map (EuclideanSpace.basisFun (Fin n) ℝ)
  let ws := ks.map (fullSourceParameterBasis d)
  refine ⟨xs, ws, ?_, ?_, ?_, ?_⟩
  · simpa [xs, ws] using hp.length_eq.symm
  · intro x hx
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hx
    exact ((EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one k).le
  · intro w hw
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hw
    cases k <;> simp [fullSourceParameterBasis]
  intro f hf x c
  let Lin := ContinuousLinearMap.inl ℝ E P
  let Rin := ContinuousLinearMap.inr ℝ E P
  have hsort := word_perm hf (hp.map (fullSourceMixedBasis n d))
  have he : (is.map Sum.inl ++ ks.map Sum.inr).map (fullSourceMixedBasis n d) =
      xs.map Lin ++ ws.map Rin := by simp [xs, ws, fullSourceMixedBasis, Lin, Rin, List.map_map, Function.comp_def]
  rw [he, word_append, List.map_ofFn] at hsort
  have hparam : word (ws.map Rin) f = fun q : E × P ↦ parameterListJet (fun b ↦ f (q.1, b)) ws q.2 := by
    funext q
    have hj : ContDiff ℝ ∞ (fun b ↦ f (q.1,b)) := hf.comp (contDiff_const.prodMk contDiff_id)
    rw [← word_eq_jet hj]
    simpa [Rin] using (congrFun (word_affine Rin (q.1, 0) hf ws) q.2).symm
  have hsp := congrFun (word_affine Lin (0, c) (word_smooth hf (ws.map Rin)) xs) x
  have hs : ContDiff ℝ ∞ (fun y ↦ word (ws.map Rin) f (y,c)) :=
    (word_smooth hf _).comp (contDiff_id.prodMk contDiff_const)
  simp only [Lin, ContinuousLinearMap.inl_apply, Prod.mk_add_mk, add_zero, zero_add, word_eq_jet hs] at hsp
  calc
    _ = parameterListJet f (List.ofFn (fullSourceMixedBasis n d ∘ v)) (x,c) :=
      (parameterListJet_ofFn ..).symm
    _ = _ := by rw [← word_eq_jet hf, hsort]; exact hsp.symm.trans (by rw [hparam])

end JanetCartan.ResponseTransfer.FullSourceEnvelopes
