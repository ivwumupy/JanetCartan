module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ParameterDerivatives.InactiveDerivatives.JetProfiles
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Reconstructing mixed source tensors from spatial and parameter words

The joint-order assertion after `app:ch_response:eq:direct-envelope-profile`
counts spatial and parameter derivatives together. Schwarz symmetry sorts each
coordinate word into spatial derivatives of an original parameter derivative.
Finite basis expansion then controls the full multilinear operator norm.
Consumer: `exists_sourceMixedJet_profile`, supplying both integrated envelopes.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace JanetCartan.ResponseTransfer.RetainedFactors.SourceMixedJets
open Complement.ParameterDerivatives

private theorem listJet_cons {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {f : X → Y}
    (hf : ContDiff ℝ ∞ f) (v : X) (vs : List X) (x : X) :
    parameterListJet f (v :: vs) x = fderiv ℝ (parameterListJet f vs) x v := by
  have hd := (hf.contDiffAt (x := x)).differentiableAt_iteratedFDeriv (m := vs.length)
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl _)
  have ht : Fin.tail (v :: vs).get = vs.get := by
    funext i
    exact List.get_cons_succ
  change iteratedFDeriv ℝ (vs.length + 1) f x (v :: vs).get =
    fderiv ℝ (fun b ↦ iteratedFDeriv ℝ vs.length f b vs.get) x v
  simpa only [ht, List.get_cons_zero] using
    hd.iteratedFDeriv_succ_apply_left' (m := (v :: vs).get)

private theorem smooth_listJet {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {f : X → Y}
    (hf : ContDiff ℝ ∞ f) (vs : List X) : ContDiff ℝ ∞ (parameterListJet f vs) :=
  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin vs.length ↦ X) Y vs.get).contDiff.comp
    (hf.iteratedFDeriv_right (by simp))

private theorem listJet_perm {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {f : X → Y}
    (hf : ContDiff ℝ ∞ f) {vs ws : List X} (h : vs.Perm ws) :
    parameterListJet f vs = parameterListJet f ws := by
  induction h with
  | nil => rfl
  | cons v h ih =>
    funext x
    rw [listJet_cons hf, listJet_cons hf, ih]
  | swap v w vs =>
    have hg := smooth_listJet hf vs
    have hd := (hg.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
    funext x
    rw [listJet_cons hf, listJet_cons hf]
    rw [show parameterListJet f (v :: vs) = (fun y ↦ fderiv ℝ (parameterListJet f vs) y v) from funext (listJet_cons hf v vs),
      show parameterListJet f (w :: vs) = (fun y ↦ fderiv ℝ (parameterListJet f vs) y w) from funext (listJet_cons hf w vs)]
    rw [fderiv_clm_apply (hd x) (differentiableAt_const _),
      fderiv_clm_apply (hd x) (differentiableAt_const _)]
    simpa using (hg.contDiffAt.isSymmSndFDerivAt (by simp)) w v
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem listJet_append {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {f : X → Y}
    (hf : ContDiff ℝ ∞ f) (vs ws : List X) :
    parameterListJet f (vs ++ ws) = parameterListJet (parameterListJet f ws) vs := by
  induction vs with
  | nil => funext x; simp [parameterListJet, iteratedFDeriv_zero_apply]
  | cons v vs ih =>
    funext x
    simp only [List.cons_append, listJet_cons hf, listJet_cons (smooth_listJet hf ws), ih]

private theorem listJet_affine {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {f : Y → Z} (hf : ContDiff ℝ ∞ f) (L : X →L[ℝ] Y) (b : Y) (vs : List X) (x : X) :
    parameterListJet (fun y ↦ f (L y + b)) vs x =
      parameterListJet f (vs.map L) (L x + b) := by
  induction vs generalizing x with
  | nil => rfl
  | cons v vs ih =>
    have hs : ContDiff ℝ ∞ (fun y ↦ f (L y + b)) := hf.comp (L.contDiff.add contDiff_const)
    rw [listJet_cons hs, List.map_cons, listJet_cons hf]
    rw [show parameterListJet (fun y ↦ f (L y + b)) vs =
      (fun y ↦ parameterListJet f (vs.map L) (L y + b)) from funext ih]
    have h := ((smooth_listJet hf (vs.map L)).differentiable (by simp) (L x + b)).hasFDerivAt.comp x
      (L.hasFDerivAt.add_const b)
    exact congrArg (fun D : X →L[ℝ] Z ↦ D v) h.fderiv

private theorem exists_sorted {α β : Type*} (ds : List (α ⊕ β)) :
    ∃ xs : List α, ∃ ws : List β, ds.Perm (xs.map Sum.inl ++ ws.map Sum.inr) := by
  induction ds with
  | nil => exact ⟨[], [], List.Perm.refl []⟩
  | cons d ds ih =>
    obtain ⟨xs, ws, h⟩ := ih
    cases d with
    | inl x => exact ⟨x :: xs, ws, h.cons _⟩
    | inr w =>
      refine ⟨xs, w :: ws, (h.cons _).trans ?_⟩
      exact List.perm_middle.symm

variable {n r : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "P" => EuclideanSpace ℝ (Fin 3)
local notation "F" => EuclideanSpace ℂ (Fin r)

/-- The fixed Cartesian basis of physical space times the three-dimensional
parameter space, used in the mixed datum bound of
`app:ch_response:eq:direct-envelope-profile`. -/
def sourceJointBasis (n : ℕ) : Module.Basis (Fin n ⊕ Fin 3) ℝ (EuclideanSpace ℝ (Fin n) × P) :=
  (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.prod
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis

/-- Finite Cartesian evaluations control the actual tensor operator norm.
This supplies the L² reconstruction for `app:ch_response:eq:direct-envelope-profile`.
-/
theorem norm_jointTensor_le_basis_sum {j : ℕ} (T : (E × P) [×j]→L[ℝ] F) :
    ‖T‖ ≤ ∑ v : Fin j → (Fin n ⊕ Fin 3), ‖T (fun k ↦ sourceJointBasis n (v k))‖ := by
  classical
  let b := sourceJointBasis n
  apply T.opNorm_le_bound (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
  intro v
  have hv : v = fun k ↦ ∑ i, b.repr (v k) i • b i := by
    funext k
    exact (b.sum_repr (v k)).symm
  calc
    ‖T v‖ = ‖∑ a : Fin j → (Fin n ⊕ Fin 3), (∏ k, b.repr (v k) (a k)) •
        T (fun k ↦ b (a k))‖ := by
      conv_lhs => rw [hv, T.map_sum]
      simp only [T.map_smul_univ]
    _ ≤ ∑ a : Fin j → (Fin n ⊕ Fin 3), ‖(∏ k, b.repr (v k) (a k)) •
        T (fun k ↦ b (a k))‖ := norm_sum_le _ _
    _ ≤ ∑ a : Fin j → (Fin n ⊕ Fin 3), ‖T (fun k ↦ b (a k))‖ * ∏ k, ‖v k‖ := by
      apply Finset.sum_le_sum
      intro a _
      rw [norm_smul, norm_prod, mul_comm]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
      intro k _
      cases a k with
      | inl i =>
        change ‖(EuclideanSpace.basisFun (Fin n) ℝ).toBasis.repr (v k).1 i‖ ≤ _
        rw [OrthonormalBasis.coe_toBasis_repr_apply]
        exact ((PiLp.norm_apply_le _ i).trans_eq (LinearIsometryEquiv.norm_map _ _)).trans
          (norm_fst_le (v k))
      | inr i =>
        change ‖(EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.repr (v k).2 i‖ ≤ _
        rw [OrthonormalBasis.coe_toBasis_repr_apply]
        exact ((PiLp.norm_apply_le _ i).trans_eq (LinearIsometryEquiv.norm_map _ _)).trans
          (norm_snd_le (v k))
    _ = _ := (Finset.sum_mul ..).symm

/-- Sort each mixed coordinate word into a spatial word applied to an original
parameter jet, preserving its exact total order and representative. This is the
algebraic input of `exists_sourceMixedJet_profile`, for the joint assertion in
`app:ch_response:thm:response-literal-transfer`. -/
theorem exists_jointBasisJet_eq_spatial_parameter {j : ℕ} (v : Fin j → (Fin n ⊕ Fin 3)) :
    ∃ xs : List E, ∃ ws : List P,
      xs.length + ws.length = j ∧
      (∀ x ∈ xs, ‖x‖ ≤ 1) ∧ (∀ w ∈ ws, ‖w‖ ≤ 1) ∧
      ∀ (f : E × P → F), ContDiff ℝ ∞ f → ∀ x c,
        iteratedFDeriv ℝ j f (x, c) (fun k ↦ sourceJointBasis n (v k)) =
          parameterListJet (fun y ↦ parameterListJet (fun b ↦ f (y, b)) ws c) xs x := by
  obtain ⟨is, ks, hp⟩ := exists_sorted (List.ofFn v)
  let xs := is.map (EuclideanSpace.basisFun (Fin n) ℝ)
  let ws := ks.map (EuclideanSpace.basisFun (Fin 3) ℝ)
  refine ⟨xs, ws, ?_, ?_, ?_, ?_⟩
  · simpa [xs, ws] using hp.length_eq.symm
  · intro x hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact ((EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one i).le
  · intro w hw
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hw
    exact ((EuclideanSpace.basisFun (Fin 3) ℝ).norm_eq_one i).le
  · intro f hf x c
    have he : (is.map Sum.inl ++ ks.map Sum.inr).map (sourceJointBasis n) =
        xs.map (ContinuousLinearMap.inl ℝ E P) ++ ws.map (ContinuousLinearMap.inr ℝ E P) := by
      simp [xs, ws, sourceJointBasis, List.map_map, Function.comp_def]
    have hh := listJet_perm hf (hp.map (sourceJointBasis n))
    rw [he] at hh
    have hl : (List.ofFn v).map (sourceJointBasis n) =
        List.ofFn (fun k ↦ sourceJointBasis n (v k)) := by simp only [List.map_ofFn, Function.comp_def]
    rw [hl] at hh
    rw [← parameterListJet_ofFn f j (fun k ↦ sourceJointBasis n (v k)), hh, listJet_append hf]
    have hi : parameterListJet f (ws.map (ContinuousLinearMap.inr ℝ E P)) =
        fun q : E × P ↦ parameterListJet (fun b ↦ f (q.1, b)) ws q.2 := by
      funext q
      simpa using (listJet_affine hf (ContinuousLinearMap.inr ℝ E P) (q.1, 0) ws q.2).symm
    have houter := listJet_affine (smooth_listJet hf (ws.map (ContinuousLinearMap.inr ℝ E P)))
      (ContinuousLinearMap.inl ℝ E P) (0, c) xs x
    simpa [hi] using houter.symm
end JanetCartan.ResponseTransfer.RetainedFactors.SourceMixedJets
