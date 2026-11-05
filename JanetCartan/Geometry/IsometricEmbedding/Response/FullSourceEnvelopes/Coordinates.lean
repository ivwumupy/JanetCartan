module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.IntegratedEnvelope.Assembly.Words
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Envelope

/-!
# Exact external coordinate transfer for the full source

The integrated primitives use a single Euclidean space. Mathlib's
`EuclideanSpace.finAddEquivProd` splits it into the original independent label
and covector. The forward split is contractive for the product norm; the inverse
need not be. Only external parameters are changed, never the spatial or elapsed
integration variables. Consumer: `app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff
namespace JanetCartan.ResponseTransfer.FullSourceEnvelopes
open Pseudodifferential
variable {d : ℕ}
local notation "P" => Euclidean 3 × Euclidean d
local notation "Pc" => Euclidean (3 + d)
local notation "splitP" => (EuclideanSpace.finAddEquivProd : Pc ≃L[ℝ] P)

/-- The squared Euclidean norm is the sum of the two squared block norms,
as required for coordinate transfer in `app:ch_response:eq:fixed-factor-transfer`. -/
theorem fullSource_coordinate_norm_sq (u : Pc) :
    ‖u‖ ^ 2 = ‖(splitP u).1‖ ^ 2 + ‖(splitP u).2‖ ^ 2 := by
  let e : Pc ≃ₗᵢ[ℝ] WithLp 2 P :=
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finSumFinEquiv.symm).trans
      (PiLp.sumPiLpEquivProdLpPiLp 2 _)
  exact (congrArg (· ^ 2) (e.norm_map u)).symm.trans (WithLp.prod_norm_sq_eq_of_L2 (e u))

/-- Euclidean unit directions split into product unit directions; pulling a
product direction back costs at most two (`app:ch_response:eq:direct-envelope-profile`). -/
theorem fullSource_coordinate_norm_bounds :
    (∀ u : Pc, ‖splitP u‖ ≤ ‖u‖) ∧ (∀ v : P, ‖(splitP).symm v‖ ≤ 2 * ‖v‖) := by
  constructor
  · intro u
    rw [Prod.norm_def]
    have h := fullSource_coordinate_norm_sq u
    exact max_le (by nlinarith [sq_nonneg ‖(splitP u).2‖, norm_nonneg u])
      (by nlinarith [sq_nonneg ‖(splitP u).1‖, norm_nonneg u])
  · intro v
    have h := fullSource_coordinate_norm_sq ((splitP).symm v)
    rw [ContinuousLinearEquiv.apply_symm_apply] at h
    have h₁ := pow_le_pow_left₀ (norm_nonneg v.1) (norm_fst_le v) 2
    have h₂ := pow_le_pow_left₀ (norm_nonneg v.2) (norm_snd_le v) 2
    nlinarith [norm_nonneg v, sq_nonneg ‖v‖]

section Change
variable {X Y Z : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- Exact jet pullback, also for a phase smooth only on its critical chart;
used on the joint source, phase and annular amplitude in
`app:ch_response:eq:direct-envelope-profile`. -/
theorem externalCoordinate_jet (e : X ≃L[ℝ] Y) (f : Y → Z) (x : X) (j : ℕ) :
    iteratedFDeriv ℝ j (f ∘ e) x =
      (iteratedFDeriv ℝ j f (e x)).compContinuousLinearMap (fun _ ↦ e.toContinuousLinearMap) := by
  simpa only [preimage_univ, iteratedFDerivWithin_univ] using
    e.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ (mem_univ (e x)) j

/-- A contractive external substitution costs no power of the scale and no
extra derivative at the low reserve (`app:ch_response:eq:direct-envelope-profile`). -/
theorem norm_externalCoordinate_jet_le (e : X ≃L[ℝ] Y) (he : ∀ x, ‖e x‖ ≤ ‖x‖)
    (f : Y → Z) (x : X) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (f ∘ e) x‖ ≤ ‖iteratedFDeriv ℝ j f (e x)‖ := by
  have h : ‖e.toContinuousLinearMap‖ ≤ 1 := e.toContinuousLinearMap.opNorm_le_bound zero_le_one
    (fun v ↦ by simpa using he v)
  rw [externalCoordinate_jet]
  exact ((iteratedFDeriv ℝ j f (e x)).norm_compContinuousLinearMap_le _).trans
    (mul_le_of_le_one_right (norm_nonneg _) (by simpa using (pow_le_one₀ (norm_nonneg _) h (n := j))))

end Change

variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
local notation "word" => orderedTransferAction (fun v g c ↦ fderiv ℝ g c v)

/-- Unit product words have unit Euclidean representatives after halving each
inverse-coordinate direction (`app:ch_response:eq:fixed-factor-transfer`). -/
theorem fullSource_coordinate_word_unit (ps : List P) (hp : ∀ v ∈ ps, ‖v‖ ≤ 1) :
    ∀ u ∈ ps.map (fun v ↦ (2 : ℝ)⁻¹ • (splitP).symm v), ‖u‖ ≤ 1 := by
  intro u hu
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : 0 < (2 : ℝ)⁻¹)]
  linarith [fullSource_coordinate_norm_bounds.2 v, hp v hv]

/-- Every original ordered parameter derivative is exactly the coordinate
word times the constant `2^length`. No regularity or estimate on the output
is assumed; the operator and frequency in the parameter function stay fixed
(`app:ch_response:thm:response-literal-transfer`). -/
theorem fullSource_word_eq_coordinate_word (ps : List P) (f : P → H) (c : P) :
    word ps f c = (2 : ℝ)^ps.length •
      word (ps.map (fun v ↦ (2 : ℝ)⁻¹ • (splitP).symm v)) (f ∘ splitP) ((splitP).symm c) := by
  let m : P → Pc := fun v ↦ (2 : ℝ)⁻¹ • (splitP).symm v
  have he (vs : List P) : word (vs.map m) (f ∘ splitP) =
      (2 : ℝ)⁻¹ ^ vs.length • (word vs f ∘ splitP) := by
    induction vs with
    | nil => simp [orderedTransferAction]
    | cons v vs ih =>
      funext u
      change (fderiv ℝ (word (vs.map m) (f ∘ splitP)) u) (m v) = _
      rw [ih, fderiv_const_smul_field]
      simp [m, (splitP).comp_right_fderiv, orderedTransferAction, smul_smul, pow_succ, mul_comm]
  change _ = (2 : ℝ) ^ ps.length • word (ps.map m) (f ∘ splitP) ((splitP).symm c)
  rw [he]
  simp [smul_smul]

/-- Convert the Euclidean assembly estimate back to the literal product word.
Only the fixed constant changes by `2^ps.length`; the spatial measure, scale,
amplitude and uniformity over the family index are unchanged
(`app:ch_response:eq:fixed-factor-transfer`). -/
theorem fullSource_profile_of_coordinate_word {I : Type} (G : GradedScale H)
    (V : Set P) (f : I → P → H) (A K : I → ℝ) (ps : List P)
    (hc : HasEnvelopeProfile G
      (fun z : I × (splitP ⁻¹' V) ↦ word (ps.map (fun v ↦ (2 : ℝ)⁻¹ • (splitP).symm v))
        (f z.1 ∘ splitP) (z.2 : Pc)) (fun z ↦ A z.1) (fun z ↦ K z.1)) :
    HasEnvelopeProfile G (fun z : I × V ↦ word ps (f z.1) (z.2 : P))
      (fun z ↦ A z.1) (fun z ↦ K z.1) := by
  intro s
  obtain ⟨C, hC, hb⟩ := hc s
  refine ⟨2 ^ ps.length * C, mul_nonneg (by positivity) hC, ?_⟩
  rintro ⟨i, c, hc⟩
  let u : splitP ⁻¹' V := ⟨(splitP).symm c, by simpa only [mem_preimage,
    ContinuousLinearEquiv.apply_symm_apply] using hc⟩
  obtain ⟨hm, hbound⟩ := hb (i,u)
  change word ps (f i) c ∈ G.level s ∧ G.gradeNorm s (word ps (f i) c) ≤ _
  rw [fullSource_word_eq_coordinate_word]
  refine ⟨(G.level s).smul_mem _ hm, ?_⟩
  let y := word (ps.map (fun v ↦ (2 : ℝ)⁻¹ • (splitP).symm v)) (f i ∘ splitP) (u : Pc)
  change G.gradeNorm s ((2 : ℝ)^ps.length • y) ≤ _
  have hmy : y ∈ G.level s := hm
  have he : G.gradeNorm s ((2 : ℝ)^ps.length • y) = 2^ps.length * G.gradeNorm s y := by
    rw [G.gradeNorm_eq ((G.level s).smul_mem _ hmy), G.gradeNorm_eq hmy]
    change G.seminorm s ((2 : ℝ)^ps.length • (⟨y,hmy⟩ : G.level s)) = _
    rw [map_smul_eq_mul, Real.norm_of_nonneg (by positivity)]
  rw [he]
  exact (mul_le_mul_of_nonneg_left hbound (by positivity : 0 ≤ (2:ℝ)^ps.length)).trans_eq (by ring)

end JanetCartan.ResponseTransfer.FullSourceEnvelopes
