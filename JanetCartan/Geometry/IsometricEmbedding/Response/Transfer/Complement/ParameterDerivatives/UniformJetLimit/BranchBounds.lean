module
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ParameterDerivatives.GraphRealization.Leibniz.Splittings
/-!
# Finite low-operator estimates for the unchanged Leibniz expansion

The low norms of the actual branch operators and the L² norms of the original
source jets bound the finite expansion, without a graph derivative estimate as
input. These are consumed by `UniformJetLimit.Assembly`, for
`app:ch_response:thm:response-literal-transfer`.
-/

@[expose] public noncomputable section
open Set Filter
open scoped Topology NNReal
namespace JanetCartan.ResponseTransfer.Complement.ParameterDerivatives.UniformJetLimit
variable {P H ι : Type*} [NormedAddCommGroup P]
  [NormedAddCommGroup H] [NormedSpace ℂ H]

omit [NormedAddCommGroup P] in
/-- The exact number of ordered kernel/source branches, with multiplicity.
Consumer: the compact-graph jet bound in
`app:ch_response:thm:response-literal-transfer`. -/
theorem parameterLeibnizSplittings_length (vs : List P) :
    (parameterLeibnizSplittings vs).length = 2 ^ vs.length := by
  induction vs with
  | nil => simp [parameterLeibnizSplittings]
  | cons v vs ih => simp [parameterLeibnizSplittings, ih, pow_succ, Nat.mul_two]

omit [NormedAddCommGroup P] in
/-- Every direction in either branch is an original parameter direction.
This transfers unit direction bounds to both factors in
`app:ch_response:thm:response-literal-transfer`. -/
theorem parameterLeibnizSplittings_directions {vs : List P} {s : List P × List P}
    (hs : s ∈ parameterLeibnizSplittings vs) :
    (∀ v ∈ s.1, v ∈ vs) ∧ (∀ v ∈ s.2, v ∈ vs) := by
  induction vs generalizing s with
  | nil => simp only [parameterLeibnizSplittings, List.mem_singleton] at hs; subst s; simp
  | cons v vs ih =>
    simp only [parameterLeibnizSplittings, List.mem_append, List.mem_map] at hs
    rcases hs with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
    · obtain ⟨h1, h2⟩ := ih ht
      constructor
      · intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (h1 w hw)
      · exact fun w hw ↦ List.mem_cons_of_mem _ (h2 w hw)
    · obtain ⟨h1, h2⟩ := ih ht
      constructor
      · exact fun w hw ↦ List.mem_cons_of_mem _ (h1 w hw)
      · intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (h2 w hw)

omit [NormedSpace ℂ H] in
private theorem norm_list_sum_le_length_mul {α : Type*} (ss : List α) (b : α → H)
    {C : ℝ} (hb : ∀ s ∈ ss, ‖b s‖ ≤ C) : ‖(ss.map b).sum‖ ≤ ss.length * C := by
  induction ss with
  | nil => simp
  | cons s ss ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    calc
      _ ≤ ‖b s‖ + ‖(ss.map b).sum‖ := norm_add_le _ _
      _ ≤ C + (ss.length : ℝ) * C := add_le_add (hb s (by simp))
        (ih (fun t ht ↦ hb t (by simp [ht])))
      _ = ((ss.length : ℝ) + 1) * C := by ring

/-- Uniform LOW operator bounds and original source-jet bounds control the
entire finite expansion on the direction unit ball. No bound on a derivative
of the graph output is assumed. Consumer: the one-higher jet estimate used by
`UniformJetLimit.Assembly` in `app:ch_response:thm:response-literal-transfer`. -/
theorem norm_leibniz_operator_sum_le (Q : List P → H →L[ℂ] H) (u : List P → H)
    (k : ℕ) (B M : ℝ≥0)
    (hQ : ∀ vs : List P, vs.length ≤ k → (∀ v ∈ vs, ‖v‖ ≤ 1) → ‖Q vs‖ ≤ B)
    (hu : ∀ vs : List P, vs.length ≤ k → (∀ v ∈ vs, ‖v‖ ≤ 1) → ‖u vs‖ ≤ M)
    (v : Fin k → P) (hv : ‖v‖ ≤ 1) :
    ‖((parameterLeibnizSplittings (List.ofFn v)).map (fun s ↦ Q s.1 (u s.2))).sum‖ ≤
      (2 : ℝ) ^ k * (B : ℝ) * (M : ℝ) := by
  have hd (w : P) (hw : w ∈ List.ofFn v) : ‖w‖ ≤ 1 := by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hw
    exact (norm_le_pi_norm v i).trans hv
  have hterm (s : List P × List P) (hs : s ∈ parameterLeibnizSplittings (List.ofFn v)) :
      ‖Q s.1 (u s.2)‖ ≤ (B : ℝ) * (M : ℝ) := by
    have hlen := parameterLeibnizSplittings_orders hs
    rw [List.length_ofFn] at hlen
    have hdir := parameterLeibnizSplittings_directions hs
    exact (Q s.1).le_of_opNorm_le (hQ s.1 (by omega) (fun w hw ↦ hd w (hdir.1 w hw))) _ |>.trans
      (mul_le_mul_of_nonneg_left (hu s.2 (by omega) (fun w hw ↦ hd w (hdir.2 w hw))) B.coe_nonneg)
  convert norm_list_sum_le_length_mul _ _ hterm using 1
  rw [parameterLeibnizSplittings_length, List.length_ofFn, Nat.cast_pow, Nat.cast_ofNat]
  ring

omit [NormedAddCommGroup P] in
/-- Strong convergence on each original fixed source passes through the
finite expansion. This is only directional pointwise convergence; the compact
uniformization is a separate proved step. Source:
`app:ch_response:thm:response-literal-transfer`. -/
theorem tendsto_leibniz_operator_sum {l : Filter ι}
    (Qreg : ι → List P → H →L[ℂ] H) (Q : List P → H →L[ℂ] H)
    (u : List P → H) (vs : List P)
    (hQ : ∀ s ∈ parameterLeibnizSplittings vs,
      Tendsto (fun a ↦ Qreg a s.1 (u s.2)) l (𝓝 (Q s.1 (u s.2)))) :
    Tendsto (fun a ↦ ((parameterLeibnizSplittings vs).map
        (fun s ↦ Qreg a s.1 (u s.2))).sum) l
      (𝓝 ((parameterLeibnizSplittings vs).map (fun s ↦ Q s.1 (u s.2))).sum) :=
  tendsto_list_sum _ hQ
end JanetCartan.ResponseTransfer.Complement.ParameterDerivatives.UniformJetLimit
