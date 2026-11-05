module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ParameterDerivatives.InactiveDerivatives.FiniteExpansion
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ParameterDerivatives.InactiveDerivatives.CompactSobolev

/-!
# Spatial profiles of the actual source parameter jets

The polynomial carrier expansion and Sobolev profiles of the ORIGINAL source
parameter jets produce the spatial profile of the normalized differentiated
source. Consumer: its Sobolev profile and the actual inactive derivative estimate
in `app:ch_response:thm:response-literal-transfer`.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace JanetCartan.ResponseTransfer.Complement.ParameterDerivatives
open MixedGrades InactiveSource Pseudodifferential
variable {p d r : ℕ}
local notation "E" => Euclidean d
local notation "P" => Euclidean p
local notation "F" => EuclideanSpace ℂ (Fin r)

/-- Spatial smoothness of an actual parameter jet of the original source,
used in the source Sobolev embedding for
`app:ch_response:thm:response-literal-transfer`. -/
theorem contDiff_originalSourceListJet {V : Set P} (hV : IsOpen V)
    {f : P → E → F} (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (V ×ˢ univ))
    (vs : List P) {c : P} (hc : c ∈ V) :
    ContDiff ℝ ∞ (fun x ↦ parameterListJet (fun a ↦ f a x) vs c) := by
  have hd := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin vs.length ↦ P) F vs.get).contDiff.comp_contDiffOn
    (contDiffOn_parameterIteratedFDeriv hV hf vs.length)
  have hdx := hd.comp (contDiffOn_const.prodMk contDiffOn_id)
    (s := (univ : Set E)) (fun x _ ↦ ⟨hc, mem_univ x⟩)
  exact contDiffOn_univ.mp hdx

private theorem norm_iteratedFDeriv_list_sum_le {ι : Type*} (l : List ι)
    (g : ι → E → F) {x : E} (hg : ∀ i ∈ l, ContDiffAt ℝ ∞ (g i) x) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun y ↦ (l.map (fun i ↦ g i y)).sum) x‖ ≤
      (l.map (fun i ↦ ‖iteratedFDeriv ℝ j (g i) x‖)).sum := by
  induction l with
  | nil => simp
  | cons i l ih =>
    have hsum : ContDiffAt ℝ ∞ (fun y ↦ (l.map (fun i ↦ g i y)).sum) x := by
      have hg' : ∀ a ∈ l, ContDiffAt ℝ ∞ (g a) x := fun a ha ↦ hg a (by simp [ha])
      clear ih hg
      induction l with
      | nil => simpa using (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : E ↦ (0 : F)) x)
      | cons a l ih =>
        simp only [List.map_cons, List.sum_cons]
        exact (hg' a (by simp)).add (ih (fun b hb ↦ hg' b (by simp [hb])))
    simp only [List.map_cons, List.sum_cons]
    change ‖iteratedFDeriv ℝ j (g i + fun y ↦ (l.map (fun i ↦ g i y)).sum) x‖ ≤ _
    rw [iteratedFDeriv_add_apply ((hg i (by simp)).of_le (by simp)) (hsum.of_le (by simp))]
    exact (norm_add_le _ _).trans (add_le_add le_rfl
      (ih (fun a ha ↦ hg a (by simp [ha]))))

private theorem spatial_polynomial_le {V : Set P} {U : Set E}
    (hV : IsOpen V) (hU : IsOpen U) {φ : P → E → ℝ}
    (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (V ×ˢ U))
    (vs : List P) (ρ : ℝ) (j : ℕ) {c : P} (hc : c ∈ V) {x : E} (hx : x ∈ U) :
    ‖iteratedFDeriv ℝ j (fun y ↦ ∑ b : CarrierJetBranch vs.length,
      (ρ : ℂ) ^ carrierJetDegree b * sourcePhaseCoefficient φ vs b c y) x‖ ≤
    ‖iteratedFDeriv ℝ j (fun z : P × E ↦ ∑ b : CarrierJetBranch vs.length,
      (ρ : ℂ) ^ carrierJetDegree b * sourcePhaseCoefficient φ vs b z.1 z.2) (c, x)‖ := by
  let T : E →L[ℝ] P × E := (0 : E →L[ℝ] P).prod (ContinuousLinearMap.id ℝ E)
  have hT : ‖T‖ ≤ 1 := T.opNorm_le_bound zero_le_one (fun y ↦ by simp [T, Prod.norm_def])
  have hpoly : ContDiffOn ℝ ∞ (fun z : P × E ↦ ∑ b : CarrierJetBranch vs.length,
      (ρ : ℂ) ^ carrierJetDegree b * sourcePhaseCoefficient φ vs b z.1 z.2) (V ×ˢ U) :=
    ContDiffOn.sum (fun b _ ↦ contDiffOn_const.mul
      (contDiffOn_sourcePhaseCoefficient hV hU hφ vs b))
  simpa [T] using norm_iteratedFDeriv_affine_contraction_le T hT (c, (0 : E))
    (hV.prod hU) hpoly j (x := x) (by simpa [T] using And.intro hc hx)

private theorem contDiffOn_sourceCarrierLeibnizTerm {V : Set P} {U : Set E}
    (hV : IsOpen V) (hU : IsOpen U) {φ : P → E → ℝ} {f : P → E → F}
    (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (V ×ˢ U))
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (V ×ˢ univ))
    (s : List P × List P) (ρ : ℝ) {c : P} (hc : c ∈ V) :
    ContDiffOn ℝ ∞ (sourceCarrierLeibnizTerm ρ φ f s c) U := by
  have hp : ContDiffOn ℝ ∞ (fun x ↦ ∑ b : CarrierJetBranch s.1.length,
      (ρ : ℂ) ^ carrierJetDegree b * sourcePhaseCoefficient φ s.1 b c x) U :=
    ContDiffOn.sum (fun b _ ↦ contDiffOn_const.mul
      ((contDiffOn_sourcePhaseCoefficient hV hU hφ s.1 b).comp
        (contDiffOn_const.prodMk contDiffOn_id) (fun _ hx ↦ ⟨hc, hx⟩)))
  exact hp.smul (contDiff_originalSourceListJet hV hf s.2 hc).contDiffOn

/-- The finite profile budget of the actual source Leibniz expansion. It uses
only phase-polynomial grades and the ORIGINAL source Sobolev profile constants.
Source: `app:ch_response:thm:response-literal-transfer`. -/
def sourceLeibnizSpatialBudget (D C : List P → ℕ → ℝ) (vs : List P) (j : ℕ) : ℝ :=
  ((parameterLeibnizSplittings vs).map (fun s ↦
    ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * D s.1 i *
      envelopeJetProfileConstant d (C s.2) (j - i))).sum

/-- Nonnegative finite source-jet profile budget, for the inactive source
Sobolev assembly (`app:ch_response:thm:response-literal-transfer`). -/
theorem sourceLeibnizSpatialBudget_nonneg (D C : List P → ℕ → ℝ)
    (hD : ∀ vs j, 0 ≤ D vs j) (vs : List P) (j : ℕ) :
    0 ≤ sourceLeibnizSpatialBudget (d := d) D C vs j := by
  apply List.sum_nonneg
  intro a ha
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp ha
  exact Finset.sum_nonneg fun i _ ↦ mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (hD _ _)) (envelopeJetProfileConstant_nonneg _ _ _)

/-- Primitive phase smoothness on the fixed compact box and the actual Sobolev
profiles of ORIGINAL source parameter jets imply the full spatial profile of
the SAME normalized carrier derivative. The frequency loss is `k`, and the
source-scale loss is `k+d+1`, both independent of the spatial order. All constants
are selected before frequency, datum, and parameter.

The parent supplies original source profiles from its envelope construction and
joint phase smoothness from its phase construction; the differentiated-envelope
profile is proved here (`app:ch_response:thm:response-literal-transfer`). -/
theorem exists_parameterCarrierJet_spatial_profile
    {V B : Set P} {U S : Set E} (hV : IsOpen V) (hU : IsOpen U)
    (hB : IsCompact B) (hBV : B ⊆ V) (hS : IsCompact S) (hSU : S ⊆ U)
    {φ : P → E → ℝ} (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (V ×ˢ U))
    (k : ℕ) (v : Fin k → P) (C : List P → ℕ → ℝ) :
    ∃ J : ℕ → ℝ, (∀ j, 0 ≤ J j) ∧
      ∀ (ρ A K : ℝ), 1 ≤ ρ → 0 ≤ A → 1 ≤ K →
      ∀ (f : P → E → F),
      ContDiffOn ℝ ∞ (Function.uncurry f) (V ×ˢ univ) →
      (∀ a ∈ V, tsupport (f a) ⊆ S) → ∀ c ∈ B,
      ∀ (hm : ∀ vs : List P, MemLp (fun x ↦ parameterListJet (fun a ↦ f a x) vs c) 2 volume),
      (∀ vs (j : ℕ), MemVectorFourierSobolev (j : ℝ) ((hm vs).toLp _)) →
      (∀ vs (j : ℕ), vectorFourierSobolevNorm (j : ℝ) ((hm vs).toLp _) ≤
        C vs j * (A * K ^ vs.length) * K ^ j) →
      ∀ j x, ‖iteratedFDeriv ℝ j (parameterCarrierJet ρ φ f k v c) x‖ ≤
        J j * (A * ρ ^ k * K ^ (k + d + 1)) * K ^ j := by
  classical
  choose D hD hDb using fun vs : List P ↦
    exists_sourceCarrierPolynomial_joint_profile hV hU hB hBV hS hSU hφ vs
  refine ⟨sourceLeibnizSpatialBudget (d := d) D C (List.ofFn v),
    sourceLeibnizSpatialBudget_nonneg D C hD (List.ofFn v), ?_⟩
  intro ρ A K hρ hA hK f hf hs c hc hm hmem hprofile j x
  have hcV := hBV hc
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hρ0 : 0 ≤ ρ := zero_le_one.trans hρ
  have hJ := sourceLeibnizSpatialBudget_nonneg (d := d) D C hD (List.ofFn v) j
  by_cases hx : x ∈ S
  swap
  · have hz : iteratedFDeriv ℝ j (parameterCarrierJet ρ φ f k v c) x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h ↦ hx
        (tsupport_parameterCarrierJet_subset_original hV hS ρ φ f hs k v hcV
          (tsupport_iteratedFDeriv_subset j h)))
    rw [hz, norm_zero]
    positivity
  have hxu := hSU hx
  have he : parameterCarrierJet ρ φ f k v c =ᶠ[𝓝 x]
      fun y ↦ ((parameterLeibnizSplittings (List.ofFn v)).map
        (fun s ↦ sourceCarrierLeibnizTerm ρ φ f s c y)).sum := by
    filter_upwards [hU.mem_nhds hxu] with y hy
    exact parameterCarrierJet_eq_leibnizPolynomial hV ρ k v hcV y
      (hφ.comp (contDiffOn_id.prodMk contDiffOn_const) (fun _ ha ↦ ⟨ha, hy⟩))
      (hf.comp (contDiffOn_id.prodMk contDiffOn_const) (fun _ ha ↦ ⟨ha, mem_univ y⟩))
  rw [(he.iteratedFDeriv ℝ j).eq_of_nhds]
  apply (norm_iteratedFDeriv_list_sum_le _ _
    (fun s _ ↦ (contDiffOn_sourceCarrierLeibnizTerm hV hU hφ hf s ρ hcV).contDiffAt
      (hU.mem_nhds hxu)) j).trans
  unfold sourceLeibnizSpatialBudget
  rw [← List.sum_map_mul_right, ← List.sum_map_mul_right]
  apply List.sum_le_sum
  intro t ht
  have horder := parameterLeibnizSplittings_orders ht
  rw [List.length_ofFn] at horder
  have hp : ContDiffOn ℝ ∞ (fun y ↦ ∑ b : CarrierJetBranch t.1.length,
      (ρ : ℂ) ^ carrierJetDegree b * sourcePhaseCoefficient φ t.1 b c y) U :=
    ContDiffOn.sum (fun b _ ↦ contDiffOn_const.mul
      ((contDiffOn_sourcePhaseCoefficient hV hU hφ t.1 b).comp
        (contDiffOn_const.prodMk contDiffOn_id) (fun _ hy ↦ ⟨hcV, hy⟩)))
  have hg := contDiff_originalSourceListJet hV hf t.2 hcV
  have hprod := norm_iteratedFDerivWithin_smul_le hp hg.contDiffOn hU.uniqueDiffOn
    hxu (n := j) (by simp)
  simp only [iteratedFDerivWithin_of_isOpen _ hU hxu] at hprod
  apply hprod.trans
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have hij : i ≤ j := Finset.mem_range_succ_iff.mp hi
  have hpoly := (spatial_polynomial_le hV hU hφ t.1 ρ i hcV hxu).trans
    (hDb t.1 ρ hρ i c hc x hx)
  have hsource := norm_iteratedFDeriv_le_envelope_profile hg.continuous (hm t.2)
    (mul_nonneg hA (pow_nonneg hK0 _)) hK (hmem t.2) (hprofile t.2) (j - i) x
  have hpower : ρ ^ t.1.length * K ^ (t.2.length + (d + 1) + (j - i)) ≤
      ρ ^ k * K ^ (k + d + 1 + j) :=
    mul_le_mul (pow_le_pow_right₀ hρ (by omega))
      (pow_le_pow_right₀ hK (by omega)) (pow_nonneg hK0 _) (pow_nonneg hρ0 _)
  calc
    _ ≤ (j.choose i : ℝ) * (D t.1 i * ρ ^ t.1.length) *
        (envelopeJetProfileConstant d (C t.2) (j - i) *
          ((A * K ^ t.2.length * K ^ (d + 1)) * K ^ (j - i))) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hpoly (Nat.cast_nonneg _)) hsource
        (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hD _ _) (by positivity)))
    _ = ((j.choose i : ℝ) * D t.1 i * envelopeJetProfileConstant d (C t.2) (j - i) * A) *
        (ρ ^ t.1.length * K ^ (t.2.length + (d + 1) + (j - i))) := by
      simp only [pow_add]; ring
    _ ≤ ((j.choose i : ℝ) * D t.1 i * envelopeJetProfileConstant d (C t.2) (j - i) * A) *
        (ρ ^ k * K ^ (k + d + 1 + j)) :=
      mul_le_mul_of_nonneg_left hpower (mul_nonneg (mul_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (hD _ _))
        (envelopeJetProfileConstant_nonneg _ _ _)) hA)
    _ = _ := by simp only [pow_add]; ring

end JanetCartan.ResponseTransfer.Complement.ParameterDerivatives
