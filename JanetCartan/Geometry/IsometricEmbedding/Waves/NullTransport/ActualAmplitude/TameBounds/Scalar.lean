module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualAmplitude.TameBounds.Footpoint

/-!
# One-high estimate for the literal scalar transport solution

The factor and prescribed initial scalar are estimated separately and then
multiplied with the additive product estimate. The only fixed low inputs are
`C³` of the characteristic coefficient, footpoint map, and initial scalar.
The resulting reserve is four, on the same compact domains at every order.
Source: `app:ch_waves:thm:leading`, `app:ch_waves:eq:joint-tame`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff
namespace JanetCartan.NullTransport.AmplitudeTame

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

private theorem pullbacks_smooth_near {K U V : Set (ℝ × E)} {L : Set E}
    {p : E} {τ σ : ℝ} (hτ : 0 < τ) (hσ : 0 < σ)
    (hU : IsOpen U) (hV : IsOpen V) (hL : IsOpen L)
    (hKU : K ⊆ U) (hJV : Icc (-τ) τ ×ˢ closedBall p σ ⊆ V)
    (hBL : closedBall p σ ⊆ L)
    {Y : ℝ × E → E} {c : ℝ × E → ℝ} {r : E → ℝ}
    (hY : ContDiffOn ℝ ∞ Y U) (hc : ContDiffOn ℝ ∞ c V) (hr : ContDiffOn ℝ ∞ r L)
    (hm : MapsTo (fun q ↦ (q.1, Y q)) K (Icc (-τ) τ ×ˢ closedBall p σ)) :
    ∃ W, IsOpen W ∧ K ⊆ W ∧ ContDiffOn ℝ ∞ (r ∘ Y) W ∧
      ContDiffOn ℝ ∞ (fun q ↦ transportFactor (fun s ↦ c (s, Y q)) 0 q.1) W := by
  let Z := fun q : ℝ × E ↦ (q.1, Y q)
  have hZ : ContDiffOn ℝ ∞ Z U := contDiffOn_fst.prodMk hY
  obtain ⟨W, hW, hJW, hf⟩ := exists_transportFactor_smooth_near_cylinder p hτ hσ hV hJV hc
  refine ⟨(U ∩ Y ⁻¹' L) ∩ (U ∩ Z ⁻¹' W),
    (hY.continuousOn.isOpen_inter_preimage hU hL).inter
      (hZ.continuousOn.isOpen_inter_preimage hU hW), ?_, ?_, ?_⟩
  · exact fun q hq ↦ ⟨⟨hKU hq, hBL (hm hq).2⟩, ⟨hKU hq, hJW (hm hq)⟩⟩
  · exact (hr.comp (hY.mono inter_subset_left) (fun _ hx ↦ hx.2)).mono inter_subset_left
  · exact (hf.comp (hZ.mono inter_subset_left) (fun _ hx ↦ hx.2)).mono inter_subset_right

/-- The scalar's smoothness near the compact working set is proved from the
coefficient, initial scalar and footpoint map. No scalar jets are assumed
(`app:ch_waves:thm:leading`). -/
theorem exists_transportFromFootpoint_smooth_near {K U V : Set (ℝ × E)} {L : Set E}
    {p : E} {τ σ : ℝ} (hτ : 0 < τ) (hσ : 0 < σ)
    (hU : IsOpen U) (hV : IsOpen V) (hL : IsOpen L)
    (hKU : K ⊆ U) (hJV : Icc (-τ) τ ×ˢ closedBall p σ ⊆ V)
    (hBL : closedBall p σ ⊆ L)
    {Y : ℝ × E → E} {c : ℝ × E → ℝ} {r : E → ℝ}
    (hY : ContDiffOn ℝ ∞ Y U) (hc : ContDiffOn ℝ ∞ c V) (hr : ContDiffOn ℝ ∞ r L)
    (hm : MapsTo (fun q ↦ (q.1, Y q)) K (Icc (-τ) τ ×ˢ closedBall p σ)) :
    ∃ W, IsOpen W ∧ K ⊆ W ∧ ContDiffOn ℝ ∞ (transportFromFootpoint c 0 r Y) W := by
  obtain ⟨W, hW, hKW, hrY, hfY⟩ := pullbacks_smooth_near hτ hσ hU hV hL hKU hJV hBL hY hc hr hm
  exact ⟨W, hW, hKW, hfY.mul hrY⟩

/-- The literal scalar solution satisfies an additive one-high bound with a
fixed reserve four. The low budgets are primitive `C³` bounds; integral,
exponential and scalar estimates are all conclusions. Constants precede all
varying inputs (`app:ch_waves:eq:joint-tame`). -/
theorem exists_cNorm_transportFromFootpoint_bounds
    (e : (ℝ × E) ≃L[ℝ] ℝ × E) (a : ℝ × E) (p : E)
    {ρ τ σ : ℝ} (hρ : 0 < ρ) (hτ : 0 < τ) (hσ : 0 < σ)
    {M : ℝ} (hM : 0 ≤ M) :
    ∃ B : ℕ → ℝ, (∀ j, 0 < B j) ∧
      ∀ (U V : Set (ℝ × E)) (L : Set E), IsOpen U → IsOpen V → IsOpen L →
      e '' closedBall a ρ ⊆ U → Icc (-τ) τ ×ˢ closedBall p σ ⊆ V →
      closedBall p σ ⊆ L →
      ∀ (Y : ℝ × E → E) (c : ℝ × E → ℝ) (r : E → ℝ),
      ContDiffOn ℝ ∞ Y U → ContDiffOn ℝ ∞ c V → ContDiffOn ℝ ∞ r L →
      MapsTo (fun q ↦ (q.1, Y q)) (e '' closedBall a ρ)
        (Icc (-τ) τ ×ˢ closedBall p σ) →
      cNorm (e '' closedBall a ρ) 3 Y ≤ M →
      cNorm (Icc (-τ) τ ×ˢ closedBall p σ) 3 c ≤ M →
      cNorm (closedBall p σ) 3 r ≤ M →
      ∀ j, cNorm (e '' closedBall a ρ) j (transportFromFootpoint c 0 r Y) ≤
        B j * (1 + cNorm (e '' closedBall a ρ) (j + 4) Y +
          cNorm (Icc (-τ) τ ×ˢ closedBall p σ) (j + 4) c +
          cNorm (closedBall p σ) (j + 4) r) := by
  let K := e '' closedBall a ρ
  let J := Icc (-τ) τ ×ˢ closedBall p σ
  obtain ⟨A, hA, hfactor⟩ := exists_cNorm_factor_footpoint_bounds e a p hρ hτ hσ hM
  choose C hC hc using fun j ↦ exists_cNorm_comp_le_ballImage (G := ℝ)
    e (ContinuousLinearEquiv.refl ℝ E) a p hρ hσ j hM hM
  have hlow : 0 < 1 + 2 * M := by linarith
  choose P hP hp using fun j ↦ exists_cNorm_smul_le_ballImage (F := ℝ) e a hρ j
    (mul_nonneg (hA 1).le hlow.le) (mul_nonneg (hC 1).le hlow.le)
  let B := fun j ↦ P j * (1 + A (j + 2) + C (j + 2))
  refine ⟨B, fun j ↦ mul_pos (hP j) (by linarith [hA (j + 2), hC (j + 2)]), ?_⟩
  intro U V L hU hV hL hKU hJV hBL Y c r hY hcoeff hr hm hYlow hclow hrlow j
  have hY1 : cNorm K 1 Y ≤ M := (cNorm_mono_order (by omega : 1 ≤ 3)).trans hYlow
  have hc1 : cNorm J 1 c ≤ M := (cNorm_mono_order (by omega : 1 ≤ 3)).trans hclow
  have hr1 : cNorm (closedBall p σ) 1 r ≤ M := (cNorm_mono_order (by omega : 1 ≤ 3)).trans hrlow
  let f := fun q : ℝ × E ↦ transportFactor (fun s ↦ c (s, Y q)) 0 q.1
  have hfn (i) : cNorm K i f ≤ A i * (1 + cNorm K (i + 2) Y + cNorm J (i + 2) c) :=
    hfactor U V hU hV hKU hJV Y c hY hcoeff hm hY1 hc1 i
  have hrn (i) : cNorm K i (r ∘ Y) ≤
      C i * (1 + cNorm K (i + 2) Y + cNorm (closedBall p σ) (i + 2) r) := by
    have hh := hc i U L hU hL hKU (by simpa using hBL) Y r hY hr
      (by intro q hq; simpa using (hm hq).2)
      hY1 (by simpa using hr1)
    simpa using hh
  have hf1 : cNorm K 1 f ≤ A 1 * (1 + 2 * M) := by
    apply (hfn 1).trans
    apply mul_le_mul_of_nonneg_left _ (hA 1).le
    change 1 + cNorm K 3 Y + cNorm J 3 c ≤ _
    linarith
  have hrY1 : cNorm K 1 (r ∘ Y) ≤ C 1 * (1 + 2 * M) := by
    apply (hrn 1).trans
    apply mul_le_mul_of_nonneg_left _ (hC 1).le
    change 1 + cNorm K 3 Y + cNorm (closedBall p σ) 3 r ≤ _
    linarith
  obtain ⟨W, hW, hKW, hrY, hfY⟩ :=
    pullbacks_smooth_near hτ hσ hU hV hL hKU hJV hBL hY hcoeff hr hm
  have hh := hp j W hW hKW f (r ∘ Y) hfY hrY hf1 hrY1
  change cNorm K j (transportFromFootpoint c 0 r Y) ≤ _ at hh
  apply hh.trans
  have hfi := hfn (j + 2)
  have hri := hrn (j + 2)
  simp only [Nat.add_assoc] at hfi hri
  have hy0 := cNorm_nonneg K (j + 4) Y
  have hc0 := cNorm_nonneg J (j + 4) c
  have hr0 := cNorm_nonneg (closedBall p σ) (j + 4) r
  have hi : 1 + cNorm K (j + 2) f + cNorm K (j + 2) (r ∘ Y) ≤
      (1 + A (j + 2) + C (j + 2)) *
        (1 + cNorm K (j + 4) Y + cNorm J (j + 4) c + cNorm (closedBall p σ) (j + 4) r) := by
    nlinarith [hA (j + 2), hC (j + 2),
      mul_nonneg (hA (j + 2)).le hr0, mul_nonneg (hC (j + 2)).le hc0]
  exact (mul_le_mul_of_nonneg_left hi (hP j).le).trans_eq (by dsimp [B]; ring)

end JanetCartan.NullTransport.AmplitudeTame
