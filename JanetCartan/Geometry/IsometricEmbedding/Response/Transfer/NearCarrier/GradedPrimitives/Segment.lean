module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.GradedPrimitives.Calculus
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ParameterPhase.CoefficientBudgets.Segment
public import JanetCartan.Analysis.Calculus.CompactParameterIntegral

/-!
# Reserve-graded normalized segment averages

The averages of the primitive mixed Hessian and covector Hessian produce `B`
and `C` in `app:ch_response:eq:direct-envelope-profile`. All derivatives here
are joint in `(x, ε, c)`. The carrier has fixed jets, while the primitive
Hessian has the scale profile. The actual segment stays in the buffered convex
chart. Smoothness and derivative bounds for the integral are conclusions.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff

namespace JanetCartan.ResponseTransfer.GradedPrimitives

variable {n p : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F]

/-- The literal normalized segment integral used for both coefficients in
`app:ch_response:thm:response-literal-transfer`. -/
def normalizedSegmentAverage (H : Euclidean n × Euclidean n → F)
    (ζ : Euclidean p → Euclidean n) (q : ParameterCoefficientSpace n p) : F :=
  ∫ t in (0 : ℝ)..1, H (q.1, ζ q.2.2 + t • q.2.1)

/-- Fixed finite carrier-composition constant for
`app:ch_response:eq:direct-envelope-profile`. -/
def segmentConstant (A : ℕ → ℝ) (Z : ℝ) (k : ℕ) : ℝ :=
  compositionConstant A (fun j ↦ (1 + Z) ^ j) k

/-- Nonnegativity of the segment constant. Source:
`app:ch_response:eq:direct-envelope-profile`. -/
theorem segmentConstant_nonneg {A : ℕ → ℝ} (hA : ∀ j, 0 ≤ A j)
    {Z : ℝ} (hZ : 0 ≤ Z) (k : ℕ) : 0 ≤ segmentConstant A Z k :=
  compositionConstant_nonneg hA (fun _ ↦ pow_nonneg (by linarith) _) k

section
variable {H : Euclidean n × Euclidean n → F} {ζ : Euclidean p → Euclidean n}
  {X D V : Set (Euclidean n)} {C : Set (Euclidean p)}
  (hX : IsOpen X) (hD : IsOpen D) (hV : IsOpen V) (hC : IsOpen C)
  (hcD : Convex ℝ D) (hζD : ∀ c ∈ C, ζ c ∈ D)
  (hbuffer : ∀ c ∈ C, ∀ ε ∈ V, ζ c + ε ∈ D)
  (hH : ContDiffOn ℝ ∞ H (X ×ˢ D)) (hζ : ContDiffOn ℝ ∞ ζ C)

include hX hD hC hcD hζD hbuffer hH hζ in
omit [CompleteSpace F] in
/-- Smoothness of the actual joint segment integrand on the buffer, for
`app:ch_response:eq:direct-envelope-profile`. -/
theorem segmentIntegrand_contDiffAt {z : ℝ × ParameterCoefficientSpace n p}
    (hz : z ∈ Icc (0 : ℝ) 1 ×ˢ (X ×ˢ V ×ˢ C)) :
    ContDiffAt ℝ ∞ (fun w : ℝ × ParameterCoefficientSpace n p ↦
      H (w.2.1, ζ w.2.2.2 + w.1 • w.2.2.1)) z := by
  have hmem : (z.2.1, ζ z.2.2.2 + z.1 • z.2.2.1) ∈ X ×ˢ D :=
    ⟨hz.2.1, hcD.add_smul_mem (hζD _ hz.2.2.2)
      (hbuffer _ hz.2.2.2 _ hz.2.2.1) hz.1⟩
  exact (hH.contDiffAt ((hX.prod hD).mem_nhds hmem)).comp z
    (contDiffAt_snd.fst.prodMk
      (((hζ.contDiffAt (hC.mem_nhds hz.2.2.2)).comp z contDiffAt_snd.snd.snd).add
        (contDiffAt_fst.smul contDiffAt_snd.snd.fst)))

include hX hD hV hC hcD hζD hbuffer hH hζ

/-- The normalized average is smooth as a consequence of primitive
smoothness and compact integration
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem normalizedSegmentAverage_contDiffOn :
    ContDiffOn ℝ ∞ (normalizedSegmentAverage H ζ) (X ×ˢ V ×ˢ C) := by
  apply contDiffOn_fixedIntervalIntegral (a := 0) (b := 1)
    (F := fun w : ℝ × ParameterCoefficientSpace n p ↦
      H (w.2.1, ζ w.2.2.2 + w.1 • w.2.2.1)) (hX.prod (hV.prod hC))
  exact fun z hz ↦ segmentIntegrand_contDiffAt hX hD hC hcD hζD hbuffer hH hζ (by simpa using hz)

omit [CompleteSpace F] hV in
/-- The normalized segment composition preserves the primitive reserve and
uses carrier jets only through the requested order
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem norm_jet_segmentIntegrand_le {N k R : ℕ} {A : ℕ → ℝ} {Z L : ℝ}
    (hA : ∀ j, 0 ≤ A j) (hZ : 0 ≤ Z) (hL : 1 ≤ L)
    (hHjet : ∀ j ≤ N, ∀ w ∈ X ×ˢ D, ‖iteratedFDeriv ℝ j H w‖ ≤ A j * L ^ (j - R))
    (hζjet : ∀ j, 1 ≤ j → j ≤ N → ∀ c ∈ C, ‖iteratedFDeriv ℝ j ζ c‖ ≤ Z)
    (hk : k ≤ N) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    {q : ParameterCoefficientSpace n p} (hq : q ∈ X ×ˢ V ×ˢ C) :
    ‖iteratedFDeriv ℝ k (fun w : ParameterCoefficientSpace n p ↦
      H (w.1, ζ w.2.2 + t • w.2.1)) q‖ ≤ segmentConstant A Z k * L ^ (k - R) := by
  let f : ParameterCoefficientSpace n p → Euclidean n × Euclidean n :=
    fun w ↦ (w.1, ζ w.2.2 + t • w.2.1)
  have hf : ContDiffAt ℝ N f q :=
    (contDiffAt_fst.prodMk
      (((hζ.contDiffAt (hC.mem_nhds hq.2.2)).comp q contDiffAt_snd.snd).add
        (contDiffAt_snd.fst.const_smul t))).of_le (by simp)
  have hmem : f q ∈ X ×ˢ D :=
    ⟨hq.1, hcD.add_smul_mem (hζD _ hq.2.2) (hbuffer _ hq.2.2 _ hq.2.1) ht⟩
  exact norm_jet_comp_fixed_inner_le hf
    ((hH.contDiffAt ((hX.prod hD).mem_nhds hmem)).of_le (by simp)) hk A
    (fun j ↦ (1 + Z) ^ j) hA (fun _ ↦ pow_nonneg (by linarith) _) hL R
    (fun j hj ↦ hHjet j (hj.trans hk) _ hmem)
    (fun j hj hjk ↦ norm_parameterCoefficient_segment_jet_le hC hζ hq.2.2 hj hZ
      (hζjet j hj (hjk.trans hk) _ hq.2.2) ht)

omit [CompleteSpace F] in
/-- The actual normalized segment integral retains the reserve. Bounds on
the primitive Hessian and fixed carrier jets justify differentiating under
the integral, rather than assuming coefficient jets. Source:
`app:ch_response:eq:direct-envelope-profile`. -/
theorem norm_jet_normalizedSegmentAverage_le {N k R : ℕ} {A : ℕ → ℝ} {Z L : ℝ}
    (hA : ∀ j, 0 ≤ A j) (hZ : 0 ≤ Z) (hL : 1 ≤ L)
    (hHjet : ∀ j ≤ N, ∀ w ∈ X ×ˢ D, ‖iteratedFDeriv ℝ j H w‖ ≤ A j * L ^ (j - R))
    (hζjet : ∀ j, 1 ≤ j → j ≤ N → ∀ c ∈ C, ‖iteratedFDeriv ℝ j ζ c‖ ≤ Z)
    (hk : k ≤ N) {q : ParameterCoefficientSpace n p} (hq : q ∈ X ×ˢ V ×ˢ C) :
    ‖iteratedFDeriv ℝ k (normalizedSegmentAverage H ζ) q‖ ≤
      segmentConstant A Z k * L ^ (k - R) := by
  have he := NormalComparison.iteratedFDeriv_unitIntervalIntegral
    (H := fun w : ℝ × ParameterCoefficientSpace n p ↦
      H (w.2.1, ζ w.2.2.2 + w.1 • w.2.2.1))
    (B := fun j ↦ segmentConstant A Z j * L ^ (j - R)) (hX.prod (hV.prod hC))
    (fun z hz ↦ segmentIntegrand_contDiffAt hX hD hC hcD hζD hbuffer hH hζ hz)
    (fun j hj t ht w hw ↦ norm_jet_segmentIntegrand_le hX hD hC hcD hζD hbuffer
      hH hζ hA hZ hL hHjet hζjet (hj.trans hk) ht hw) hq
  change ‖iteratedFDeriv ℝ k (fun w ↦ ∫ t in (0 : ℝ)..1,
    H (w.1, ζ w.2.2 + t • w.2.1)) q‖ ≤ _
  rw [he]
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (fun t ht ↦ norm_jet_segmentIntegrand_le hX hD hC hcD hζD hbuffer hH hζ
      hA hZ hL hHjet hζjet hk (by simpa using uIoc_subset_uIcc ht) hq)

end
end JanetCartan.ResponseTransfer.GradedPrimitives
