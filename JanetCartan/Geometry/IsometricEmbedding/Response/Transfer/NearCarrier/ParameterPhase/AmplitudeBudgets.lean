module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ParameterPhase.AmplitudeBudgets.CarrierShift
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ParameterPhase.AmplitudeBudgets.Scaling

/-!
# Finite mixed jets of the selected carrier amplitude

The amplitude estimate of `app:ch_response:thm:response-literal-transfer`, feeding
`app:ch_response:eq:direct-envelope-profile`. We retain the two physical positions,
the normalized covector, and the carrier parameter as independent joint variables.

All analytic inputs below concern the unshifted normalized full amplitude, the
selector, and the carrier. The open set `U` is a buffer around the compact carrier
box; its three mapping hypotheses are the geometric buffer obligations. The bounds
hold everywhere on `U`, hence on every compact box contained in it. The explicit
composition and Leibniz constants contain no frequency. Actual symbol producers
must supply these primitive bounds uniformly in frequency; this file proves no
unconditional FIO envelope theorem.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer

open FourierIntegral ParameterAmplitudeBudget

variable {n r : ℕ} {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Unshifted primitive normalized full amplitude for
`app:ch_response:thm:response-literal-transfer`. -/
def normalizedFullAmplitude (A : FullAmplitude n r) (ρ : ℝ)
    (v : Euclidean n × Euclidean n × Euclidean n) :=
  A v.1 v.2.1 (ρ • v.2.2)

/-- Full normalized selected amplitude of
`app:ch_response:thm:response-literal-transfer`. -/
def normalizedParameterAmplitude (A : FullAmplitude n r)
    (q : P × Euclidean n → ℂ) (ζ : P → Euclidean n) (ρ : ℝ)
    (p : ParameterAmplitudePoint n P) :=
  q (p.2, p.1.2.2) • A p.1.1 p.1.2.1 (ρ • (ζ p.2 + p.1.2.2))

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
/-- Exact substitution `δ = ρ ε`, including the normalized selector, for
`app:ch_response:thm:response-literal-transfer`. Both physical positions may
vary with the parameter. -/
theorem normalizedParameterAmplitude_eq_parameterSelectedAmplitude
    (A : FullAmplitude n r) (q : P × Euclidean n → ℂ)
    (x y ζ ε : P → Euclidean n) {ρ : ℝ} (hρ : ρ ≠ 0) (c : P) :
    normalizedParameterAmplitude A q ζ ρ ((x c, y c, ε c), c) =
      parameterSelectedAmplitude A q x y ζ (fun d ↦ ρ • ε d) ρ c := by
  simp [normalizedParameterAmplitude, parameterSelectedAmplitude, smul_add,
    smul_smul, hρ]

/-- The explicit Leibniz constant for the mixed amplitude jets in
`app:ch_response:eq:direct-envelope-profile`. `M` bounds the primitive amplitude
jets through the required order, `Q i` bounds selector jets, and `Z` bounds positive
carrier jets. No frequency appears. -/
def parameterAmplitudeJetBudget (M : ℝ) (Q : ℕ → ℝ) (Z : ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * Q i *
    ((k - i).factorial * M * (max 1 (1 + Z)) ^ (k - i))

/-- Finite smoothness is derived from the three primitive functions, including
all selector derivatives (`app:ch_response:eq:direct-envelope-profile`). -/
theorem normalizedParameterAmplitude_contDiffOn
    {A : FullAmplitude n r} {q : P × Euclidean n → ℂ} {ζ : P → Euclidean n}
    {ρ : ℝ} {N : ℕ} {U : Set (ParameterAmplitudePoint n P)}
    {V : Set (Euclidean n × Euclidean n × Euclidean n)}
    {W : Set (P × Euclidean n)} {C : Set P}
    (hA : ContDiffOn ℝ N (normalizedFullAmplitude A ρ) V)
    (hq : ContDiffOn ℝ N q W) (hζ : ContDiffOn ℝ N ζ C)
    (hUV : MapsTo (carrierAmplitudeShift ζ) U V)
    (hUW : ∀ p ∈ U, (p.2, p.1.2.2) ∈ W) (hUC : ∀ p ∈ U, p.2 ∈ C) :
    ContDiffOn ℝ N (normalizedParameterAmplitude A q ζ ρ) U :=
  (hq.comp (selectorProjection (n := n) (P := P)).contDiff.contDiffOn hUW).smul
    (hA.comp (carrierAmplitudeShift_contDiffOn hζ hUC) hUV)

/-- Finite mixed jet bound on the open buffer of the compact carrier box, for
`app:ch_response:eq:direct-envelope-profile`. The joint derivative contains every
mixture of the two physical positions, normalized covector, and parameter.
The primitive bounds do not mention a carrier-composed amplitude. -/
theorem norm_iteratedFDeriv_normalizedParameterAmplitude_le
    {A : FullAmplitude n r} {q : P × Euclidean n → ℂ} {ζ : P → Euclidean n}
    {ρ : ℝ} {N k : ℕ} {U : Set (ParameterAmplitudePoint n P)}
    {V : Set (Euclidean n × Euclidean n × Euclidean n)}
    {W : Set (P × Euclidean n)} {C : Set P}
    (hU : IsOpen U) (hV : IsOpen V) (hW : IsOpen W) (hC : IsOpen C)
    (hA : ContDiffOn ℝ N (normalizedFullAmplitude A ρ) V)
    (hq : ContDiffOn ℝ N q W) (hζ : ContDiffOn ℝ N ζ C)
    (hUV : MapsTo (carrierAmplitudeShift ζ) U V)
    (hUW : ∀ p ∈ U, (p.2, p.1.2.2) ∈ W) (hUC : ∀ p ∈ U, p.2 ∈ C)
    {M Z : ℝ} {Q : ℕ → ℝ}
    (hAjet : ∀ i ≤ N, ∀ v ∈ V, ‖iteratedFDeriv ℝ i (normalizedFullAmplitude A ρ) v‖ ≤ M)
    (hqjet : ∀ i ≤ N, ∀ w ∈ W, ‖iteratedFDeriv ℝ i q w‖ ≤ Q i)
    (hζjet : ∀ i, 1 ≤ i → i ≤ N → ∀ c ∈ C, ‖iteratedFDeriv ℝ i ζ c‖ ≤ Z)
    (hk : k ≤ N) {p : ParameterAmplitudePoint n P} (hp : p ∈ U) :
    ‖iteratedFDeriv ℝ k (normalizedParameterAmplitude A q ζ ρ) p‖ ≤
      parameterAmplitudeJetBudget M Q Z k := by
  let f := q ∘ (selectorProjection (n := n) (P := P))
  let g := normalizedFullAmplitude A ρ ∘ carrierAmplitudeShift ζ
  have hf : ContDiffOn ℝ N f U := hq.comp (selectorProjection (n := n) (P := P)).contDiff.contDiffOn hUW
  have hg : ContDiffOn ℝ N g U :=
    hA.comp (carrierAmplitudeShift_contDiffOn hζ hUC) hUV
  have hfjet (i : ℕ) (hi : i ≤ N) : ‖iteratedFDeriv ℝ i f p‖ ≤ Q i :=
    (norm_jet_comp_contraction_le (selectorProjection (n := n) (P := P))
      norm_selectorProjection_le hW hq hi (p := p) (hUW p hp)).trans (hqjet i hi _ (hUW p hp))
  have hgjet (j : ℕ) (hj : j ≤ N) :
      ‖iteratedFDeriv ℝ j g p‖ ≤ (j.factorial : ℝ) * M * (max 1 (1 + Z)) ^ j :=
    norm_jet_comp_le hU hV (carrierAmplitudeShift_contDiffOn hζ hUC) hA hUV hj hp
      (fun i hi ↦ hAjet i (hi.trans hj) _ (hUV hp))
      (fun i hi hij ↦ norm_jet_carrierAmplitudeShift_le hC hζ (hij.trans hj) hi
        (p := p) (hUC p hp) (hζjet i hi (hij.trans hj) _ (hUC p hp)))
  have hb := norm_iteratedFDerivWithin_smul_le hf hg hU.uniqueDiffOn hp
    (n := k) (by exact_mod_cast hk)
  simp only [iteratedFDerivWithin_of_isOpen _ hU hp] at hb
  change ‖iteratedFDeriv ℝ k (fun u ↦ f u • g u) p‖ ≤ _
  refine hb.trans (Finset.sum_le_sum fun i hi ↦ ?_)
  have hiN : i ≤ N := (Finset.mem_range_succ_iff.mp hi).trans hk
  have hjN : k - i ≤ N := (Nat.sub_le k i).trans hk
  have hQi : 0 ≤ Q i := (norm_nonneg _).trans (hfjet i hiN)
  exact mul_le_mul (mul_le_mul_of_nonneg_left (hfjet i hiN) (Nat.cast_nonneg _))
    (hgjet (k - i) hjN) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hQi)

/-- Evaluated mixed directional jets obey the same budget, times the product
of direction norms. In particular one may choose any sequence of unit directions
supported in the `x`, `y`, `ε`, or `c` slots
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem norm_normalizedParameterAmplitude_mixedJet_le
    {A : FullAmplitude n r} {q : P × Euclidean n → ℂ} {ζ : P → Euclidean n}
    {ρ : ℝ} {N k : ℕ} {U : Set (ParameterAmplitudePoint n P)}
    {V : Set (Euclidean n × Euclidean n × Euclidean n)}
    {W : Set (P × Euclidean n)} {C : Set P}
    (hU : IsOpen U) (hV : IsOpen V) (hW : IsOpen W) (hC : IsOpen C)
    (hA : ContDiffOn ℝ N (normalizedFullAmplitude A ρ) V)
    (hq : ContDiffOn ℝ N q W) (hζ : ContDiffOn ℝ N ζ C)
    (hUV : MapsTo (carrierAmplitudeShift ζ) U V)
    (hUW : ∀ p ∈ U, (p.2, p.1.2.2) ∈ W) (hUC : ∀ p ∈ U, p.2 ∈ C)
    {M Z : ℝ} {Q : ℕ → ℝ}
    (hAjet : ∀ i ≤ N, ∀ v ∈ V, ‖iteratedFDeriv ℝ i (normalizedFullAmplitude A ρ) v‖ ≤ M)
    (hqjet : ∀ i ≤ N, ∀ w ∈ W, ‖iteratedFDeriv ℝ i q w‖ ≤ Q i)
    (hζjet : ∀ i, 1 ≤ i → i ≤ N → ∀ c ∈ C, ‖iteratedFDeriv ℝ i ζ c‖ ≤ Z)
    (hk : k ≤ N) {p : ParameterAmplitudePoint n P} (hp : p ∈ U) (v : Fin k → ParameterAmplitudePoint n P) :
    ‖iteratedFDeriv ℝ k (normalizedParameterAmplitude A q ζ ρ) p v‖ ≤
      parameterAmplitudeJetBudget M Q Z k * ∏ i, ‖v i‖ := by
  have hB := norm_iteratedFDeriv_normalizedParameterAmplitude_le hU hV hW hC
    hA hq hζ hUV hUW hUC hAjet hqjet hζjet hk hp
  exact ((iteratedFDeriv ℝ k (normalizedParameterAmplitude A q ζ ρ) p).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right hB (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _))

end JanetCartan.ResponseTransfer
