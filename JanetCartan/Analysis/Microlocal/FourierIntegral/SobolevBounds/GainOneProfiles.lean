module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.GainOneProfiles.LocalProfiles

/-!
# Normalized original primitive profiles for Sobolev gain one

`exists_finiteGainOne_primitive_inputs` supplies exactly the three original
primitive hypotheses in `exists_graph_gain_one_constant_of_primitive_profiles`;
the amplitude and scalar conclusions also supply its literal-adjoint counterpart.
The amplitude is normalized as `R • A(x,y,Rη)`, with a supremum over all `R ≥ 1`.
The phase convention agrees with `R⁻¹ S(x,Rη)` by
`PrimitiveProfiles.cNorm_normalizedPhase_eq`. The fixed high shift is `μ₀+2`
relative to the output order `t+1`; the low phase baseline is `μ₀+3`.

Individual interpolation, the physical frequency weights, and high inverse jets
are proved. The constants precede the phase, amplitude, and high seminorms.
The case `t=0` uses only the fixed enlarged low baseline. Both physical positions,
all masks, the matrix Frobenius norm, and the physical covector order are retained.

The geometric finite cover, ordinary smoothness, positive phase homogeneity,
symbol-class finiteness, fixed low bounds, and actual zeroth-order inverse gap
remain inputs from the phase and carrier constructions. The parent retains
operator realization, low L² estimates, and substitution into `GainOneAssembly`.
Source: Step 3 before `app:ch_regular_base:eq:fio-input` and the gain-one paragraph
following `app:ch_regular_base:eq:graph-derivative-transfer`.
-/

@[expose] public noncomputable section
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.GainOneProfiles
open FullAmplitudePrimitiveBudget FullAmplitudePrimitiveBudget.Local FirstOutputJets
open PrimitiveProfiles GainOneBranches
variable {n r : ℕ} {ι : Type*} [Fintype ι]

/-- The manuscript's actual `1 + |A|_{-1,j} + |S|_j` on a fixed finite
normalized cover. Source: `app:ch_regular_base:eq:fio-input`, gain one. -/
def normalizedGainOneHigh (z : ι → Point n) (δ : ι → ℝ) (j : ℕ)
    (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r) : ℝ :=
  1 + (∑ i, orderMinusOneSeminorm (Metric.closedBall (z i) (δ i)) j A) +
    ∑ i, cNorm (Metric.closedBall (z i) (δ i)) j (fun p : Point n ↦ S p.1.1 p.2)

/-- Positivity of the normalized gain-one high quantity
(`app:ch_regular_base:eq:fio-input`). -/
theorem one_le_normalizedGainOneHigh (z : ι → Point n) (δ : ι → ℝ) (j : ℕ)
    (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r) :
    1 ≤ normalizedGainOneHigh z δ j S A := by
  have ha := Finset.sum_nonneg (s := Finset.univ)
    (fun i _ ↦ orderMinusOneSeminorm_nonneg (Metric.closedBall (z i) (δ i)) j A)
  have hs := Finset.sum_nonneg (s := Finset.univ)
    (fun i _ ↦ cNorm_nonneg (Metric.closedBall (z i) (δ i)) j
      (fun p : Point n ↦ S p.1.1 p.2))
  unfold normalizedGainOneHigh
  linarith

/-- Finite normalized charts produce the exact original primitive inputs for
both gain-one assembly theorems. The constants `P` and `C` depend only on the
fixed geometry, low bounds, inverse gap, and orders, and precede `S`, `A`, and
all high seminorms. The fixed shift is `μ = μ₀+2`, independent of `t`.
The geometric comparison `ρ ≤ R ≤ cρ` gives the order-minus-one amplitude,
order-one phase, and order-zero scalar weights. Interpolation and actual high
inverse jets are conclusions of the construction, not premises.
Source: gain one after `app:ch_regular_base:eq:graph-derivative-transfer`.

The carrier `T` is `(X₀ ×ˢ Y₀) ×ˢ F₀` for the forward consumer and `K₀ ×ˢ F₀`
for the literal adjoint. The phase/carrier producers owe the listed geometric
and low analytic inputs; the parent owes the final operator instantiation. -/
theorem exists_finiteGainOne_primitive_inputs
    (z : ι → Point n) (δ : ι → ℝ) (hδ : ∀ i, 0 < δ i)
    (U : ι → Set (Point n)) {V : Set (Point n)}
    (hU : ∀ i, IsOpen (U i)) (hV : IsOpen V)
    (hball : ∀ i, Metric.closedBall (z i) (δ i) ⊆ U i)
    (hrad : ∀ i, ∀ R : ℝ, 1 ≤ R → ∀ p ∈ U i, (p.1, R • p.2) ∈ V)
    {X D : Set (Euclidean n)} (hX : IsOpen X) (hD : IsOpen D)
    (hchart : ∀ p ∈ V, p.1.1 ∈ X ∧ p.2 ∈ D)
    (hcone : ∀ R : ℝ, 0 < R → ∀ η ∈ D, R • η ∈ D)
    (μ₀ : ℕ) {M : ℝ} (hM : 0 ≤ M) (B c : ℝ) (hc : 1 ≤ c) :
    ∀ t : ℕ, ∃ P C : ℝ, 1 ≤ P ∧ 1 ≤ C ∧
      ∀ (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r),
      ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D) →
      (∀ R : ℝ, 0 < R → ∀ x ∈ X, ∀ η ∈ D, S x (R • η) = R * S x η) →
      (∀ p ∈ V, IsUnit (mixedPhaseMatrix S p.1.1 p.2).det) →
      (∀ i, ∀ p ∈ Metric.closedBall (z i) (δ i), ‖(mixedPhaseMatrix S p.1.1 p.2)⁻¹‖ ≤ B) →
      ContDiffOn ℝ ∞ (uncurry A) V →
      (∀ i j, BoundedOrderMinusOneSeminorm (Metric.closedBall (z i) (δ i)) j A) →
      (∀ i, cNorm (Metric.closedBall (z i) (δ i)) (μ₀ + 3)
        (fun p : Point n ↦ S p.1.1 p.2) ≤ M) →
      (∀ i, orderMinusOneSeminorm (Metric.closedBall (z i) (δ i)) (μ₀ + 1) A ≤ M) →
      let H := C * normalizedGainOneHigh z δ (t + 1 + (μ₀ + 2)) S A
      1 ≤ H ∧ ∀ (T : Set (Point n)) (ρ : Euclidean n → ℝ), (∀ η, 1 ≤ ρ η) →
        (∀ p ∈ T, ∃ i, ∃ R : ℝ, 1 ≤ R ∧ ∃ v ∈ Metric.closedBall (z i) (δ i),
          p = (v.1, R • v.2) ∧ ρ p.2 ≤ R ∧ R ≤ c * ρ p.2) →
        (∀ p ∈ T, ∀ w : List (Coordinate n), w.length ≤ μ₀ + (t + 1) →
          (ρ p.2) ^ frequencyOrder w * ‖uncurry (jet w A) p‖ ≤
            P * profile (μ₀ + 1) t H w.length / ρ p.2) ∧
        (∀ p ∈ T, ∀ w : List (Coordinate n), w.length ≤ μ₀ + (t + 1) →
          (ρ p.2) ^ frequencyOrder w * ‖uncurry (jet w (phasePrimitive S)) p‖ ≤
            P * profile (μ₀ + 1) t H w.length * ρ p.2) ∧
        (∀ p ∈ T, ∀ a (w : List (Coordinate n)), w.length ≤ μ₀ + (t + 1) →
          (ρ p.2) ^ frequencyOrder w * ‖uncurry (jet w (scalarPrimitive S a)) p‖ ≤
            P * profile (μ₀ + 1) t H w.length) := by
  classical
  intro t
  choose P C hP hC hb using fun i ↦ exists_localGainOne_profiles (r := r)
    (z i) (hδ i) (hU i) (hball i) (hrad i) hX hD hchart hcone μ₀ t hM B
  let Psum := 1 + ∑ i, P i
  let Csum := 1 + ∑ i, C i
  have hPn (i) := zero_le_one.trans (hP i)
  have hCn (i) := zero_le_one.trans (hC i)
  have hPsum : 1 ≤ Psum := by
    dsimp [Psum]
    linarith [Finset.sum_nonneg (s := Finset.univ) (fun i _ ↦ hPn i)]
  have hCsum : 1 ≤ Csum := by
    dsimp [Csum]
    linarith [Finset.sum_nonneg (s := Finset.univ) (fun i _ ↦ hCn i)]
  have hPi (i : ι) : P i ≤ Psum := by
    have he := Finset.single_le_sum (fun i _ ↦ hPn i) (Finset.mem_univ i)
    dsimp [Psum]
    linarith
  have hCi (i : ι) : C i ≤ Csum := by
    have he := Finset.single_le_sum (fun i _ ↦ hCn i) (Finset.mem_univ i)
    dsimp [Csum]
    linarith
  have hPi' (i : ι) : P i ≤ c * Psum :=
    (hPi i).trans (le_mul_of_one_le_left (zero_le_one.trans hPsum) hc)
  refine ⟨c * Psum, Csum, one_le_mul_of_one_le_of_one_le hc hPsum, hCsum, ?_⟩
  intro S A hS hhom hinv hgap hA hbA hlowS hlowA
  dsimp only
  let k := t + 1 + (μ₀ + 2)
  let H := Csum * normalizedGainOneHigh z δ k S A
  have hH : 1 ≤ H := one_le_mul_of_one_le_of_one_le hCsum (one_le_normalizedGainOneHigh _ _ _ _ _)
  have hlocal (i : ι) := hb i S A hS hhom hinv (hgap i) hA (hbA i) (hlowS i) (hlowA i)
  have hHi (i : ι) : C i *
      (1 + orderMinusOneSeminorm (Metric.closedBall (z i) (δ i)) k A +
        cNorm (Metric.closedBall (z i) (δ i)) k (fun p : Point n ↦ S p.1.1 p.2)) ≤ H := by
    have ha := Finset.single_le_sum
      (fun i _ ↦ orderMinusOneSeminorm_nonneg (Metric.closedBall (z i) (δ i)) k A)
      (Finset.mem_univ i)
    have hs := Finset.single_le_sum
      (fun i _ ↦ cNorm_nonneg (Metric.closedBall (z i) (δ i)) k
        (fun p : Point n ↦ S p.1.1 p.2)) (Finset.mem_univ i)
    apply mul_le_mul (hCi i) _
      (add_nonneg (add_nonneg zero_le_one (orderMinusOneSeminorm_nonneg _ _ _))
        (cNorm_nonneg _ _ _)) (zero_le_one.trans hCsum)
    exact add_le_add (add_le_add (le_refl 1) ha) hs
  have hprofiles (i : ι) := hlocal i H hH (hHi i)
  have hSP : ContDiffOn ℝ ∞ (fun p : Point n ↦ S p.1.1 p.2) V := by
    intro p hp
    exact ((hS.contDiffAt ((hX.prod hD).mem_nhds (hchart p hp))).comp p
      (contDiffAt_fst.fst.prodMk contDiffAt_snd)).contDiffWithinAt
  have hUV (i : ι) : U i ⊆ V := by intro p hp; simpa using hrad i 1 le_rfl p hp
  refine ⟨hH, ?_⟩
  intro T ρ hρ hcover
  refine ⟨?_, ?_, ?_⟩
  · intro p hp w hw
    obtain ⟨i, R, hR, v, hv, rfl, hρR, _⟩ := hcover p hp
    have hρpos : 0 < ρ (R • v.2) := lt_of_lt_of_le zero_lt_one (hρ _)
    apply (weighted_amplitude_jet_le (z i) (hU i) hV (hball i) (hrad i)
      hA hR hρpos hρR hv w).trans
    apply div_le_div_of_nonneg_right _ hρpos.le
    exact ((hprofiles i).1 R hR w.length (by omega)).trans
      (mul_le_mul_of_nonneg_right (hPi' i) (profile_nonneg _ _ _ hH))
  · intro p hp w hw
    obtain ⟨i, R, hR, v, hv, rfl, hρR, hRc⟩ := hcover p hp
    apply (weighted_phase_jet_le (z i) (hU i) hV (hball i) (hrad i) hSP
      (fun R hR p hp ↦ hhom R hR p.1.1 (hchart p (hUV i hp)).1 p.2
        (hchart p (hUV i hp)).2)
      hR (zero_le_one.trans (hρ _)) hρR hRc hv w).trans
    apply mul_le_mul_of_nonneg_right _ (zero_le_one.trans (hρ _))
    calc
      _ ≤ c * (P i * profile (μ₀ + 1) t H w.length) :=
        mul_le_mul_of_nonneg_left ((hprofiles i).2.1 w.length (by omega)) (zero_le_one.trans hc)
      _ ≤ c * (Psum * profile (μ₀ + 1) t H w.length) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (hPi i) (profile_nonneg _ _ _ hH)) (zero_le_one.trans hc)
      _ = _ := by ring
  · intro p hp a w hw
    obtain ⟨i, R, hR, v, hv, rfl, hρR, _⟩ := hcover p hp
    have hreg (j : ℕ) := normalized_scalarPrimitive_regular hX hD hcone hS hhom
      (hU i) (hball i) (fun p hp ↦ hchart p (hUV i hp))
      (fun p hp ↦ hinv p (hUV i hp)) a j
    have hj := weighted_jet_le_normalizedSeminorm (z i) (hU i) hV (hball i)
      (contDiffOn_joint_scalarPrimitive hX hD hS hchart hinv a)
      (fun R hR ↦ contDiffOn_normalizedField_of_dilations
        (contDiffOn_joint_scalarPrimitive hX hD hS hchart hinv a) (hrad i) hR)
      w (hreg w.length).2.1 hR v hv (hrad i R hR v (hball i hv))
    apply (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (zero_le_one.trans (hρ _)) hρR _) (norm_nonneg _)).trans
    exact hj.trans (((hprofiles i).2.2 a w.length (by omega)).trans
      (mul_le_mul_of_nonneg_right (hPi' i) (profile_nonneg _ _ _ hH)))

end JanetCartan.FourierIntegral.GainOneProfiles
