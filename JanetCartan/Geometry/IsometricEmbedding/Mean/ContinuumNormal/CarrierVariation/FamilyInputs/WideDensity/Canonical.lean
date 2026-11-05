module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.WideDensity.Calculus
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.DensityFootpoint

/-!
# The original density class at the actual ODE footpoints

Both physical positions in `app:ch_background:eq:bg-full-complex-amplitude`
retain their literal ODE inverse labels. The Hamilton map defining the phase
is never substituted for this inverse. The finite bounds below are uniform
over the original wider class of `paper.tex`, `app:ch_background:prop:bg-frame`.
Their primitive inputs are the footpoint bounds of `MatchedSeedCoefficients`
and the footpoint differences of `PositiveReference`.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.WideDensity
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport
open ContinuumRow CanonicalCarrier ContinuumNormalReduction.TransportSymbol
open PositiveReference ConstructedCarrierJets

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- The fixed endpoint evaluation before conic inverse substitution in
`app:ch_background:eq:bg-full-complex-amplitude`. -/
def densityEndpoint (right : Bool) (p : InputVariables n) : Euclidean n × CarrierParameter :=
  ((if right then p.1.2 else p.1.1), p.2.1)

/-- Endpoint evaluation is a fixed smooth coordinate projection; its finite
pullback constants are independent of the density and flow. Source:
`app:ch_background:eq:bg-full-complex-amplitude`. -/
theorem densityEndpoint_contDiff (right : Bool) : ContDiff ℝ ∞ (@densityEndpoint n right) := by
  cases right
  · exact (contDiff_fst.fst).prodMk contDiff_snd.fst
  · exact (contDiff_fst.snd).prodMk contDiff_snd.fst

/-- The two literal ODE footpoints of the canonical input density in
`app:ch_background:eq:bg-full-complex-amplitude`. -/
def canonicalDensityPair
    (v : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3) :
    InputVariables n → ℝ :=
  densityPair v (fun b ↦ densityFootpoint T Y ∘ densityEndpoint b)

/-- The original pointwise density range gives a positive lower and upper
bound for the product of BOTH factors. No smallness around zero is required.
Source: `app:ch_background:prop:bg-frame`. -/
theorem canonicalDensityPair_bounds
    (v : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (p : InputVariables n)
    (hv : ∀ b, (1 / 2 : ℝ) ≤ 1 + v (densityFootpoint T Y (densityEndpoint b p)) ∧
      1 + v (densityFootpoint T Y (densityEndpoint b p)) ≤ 3 / 2) :
    (1 / 4 : ℝ) ≤ canonicalDensityPair T v Y p ∧ canonicalDensityPair T v Y p ≤ 9 / 4 := by
  have hl := hv false
  have hr := hv true
  dsimp [canonicalDensityPair, densityPair]
  constructor
  · nlinarith [mul_le_mul hl.1 hr.1 (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by linarith : 0 ≤ 1 + v (densityFootpoint T Y (densityEndpoint false p)))]
  · nlinarith [mul_le_mul hl.2 hr.2
      (by linarith : 0 ≤ 1 + v (densityFootpoint T Y (densityEndpoint true p)))
      (by norm_num : (0 : ℝ) ≤ 3 / 2)]

/-- Identification with the actual canonical carrier, including its two
normal factors, masks and Jacobian division. This uses the literal scalar
initial-value formula, not an amplitude factorization premise. Source:
`app:ch_background:eq:bg-T`, `app:ch_background:eq:bg-full-complex-amplitude`. -/
theorem canonical_inputDensity_eq_densityPair {N : ℕ}
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)
    (v : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (J : InputVariables n → ℝ) (p : InputVariables n)
    (hv : ∀ b, 0 ≤ 1 + v (densityFootpoint T Y (densityEndpoint b p))) :
    let a := fun initial ↦ TransportKernel.coefficientsOfCarrier
      (data T Q F row col Φ Y initial hr hcell angular high) (FixedCutoffs.physical hr 1)
    inputDensity (a (fun q ↦ Real.sqrt (1 + v q))) J p =
      canonicalDensityPair T v Y p • inputDensity (a (fun _ ↦ 1)) J p := by
  apply canonical_inputDensity_sqrtDensity T Q F row col Φ Y hr hcell angular high v J p
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · exact hv false
  · have hx' := Set.mem_singleton_iff.mp hx
    subst x
    exact hv true

/-- The wider multiplier acts on the prescribed initial scalar, including
the actual source scalar `σ`. Both ODE factors multiply the same unperturbed
canonical density; no normalization of the initial scalar to one is needed.
Source: `app:ch_background:prop:bg-frame`, `app:ch_background:eq:bg-Nsigma`,
`app:ch_background:eq:bg-full-complex-amplitude`. -/
theorem canonical_inputDensity_initial_mul_sqrtDensity {N : ℕ}
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)
    (initial v : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (J : InputVariables n → ℝ) (p : InputVariables n)
    (hv : ∀ b, 0 ≤ 1 + v (densityFootpoint T Y (densityEndpoint b p))) :
    let a := fun initial ↦ TransportKernel.coefficientsOfCarrier
      (data T Q F row col Φ Y initial hr hcell angular high) (FixedCutoffs.physical hr 1)
    inputDensity (a (fun q ↦ initial q * Real.sqrt (1 + v q))) J p =
      canonicalDensityPair T v Y p • inputDensity (a initial) J p := by
  dsimp only
  rw [canonical_inputDensity_initial T Q F row col Φ Y hr hcell angular high
      (fun q ↦ initial q * Real.sqrt (1 + v q)) J p,
    canonical_inputDensity_initial T Q F row col Φ Y hr hcell angular high initial J p]
  change ((initial (densityFootpoint T Y (densityEndpoint false p)) *
      Real.sqrt (1 + v (densityFootpoint T Y (densityEndpoint false p)))) ^ 2 *
      (initial (densityFootpoint T Y (densityEndpoint true p)) *
      Real.sqrt (1 + v (densityFootpoint T Y (densityEndpoint true p)))) ^ 2) • _ = _
  rw [mul_pow, mul_pow, Real.sq_sqrt (hv false), Real.sq_sqrt (hv true), smul_smul]
  congr 1
  dsimp [canonicalDensityPair, densityPair, densityEndpoint, densityFootpoint,
    densityCoordinates]
  ring

/-- Fixed compact endpoint projections transfer the proved primitive ODE
footpoint differences to BOTH density factors. All constants precede `v`,
both flows and `d`. The one extra density derivative is part of the original
fixed low reserve. Consumer: the positive-reference assembly below and the
full-amplitude comparison after inverse substitution. Source:
`app:ch_background:prop:bg-normalized`, `app:ch_osc:prop:osc-normal`, Step 4'. -/
theorem exists_densityPair_endpoint_sub_bound
    {K : Set (InputVariables n)} {S : Set (Euclidean n × CarrierParameter)}
    {L : Set (Euclidean (n - 1) × Euclidean 3)}
    (hK : IsCompact K) (hS : IsCompact S) (hL : IsCompact L) (hconv : Convex ℝ L)
    (hKS : ∀ b, MapsTo (densityEndpoint b) K S) (m : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    ∃ C > 0, ∀ (v : Euclidean (n - 1) × Euclidean 3 → ℝ)
      (Y Y₀ : Euclidean n × CarrierParameter → Euclidean (n - 1) × Euclidean 3)
      (d : ℝ), 0 ≤ d →
      (∀ q ∈ L, ContDiffAt ℝ ∞ v q) → cNorm L (m + 1) v ≤ 1 →
      (∀ q ∈ S, ContDiffAt ℝ ∞ (Y) q) →
      (∀ q ∈ S, ContDiffAt ℝ ∞ (Y₀) q) →
      MapsTo (Y) S L → MapsTo (Y₀) S L →
      cNorm S m (Y) ≤ B → cNorm S m (Y₀) ≤ B →
      cNorm S m (Y - Y₀) ≤ d →
      (∀ p ∈ K, ContDiffAt ℝ ∞ (densityPair v (fun b ↦ Y ∘ densityEndpoint b)) p ∧
        ContDiffAt ℝ ∞ (densityPair v (fun b ↦ Y₀ ∘ densityEndpoint b)) p) ∧
      cNorm K m (densityPair v (fun b ↦ Y ∘ densityEndpoint b)) ≤ C ∧
      cNorm K m (densityPair v (fun b ↦ Y₀ ∘ densityEndpoint b)) ≤ C ∧
      cNorm K m (densityPair v (fun b ↦ Y ∘ densityEndpoint b) - densityPair v (fun b ↦ Y₀ ∘ densityEndpoint b)) ≤ C * d := by
  have hpull (b : Bool) := exists_cNorm_fixed_pullback_le
    (G := Euclidean (n - 1) × Euclidean 3) hK hS
    (fun _ _ ↦ (densityEndpoint_contDiff b).contDiffAt) (hKS b)
  choose A hA hpull using hpull
  let M := A false m + A true m
  have hM : 0 < M := add_pos (hA false m) (hA true m)
  have hAM (b : Bool) : A b m ≤ M := by cases b <;> dsimp [M] <;> linarith [hA false m, hA true m]
  obtain ⟨C, hC, hpair⟩ := exists_densityPair_sub_bound hK hL hconv m (mul_nonneg hM.le hB)
  refine ⟨1 + C + C * M, by positivity, ?_⟩
  intro v Y Y₀ d hd hv hvm hY hY₀ hr hr₀ hm hm₀ hdiff
  have hpb (Z) (hZ : ∀ q ∈ S, ContDiffAt ℝ ∞ (Z) q)
      (hZm : cNorm S m (Z) ≤ B) (b : Bool) :
      cNorm K m (Z ∘ densityEndpoint b) ≤ M * B :=
    (hpull b (Z) hZ m).trans
      (mul_le_mul (hAM b) hZm (cNorm_nonneg ..) hM.le)
  have hdif (b : Bool) :
      cNorm K m (Y ∘ densityEndpoint b -
        Y₀ ∘ densityEndpoint b) ≤ M * d :=
    (hpull b (Y - Y₀)
      (fun q hq ↦ (hY q hq).sub (hY₀ q hq)) m).trans
        (mul_le_mul (hAM b) hdiff (cNorm_nonneg ..) hM.le)
  have hb := hpair v (fun b ↦ Y ∘ densityEndpoint b)
    (fun b ↦ Y₀ ∘ densityEndpoint b) (M * d) (mul_nonneg hM.le hd)
    hv hvm (fun b p hp ↦ (hY _ (hKS b hp)).comp p (densityEndpoint_contDiff b).contDiffAt)
    (fun b p hp ↦ (hY₀ _ (hKS b hp)).comp p (densityEndpoint_contDiff b).contDiffAt)
    (fun b ↦ hr.comp (hKS b)) (fun b ↦ hr₀.comp (hKS b))
    (hpb Y hY hm) (hpb Y₀ hY₀ hm₀) hdif
  exact ⟨hb.1, hb.2.1.trans (by nlinarith), hb.2.2.1.trans (by nlinarith),
    hb.2.2.2.trans (by nlinarith)⟩


/-- Specialize the fixed endpoint estimate to the literal ODE density labels.
The primitive ranges, finite bounds and differences are supplied by the same
source or positive-reference flow constructors. Source:
`app:ch_background:eq:bg-full-complex-amplitude`. -/
theorem exists_canonicalDensityPair_sub_bound
    {K : Set (InputVariables n)} {S : Set (Euclidean n × CarrierParameter)}
    {L : Set (Euclidean (n - 1) × Euclidean 3)}
    (hK : IsCompact K) (hS : IsCompact S) (hL : IsCompact L) (hconv : Convex ℝ L)
    (hKS : ∀ b, MapsTo (densityEndpoint b) K S) (m : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    ∃ C > 0, ∀ (v : Euclidean (n - 1) × Euclidean 3 → ℝ)
      (Y Y₀ : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
      (d : ℝ), 0 ≤ d →
      (∀ q ∈ L, ContDiffAt ℝ ∞ v q) → cNorm L (m + 1) v ≤ 1 →
      (∀ q ∈ S, ContDiffAt ℝ ∞ (densityFootpoint T Y) q) →
      (∀ q ∈ S, ContDiffAt ℝ ∞ (densityFootpoint T Y₀) q) →
      MapsTo (densityFootpoint T Y) S L → MapsTo (densityFootpoint T Y₀) S L →
      cNorm S m (densityFootpoint T Y) ≤ B → cNorm S m (densityFootpoint T Y₀) ≤ B →
      cNorm S m (densityFootpoint T Y - densityFootpoint T Y₀) ≤ d →
      (∀ p ∈ K, ContDiffAt ℝ ∞ (canonicalDensityPair T v Y) p ∧
        ContDiffAt ℝ ∞ (canonicalDensityPair T v Y₀) p) ∧
      cNorm K m (canonicalDensityPair T v Y) ≤ C ∧
      cNorm K m (canonicalDensityPair T v Y₀) ≤ C ∧
      cNorm K m (canonicalDensityPair T v Y - canonicalDensityPair T v Y₀) ≤ C * d := by
  obtain ⟨C, hC, hb⟩ := exists_densityPair_endpoint_sub_bound hK hS hL hconv hKS m hB
  exact ⟨C, hC, fun v Y Y₀ d ↦ hb v (densityFootpoint T Y) (densityFootpoint T Y₀) d⟩

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.WideDensity
