module
public import JanetCartan.Analysis.Microlocal.InitialSignedChainSource.Sampled
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.ComplexSource
public import JanetCartan.Iteration.PhysicalInitialization.OriginalSampledObserved

/-! # The first-mask estimate at the supplied pair's TRUE frequency

Apply the signed reduced local accuracy theorem directly, with ONE already
specified label, frequency and normalized scalar; unlike the sampled
existential corollary, this proof does not select a signed pair or frequency.
The real measured source may be given by its genuine `zeroExtend` equality;
there is no assumption that its inner bump equals one on its own support.
`app:ch_regular:eq:source-tail`, `app:ch_pairs:prop:pairs-lag-sum`.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 520000
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology NNReal ENNReal ComplexConjugate Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.PhysicalPairs.SampledMask
open LocalSobolev SmallSupport SignedPairs InitialSignedChainSource InitialSourceLocalization
open Sampling.BackgroundModulation ResponseSourceExtension ResponseTransfer.SourceNegative
open RegularSector.Characteristic.RetardedLocalization ArbitraryAccuracy ArbitraryAccuracy.ResidualLocalization ArbitraryAccuracy.SelectedLocalization
open PhysicalInitialization.OriginalSampledObserved
local instance : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩
variable {d N : ℕ}
local notation "E" => Euclidean (d+1)
local notation "CV" => EuclideanSpace ℂ (Fin (d+1))
local notation "RV" => EuclideanSpace ℝ (Fin (d+1))

/-- Normalized representative of the SUPPLIED signed pair, with its actual beat. -/
def normalized {G : Type} {Z : G → Set (Euclidean 3)} (q : Pair G (Euclidean 3) Z)
    (Φ : G → E × Euclidean 3 → ℝ) : E → ℝ := fun x ↦ q.vector (fun g z ↦ Φ g (x,z))/q.beat

theorem normalization {G : Type} {Z : G → Set (Euclidean 3)} (hZ : ∀ g, Convex ℝ (Z g))
    (q : Pair G (Euclidean 3) Z) (Φ : G → E × Euclidean 3 → ℝ) (hΦ : ∀ g, ContDiff ℝ ∞ (Φ g))
    (raw : G → Euclidean 3 → E → ℝ) {S : Set E}
    (he : ∀ g v, v ∈ S ×ˢ Z g → Φ g =ᶠ[𝓝 v] fun w ↦ raw g w.2 w.1)
    {L : ℝ} (hL : 1 ≤ L) (P : ℕ → ℝ) (hP : ∀ m, 0 ≤ P m)
    (hj : ∀ g v, v ∈ S ×ˢ Z g → ∀ m, ‖iteratedFDeriv ℝ m (Φ g) v‖ ≤ P m*L^(m-2)) :
    ContDiff ℝ ∞ (normalized q Φ) ∧
    ∀ x ∈ S, (normalized q Φ =ᶠ[𝓝 x] (fun y ↦ q.vector (fun g z ↦ raw g z y)/q.beat)) ∧
      ‖fderiv ℝ (normalized q Φ) x‖ ≤ 2*(P 1+P 2) ∧
      ∀ m, ‖iteratedFDeriv ℝ (m+1) (normalized q Φ) x‖ ≤ (2*(P (m+1)+P (m+2)))*L^m := by
  have hs g (z : Euclidean 3) : ContDiff ℝ ∞ (fun x : E ↦ Φ g (x,z)) :=
    (hΦ g).comp (contDiff_id.prodMk contDiff_const)
  constructor
  · apply ContDiff.div_const
    cases q with
    | difference g z w hne => exact (hs g z).sub (hs g w)
    | sum g z w => exact (hs g z).add (hs g w)
    | cross g k hne z w a b ha hb => exact ((hs g z).const_smul a).add ((hs k w).const_smul b)
  intro x hx
  have hh g z (hz : z ∈ Z g) : (fun y : E ↦ Φ g (y,z)) =ᶠ[𝓝 x] raw g z :=
    (he g (x,z) ⟨hx,hz⟩).comp_tendsto (continuous_id.prodMk continuous_const).continuousAt
  have hjet := normalized_sample_pair_joint_jets_le hZ q Φ hΦ hL P hP x (fun g z hz ↦ hj g (x,z) ⟨hx,hz⟩)
  have hu : ‖fderiv ℝ (normalized q Φ) x‖ ≤ 2*(P 1+P 2) := by
    change ‖fderiv ℝ (fun y : E ↦ q.vector (fun g z ↦ Φ g (y,z))/q.beat) x‖ ≤ _
    simpa only [Nat.reduceAdd,norm_iteratedFDeriv_one,pow_zero,mul_one] using hjet 0
  refine ⟨?_,hu,hjet⟩
  cases q with
  | difference g z w _ =>
    filter_upwards [hh g z z.property,hh g w w.property] with y hy hz
    simp only [normalized,Pair.vector,hy,hz]
  | sum g z w =>
    filter_upwards [hh g z z.property,hh g w w.property] with y hy hz
    simp only [normalized,Pair.vector,hy,hz]
  | cross g k _ z w a b _ _ =>
    filter_upwards [hh g z z.property,hh k w w.property] with y hy hz
    simp only [normalized,Pair.vector,hy,hz]

/-- Exact complex inclusion of the real signed quadrature. The comparison
starts with the native measured datum and its actual zero extension. -/
theorem complex_quadrature {W : Set E} (hW : MeasurableSet W) (u : LocalL2 W RV)
    {f : E → CV} (hf : MemLp f 2 volume)
    (he : zeroExtend hW u =ᵐ[volume] fun y ↦ euclideanRealPart (f y)) :
    complexSource hW u = l2ComplexInclusion (volume.restrict univ)
      (l2RealPart (volume.restrict univ) (restrictL2 univ (hf.toLp f))) := by
  apply Lp.ext
  filter_upwards [restrictL2_coeFn univ (l2ComplexInclusion volume (zeroExtend hW u)),
    ae_restrict_of_ae (euclideanComplexInclusion.coeFn_compLpL (zeroExtend hW u)),ae_restrict_of_ae he,
    euclideanComplexInclusion.coeFn_compLpL (l2RealPart (volume.restrict univ) (restrictL2 univ (hf.toLp f))),
    euclideanRealPart.coeFn_compLpL (restrictL2 univ (hf.toLp f)),restrictL2_coeFn univ (hf.toLp f),
    ae_restrict_of_ae hf.coeFn_toLp] with y hr hi he hc ha hb hf
  exact hr.trans (hi.trans ((congrArg euclideanComplexInclusion he).trans
    (hc.trans (congrArg euclideanComplexInclusion (ha.trans (congrArg euclideanRealPart (hb.trans hf))))).symm))

def reduced_wave (χ ψ : E → ℝ) (Q : E → Fin (d+1) → MetricTensor (d+1))
    (A B : E → Matrix (Fin N) (Fin (d+1)) ℂ) (minus : Bool) (φ : E → ℝ) (ρ : ℝ) : E → CV :=
  modulatedSource χ φ (fun y ↦ ψ y • ((1/2:ℝ) • complexStressContraction (Q y)
    (if minus then symmetricBilinearTensor (A y) ((B y).map conj) else symmetricBilinearTensor (A y) (B y)))) ρ

/-- Actual chain consumer from the phase/amplitude kernel inputs, not from a
source localization-success assumption. The bound is selected for ALL labels
before any history/frequency is queried, with literal unit source amplitude. -/
theorem first_mask {β : Type} {U W : Set E} (hU : IsOpen U) (hW : MeasurableSet W)
    (χ ψ : E → ℝ) (hc : HasCompactSupport χ) (hχU : tsupport χ ⊆ U)
    (hχ : ContDiffOn ℝ ∞ χ U) (hψ : ContDiffOn ℝ ∞ ψ U) (K : Set E)
    (Q : β → E → Fin (d+1) → MetricTensor (d+1)) (A B : β → E → Matrix (Fin N) (Fin (d+1)) ℂ)
    (minus : β → Bool) (φ : β → E → ℝ) (ρ L : β → ℝ) (u : β → LocalL2 W RV)
    (hQ : ∀ t, ContDiffOn ℝ ∞ (Q t) U) (hA : ∀ t, ContDiffOn ℝ ∞ (A t) U) (hB : ∀ t, ContDiffOn ℝ ∞ (B t) U)
    (hφ : ∀ t, ContDiffOn ℝ ∞ (φ t) U) (hL : ∀ t, 1 ≤ L t) (hρ : ∀ t, 1 ≤ ρ t)
    (hwindow : ∀ t, L t ≤ (ρ t)^(1-(1/1000:ℝ))) (G : ℝ) (P X Y CQ C : ℕ → ℝ)
    (hP : ∀ j, 0 ≤ P j) (hX : ∀ j, 0 ≤ X j) (hY : ∀ j, 0 ≤ Y j) (hCQ : ∀ j, 0 ≤ CQ j) (hC : ∀ j, 0 ≤ C j)
    (hχj : ∀ t y, y ∈ U → ∀ j, ‖iteratedFDeriv ℝ j χ y‖ ≤ X j*(L t)^j)
    (hψj : ∀ t y, y ∈ U → ∀ j, ‖iteratedFDeriv ℝ j ψ y‖ ≤ Y j*(L t)^j)
    (hQj : ∀ t y, y ∈ U → ∀ j, ‖iteratedFDeriv ℝ j (Q t) y‖ ≤ CQ j*(L t)^j)
    (hAj : ∀ t y, y ∈ U → ∀ j, ‖iteratedFDeriv ℝ j (A t) y‖ ≤ C j*(L t)^j)
    (hBj : ∀ t y, y ∈ U → ∀ j, ‖iteratedFDeriv ℝ j (B t) y‖ ≤ C j*(L t)^j)
    (hgrad : ∀ t y, y ∈ tsupport χ → gradient (φ t) y ∈ K)
    (hupper : ∀ t y, y ∈ U → ‖fderiv ℝ (φ t) y‖ ≤ G)
    (hphase : ∀ t y, y ∈ tsupport χ → ∀ j, 1 ≤ j → ‖iteratedFDeriv ℝ (j+1) (φ t) y‖ ≤ P j*(L t)^j)
    (he : ∀ t, zeroExtend hW (u t) =ᵐ[volume] fun y ↦
      euclideanRealPart (reduced_wave χ ψ (Q t) (A t) (B t) (minus t) (φ t) (ρ t) y)) :
    FirstMaskInput ρ (fun t ↦ complexSource hW (u t)) (tsupport χ ×ˢ K) := by
  intro δ hδ D hD m hm hmc _hrange hmj heven hplateau M hM s accuracy
  obtain ⟨C₀,hC₀,hbound⟩ := exists_reducedSigned_local_initialSource_accuracy_constants (N := N)
    (tsupport χ) hc δ G hδ P D X Y CQ C hP hD hX hY hCQ hC s (σ := 1/1000) (by norm_num) accuracy
  let inc := ‖euclideanComplexInclusion (ι := Fin (d+1))‖+1
  have hinc : 0 ≤ inc := by dsimp [inc]; positivity
  refine ⟨inc*C₀,mul_nonneg hinc hC₀,?_⟩
  intro t
  obtain ⟨hf,hb⟩ := hbound (m t) (hm t) (hmc t) (hmj t) (heven t) _ (hplateau t) U hU hχU
    χ ψ (Q t) (A t) (B t) hχ hψ (hQ t) (hA t) (hB t) (Subset.refl _) (L t) (hL t)
    (hχj t) (hψj t) (hQj t) (hAj t) (hBj t) (fun _ ↦ φ t) (fun _ ↦ ρ t)
    (fun _ ↦ hφ t) (fun _ ↦ hρ t) (fun _ ↦ hwindow t) (fun _ y hy ↦ ⟨hy,hgrad t y hy⟩)
    (fun _ ↦ hupper t) (fun _ ↦ hphase t) (minus t)
  let v := l2RealPart (volume.restrict univ) (restrictL2 univ (hf.toLp _))
  let e := v - localRealCompression MeasurableSet.univ univ (M t) v
  have hreal : e ∈ (restrictionSobolevScale univ RV MeasurableSet.univ).level s ∧
      (restrictionSobolevScale univ RV MeasurableSet.univ).gradeNorm s e ≤ C₀*(ρ t)^(-accuracy) := by
    simpa only [one_smul] using hb (M t) (hM t) univ MeasurableSet.univ (subset_univ _) 1 (by simp)
  dsimp only
  rw [complex_quadrature hW (u t) hf (he t),complex_source_leakage_eq_of_even MeasurableSet.univ (ρ t) (m t) (heven t) (M t) (hM t)]
  obtain ⟨hmemb,hnorm⟩ := compLp_restrictionSobolev_bound (euclideanComplexInclusion (ι := Fin (d+1))) hreal.1
  refine ⟨hmemb,?_⟩
  change (restrictionSobolevScale univ CV MeasurableSet.univ).gradeNorm s
    ((euclideanComplexInclusion (ι := Fin (d+1))).compLp e) ≤ _
  rw [restrictionSobolevScale_gradeNorm MeasurableSet.univ hmemb]
  apply hnorm.trans
  rw [← restrictionSobolevScale_gradeNorm MeasurableSet.univ hreal.1]
  exact (mul_le_mul_of_nonneg_left hreal.2 hinc).trans_eq (by dsimp [inc];ring)
end JanetCartan.PhysicalPairs.SampledMask
end
