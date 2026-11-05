module

public import JanetCartan.Analysis.Microlocal.ProtectedFlow.FrameExtension
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.ImageGeometry.JetFormula

/-!
# The fixed extension of the complete reduced-operator array

For `app:ch_regular:thm:no-return`, extend the actual coefficient array,
including the zeroth-order stress-Christoffel contraction. Its principal frame
is exactly the fixed extension used in the protected Hamiltonian. No new frame
or coefficient operator is chosen. The lower-order background is any fixed
smooth completion, so it can be the reference connection coefficient.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ProtectedFlow
open GeometricProfile ProjectedStressFrame

/-- Frozen principal coefficients and a fixed lower-order completion in
`app:ch_regular:eq:coefficient-extension`. -/
def reducedCoefficientBackground {n : ℕ}
    (Z₀ : Euclidean n → Fin n × Fin n → ℝ) (x : Euclidean n) : ReducedCoefficientIndex n → ℝ
  | .inl (a, i, k) => cubeStress n i a k
  | .inr (i, k) => Z₀ x (i, k)

/-- A fixed smooth lower-order completion gives a smooth full background
(`app:ch_regular:eq:coefficient-extension`). -/
theorem contDiff_reducedCoefficientBackground {n : ℕ}
    {Z₀ : Euclidean n → Fin n × Fin n → ℝ} (hZ₀ : ContDiff ℝ ∞ Z₀) :
    ContDiff ℝ ∞ (reducedCoefficientBackground Z₀) := by
  apply contDiff_pi.mpr
  rintro (⟨a, i, k⟩ | ⟨i, k⟩)
  · exact contDiff_const
  · exact (contDiff_pi.mp hZ₀) (i, k)

/-- The literal affine extension of every coefficient of `P_F`, using the
same ball and Seeley operator as `extendedProjectedStress`
(`app:ch_regular:eq:coefficient-extension`). -/
def extendedReducedCoefficients {n N : ℕ} (p : BallExtension.Parameters (Euclidean n))
    (Z₀ : Euclidean n → Fin n × Fin n → ℝ)
    (F : Euclidean n → Euclidean N) : Euclidean n → ReducedCoefficientIndex n → ℝ :=
  (reducedCoefficientBackground Z₀) +
    p.seeleyExtension (geometricReducedCoefficients F - reducedCoefficientBackground Z₀)

/-- The complete extended array agrees with the actual array on the closed
coefficient ball, including all lower-order entries
(`app:ch_regular:thm:no-return`). -/
theorem extendedReducedCoefficients_eqOn {n N : ℕ}
    (p : BallExtension.Parameters (Euclidean n))
    (Z₀ : Euclidean n → Fin n × Fin n → ℝ) (F : Euclidean n → Euclidean N) :
    EqOn (extendedReducedCoefficients p Z₀ F) (geometricReducedCoefficients F)
      (closedBall p.center p.radius) := by
  intro x hx
  change reducedCoefficientBackground Z₀ x + p.seeleyExtension
    (geometricReducedCoefficients F - reducedCoefficientBackground Z₀) x = _
  rw [p.seeleyExtension_eq_on_closedBall _ hx]
  simp

/-- Smoothness of the full extension follows from smooth immersion and full
normal rank on the coefficient neighborhood, with no coefficient-smoothness
assumption (`app:ch_regular:thm:no-return`). -/
theorem contDiff_extendedReducedCoefficients {n N : ℕ}
    (p : BallExtension.Parameters (Euclidean n))
    (Z₀ : Euclidean n → Fin n × Fin n → ℝ) (hZ₀ : ContDiff ℝ ∞ Z₀)
    {F : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F)
    {U : Set (Euclidean n)} (hU : IsOpen U)
    (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    (hpU : closedBall p.center p.radius ⊆ U) :
    ContDiff ℝ ∞ (extendedReducedCoefficients p Z₀ F) := by
  exact (contDiff_reducedCoefficientBackground hZ₀).add (p.contDiff_seeleyExtension
    (((ContinuumRow.ImageGeometry.contDiffOn_geometricReducedCoefficients hF hU hi hrank).mono
      hpU).sub (contDiff_reducedCoefficientBackground hZ₀).contDiffOn))

/-- The full perturbation, including the lower-order entries, has the same
fixed compact support as the extended principal frame
(`app:ch_regular:eq:coefficient-extension`). -/
theorem tsupport_extendedReducedCoefficients_sub {n N : ℕ}
    (p : BallExtension.Parameters (Euclidean n))
    (Z₀ : Euclidean n → Fin n × Fin n → ℝ) (F : Euclidean n → Euclidean N) :
    tsupport (extendedReducedCoefficients p Z₀ F - reducedCoefficientBackground Z₀) ⊆
      closedBall p.center (p.radius + p.width / 2) := by
  simpa only [extendedReducedCoefficients, add_sub_cancel_left] using
    p.tsupport_seeleyExtension_subset
      (geometricReducedCoefficients F - reducedCoefficientBackground Z₀)

private def reducedPrincipalFrame (n : ℕ) :
    (ReducedCoefficientIndex n → ℝ) →ₗ[ℝ] (Fin n → MetricTensor n) where
  toFun a := fun i j k ↦ a (.inl (j, i, k))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Commutation of the fixed extension with the principal-coordinate
projection identifies the actual Hamiltonian used by protection. The full
array and the projected frame use exactly the same extension, everywhere
(`app:ch_regular:thm:no-return`). -/
theorem extendedReducedCoefficients_principal {n N : ℕ}
    (p : BallExtension.Parameters (Euclidean n))
    (Z₀ : Euclidean n → Fin n × Fin n → ℝ)
    {F : Euclidean n → Euclidean N}
    (hF : ∀ x ∈ closedBall p.center p.radius, ContDiffAt ℝ 2 F x)
    (hrank : HasFullNormalRankOn F (closedBall p.center p.radius))
    (x : Euclidean n) (a i k : Fin n) :
    extendedReducedCoefficients p Z₀ F x (.inl (a, i, k)) =
      extendedProjectedStress p F x i a k := by
  let L := reducedPrincipalFrame n
  have hmap := p.seeleyExtension_map L
    (geometricReducedCoefficients F - reducedCoefficientBackground Z₀)
  have he : p.seeleyExtension
      (L ∘ (geometricReducedCoefficients F - reducedCoefficientBackground Z₀)) =
      p.seeleyExtension (projectedStress F - fun _ ↦ cubeStress n) := by
    apply p.seeleyExtension_congr
    intro y hy
    funext i a k
    change (StressFrame.geometricCubeStress F y i).val a k - cubeStress n i a k = _
    rw [ContinuumRow.ImageGeometry.geometricCubeStress_val_eq_projectedStress
      (hF y hy) (hrank y hy) i]
    rfl
  have hv := congrArg (fun f : Euclidean n → Fin n → MetricTensor n ↦ f x i a k)
    (hmap.symm.trans he)
  change cubeStress n i a k + _ = cubeStress n i a k + _
  exact congrArg (fun v ↦ cubeStress n i a k + v) hv

/-- The differential operator associated to the full coefficient array.
This is the literal first-order expansion of `P_F`
(`app:ch_waves:eq:reduced-symbol`). -/
def reducedCoefficientOperator {n : ℕ}
    (a : Euclidean n → ReducedCoefficientIndex n → ℝ)
    (u : Euclidean n → Euclidean n) (x : Euclidean n) (i : Fin n) : ℝ :=
  (∑ j, ∑ k, a x (.inl (j, i, k)) * partialDeriv (fun y ↦ u y k) x j) +
    ∑ k, a x (.inr (i, k)) * u x k

/-- The operator with the extended full array equals the original reduced
operator on the whole coefficient ball. The lower-order connection is retained
and the test covector field is arbitrary (`app:ch_regular:thm:no-return`). -/
theorem extendedReducedCoefficientOperator_eq {n N : ℕ}
    (p : BallExtension.Parameters (Euclidean n))
    (Z₀ : Euclidean n → Fin n × Fin n → ℝ)
    {F : Euclidean n → Euclidean N}
    (hF : ∀ x ∈ closedBall p.center p.radius, ContDiffAt ℝ 2 F x)
    (hrank : HasFullNormalRankOn F (closedBall p.center p.radius))
    (u : Euclidean n → Euclidean n) {x : Euclidean n}
    (hx : x ∈ closedBall p.center p.radius) (i : Fin n) :
    reducedCoefficientOperator (extendedReducedCoefficients p Z₀ F) u x i =
      NullTransport.reducedOperator F (projectedStress F) u x i := by
  have harray := extendedReducedCoefficients_eqOn p Z₀ F hx
  have hframe : (fun j ↦ (StressFrame.geometricCubeStress F x j).val) = projectedStress F x := by
    funext j
    exact ContinuumRow.ImageGeometry.geometricCubeStress_val_eq_projectedStress
      (hF x hx) (hrank x hx) j
  unfold reducedCoefficientOperator
  rw [harray, ← reducedOperator_geometricCubeStress_eq]
  change tensorPairing _ _ = tensorPairing _ _
  exact congrArg (fun Q ↦ tensorPairing Q (symmCovariantDeriv F u x)) (congrFun hframe i)

/-- All-order perturbation and coefficient bounds for the full *actual* array.
The same extension is used at every order, and the constant precedes the
current immersion. Smoothness is derived from its geometric hypotheses
(`app:ch_regular:eq:coefficient-extension`). -/
theorem exists_extendedReducedCoefficients_bounds {n N : ℕ}
    (p : BallExtension.Parameters (Euclidean n))
    (Z₀ : Euclidean n → Fin n × Fin n → ℝ) (hZ₀ : ContDiff ℝ ∞ Z₀)
    {U K : Set (Euclidean n)} (hU : IsOpen U) (hK : IsCompact K)
    (hpU : closedBall p.center p.radius ⊆ U) (m : ℕ) :
    ∃ C > (0 : ℝ), ∀ F : Euclidean n → Euclidean N, ContDiff ℝ ∞ F →
      IsImmersionOn F U → HasFullNormalRankOn F U →
      cNorm univ m (extendedReducedCoefficients p Z₀ F - reducedCoefficientBackground Z₀) ≤
        C * cNorm (closedBall p.center p.radius) m
          (geometricReducedCoefficients F - reducedCoefficientBackground Z₀) ∧
      cNorm K m (extendedReducedCoefficients p Z₀ F) ≤
        C * (1 + cNorm (closedBall p.center p.radius) m (geometricReducedCoefficients F)) := by
  let a₀ : Euclidean n → ReducedCoefficientIndex n → ℝ := reducedCoefficientBackground Z₀
  have h₀ : ContDiff ℝ ∞ a₀ := contDiff_reducedCoefficientBackground hZ₀
  obtain ⟨A, hA, hb⟩ := exists_cNorm_vector_seeleyExtension_le
    (F := ReducedCoefficientIndex n → ℝ) p m
  let B := cNorm K m a₀ + A * cNorm (closedBall p.center p.radius) m a₀
  have hB : 0 ≤ B := add_nonneg (cNorm_nonneg _ _ _) (mul_nonneg hA.le (cNorm_nonneg _ _ _))
  refine ⟨A + B + 1, by positivity, ?_⟩
  intro F hF hi hrank
  let a := geometricReducedCoefficients F
  have ha : ∀ x ∈ closedBall p.center p.radius, ContDiffAt ℝ ∞ a x := fun x hx ↦
    (ContinuumRow.ImageGeometry.contDiffOn_geometricReducedCoefficients hF hU hi hrank).contDiffAt
      (hU.mem_nhds (hpU hx))
  have hd : ∀ x ∈ closedBall p.center p.radius, ContDiffAt ℝ ∞ (a - a₀) x :=
    fun x hx ↦ (ha x hx).sub h₀.contDiffAt
  have he := hb (a - a₀) hd
  constructor
  · change cNorm univ m (a₀ + p.seeleyExtension (a - a₀) - a₀) ≤ _
    rw [add_sub_cancel_left]
    exact he.trans (mul_le_mul_of_nonneg_right (by linarith) (cNorm_nonneg _ _ _))
  · have heSmooth : ContDiff ℝ ∞ (p.seeleyExtension (a - a₀)) :=
      p.contDiff_seeleyExtension (fun x hx ↦ (hd x hx).contDiffWithinAt)
    obtain ⟨M, _, hM⟩ := (p.hasCompactSupport_seeleyExtension (a - a₀)).exists_bound_iteratedFDeriv
      heSmooth m
    have hlocal : cNorm K m (p.seeleyExtension (a - a₀)) ≤
        cNorm univ m (p.seeleyExtension (a - a₀)) := by
      apply cNorm_mono_set_of_bddAbove (subset_univ K)
      intro j hj
      exact ⟨M, by rintro _ ⟨x, _, rfl⟩; exact hM j hj x⟩
    have hsub : cNorm (closedBall p.center p.radius) m (a - a₀) ≤
        cNorm (closedBall p.center p.radius) m a + cNorm (closedBall p.center p.radius) m a₀ := by
      simpa only [sub_eq_add_neg, cNorm_neg] using
        cNorm_add_le_of_contDiffAt (f := a) (g := -a₀) (isCompact_closedBall p.center p.radius)
          (fun x hx ↦ (ha x hx).of_le (by simp : (m : ℕ∞ω) ≤ ∞))
          (fun _ _ ↦ (h₀.of_le (by simp : (m : ℕ∞ω) ≤ ∞)).contDiffAt.neg)
    have htotal : cNorm K m (extendedReducedCoefficients p Z₀ F) ≤
        B + A * cNorm (closedBall p.center p.radius) m a := by
      calc
        _ ≤ cNorm K m a₀ + cNorm K m (p.seeleyExtension (a - a₀)) :=
          cNorm_add_le hK (h₀.of_le (by simp)) (heSmooth.of_le (by simp))
        _ ≤ cNorm K m a₀ + A * cNorm (closedBall p.center p.radius) m (a - a₀) :=
          add_le_add le_rfl (hlocal.trans he)
        _ ≤ cNorm K m a₀ + A * (cNorm (closedBall p.center p.radius) m a +
            cNorm (closedBall p.center p.radius) m a₀) := by gcongr
        _ = _ := by dsimp [B]; ring
    exact htotal.trans (by nlinarith [cNorm_nonneg (closedBall p.center p.radius) m a])

/-- Shrinking the actual full-coefficient neighborhood puts its fixed affine
extension in any prescribed low class. The principal Hamiltonian is still the
one identified by `extendedReducedCoefficients_principal`
(`app:ch_regular:thm:no-return`). -/
theorem exists_extendedReducedCoefficients_low_radius {n N : ℕ}
    (p : BallExtension.Parameters (Euclidean n))
    (Z₀ : Euclidean n → Fin n × Fin n → ℝ) (hZ₀ : ContDiff ℝ ∞ Z₀)
    {U : Set (Euclidean n)} (hU : IsOpen U)
    (hpU : closedBall p.center p.radius ⊆ U) (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ F : Euclidean n → Euclidean N, ContDiff ℝ ∞ F →
      IsImmersionOn F U → HasFullNormalRankOn F U →
      cNorm (closedBall p.center p.radius) m
        (geometricReducedCoefficients F - reducedCoefficientBackground Z₀) < δ →
      cNorm univ m (extendedReducedCoefficients p Z₀ F - reducedCoefficientBackground Z₀) < ε := by
  obtain ⟨C, hC, hb⟩ := exists_extendedReducedCoefficients_bounds (N := N) p Z₀ hZ₀ hU
    (isCompact_closedBall (0 : Euclidean n) 1) hpU m
  refine ⟨ε / C, div_pos hε hC, fun F hF hi hrank hsmall ↦ ?_⟩
  exact (hb F hF hi hrank).1.trans_lt
    ((mul_lt_mul_of_pos_left hsmall hC).trans_eq (mul_div_cancel₀ ε hC.ne'))

/-- Every stated coefficient profile is preserved by the same full extension.
The constants precede the slow scale, the immersion, and all requested
accuracy; no extension is reselected for higher orders
(`app:ch_regular:thm:no-return`, `app:ch_regular:eq:initial-coefficient-profile`). -/
theorem extendedReducedCoefficients_preserves_profile {n N : ℕ}
    (p : BallExtension.Parameters (Euclidean n))
    (Z₀ : Euclidean n → Fin n × Fin n → ℝ) (hZ₀ : ContDiff ℝ ∞ Z₀)
    {U K : Set (Euclidean n)} (hU : IsOpen U) (hK : IsCompact K)
    (hpU : closedBall p.center p.radius ⊆ U) (D : ℕ → ℝ) (r₀ : ℕ) :
    ∃ C : ℕ → ℝ, (∀ r, 0 < C r) ∧
      ∀ T : ℝ, 1 ≤ T → ∀ F : Euclidean n → Euclidean N, ContDiff ℝ ∞ F →
        IsImmersionOn F U → HasFullNormalRankOn F U →
        HasDerivativeProfile (closedBall p.center p.radius) (geometricReducedCoefficients F) r₀ T D →
        HasDerivativeProfile K (extendedReducedCoefficients p Z₀ F) r₀ T C := by
  choose B hB hb using exists_extendedReducedCoefficients_bounds (N := N) p Z₀ hZ₀ hU hK hpU
  refine ⟨fun r ↦ B r * (1 + max 0 (D r)), fun r ↦ mul_pos (hB r) (by positivity), ?_⟩
  intro T hT F hF hi hrank hprofile r
  have hp : 1 ≤ T ^ (r - r₀) := one_le_pow₀ hT
  have hd := (hprofile r).trans (mul_le_mul_of_nonneg_right (le_max_right 0 (D r))
    (zero_le_one.trans hp))
  calc
    _ ≤ B r * (1 + cNorm (closedBall p.center p.radius) r (geometricReducedCoefficients F)) :=
      (hb r F hF hi hrank).2
    _ ≤ B r * ((1 + max 0 (D r)) * T ^ (r - r₀)) :=
      mul_le_mul_of_nonneg_left (by nlinarith) (hB r).le
    _ = _ := by ring

end JanetCartan.ProtectedFlow
