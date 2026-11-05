module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.HigherRegularity.RealCommutator.Coordinates
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Differential.SobolevNormal
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Translation.Assembly
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.MatrixBounds.VectorInteger

@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff RealInnerProductSpace Matrix.Norms.Frobenius
open JanetCartan.AmplitudeBound JanetCartan.Pseudodifferential JanetCartan.PeriodicLocalL2
open JanetCartan.Pseudodifferential.DifferentialChart
namespace JanetCartan.ContinuumCommutator.HigherRegularity.RealCommutator
open PeriodicSobolevSpace
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℂ (Fin n)
local notation "L²" => PeriodicL2 n ℂ
local notation "VL²" => PeriodicL2 n V

private def scalarCommutator
    (hn : 0 < n) (R : ℝ) (hR : R < 1 / 2) (s : ℕ) (M : ℝ)
    (b : E → EuclideanSpace ℝ (Fin (2*n)) → Matrix (Fin n) (Fin n) ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hs : ∀ ξ i j, SupportedInCenteredBox R (fun z ↦ b ξ z i j))
    (H : ℝ)
    (hM : ∀ i j, HasAmplitudeDerivativeBound (fun ξ z ↦ b ξ z i j)
      (2 * (n + 1) + 1) M)
    (i j : Fin n) (is : List (Fin n)) (hlen : is.length = s + 1)
    (hH : ∀ i j, HasAmplitudeDerivativeBound (fun ξ z ↦ b ξ z i j)
      (2 * (n + 1) + is.length) H) :
    PeriodicSobolevSpace n ℂ s →L[ℝ] L² :=
  torusSobolevCommutator hn R hR s M (fun ξ z ↦ b ξ z i j) ((matrixEntryEvaluation i j).contDiff.comp hb)
    (fun ξ ↦ hs ξ i j) H (hM i j) is hlen (hH i j)

private def matrixRows
    (hn : 0 < n) (R : ℝ) (hR : R < 1 / 2) (s : ℕ) (M : ℝ)
    (b : E → EuclideanSpace ℝ (Fin (2*n)) → Matrix (Fin n) (Fin n) ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hs : ∀ ξ i j, SupportedInCenteredBox R (fun z ↦ b ξ z i j))
    (H : ℝ)
    (hM : ∀ i j, HasAmplitudeDerivativeBound (fun ξ z ↦ b ξ z i j)
      (2 * (n + 1) + 1) M)
    (is : List (Fin n)) (hlen : is.length = s + 1)
    (hH : ∀ i j, HasAmplitudeDerivativeBound (fun ξ z ↦ b ξ z i j)
      (2 * (n + 1) + is.length) H) :
    PeriodicSobolevSpace n V s →L[ℝ]
      PiLp 2 (fun _ : Fin n ↦ L²) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ L²)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i ↦
      ∑ j : Fin n, (scalarCommutator hn R hR s M b hb hs H hM i j is hlen hH).comp
        (sobolevMap (valueCoordinate j) s)))

private def matrixK
    (hn : 0 < n) (R : ℝ) (hR : R < 1 / 2) (s : ℕ) (M : ℝ)
    (b : E → EuclideanSpace ℝ (Fin (2*n)) → Matrix (Fin n) (Fin n) ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hs : ∀ ξ i j, SupportedInCenteredBox R (fun z ↦ b ξ z i j))
    (H : ℝ)
    (hM : ∀ i j, HasAmplitudeDerivativeBound (fun ξ z ↦ b ξ z i j)
      (2 * (n + 1) + 1) M)
    (is : List (Fin n)) (hlen : is.length = s + 1)
    (hH : ∀ i j, HasAmplitudeDerivativeBound (fun ξ z ↦ b ξ z i j)
      (2 * (n + 1) + is.length) H) :
    PeriodicSobolevSpace n V s →L[ℝ] VL² :=
  (finiteL2CoordinateIsometry (X := Torus n) (I := Fin n) volume).symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ |>.comp
    (matrixRows hn R hR s M b hb hs H hM is hlen hH)

private lemma finite_coord_ae_phys (g : EuclideanL2 n V) (i : Fin n) :
    finiteL2CoordinateIsometry (X := EuclideanSpace ℝ (Fin n)) (I := Fin n) volume g i =ᵐ[volume]
      fun x => g x i := by
  have hg : (Lp.memLp g).toLp (fun x => g x) = g := by
    apply Lp.ext
    exact (Lp.memLp g).coeFn_toLp
  have h := finiteL2CoordinateIsometry_toLp (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (u := fun x => g x) (Lp.memLp g)
  rw [hg] at h
  have hi := congrArg (fun z => z i) h
  rw [hi]
  simpa only [PiLp.toLp_apply] using ((Lp.memLp g).eval_piLp i).coeFn_toLp

private lemma finite_coord_ae_torus (u : VL²) (i : Fin n) :
    finiteL2CoordinateIsometry (X := Torus n) (I := Fin n) volume u i =ᵐ[volume]
      fun x => u x i := by
  have hu : (Lp.memLp u).toLp (fun x => u x) = u := by
    apply Lp.ext
    exact (Lp.memLp u).coeFn_toLp
  have h := finiteL2CoordinateIsometry_toLp (μ := (volume : Measure (Torus n)))
    (u := fun x => u x) (Lp.memLp u)
  rw [hu] at h
  have hi := congrArg (fun z => z i) h
  rw [hi]
  simpa only [PiLp.toLp_apply] using ((Lp.memLp u).eval_piLp i).coeFn_toLp

private lemma finite_coord_toTorus (g : EuclideanL2 n V) (i : Fin n) :
    finiteL2CoordinateIsometry (X := Torus n) (I := Fin n) volume
      (toTorus (𝕜 := ℂ) g) i =
      toTorus (𝕜 := ℂ) (finiteL2CoordinateIsometry
        (X := EuclideanSpace ℝ (Fin n)) (I := Fin n) volume g i) := by
  apply Lp.ext
  have hcoord := finite_coord_ae_phys g i
  have hcoord' := Filter.EventuallyEq.restrict (s := halfOpenCell n) hcoord
  have hcomp := measurePreserving_representative.quasiMeasurePreserving.ae_eq_comp hcoord'
  have hxi := finite_coord_ae_torus (toTorus (𝕜 := ℂ) g) i
  have htorc := toTorus_coe (𝕜 := ℂ) (finiteL2CoordinateIsometry
    (X := EuclideanSpace ℝ (Fin n)) (I := Fin n) volume g i)
  filter_upwards [hxi, toTorus_coe (𝕜 := ℂ) g, hcomp, htorc] with x hx htor hcomp htorc
  rw [hx, htorc, htor]
  exact hcomp.symm

private lemma finite_coord_toEuclidean (u : VL²) (i : Fin n) :
    finiteL2CoordinateIsometry (X := EuclideanSpace ℝ (Fin n)) (I := Fin n) volume
      (toEuclidean (𝕜 := ℂ) u) i =
      toEuclidean (𝕜 := ℂ) (finiteL2CoordinateIsometry
        (X := Torus n) (I := Fin n) volume u i) := by
  apply Lp.ext
  have hcoord := finite_coord_ae_torus u i
  have hcomp0 := measurePreserving_quotient.quasiMeasurePreserving.ae_eq_comp hcoord
  have hcomp := (ae_restrict_iff' measurableSet_halfOpenCell).mp hcomp0
  have hxi := finite_coord_ae_phys (toEuclidean (𝕜 := ℂ) u) i
  have hec := toEuclidean_coe (𝕜 := ℂ) (finiteL2CoordinateIsometry
    (X := Torus n) (I := Fin n) volume u i)
  filter_upwards [hxi, toEuclidean_coe (𝕜 := ℂ) u, hcomp, hec] with x hx he hcomp hec
  rw [hx, he, hec]
  by_cases hcell : x ∈ halfOpenCell n
  · simp only [indicator_of_mem hcell, periodicLift, Function.comp_apply]
    exact (hcomp hcell).symm
  · simp only [indicator_of_notMem hcell]
    rfl

private lemma finite_coord_transfer (B : Fin n → Fin n → EuclideanL2 n ℂ →L[ℂ] EuclideanL2 n ℂ)
    (u : VL²) (i : Fin n) :
    finiteL2CoordinateIsometry (X := Torus n) (I := Fin n) volume
      (transferOperator (vectorMatrixL2Operator B) u) i =
      ∑ j, transferOperator (B i j)
        (finiteL2CoordinateIsometry (X := Torus n) (I := Fin n) volume u j) := by
  rw [transferOperator]
  change finiteL2CoordinateIsometry (X := Torus n) (I := Fin n) volume
      (toTorus (𝕜 := ℂ) (vectorMatrixL2Operator B (toEuclidean (𝕜 := ℂ) u))) i = _
  rw [finite_coord_toTorus]
  rw [finiteL2CoordinateIsometry_vectorMatrixL2Operator]
  rw [matrixOperator_apply]
  simp_rw [finite_coord_toEuclidean]
  simp only [map_sum, transferOperator]
  rfl

/-- The complex vector-valued periodic commutator obtained by exact coordinate
transfer of the scalar chart commutators (`app:ch_background:eq:bg-commutator`). -/
theorem exists_vectorTwoPosition_sobolev_commutator_bound
    (hn : 0 < n) (R : ℝ) (hR : R < 1 / 2) (s : ℕ) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (b : E → EuclideanSpace ℝ (Fin (2*n)) → Matrix (Fin n) (Fin n) ℂ)
        (hb : ContDiff ℝ ∞ (Function.uncurry b))
        (hs : ∀ ξ i j, SupportedInCenteredBox R (fun z ↦ b ξ z i j)) (H : ℝ)
        (hM : ∀ i j, HasAmplitudeDerivativeBound (fun ξ z ↦ b ξ z i j)
          (2 * (n + 1) + 1) M)
        (is : List (Fin n)) (_hlen : is.length = s + 1)
        (_hH : ∀ i j, HasAmplitudeDerivativeBound (fun ξ z ↦ b ξ z i j)
          (2 * (n + 1) + is.length) H),
        ∃ K : PeriodicSobolevSpace n V s →L[ℝ] VL²,
          (∀ f : Torus n → V, ∀ hf : IsSmoothPeriodic f,
            HasPeriodicWeakDerivativeList is
              ((transferOperator (vectorTwoPositionL2Operator hn R b hb hs M
                (fun i j ξ js hjs ↦ hM i j ξ js (Nat.le_succ_of_le hjs))))
                (toL2 s (ofSmooth s f hf)))
              (((transferOperator (vectorTwoPositionL2Operator hn R b hb hs M
                (fun i j ξ js hjs ↦ hM i j ξ js (Nat.le_succ_of_le hjs))))
                (toL2 0 (ofSmooth 0 (periodicCoordinateDerivList is f)
                  (hf.coordinateDerivList is)))) + K (ofSmooth s f hf))) ∧
          (∀ u, ‖K u‖ ≤ C * (‖u‖ + max 1 H * ‖toL2 s u‖)) := by
  let C₀ := (exists_torusL2Operator_sobolev_commutator_bound hn R hR s M).choose
  have hC₀ : 0 ≤ C₀ :=
    (exists_torusL2Operator_sobolev_commutator_bound hn R hR s M).choose_spec.1
  refine ⟨(n : ℝ) ^ 2 * C₀, by positivity, ?_⟩
  intro b hb hs H hM is _hlen _hH
  let B := fun i j : Fin n ↦
    twoPositionL2Operator hn R (fun ξ z ↦ b ξ z i j)
      ((matrixEntryEvaluation i j).contDiff.comp hb) (fun ξ ↦ hs ξ i j) M
      (amplitudeDerivativeBound_of_le (hM i j) (Nat.le_succ _))
  let T := transferOperator (vectorTwoPositionL2Operator hn R b hb hs M
    (fun i j ξ js hjs ↦ hM i j ξ js (Nat.le_succ_of_le hjs)))
  let K := matrixK hn R hR s M b hb hs H hM is _hlen _hH
  refine ⟨K, ?_, ?_⟩
  · intro f hf
    rw [weakDerivativeList_coordinates_iff]
    intro i
    have hT := finite_coord_transfer B (toL2 s (ofSmooth s f hf)) i
    have hTd := finite_coord_transfer B
      (toL2 0 (ofSmooth 0 (periodicCoordinateDerivList is f)
        (hf.coordinateDerivList is))) i
    change HasPeriodicWeakDerivativeList is
      (finiteL2CoordinateIsometry volume (T (toL2 s (ofSmooth s f hf))) i)
      (finiteL2CoordinateIsometry volume
        (T (toL2 0 (ofSmooth 0 (periodicCoordinateDerivList is f)
          (hf.coordinateDerivList is))) + K (ofSmooth s f hf)) i)
    have hsum := congrArg (fun z : PiLp 2 (fun _ : Fin n ↦ PeriodicL2 n ℂ) ↦ z i)
      (map_add (finiteL2CoordinateIsometry (X := Torus n) (I := Fin n) volume)
        (T (toL2 0 (ofSmooth 0 (periodicCoordinateDerivList is f)
          (hf.coordinateDerivList is)))) (K (ofSmooth s f hf)))
    rw [hsum]
    simp only [PiLp.add_apply]
    rw [show T = transferOperator (vectorMatrixL2Operator B) by rfl, hT, hTd]
    have hf_j (j : Fin n) : IsSmoothPeriodic (fun x ↦ f x j) := by
      simpa only [valueCoordinate, ContinuousLinearMap.coe_restrictScalars',
        PiLp.proj_apply] using hf.comp_clm (valueCoordinate j)
    have hKcoord : finiteL2CoordinateIsometry (X := Torus n) (I := Fin n) volume
        (K (ofSmooth s f hf)) i =
      ∑ j, (scalarCommutator hn R hR s M b hb hs H hM i j is _hlen _hH)
        (ofSmooth s (fun x ↦ f x j) (hf_j j)) := by
      dsimp [K, matrixK, matrixRows]
      rw [(finiteL2CoordinateIsometry (X := Torus n) (I := Fin n) volume).apply_symm_apply]
      simp only [PiLp.continuousLinearEquiv_symm_apply, PiLp.toLp_apply, sum_apply]
      change (∑ j, (scalarCommutator hn R hR s M b hb hs H hM i j is _hlen _hH)
        (sobolevMap (valueCoordinate j) s (ofSmooth s f hf))) = _
      apply Finset.sum_congr rfl
      intro j _
      rw [sobolevMap_ofSmooth]
      rfl
    rw [hKcoord]
    have hcoordS (j : Fin n) :
        finiteL2CoordinateIsometry (X := Torus n) (I := Fin n) volume
            (toL2 s (ofSmooth s f hf)) j =
          toL2 s (ofSmooth s (fun x ↦ f x j)
            (hf_j j)) :=
      coordinateIsometry_ofSmooth s s f hf j
    have hcoordD (j : Fin n) :
        finiteL2CoordinateIsometry (X := Torus n) (I := Fin n) volume
            (toL2 0 (ofSmooth 0 (periodicCoordinateDerivList is f)
              (hf.coordinateDerivList is))) j =
          toL2 0 (ofSmooth 0 (periodicCoordinateDerivList is (fun x ↦ f x j))
            ((hf_j j).coordinateDerivList is)) := by
      rw [coordinateIsometry_ofSmooth 0 0 (periodicCoordinateDerivList is f)
        (hf.coordinateDerivList is) j]
      congr 2
      exact (periodicCoordinateDerivList_comp_clm hf (valueCoordinate j) is).symm
    simp_rw [hcoordS, hcoordD]
    have hrow (i : Fin n) :
        HasPeriodicWeakDerivativeList is
          (∑ j, (transferOperator (B i j))
            (toL2 s (ofSmooth s (fun x ↦ f x j)
              (hf_j j))))
          (∑ j, (transferOperator (B i j))
            (toL2 0 (ofSmooth 0 (periodicCoordinateDerivList is (fun x ↦ f x j))
              ((hf_j j).coordinateDerivList is))) +
            ∑ j, (scalarCommutator hn R hR s M b hb hs H hM i j is _hlen _hH)
              (ofSmooth s (fun x ↦ f x j)
                (hf_j j))) := by
      have hj (j : Fin n) : HasPeriodicWeakDerivativeList is
          ((transferOperator (B i j))
            (toL2 s (ofSmooth s (fun x ↦ f x j)
              (hf_j j))))
          (((transferOperator (B i j))
            (toL2 0 (ofSmooth 0 (periodicCoordinateDerivList is (fun x ↦ f x j))
              ((hf_j j).coordinateDerivList is)))) +
            (scalarCommutator hn R hR s M b hb hs H hM i j is _hlen _hH)
              (ofSmooth s (fun x ↦ f x j)
                (hf_j j))) := by
        simpa only [B, scalarCommutator, torusL2Operator] using
          torusSobolevCommutator_ofSmooth hn R hR s M
            (fun ξ z ↦ b ξ z i j) ((matrixEntryEvaluation i j).contDiff.comp hb)
            (fun ξ ↦ hs ξ i j) H (hM i j) is _hlen (_hH i j)
            (fun x ↦ f x j) (hf_j j)
      have hsums := weakDerivativeList_sum (t := Finset.univ) is
        (fun j ↦ (transferOperator (B i j))
          (toL2 s (ofSmooth s (fun x ↦ f x j)
            (hf_j j))))
        (fun j ↦ (transferOperator (B i j))
          (toL2 0 (ofSmooth 0 (periodicCoordinateDerivList is (fun x ↦ f x j))
            ((hf_j j).coordinateDerivList is))) +
          (scalarCommutator hn R hR s M b hb hs H hM i j is _hlen _hH)
            (ofSmooth s (fun x ↦ f x j)
              (hf_j j)))
        (fun j _ ↦ hj j)
      simpa only [Finset.sum_add_distrib] using hsums
    exact hrow i
  · intro u
    have hKcoord : finiteL2CoordinateIsometry (X := Torus n) (I := Fin n) volume
        (K u) = matrixRows hn R hR s M b hb hs H hM is _hlen _hH u := by
      dsimp [K, matrixK]
      exact (finiteL2CoordinateIsometry (X := Torus n) (I := Fin n) volume).apply_symm_apply _
    rw [← (finiteL2CoordinateIsometry (X := Torus n) (I := Fin n) volume).norm_map]
    rw [hKcoord]
    let X := ‖u‖ + max 1 H * ‖toL2 s u‖
    have hcoord (j : Fin n) :
        ‖sobolevMap (valueCoordinate j) s u‖ ≤ ‖u‖ := by
      simpa only [sobolevCoordinates_apply] using norm_sobolevCoordinates_apply_le s u j
    have hcoordL2 (j : Fin n) :
        ‖toL2 s (sobolevMap (valueCoordinate j) s u)‖ ≤ ‖toL2 s u‖ := by
      have h := congrArg (fun z : PiLp 2 (fun _ : Fin n ↦ PeriodicL2 n ℂ) ↦ z j)
        (toL2_sobolevCoordinates s u)
      have he : ‖toL2 s (sobolevMap (valueCoordinate j) s u)‖ =
          ‖finiteL2CoordinateIsometry (X := Torus n) (I := Fin n) volume
            (toL2 s u) j‖ := by
        simpa only [sobolevCoordinates_apply, PiLp.toLp_apply] using congrArg norm h
      rw [he]
      exact (PiLp.norm_apply_le _ j).trans_eq
        ((finiteL2CoordinateIsometry (X := Torus n) (I := Fin n) volume).norm_map _)
    have hentry (i j : Fin n) :
        ‖(scalarCommutator hn R hR s M b hb hs H hM i j is _hlen _hH)
          (sobolevMap (valueCoordinate j) s u)‖ ≤ C₀ * X := by
      have h := norm_torusSobolevCommutator_le hn R hR s M
        (fun ξ z ↦ b ξ z i j) ((matrixEntryEvaluation i j).contDiff.comp hb)
        (fun ξ ↦ hs ξ i j) H (hM i j) is _hlen (_hH i j)
        (sobolevMap (valueCoordinate j) s u)
      apply h.trans
      apply mul_le_mul_of_nonneg_left _ hC₀
      dsimp only [X]
      exact add_le_add (hcoord j)
        (mul_le_mul_of_nonneg_left (hcoordL2 j) (by positivity))
    have hrow (i : Fin n) : ‖matrixRows hn R hR s M b hb hs H hM is _hlen _hH u i‖ ≤
        (n : ℝ) * C₀ * X := by
      dsimp [matrixRows]
      simp only [PiLp.continuousLinearEquiv_symm_apply, PiLp.toLp_apply]
      rw [sum_apply]
      calc
        _ ≤ ∑ j, ‖(scalarCommutator hn R hR s M b hb hs H hM i j is _hlen _hH)
            (sobolevMap (valueCoordinate j) s u)‖ := norm_sum_le _ _
        _ ≤ ∑ _j : Fin n, C₀ * X := Finset.sum_le_sum fun j _ ↦ hentry i j
        _ = (n : ℝ) * C₀ * X := by simp [mul_assoc]
    let W := matrixRows hn R hR s M b hb hs H hM is _hlen _hH u
    have hW : W = ∑ i : Fin n, PiLp.single 2 i (W i) := by
      ext i
      simp [Pi.single_apply]
    calc
      ‖W‖ = ‖∑ i, PiLp.single 2 i (W i)‖ := congrArg norm hW
      _ ≤ ∑ i, ‖W i‖ := by
        simpa only [PiLp.norm_single] using norm_sum_le Finset.univ
          (fun i ↦ (PiLp.single 2 i (W i) : PiLp 2 (fun _ : Fin n ↦ L²)))
      _ ≤ ∑ _i : Fin n, (n : ℝ) * C₀ * X :=
        Finset.sum_le_sum fun i _ ↦ hrow i
      _ = (n : ℝ) ^ 2 * C₀ * X := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        simp only [Fintype.card_fin]
        ring
      _ = (n : ℝ) ^ 2 * C₀ * (‖u‖ + max 1 H * ‖toL2 s u‖) := by rfl

end JanetCartan.ContinuumCommutator.HigherRegularity.RealCommutator
