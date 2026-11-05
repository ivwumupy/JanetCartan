module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Retarded.NormComparison.MixedEvaluations

/-!
# Retarded mixed jets as Euclidean jet evaluations

The ordered derivatives in `app:ch_osc:prop:osc-retarded-tube` are evaluations of
the actual Euclidean Fréchet jets. This identity supplies the coordinate part of
the norm comparison consumed by `app:ch_response:eq:fixed-factor-transfer`.
The proof retains the time-first order and all repeated transverse directions,
and includes the case of no transverse coordinates.
-/

@[expose] public noncomputable section

open scoped ContDiff

namespace JanetCartan.ResponseTransfer

open RetardedSobolev RetardedSobolev.Spaces

/-- Ordered differentiation on the retarded product chart, used to identify
the mixed jets in `app:ch_osc:prop:osc-retarded-tube`. -/
private theorem iteratedFDeriv_eq_directionalFold {d : ℕ}
    {f : ℝ × (Fin d → ℝ) → ℂ} (hf : ContDiff ℝ ∞ f) (n : ℕ)
    (v : Fin n → ℝ × (Fin d → ℝ)) (x : ℝ × (Fin d → ℝ)) :
    iteratedFDeriv ℝ n f x v =
      (List.ofFn v).foldr (fun w g x ↦ fderiv ℝ g x w) f x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [(hf.differentiable_iteratedFDeriv (m := n)
      (by exact_mod_cast ENat.natCast_lt_top n) x).iteratedFDeriv_succ_apply_left']
    simp only [List.ofFn_succ, List.foldr_cons]
    have he := funext (ih (Fin.tail v))
    rw [he]
    rfl

/-- The transverse block of the mixed jet in
`app:ch_osc:prop:osc-retarded-tube` is an ordered fold of full differentials. -/
private theorem transverseJet_eq_directionalFold {d : ℕ}
    {f : ℝ × (Fin d → ℝ) → ℂ} (hf : ContDiff ℝ ∞ f) (vs : List (Fin d → ℝ)) :
    transverseJet vs f =
      (vs.map (fun v ↦ (0, v))).foldr (fun w g x ↦ fderiv ℝ g x w) f := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    rw [transverseJet, transverseDeriv_eq_fderiv
      v ((contDiff_transverseJet hf vs).differentiable (by simp)), ih]
    rfl

/-- The time block of the mixed jet in `app:ch_osc:prop:osc-retarded-tube`
is repeated full differentiation in the time direction. -/
private theorem timeJet_eq_directionalFold {d : ℕ}
    {f : ℝ × (Fin d → ℝ) → ℂ} (hf : ContDiff ℝ ∞ f) (t : ℕ) :
    timeJet t f =
      (List.replicate t (1, (0 : Fin d → ℝ))).foldr
        (fun w g x ↦ fderiv ℝ g x w) f := by
  induction t with
  | zero => simp [timeJet_zero]
  | succ t ih =>
    rw [timeJet_succ, timeDeriv_eq_fderiv
      ((contDiff_timeJet hf t).differentiable (by simp)), ih]
    rfl

/-- The first Euclidean basis vector is the time direction of
`app:ch_osc:prop:osc-retarded-tube`. -/
private theorem retardedCoordinates_basisFun_zero (d : ℕ) :
    retardedCoordinates d (EuclideanSpace.basisFun (Fin (d + 1)) ℝ 0) =
      (1, (0 : Fin d → ℝ)) := by
  ext j <;> simp [retardedCoordinates_apply, EuclideanSpace.basisFun_apply]

/-- The remaining Euclidean basis vectors are the transverse directions of
`app:ch_osc:prop:osc-retarded-tube`. -/
private theorem retardedCoordinates_basisFun_succ {d : ℕ} (r : Fin d) :
    retardedCoordinates d (EuclideanSpace.basisFun (Fin (d + 1)) ℝ r.succ) =
      (0, Pi.single r 1) := by
  ext j <;> simp [retardedCoordinates_apply, EuclideanSpace.basisFun_apply, Pi.single_apply]

/-- The published directions retain exactly the time and transverse blocks,
including multiplicities, of `app:ch_osc:prop:osc-retarded-tube`. -/
private theorem retardedJetDirections_ofFn {d s : ℕ} (i : JetIndex d s) :
    List.ofFn (fun q ↦ retardedCoordinates d (retardedJetDirections i q)) =
      List.replicate i.2.2.val (1, (0 : Fin d → ℝ)) ++
      (List.ofFn (fun r ↦ Pi.single (i.2.1 r) 1)).map (fun v ↦ (0, v)) := by
  unfold retardedJetDirections retardedJetOrder
  rw [List.map_ofFn]
  have he : (fun q : Fin (i.2.2.val + i.1.val) ↦
      retardedCoordinates d (EuclideanSpace.basisFun (Fin (d + 1)) ℝ
        (Fin.addCases (fun _ : Fin i.2.2.val ↦ 0) (fun r ↦ (i.2.1 r).succ) q))) =
      Fin.append (fun _ : Fin i.2.2.val ↦ (1, (0 : Fin d → ℝ)))
        (fun r ↦ (0, Pi.single (i.2.1 r) 1)) := by
    funext q
    refine Fin.addCases ?_ ?_ q
    · intro a
      simpa only [Fin.append, Fin.addCases_left] using retardedCoordinates_basisFun_zero d
    · intro b
      simpa only [Fin.append, Fin.addCases_right] using
        retardedCoordinates_basisFun_succ (i.2.1 b)
  rw [he, List.ofFn_fin_append, List.ofFn_const]
  rfl

/-- Every retarded mixed jet in `app:ch_osc:prop:osc-retarded-tube` is the
evaluation of the Euclidean Fréchet jet on its ordered coordinate directions.
Together with L² transport, this supplies the mixed-jet identity for the norm
comparison in `app:ch_response:eq:fixed-factor-transfer`. -/
theorem retardedJetEvaluation_iteratedFDeriv {d s : ℕ} (f : Test d)
    (i : JetIndex d s) (x : Euclidean (d + 1)) :
    retardedJetEvaluation (fun j ↦ iteratedFDeriv ℝ j (retardedTestFunction f) x) i =
      jet i f (Prod.swap (retardedCoordinates d x)) := by
  change iteratedFDeriv ℝ (retardedJetOrder i)
    (f.val ∘ (retardedCoordinates d).toContinuousLinearMap) x (retardedJetDirections i) = _
  rw [(retardedCoordinates d).toContinuousLinearMap.iteratedFDeriv_comp_right
    f.property.1 x (by simp)]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousLinearEquiv.coe_coe]
  rw [iteratedFDeriv_eq_directionalFold f.property.1, retardedJetDirections_ofFn,
    List.foldr_append]
  change _ = timeJet i.2.2.val
    (transverseJet (List.ofFn (fun r ↦ Pi.single (i.2.1 r) 1)) f) (retardedCoordinates d x)
  rw [timeJet_eq_directionalFold (contDiff_transverseJet f.property.1 _),
    transverseJet_eq_directionalFold f.property.1]

end JanetCartan.ResponseTransfer
