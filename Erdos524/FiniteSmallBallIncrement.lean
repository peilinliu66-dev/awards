import Erdos524.FiniteGaussianCubes

/-! A uniform radius-increment estimate for the full finite-evaluation infimum. -/

namespace Erdos524.FiniteSmallBallIncrement

open Set Filter MeasureTheory ProbabilityTheory Matrix WithLp
open scoped ENNReal
open Erdos524.FiniteGaussianCubes Erdos524.FiniteSmallBallEnvelope
open Erdos524.FiniteSmallBallBasic Erdos524.LaplaceKernelComparison Erdos524.GaussianBoxDensity

variable {n : ℕ}

theorem finiteKernel_cube_increment (u : Fin n → ℝ) (hu : ∀ i, 0 ≤ u i)
    {T δ ε : ℝ} (hT : 0 ≤ T) (hδ : 0 < δ) (hε : 0 ≤ ε) :
    (multivariateGaussian 0 (finiteKernel u)) (ofLp ⁻¹' cube n (δ + ε)) ≤
      (multivariateGaussian 0 (finiteKernel u)) (ofLp ⁻¹' cube n δ) +
        (ENNReal.ofReal (2 * ε / Real.exp (-T)) +
          ENNReal.ofReal (Real.exp 1 / (δ * Real.sqrt (T + 1)))) := by
  classical
  let P := multivariateGaussian 0 (finiteKernel u)
  let s : Finset (Fin n) := Finset.univ.filter (fun i ↦ u i ≤ T)
  let f : Fin s.card → Fin n := fun i ↦ (s.equivFin.symm i).val
  let g : Fin sᶜ.card → Fin n := fun i ↦ (sᶜ.equivFin.symm i).val
  let A := fun d : ℝ ↦ (fun z : EuclideanSpace ℝ (Fin n) ↦ fun i ↦ z (f i)) ⁻¹' cube s.card d
  let B := fun d : ℝ ↦ (fun z : EuclideanSpace ℝ (Fin n) ↦ fun i ↦ z (g i)) ⁻¹' cube sᶜ.card d
  have hcover (j : Fin n) : (∃ i, f i = j) ∨ ∃ i, g i = j := by
    by_cases hj : j ∈ s
    · left
      exact ⟨s.equivFin ⟨j, hj⟩, congrArg Subtype.val (s.equivFin.symm_apply_apply ⟨j, hj⟩)⟩
    · right
      have hj' : j ∈ sᶜ := Finset.mem_compl.mpr hj
      exact ⟨sᶜ.equivFin ⟨j, hj'⟩, congrArg Subtype.val (sᶜ.equivFin.symm_apply_apply ⟨j, hj'⟩)⟩
  have hcore (i : Fin s.card) : u (f i) ≤ T := (Finset.mem_filter.mp (s.equivFin.symm i).property).2
  have htail (i : Fin sᶜ.card) : T ≤ u (g i) := by
    have hnot : g i ∉ s := Finset.mem_compl.mp (sᶜ.equivFin.symm i).property
    apply le_of_lt
    apply lt_of_not_ge
    intro hi
    exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
  have hinc : P (A (δ + ε)) ≤ P (A δ) + ENNReal.ofReal (2 * ε / Real.exp (-T)) := by
    dsimp only [P, A]
    rw [finiteKernel_projection_cube u hu f, finiteKernel_projection_cube u hu f]
    exact finiteKernel_cube_increment_bounded (fun i ↦ u (f i)) (fun i ↦ hu (f i)) hcore hε δ
  have hbad : P (B δ)ᶜ ≤ ENNReal.ofReal (Real.exp 1 / (δ * Real.sqrt (T + 1))) := by
    have hp := finiteKernel_projection_cube u hu g δ
    have ht := finiteKernel_cube_compl_tail (fun i ↦ u (g i)) hT htail hδ
    rw [prob_compl_eq_one_sub ((measurable_cube _ _).preimage (by fun_prop))] at ht
    rw [← hp] at ht
    rw [prob_compl_eq_one_sub ((measurable_cube _ _).preimage (by fun_prop))]
    exact ht
  have hsplit (d : ℝ) : (ofLp : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ)) ⁻¹' cube n d = A d ∩ B d :=
    cube_split f g hcover d
  have hcoreP := measure_le_inter_add_compl P (A δ) (B δ)
  rw [← hsplit δ] at hcoreP
  calc
    _ ≤ P (A (δ + ε)) := measure_mono (by rw [hsplit]; exact inter_subset_left)
    _ ≤ P (A δ) + ENNReal.ofReal (2 * ε / Real.exp (-T)) := hinc
    _ ≤ (P (ofLp ⁻¹' cube n δ) + P (B δ)ᶜ) + ENNReal.ofReal (2 * ε / Real.exp (-T)) :=
      add_le_add hcoreP le_rfl
    _ ≤ (P (ofLp ⁻¹' cube n δ) + ENNReal.ofReal (Real.exp 1 / (δ * Real.sqrt (T + 1)))) +
        ENNReal.ofReal (2 * ε / Real.exp (-T)) := by gcongr
    _ = _ := by ac_rfl

theorem finiteSmallBall_increment {T δ ε : ℝ} (hT : 0 ≤ T) (hδ : 0 < δ) (hε : 0 ≤ ε) :
    finiteSmallBall (δ + ε) ≤ finiteSmallBall δ +
      (ENNReal.ofReal (2 * ε / Real.exp (-T)) +
        ENNReal.ofReal (Real.exp 1 / (δ * Real.sqrt (T + 1)))) := by
  change finiteSmallBall (δ + ε) ≤ (⨅ (n : ℕ) (u : Fin (n + 1) → NNReal),
    (multivariateGaussian 0 (finiteKernel (fun i ↦ (u i : ℝ))))
      (ofLp ⁻¹' box (fun _ ↦ δ))) + _
  rw [ENNReal.iInf_add]
  apply le_iInf
  intro n
  rw [ENNReal.iInf_add]
  apply le_iInf
  intro u
  have h := finiteKernel_cube_increment (fun i ↦ (u i : ℝ)) (fun i ↦ (u i).property) hT hδ hε
  exact (finiteSmallBall_le_evaluation (δ + ε) n u).trans h

theorem smallBallReal_increment {T δ ε : ℝ} (hT : 0 ≤ T) (hδ : 0 < δ) (hε : 0 ≤ ε) :
    smallBallReal (δ + ε) ≤ smallBallReal δ + 2 * ε / Real.exp (-T) +
      Real.exp 1 / (δ * Real.sqrt (T + 1)) := by
  have h := (ENNReal.toReal_le_toReal (finiteSmallBall_ne_top _) (by simp [ENNReal.add_ne_top, finiteSmallBall_ne_top])).mpr
    (finiteSmallBall_increment hT hδ hε)
  rw [ENNReal.toReal_add (finiteSmallBall_ne_top _) (by finiteness),
    ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * ε / Real.exp (-T)),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.exp 1 / (δ * Real.sqrt (T + 1)))] at h
  simpa only [smallBallReal, add_assoc] using h

end Erdos524.FiniteSmallBallIncrement
