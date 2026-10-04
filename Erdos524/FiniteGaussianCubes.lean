import Erdos524.FiniteLaplaceBand

/-! Coordinate projection and splitting of Gaussian cubes, including empty subvectors. -/

namespace Erdos524.FiniteGaussianCubes

open Set MeasureTheory ProbabilityTheory Matrix WithLp
open scoped ENNReal
open Erdos524.GaussianCoordinateProjection Erdos524.LaplaceKernelComparison
open Erdos524.GaussianBoxDensity Erdos524.FiniteLaplaceBand Erdos524.FiniteSmallBallTail

variable {n k l : ℕ}

def cube (m : ℕ) (δ : ℝ) : Set (Fin m → ℝ) := Set.univ.pi (fun _ ↦ Icc (-δ) δ)

theorem measurable_cube (m : ℕ) (δ : ℝ) : MeasurableSet (cube m δ) :=
  MeasurableSet.univ_pi (fun _ ↦ measurableSet_Icc)

theorem cube_zero (δ : ℝ) : cube 0 δ = univ := by ext z; simp [cube]

theorem finiteKernel_projection_cube (u : Fin n → ℝ) (hu : ∀ i, 0 ≤ u i)
    (f : Fin k → Fin n) (δ : ℝ) :
    (multivariateGaussian 0 (finiteKernel u))
        ((fun z ↦ fun i ↦ z (f i)) ⁻¹' cube k δ) =
      (multivariateGaussian 0 (finiteKernel (fun i ↦ u (f i)))) (ofLp ⁻¹' cube k δ) := by
  have h := congrArg (fun μ : Measure (Fin k → ℝ) ↦ μ (cube k δ))
    (gaussian_coordinate_projection (finiteKernel_posSemidef u hu) f)
  rw [Measure.map_apply (by fun_prop) (measurable_cube _ _),
    Measure.map_apply (by fun_prop) (measurable_cube _ _)] at h
  exact h

theorem finiteKernel_cube_increment_bounded (u : Fin n → ℝ)
    {T ε : ℝ} (hu : ∀ i, 0 ≤ u i) (hT : ∀ i, u i ≤ T) (hε : 0 ≤ ε) (δ : ℝ) :
    (multivariateGaussian 0 (finiteKernel u)) (ofLp ⁻¹' cube n (δ + ε)) ≤
      (multivariateGaussian 0 (finiteKernel u)) (ofLp ⁻¹' cube n δ) +
        ENNReal.ofReal (2 * ε / Real.exp (-T)) := by
  cases n with
  | zero => simp only [cube_zero, preimage_univ, measure_univ]; exact le_self_add
  | succ n => exact finite_laplace_cube_increment u hu hT hε δ

theorem finiteKernel_cube_compl_tail (u : Fin n → ℝ)
    {T δ : ℝ} (hT : 0 ≤ T) (hu : ∀ i, T ≤ u i) (hδ : 0 < δ) :
    (multivariateGaussian 0 (finiteKernel u)) (ofLp ⁻¹' cube n δ)ᶜ ≤
      ENNReal.ofReal (Real.exp 1 / (δ * Real.sqrt (T + 1))) := by
  cases n with
  | zero => simp [cube_zero]
  | succ n =>
    rw [prob_compl_eq_one_sub ((measurable_cube _ _).preimage (by fun_prop))]
    have h := finiteKernel_box_lower u hT hu hδ
    apply tsub_le_iff_right.mpr
    simpa only [cube, box, add_comm] using tsub_le_iff_right.mp h

theorem cube_split (f : Fin k → Fin n) (g : Fin l → Fin n)
    (hcover : ∀ j, (∃ i, f i = j) ∨ ∃ i, g i = j) (δ : ℝ) :
    (ofLp : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ)) ⁻¹' cube n δ =
      (fun z : EuclideanSpace ℝ (Fin n) ↦ fun i ↦ z (f i)) ⁻¹' cube k δ ∩
      (fun z : EuclideanSpace ℝ (Fin n) ↦ fun i ↦ z (g i)) ⁻¹' cube l δ := by
  ext z
  simp only [Set.mem_preimage, cube, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc, Set.mem_inter_iff]
  constructor
  · intro h
    exact ⟨fun i ↦ h (f i), fun i ↦ h (g i)⟩
  · intro h j
    rcases hcover j with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact h.1 i
    · exact h.2 i

theorem measure_le_inter_add_compl {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (A B : Set Ω) : μ A ≤ μ (A ∩ B) + μ Bᶜ := by
  apply (measure_mono (show A ⊆ (A ∩ B) ∪ Bᶜ from ?_)).trans (measure_union_le _ _)
  intro x hx
  by_cases hb : x ∈ B
  · exact Or.inl ⟨hx, hb⟩
  · exact Or.inr hb

end Erdos524.FiniteGaussianCubes
