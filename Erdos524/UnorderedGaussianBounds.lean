import Erdos524.GaussianCoordinateProjection
import Erdos524.FiniteGaussianCoreBound
import Mathlib.Data.Finset.Sort

/-! Uniform finite Gaussian bounds without ordering or distinctness assumptions on evaluations. -/

namespace Erdos524.UnorderedGaussianBounds

open MeasureTheory ProbabilityTheory Matrix WithLp
open Erdos524.CauchyKernel Erdos524.GaussianCoordinateProjection
open Erdos524.FiniteGaussianTailBound Erdos524.FiniteGaussianCoreBound

variable {n : ℕ}

theorem finite_ordered_factorization (v : Fin (n + 1) → ℝ) :
    ∃ m : ℕ, ∃ t : Fin (m + 1) → ℝ, ∃ f : Fin (n + 1) → Fin (m + 1),
      StrictMono t ∧ (∀ i, t (f i) = v i) ∧ ∀ j, ∃ i, t j = v i := by
  classical
  let s := Finset.univ.image v
  have hs : s.Nonempty := ⟨v 0, Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Finset.card_ne_zero.mpr hs)
  let e := s.orderIsoOfFin hm
  let t : Fin (m + 1) → ℝ := s.orderEmbOfFin hm
  let f : Fin (n + 1) → Fin (m + 1) :=
    fun i ↦ e.symm ⟨v i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  refine ⟨m, t, f, (s.orderEmbOfFin hm).strictMono, ?_, ?_⟩
  · intro i
    exact congrArg Subtype.val (e.apply_symm_apply ⟨v i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩)
  · intro j
    obtain ⟨i, _, he⟩ := Finset.mem_image.mp (s.orderEmbOfFin_mem hm j)
    exact ⟨i, he.symm⟩

theorem integral_cauchy_sup_norm_unordered_le (v : Fin (n + 1) → ℝ)
    {V : ℝ} (hV : 0 < V) (hv : ∀ i, V ≤ v i) :
    (∫ z : EuclideanSpace ℝ (Fin (n + 1)), ‖ofLp z‖ ∂multivariateGaussian 0 (cauchy v)) ≤
      1 / Real.sqrt V := by
  obtain ⟨m, t, f, ht, hf, hrange⟩ := finite_ordered_factorization v
  have hlow (j : Fin (m + 1)) : V ≤ t j := by
    obtain ⟨i, hi⟩ := hrange j
    rw [hi]
    exact hv i
  have htpos (j : Fin (m + 1)) : 0 < t j := hV.trans_le (hlow j)
  have he : (cauchy t).submatrix f f = cauchy v := by ext i j; simp only [Matrix.submatrix_apply, cauchy, hf]
  have hp := integral_projection_sup_norm_le (posSemidef_cauchy_fin t htpos) f
  rw [he] at hp
  refine hp.trans ((integral_cauchy_sup_norm_le t htpos (fun j ↦ ht.monotone (by change j.val ≤ j.val + 1; omega))).trans ?_)
  exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr hV) (Real.sqrt_le_sqrt (hlow 0))

theorem integral_stationary_sup_norm_unordered_le (v : Fin (n + 1) → ℝ)
    {a b : ℝ} (hlo : ∀ i, a ≤ v i) (hhi : ∀ i, v i ≤ b) :
    (∫ z : EuclideanSpace ℝ (Fin (n + 1)), ‖ofLp z‖
      ∂multivariateGaussian 0 (normalized (fun i ↦ Real.exp (v i)))) ≤
        1 + (b - a) / Real.sqrt 8 := by
  obtain ⟨m, t, f, ht, hf, hrange⟩ := finite_ordered_factorization v
  have hlow (j : Fin (m + 1)) : a ≤ t j := by
    obtain ⟨i, hi⟩ := hrange j
    rw [hi]
    exact hlo i
  have hhigh (j : Fin (m + 1)) : t j ≤ b := by
    obtain ⟨i, hi⟩ := hrange j
    rw [hi]
    exact hhi i
  have he : (normalized (fun j ↦ Real.exp (t j))).submatrix f f =
      normalized (fun i ↦ Real.exp (v i)) := by
    ext i j
    simp only [Matrix.submatrix_apply, normalized, hf]
  have hp := integral_projection_sup_norm_le
    (posSemidef_normalized_fin (fun j ↦ Real.exp (t j)) (fun j ↦ Real.exp_pos _)) f
  rw [he] at hp
  refine hp.trans ((integral_stationary_sup_norm_le t (fun j ↦ ht.monotone (by change j.val ≤ j.val + 1; omega))).trans ?_)
  apply add_le_add_right
  exact div_le_div_of_nonneg_right (by linarith [hlow 0, hhigh (Fin.last m)]) (Real.sqrt_nonneg _)

end Erdos524.UnorderedGaussianBounds
