import Erdos524.GaussianGridBudget
import Erdos524.PolynomialGridCover

namespace Erdos524.GaussianGridOscillation
open MeasureTheory ProbabilityTheory Filter Set Matrix WithLp
open Erdos524.LaplaceKernelComparison Erdos524.LaplaceIncrementBudget Erdos524.FiniteGaussianTailBound
open Erdos524.FiniteCellVariation Erdos524.FiniteL2Variation Erdos524.GaussianGridBudget

noncomputable def gridPoints (J : ℕ) (h : ℝ) : Fin (J+1) → ℝ := fun j => (j:ℝ)*h
noncomputable def jointPoints {m : ℕ} (J : ℕ) (h : ℝ) (u : Fin m → ℝ) : Fin ((J+1)+m) → ℝ :=
  Fin.addCases (gridPoints J h) u
noncomputable def jointMeasure {m : ℕ} (J : ℕ) (h : ℝ) (u : Fin m → ℝ) : Measure (EuclideanSpace ℝ (Fin ((J+1)+m))) :=
  multivariateGaussian 0 (finiteKernel (jointPoints J h u))
instance {m : ℕ} (J : ℕ) (h : ℝ) (u : Fin m → ℝ) : IsProbabilityMeasure (jointMeasure J h u) := by unfold jointMeasure; infer_instance

theorem jointPoints_nonneg {m : ℕ} (J : ℕ) {h : ℝ} (hh : 0≤h) (u : Fin m → ℝ) (hu : ∀ i, 0≤u i) :
    ∀ i, 0≤jointPoints J h u i := by
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [jointPoints,Fin.addCases_left,gridPoints]
    positivity
  · simpa only [jointPoints,Fin.addCases_right] using hu j

theorem cell_variation_on_joint {m : ℕ} (J : ℕ) {h : ℝ} (hh : 0≤h) (u : Fin m → ℝ) (hu : ∀ i, 0≤u i)
    (j : Fin (J+1)) :
    ∃ V : EuclideanSpace ℝ (Fin ((J+1)+m)) → ℝ,
      Measurable V ∧ MemLp V 2 (jointMeasure J h u) ∧ (∀ z, 0≤V z) ∧
      (∀ z i, (j:ℝ)*h≤u i → u i≤((j.val+1:ℕ):ℝ)*h → |z (Fin.natAdd (J+1) i)-z (Fin.castAdd m j)|≤V z) ∧
      (∫ z, (V z)^2 ∂jointMeasure J h u)≤(cellBudget h j.val)^2 := by
  classical
  let s : Finset (Fin m) := Finset.univ.filter (fun i => (j:ℝ)*h≤u i ∧ u i≤((j.val+1:ℕ):ℝ)*h)
  let f : Fin s.card → Fin m := fun k => (s.equivFin.symm k).val
  let q : Fin (s.card+1) → Fin ((J+1)+m) := Fin.cons (Fin.castAdd m j) (fun k => Fin.natAdd (J+1) (f k))
  let p := fun k => jointPoints J h u (q k)
  let X : EuclideanSpace ℝ (Fin ((J+1)+m)) → Fin (s.card+1) → ℝ := fun z k => z (q k)
  have hmem (k : Fin s.card) : (j:ℝ)*h≤u (f k) ∧ u (f k)≤((j.val+1:ℕ):ℝ)*h :=
    (Finset.mem_filter.mp (s.equivFin.symm k).property).2
  have hlo : ∀ k, (j:ℝ)*h≤p k := by
    intro k
    refine Fin.cases ?_ (fun k => ?_) k
    · simp only [p,q,Fin.cons_zero,jointPoints,Fin.addCases_left,gridPoints]
      exact le_rfl
    · simpa only [p,q,Fin.cons_succ,jointPoints,Fin.addCases_right] using (hmem k).1
  have hhi : ∀ k, p k≤((j.val+1:ℕ):ℝ)*h := by
    intro k
    refine Fin.cases ?_ (fun k => ?_) k
    · simp only [p,q,Fin.cons_zero,jointPoints,Fin.addCases_left,gridPoints]
      push_cast
      nlinarith
    · simpa only [p,q,Fin.cons_succ,jointPoints,Fin.addCases_right] using (hmem k).2
  have hinc : ∀ i k, (∫ z, (X z i-X z k)^2 ∂jointMeasure J h u)≤(Real.exp 1*(rootBudget (p i)-rootBudget (p k)))^2 :=
    fun i k => finite_increment_budget (jointPoints J h u) (jointPoints_nonneg J hh u hu) (q i) (q k)
  obtain ⟨V,hVm,hVp,hV0,hVb,hVE⟩ := exists_cell_variation p X (by intro k; fun_prop)
    (fun k => gaussian_coordinate_memLp_two _ (q k)) (by positivity : (0:ℝ)≤(j:ℝ)*h) hlo hhi hinc
  refine ⟨V,hVm,hVp,hV0,?_,hVE⟩
  intro z i hi hi'
  have his : i∈s := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi,hi'⟩
  let k : Fin s.card := s.equivFin ⟨i,his⟩
  have hf : f k=i := congrArg Subtype.val (s.equivFin.symm_apply_apply ⟨i,his⟩)
  have hb := hVb z k.succ 0
  simpa only [X,q,Fin.cons_succ,Fin.cons_zero,hf] using hb

theorem exists_grid_oscillation {m : ℕ} (J : ℕ) {h : ℝ} (hh : 0<h) (u : Fin m → ℝ)
    (hu : ∀ i, 0≤u i) (hub : ∀ i, u i≤(J:ℝ)*h) :
    ∃ W : EuclideanSpace ℝ (Fin ((J+1)+m)) → ℝ,
      Measurable W ∧ Integrable W (jointMeasure J h u) ∧ (∀ z, 0≤W z) ∧
      (∀ z i, ∃ j : Fin (J+1), |z (Fin.natAdd (J+1) i)-z (Fin.castAdd m j)|≤W z) ∧
      (∫ z, W z ∂jointMeasure J h u)≤Real.sqrt (2*(Real.exp 1)^2*h) := by
  classical
  choose V hVm hVp hV0 hVb hVE using cell_variation_on_joint J hh.le u hu
  let W : EuclideanSpace ℝ (Fin ((J+1)+m)) → ℝ := fun z => ‖fun j : Fin (J+1) => V j z‖
  have hvec : MemLp (fun z => fun j : Fin (J+1) => V j z) 2 (jointMeasure J h u) := memLp_pi_iff.mpr hVp
  refine ⟨W,?_,(hvec.integrable (by norm_num)).norm,fun z => norm_nonneg _,?_,?_⟩
  · exact (measurable_pi_iff.mpr hVm).norm
  · intro z i
    let k : ℕ := ⌊u i/h⌋₊
    have hk : k≤J := by
      have hf := Nat.floor_le (div_nonneg (hu i) hh.le)
      have hb : u i/h≤(J:ℝ) := (div_le_iff₀ hh).mpr (hub i)
      have hl : (k:ℝ)≤(J:ℝ) := hf.trans hb
      exact_mod_cast hl
    let j : Fin (J+1) := ⟨k,by omega⟩
    have hlo : (j:ℝ)*h≤u i := (le_div_iff₀ hh).mp (Nat.floor_le (div_nonneg (hu i) hh.le))
    have hhi : u i≤((j.val+1:ℕ):ℝ)*h := by
      have he := Nat.lt_floor_add_one (u i/h)
      apply (div_le_iff₀ hh).mp
      simpa only [Nat.cast_add,Nat.cast_one] using he.le
    refine ⟨j,(hVb j z i hlo hhi).trans ?_⟩
    have hn := norm_le_pi_norm (fun j : Fin (J+1) => V j z) j
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hV0 j z)] using hn
  · have he := integral_pi_norm_le_sqrt_sum (fun z => fun j : Fin (J+1) => V j z) hVp
    apply he.trans
    apply Real.sqrt_le_sqrt
    exact (Finset.sum_le_sum (fun j _ => hVE j)).trans (sum_cellBudget_sq_le (J+1) hh.le)

end Erdos524.GaussianGridOscillation
