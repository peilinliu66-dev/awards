import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

namespace Erdos524.FiniteCouplingComparison
open MeasureTheory Filter Set

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

noncomputable def box {d : ℕ} (X : Ω → Fin d → ℝ) (r : ℝ) : Set Ω := {ω | ∀ j, |X ω j|≤r}
noncomputable def bad {d : ℕ} (X Y : Ω → Fin d → ℝ) (η : ℝ) : Set Ω := {ω | ∃ j, η < |X ω j-Y ω j| }

theorem box_measurable {d : ℕ} (X : Ω → Fin d → ℝ) (hX : ∀ j, Measurable (fun ω => X ω j)) (r : ℝ) :
    MeasurableSet (box X r) := by
  have he : box X r=⋂ j : Fin d, {ω | |X ω j|≤r} := by ext ω; simp [box]
  rw [he]
  exact MeasurableSet.iInter (fun j => measurableSet_le (continuous_abs.measurable.comp (hX j)) measurable_const)

theorem bad_measurable {d : ℕ} (X Y : Ω → Fin d → ℝ)
    (hX : ∀ j, Measurable (fun ω => X ω j)) (hY : ∀ j, Measurable (fun ω => Y ω j)) (η : ℝ) :
    MeasurableSet (bad X Y η) := by
  have he : bad X Y η=⋃ j : Fin d, {ω | η < |X ω j-Y ω j| } := by ext ω; simp [bad]
  rw [he]
  exact MeasurableSet.iUnion (fun j => measurableSet_lt measurable_const (continuous_abs.measurable.comp ((hX j).sub (hY j))))

theorem bad_probability_le {d : ℕ} (X Y : Ω → Fin d → ℝ)
    (hX : ∀ j, Measurable (fun ω => X ω j)) (hY : ∀ j, Measurable (fun ω => Y ω j))
    (hL : ∀ j, MemLp (fun ω => X ω j-Y ω j) 2 P) {η : ℝ} (hη : 0<η) :
    P.real (bad X Y η)≤(∑ j, ∫ ω, (X ω j-Y ω j)^2 ∂P)/η^2 := by
  have hi (j : Fin d) : Integrable (fun ω => (X ω j-Y ω j)^2) P := by
    simpa only [Real.norm_eq_abs,sq_abs] using (hL j).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hs : Integrable (fun ω => (∑ j, (X ω j-Y ω j)^2)/η^2) P :=
    (integrable_finsetSum Finset.univ (fun j _ => hi j)).div_const _
  rw [← integral_indicator_one (bad_measurable X Y hX hY η)]
  have he := integral_mono_ae ((integrable_const (1:ℝ)).indicator (bad_measurable X Y hX hY η)) hs (Eventually.of_forall (fun ω => ?_))
  · simpa only [integral_div,integral_finsetSum _ (fun j _ => hi j),Pi.one_def] using he
  · by_cases hb : ω∈bad X Y η
    · rw [Set.indicator_of_mem hb]
      change (1:ℝ)≤(∑ j, (X ω j-Y ω j)^2)/η^2
      apply (le_div_iff₀ (sq_pos_of_pos hη)).mpr
      obtain ⟨j,hj⟩ := hb
      have hsingle := Finset.single_le_sum (s := Finset.univ) (fun k _ => sq_nonneg (X ω k-Y ω k)) (Finset.mem_univ j)
      have hsq : η^2≤(X ω j-Y ω j)^2 := by nlinarith [sq_abs (X ω j-Y ω j)]
      simpa only [one_mul] using hsq.trans hsingle
    · rw [Set.indicator_of_notMem hb]
      positivity

theorem box_subset_enlarged_union_bad {d : ℕ} (X Y : Ω → Fin d → ℝ) (r η : ℝ) :
    box X r ⊆ box Y (r+η) ∪ bad X Y η := by
  intro ω hω
  by_cases hb : ω∈bad X Y η
  · exact Or.inr hb
  · left
    intro j
    have hd : |X ω j-Y ω j|≤η := le_of_not_gt (fun h => hb ⟨j,h⟩)
    have hh : |Y ω j|≤|X ω j|+|X ω j-Y ω j| := by
      have ht := abs_add_le (X ω j) (Y ω j-X ω j)
      have he : X ω j+(Y ω j-X ω j)=Y ω j := by ring
      rw [he,abs_sub_comm (Y ω j) (X ω j)] at ht
      exact ht
    exact hh.trans (add_le_add (hω j) hd)

theorem box_probability_comparison {d : ℕ} (X Y : Ω → Fin d → ℝ)
    (hX : ∀ j, Measurable (fun ω => X ω j)) (hY : ∀ j, Measurable (fun ω => Y ω j))
    (hL : ∀ j, MemLp (fun ω => X ω j-Y ω j) 2 P) {η : ℝ} (hη : 0<η) (r : ℝ) :
    P.real (box X r)≤P.real (box Y (r+η))+(∑ j, ∫ ω, (X ω j-Y ω j)^2 ∂P)/η^2 := by
  calc
    _ ≤ P.real (box Y (r+η) ∪ bad X Y η) := measureReal_mono (box_subset_enlarged_union_bad X Y r η)
    _ ≤ P.real (box Y (r+η))+P.real (bad X Y η) := measureReal_union_le _ _
    _ ≤ _ := add_le_add le_rfl (bad_probability_le X Y hX hY hL hη)

end Erdos524.FiniteCouplingComparison
