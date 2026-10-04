import Erdos524.SignConcentration
import Erdos524.ProductCoordinateReplacement
import Mathlib.MeasureTheory.Integral.Indicator

namespace Erdos524.FiniteSignWalk
open MeasureTheory ProbabilityTheory Set Filter
open Erdos524.SignGaussianMoments Erdos524.ProductCoordinateReplacement

noncomputable def walkPrefix {N : ℕ} (z : Fin N → ℝ) (k : ℕ) : ℝ := ∑ i, if i.val<k then z i else 0
noncomputable def hitEvent (N : ℕ) (t s : ℝ) : Set (Fin N → ℝ) := {z | ∃ k≤N, t≤s+walkPrefix z k}
noncomputable def hitProbability (N : ℕ) (t s : ℝ) : ℝ := (Measure.pi (fun _ : Fin N => signLaw)).real (hitEvent N t s)

theorem walkPrefix_zero {N : ℕ} (z : Fin N → ℝ) : walkPrefix z 0=0 := by simp [walkPrefix]
theorem walkPrefix_cons {N : ℕ} (a : ℝ) (z : Fin N → ℝ) (k : ℕ) :
    walkPrefix (Fin.cons a z) (k+1)=a+walkPrefix z k := by
  unfold walkPrefix
  rw [Fin.sum_univ_succ]
  simp

theorem hitEvent_measurable (N : ℕ) (t s : ℝ) : MeasurableSet (hitEvent N t s) := by
  have hm (k : ℕ) : Measurable (fun z : Fin N → ℝ => walkPrefix z k) := by
    unfold walkPrefix
    fun_prop
  have he : hitEvent N t s=⋃ k : Fin (N+1), {z | t≤s+walkPrefix z k.val} := by
    ext z
    simp only [hitEvent,Set.mem_setOf_eq,Set.mem_iUnion]
    constructor
    · rintro ⟨k,hk,hh⟩
      exact ⟨⟨k,by omega⟩,hh⟩
    · rintro ⟨k,hh⟩
      exact ⟨k.val,by omega,hh⟩
  rw [he]
  exact MeasurableSet.iUnion (fun k => measurableSet_le measurable_const (measurable_const.add (hm k.val)))

theorem hitEvent_cons_iff {N : ℕ} (a : ℝ) (z : Fin N → ℝ) (t s : ℝ) :
    Fin.cons a z∈hitEvent (N+1) t s ↔ t≤s ∨ z∈hitEvent N t (s+a) := by
  constructor
  · rintro ⟨k,hk,hh⟩
    cases k with
    | zero => left; simpa only [walkPrefix_zero,add_zero] using hh
    | succ k =>
      right
      refine ⟨k,by omega,?_⟩
      rw [walkPrefix_cons] at hh
      linarith
  · rintro (h|⟨k,hk,hh⟩)
    · exact ⟨0,by omega,by simpa only [walkPrefix_zero,add_zero] using h⟩
    · refine ⟨k+1,by omega,?_⟩
      rw [walkPrefix_cons]
      linarith

theorem insertCoordinate_zero {N : ℕ} (a : ℝ) (z : Fin N → ℝ) : insertCoordinate (0 : Fin (N+1)) a z=Fin.cons a z := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;>
    simp [insertCoordinate,MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv]

theorem hitProbability_of_le {N : ℕ} {t s : ℝ} (ht : t≤s) : hitProbability N t s=1 := by
  have he : hitEvent N t s=univ := by
    ext z
    simp only [Set.mem_univ,iff_true]
    exact ⟨0,by omega,by simpa only [walkPrefix_zero,add_zero] using ht⟩
  simp [hitProbability,he]

theorem hitProbability_zero (t s : ℝ) : hitProbability 0 t s=if t≤s then 1 else 0 := by
  by_cases h : t≤s
  · simp [h,hitProbability_of_le h]
  · have he : hitEvent 0 t s=∅ := by
      ext z
      simp only [hitEvent,Set.mem_setOf_eq,Set.mem_empty_iff_false,iff_false,not_exists]
      rintro k ⟨hk,hh⟩
      have hk0 : k=0 := by omega
      subst k
      exact h (by simpa only [walkPrefix_zero,add_zero] using hh)
    simp [hitProbability,he,h]

end Erdos524.FiniteSignWalk
