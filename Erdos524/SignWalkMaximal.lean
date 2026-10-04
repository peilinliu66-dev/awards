import Erdos524.SignWalkExponential
import Erdos524.SignSymmetry

namespace Erdos524.FiniteSignWalk
open MeasureTheory ProbabilityTheory Set
open Erdos524.SignGaussianMoments Erdos524.SignSymmetry

noncomputable def absHitEvent (N : ℕ) (t : ℝ) : Set (Fin N → ℝ) := {z | ∃ k≤N, t≤|walkPrefix z k|}

theorem walkPrefix_neg {N : ℕ} (z : Fin N → ℝ) (k : ℕ) : walkPrefix (fun i => -z i) k=-walkPrefix z k := by
  unfold walkPrefix
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs <;> simp

theorem absHitEvent_eq_union (N : ℕ) (t : ℝ) : absHitEvent N t=hitEvent N t 0 ∪
    (fun z : Fin N → ℝ => fun i => -z i) ⁻¹' hitEvent N t 0 := by
  ext z
  simp only [absHitEvent,hitEvent,Set.mem_setOf_eq,Set.mem_union,Set.mem_preimage,zero_add,walkPrefix_neg,le_abs]
  constructor
  · rintro ⟨k,hk,h|h⟩
    · exact Or.inl ⟨k,hk,h⟩
    · exact Or.inr ⟨k,hk,h⟩
  · rintro (⟨k,hk,h⟩|⟨k,hk,h⟩)
    · exact ⟨k,hk,Or.inl h⟩
    · exact ⟨k,hk,Or.inr h⟩

theorem absHitEvent_measurable (N : ℕ) (t : ℝ) : MeasurableSet (absHitEvent N t) := by
  rw [absHitEvent_eq_union]
  exact (hitEvent_measurable N t 0).union ((hitEvent_measurable N t 0).preimage (by fun_prop))

theorem abs_maximal_hoeffding {N : ℕ} (hN : 0<N) {t : ℝ} (ht : 0≤t) :
    (Measure.pi (fun _ : Fin N => signLaw)).real (absHitEvent N t)≤2*Real.exp (-t^2/(2*(N:ℝ))) := by
  have hm := congrArg (fun μ : Measure (Fin N → ℝ) => μ.real (hitEvent N t 0)) (pi_sign_map_neg N)
  simp only [Measure.real] at hm
  rw [Measure.map_apply (by fun_prop) (hitEvent_measurable N t 0)] at hm
  have hu := measureReal_union_le (μ := Measure.pi (fun _ : Fin N => signLaw)) (hitEvent N t 0)
    ((fun z : Fin N → ℝ => fun i => -z i) ⁻¹' hitEvent N t 0)
  rw [absHitEvent_eq_union]
  have hh := hitProbability_hoeffding hN ht
  change (Measure.pi (fun _ : Fin N => signLaw)).real ((fun z : Fin N → ℝ => fun i => -z i) ⁻¹' hitEvent N t 0)=hitProbability N t 0 at hm
  rw [hm] at hu
  change (Measure.pi (fun _ : Fin N => signLaw)).real _≤hitProbability N t 0+hitProbability N t 0 at hu
  linarith

end Erdos524.FiniteSignWalk
