import Erdos524.RandomPolynomialTail
import Erdos524.RandomPolynomialSplit

namespace Erdos524.RandomPolynomialModel
open MeasureTheory ProbabilityTheory Set
open Erdos524.SignGaussianMoments Erdos524.FiniteSignWalk Erdos524.FinitePolynomialAbel
open Erdos524.PolynomialAbel Erdos524.UniformPolynomialTail

noncomputable def twoWalkMax {N : ℕ} (z : Fin N → ℝ) : ℝ := max (walkMax z) (walkMax (alternatingVector z))

theorem twoWalkMax_measurable (N : ℕ) : Measurable (twoWalkMax (N := N)) :=
  (walkMax_continuous N).measurable.max ((walkMax_continuous N).measurable.comp (by unfold alternatingVector; fun_prop))

theorem twoWalkMax_tail {N : ℕ} (hN : 0<N) {t : ℝ} (ht : 0<t) :
    (Measure.pi (fun _ : Fin N => signLaw)).real {z | t≤twoWalkMax z}≤4*Real.exp (-t^2/(2*(N:ℝ))) := by
  let μ := Measure.pi (fun _ : Fin N => signLaw)
  let E := {z : Fin N → ℝ | t≤walkMax z}
  have hm : MeasurableSet E := measurableSet_le measurable_const (walkMax_continuous N).measurable
  have hA : Measurable (alternatingVector (N := N)) := by unfold alternatingVector; fun_prop
  have hlaw := congrArg (fun ν : Measure (Fin N → ℝ) => ν.real E) (alternatingVector_map N)
  unfold Measure.real at hlaw
  rw [Measure.map_apply hA hm] at hlaw
  have he : {z : Fin N → ℝ | t≤twoWalkMax z}=E ∪ alternatingVector ⁻¹' E := by ext z; simp [twoWalkMax,E,le_max_iff]
  have hb : μ.real E≤2*Real.exp (-t^2/(2*(N:ℝ))) := by
    rw [show E=absHitEvent N t from walkMax_level_eq ht]
    exact abs_maximal_hoeffding hN ht.le
  change μ.real (alternatingVector ⁻¹' E)=μ.real E at hlaw
  rw [he]
  have hu := measureReal_union_le (μ := μ) E (alternatingVector ⁻¹' E)
  rw [hlaw] at hu
  linarith

theorem walkPrefix_finitePrefix (ω : Ω) {N k : ℕ} (hk : k≤N) :
    walkPrefix (finitePrefix N ω) k=partialSum ω k := by
  let f : ℕ → ℝ := fun i => if i<k then ω i else 0
  have he : walkPrefix (finitePrefix N ω) k=∑ i : Fin N, f i.val := rfl
  rw [he,Fin.sum_univ_eq_sum_range f]
  exact sum_range_indicator hk ω

theorem fullNorm_le_twoWalkMax_prefix (ω : Ω) {N k : ℕ} (hk : k≤N) :
    fullNorm ω k≤twoWalkMax (finitePrefix N ω) := by
  have hR : 0≤twoWalkMax (finitePrefix N ω) := (norm_nonneg _).trans (le_max_left _ _)
  apply (fullNorm_le_iff ω k hR).mpr
  intro x
  apply polynomial_abs_le_two_walks ω k (abs_le.mpr x.property) hR
  · intro j hj
    rw [← walkPrefix_finitePrefix ω (hj.trans hk)]
    have h := norm_le_pi_norm (fun j : Fin (N+1) => walkPrefix (finitePrefix N ω) j.val) ⟨j,by omega⟩
    exact h.trans (le_max_left _ _)
  · intro j hj
    rw [← walkPrefix_finitePrefix (alternating ω) (hj.trans hk)]
    have h := norm_le_pi_norm (fun j : Fin (N+1) => walkPrefix (alternatingVector (finitePrefix N ω)) j.val) ⟨j,by omega⟩
    exact h.trans (le_max_right _ _)

theorem freshNorm_le_twoWalkMax (a : ℕ) (ω : Ω) {N k : ℕ} (hk : k≤N) :
    freshNorm a k ω≤twoWalkMax (finiteBlock a N ω) := by
  have h := fullNorm_le_twoWalkMax_prefix (fun i => ω (a+i)) hk
  rw [← finiteNorm_prefix] at h
  exact h

theorem freshNorm_maximal_tail (a : ℕ) {N : ℕ} (hN : 0<N) {t : ℝ} (ht : 0<t) :
    P.real {ω | ∃ k≤N, t≤freshNorm a k ω}≤4*Real.exp (-t^2/(2*(N:ℝ))) := by
  have hs : {ω : Ω | ∃ k≤N, t≤freshNorm a k ω}⊆(finiteBlock a N) ⁻¹' {z | t≤twoWalkMax z} := by
    rintro ω ⟨k,hk,hh⟩
    exact hh.trans (freshNorm_le_twoWalkMax a ω hk)
  have hm := congrArg (fun μ : Measure (Fin N → ℝ) => μ.real {z | t≤twoWalkMax z}) (finiteBlock_law a N)
  unfold Measure.real at hm
  rw [Measure.map_apply (measurable_finiteBlock a N) (measurableSet_le measurable_const (twoWalkMax_measurable N))] at hm
  have h := measureReal_mono (μ := P) hs
  change P.real ((finiteBlock a N) ⁻¹' {z | t≤twoWalkMax z})=_ at hm
  rw [hm] at h
  exact h.trans (twoWalkMax_tail hN ht)

theorem fullNorm_increment_maximal_tail (a : ℕ) {N : ℕ} (hN : 0<N) {t : ℝ} (ht : 0<t) :
    P.real {ω | ∃ n, a≤n ∧ n≤a+N ∧ t≤|fullNorm ω n-fullNorm ω a|}≤4*Real.exp (-t^2/(2*(N:ℝ))) := by
  have hs : {ω : Ω | ∃ n, a≤n ∧ n≤a+N ∧ t≤|fullNorm ω n-fullNorm ω a|}⊆
      {ω | ∃ k≤N, t≤freshNorm a k ω} := by
    rintro ω ⟨n,han,hn,hh⟩
    refine ⟨n-a,by omega,?_⟩
    have h := fullNorm_increment_le ω a (n-a)
    rw [Nat.add_sub_of_le han] at h
    exact hh.trans h
  exact (measureReal_mono hs).trans (freshNorm_maximal_tail a hN ht)

theorem fullNorm_maximal_tail {N : ℕ} (hN : 0<N) {t : ℝ} (ht : 0<t) :
    P.real {ω | ∃ k≤N, t≤fullNorm ω k}≤4*Real.exp (-t^2/(2*(N:ℝ))) := by
  have he (k : ℕ) (ω : Ω) : freshNorm 0 k ω=fullNorm ω k := by
    rw [freshNorm,show finiteBlock 0 k ω=finitePrefix k ω by ext i; simp [finiteBlock,finitePrefix],finiteNorm_prefix]
  simpa only [he] using freshNorm_maximal_tail 0 hN ht

end Erdos524.RandomPolynomialModel
