import Erdos524.WeightedTruncation

namespace Erdos524.QuantileCounting
open Set MeasureTheory
open scoped BigOperators
open Erdos524.CauchyKernel

noncomputable def affinePotential (a b A B t : ℝ) : ℝ :=
  ∫ x in Icc a b, (A-B*x)*evenPotential (x-t)
noncomputable def affineTruncatedPotential (a b A B τ t : ℝ) : ℝ :=
  ∫ x in Icc a b, (A-B*x)*truncatedPotential τ (x-t)

theorem potential_reciprocal_bound {M : ℝ} (hM : 1≤M) :
    logTanhPotential (1/M)≤Real.log (4*M) := by
  have hp : 0<M := by linarith
  have h := logTanhPotential_near_zero (by positivity : 0<1/M) ((div_le_one hp).mpr hM)
  simpa only [one_div,div_inv_eq_mul] using h

theorem affine_quantile_truncation_estimates {a b A B : ℝ}
    (hab : a<b) (hB : 0≤B) (hr : 0<A-B*b) (hM : 1≤A-B*a)
    (mesh : QuantileMesh a b (affineCDF a A B) ⌊affineCDF a A B b⌋₊) (t : ℝ) :
    0≤affinePotential a b A B t-affineTruncatedPotential a b A B (1/(A-B*a)) t ∧
    affinePotential a b A B t-affineTruncatedPotential a b A B (1/(A-B*a)) t ≤
      2*Real.log (4*(A-B*a))+2 ∧
    |(∑ i, truncatedPotential (1/(A-B*a)) (mesh.node i-t))-
      affineTruncatedPotential a b A B (1/(A-B*a)) t|≤3*logTanhPotential (1/(A-B*a)) := by
  have hMp : 0<A-B*a := by linarith
  have hbound : ∀ x ∈ Icc a b, 0≤A-B*x ∧ A-B*x≤A-B*a := by
    intro x hx
    have h1 := mul_le_mul_of_nonneg_left hx.1 hB
    have h2 := mul_le_mul_of_nonneg_left hx.2 hB
    constructor <;> linarith
  have hgap := weighted_truncation_gap a b A B t (by positivity : 0<1/(A-B*a)) hMp.le hbound
  have hdisc := affine_quantile_potential_discrepancy hab hB hr (by positivity : 0<1/(A-B*a)) mesh t
  rw [integral_affineMeasure hB hr.le] at hdisc
  exact ⟨hgap.1,hgap.2.trans (scaled_near_integral_bound hM),hdisc⟩

theorem truncated_omitted_lower {N : ℕ} (node : Fin N → ℝ) {τ : ℝ} (hτ : 0<τ)
    (i : Fin N) (t : ℝ) (hne : ∀ j, j≠i → node j≠t) :
    (∑ j, truncatedPotential τ (node j-t))-logTanhPotential τ ≤
      ∑ j ∈ Finset.univ.erase i, evenPotential (node j-t) := by
  classical
  have hsum := Finset.sum_erase_add Finset.univ (fun j => truncatedPotential τ (node j-t)) (Finset.mem_univ i)
  have he : (∑ j ∈ Finset.univ.erase i, truncatedPotential τ (node j-t)) ≤
      ∑ j ∈ Finset.univ.erase i, evenPotential (node j-t) := by
    apply Finset.sum_le_sum
    intro j hj
    exact sub_nonneg.mp (potential_truncation_nonneg hτ (sub_ne_zero.mpr (hne j (Finset.mem_erase.mp hj).1)))
  have hi := truncatedPotential_le hτ (node i-t)
  linarith

theorem affine_omitted_potential_lower {a b A B : ℝ}
    (hab : a<b) (hB : 0≤B) (hr : 0<A-B*b) (hM : 1≤A-B*a)
    (mesh : QuantileMesh a b (affineCDF a A B) ⌊affineCDF a A B b⌋₊)
    (i : Fin ⌊affineCDF a A B b⌋₊) (t : ℝ) (hne : ∀ j, j≠i → mesh.node j≠t) :
    affinePotential a b A B t-6*Real.log (4*(A-B*a))-2 ≤
      ∑ j ∈ Finset.univ.erase i, evenPotential (mesh.node j-t) := by
  have he := affine_quantile_truncation_estimates hab hB hr hM mesh t
  have hd := abs_le.mp he.2.2
  have hMp : 0<A-B*a := by linarith
  have ho := truncated_omitted_lower mesh.node (by positivity : 0<1/(A-B*a)) i t hne
  have hf := potential_reciprocal_bound hM
  linarith [he.2.1,hd.1]


theorem pair_minsep_of_full_separation {N : ℕ} (node : Fin N → ℝ) {M : ℝ} (hM : 0<M)
    (hsep : ∀ i j : Fin N, i<j → ((j:ℝ)-(i:ℝ))/M≤node j-node i)
    (i j : Fin N) (hij : i≠j) : 1/M≤|node j-node i| := by
  rcases lt_or_gt_of_ne hij with h | h
  · have hc : (i:ℝ)+1≤(j:ℝ) := by exact_mod_cast h
    have hd : 1/M≤((j:ℝ)-(i:ℝ))/M := (div_le_div_iff_of_pos_right hM).mpr (by linarith)
    exact (hd.trans (hsep i j h)).trans (le_abs_self _)
  · have hc : (j:ℝ)+1≤(i:ℝ) := by exact_mod_cast h
    have hd : 1/M≤((i:ℝ)-(j:ℝ))/M := (div_le_div_iff_of_pos_right hM).mpr (by linarith)
    have he := (hd.trans (hsep j i h)).trans (le_abs_self (node i-node j))
    simpa only [abs_sub_comm] using he

theorem truncatedPotential_eq_even_of_far {τ x : ℝ} (h : τ≤|x|) :
    truncatedPotential τ x=evenPotential x := by
  unfold truncatedPotential evenPotential
  by_cases hx : |x|≤τ
  · rw [if_pos hx,le_antisymm h hx]
  · rw [if_neg hx]

theorem affine_node_potential_upper {a b A B : ℝ}
    (hab : a<b) (hB : 0≤B) (hr : 0<A-B*b) (hM : 1≤A-B*a)
    (mesh : QuantileMesh a b (affineCDF a A B) ⌊affineCDF a A B b⌋₊)
    (i : Fin ⌊affineCDF a A B b⌋₊) :
    (∑ j ∈ Finset.univ.erase i, evenPotential (mesh.node j-mesh.node i)) ≤
      affinePotential a b A B (mesh.node i)+2*Real.log (4*(A-B*a)) := by
  have hMp : 0<A-B*a := by linarith
  have ht : 0<1/(A-B*a) := by positivity
  have hsep := affine_quantile_separation hab.le hB hr mesh
  have heq (j : Fin ⌊affineCDF a A B b⌋₊) (hj : j ∈ Finset.univ.erase i) :
      truncatedPotential (1/(A-B*a)) (mesh.node j-mesh.node i)=evenPotential (mesh.node j-mesh.node i) := by
    apply truncatedPotential_eq_even_of_far
    exact pair_minsep_of_full_separation mesh.node hMp hsep i j (Ne.symm (Finset.mem_erase.mp hj).1)
  have he := affine_quantile_truncation_estimates hab hB hr hM mesh (mesh.node i)
  have hsum := Finset.sum_erase_add Finset.univ
    (fun j => truncatedPotential (1/(A-B*a)) (mesh.node j-mesh.node i)) (Finset.mem_univ i)
  have hself : truncatedPotential (1/(A-B*a)) (mesh.node i-mesh.node i)=logTanhPotential (1/(A-B*a)) := by
    simp only [sub_self,truncatedPotential,abs_zero,if_pos ht.le]
  rw [hself,Finset.sum_congr rfl heq] at hsum
  have hd := abs_le.mp he.2.2
  have hf := potential_reciprocal_bound hM
  linarith [he.1,hd.2]

end Erdos524.QuantileCounting
