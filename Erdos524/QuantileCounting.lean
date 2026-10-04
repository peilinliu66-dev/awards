import Erdos524.LogTanhPotential
import Mathlib.Data.Fintype.Fin
import Mathlib.Topology.Order.IntermediateValue

namespace Erdos524.QuantileCounting
open Set
open scoped BigOperators

noncomputable def midpointCount (N : ℕ) (z : ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i : Fin N => (i:ℝ)+(1/2:ℝ)≤z)).card

theorem midpointCount_le (N : ℕ) (z : ℝ) : midpointCount N z ≤ N := by
  classical
  exact (Finset.card_filter_le _ _).trans_eq (by simp)

theorem lt_midpointCount_iff {N : ℕ} (z : ℝ) (j : Fin N) :
    j.val < midpointCount N z ↔ (j:ℝ)+(1/2:ℝ)≤z := by
  classical
  apply Fin.lt_card_filter_univ_iff_apply_of_imp
  intro i k hki hi
  have hc : (k:ℝ)≤(i:ℝ) := by exact_mod_cast hki
  linarith

theorem midpointCount_discrepancy (N : ℕ) {z : ℝ} (hz : 0≤z) (hzN : z≤(N:ℝ)+1) :
    |(midpointCount N z : ℝ)-z|≤1 := by
  have hc := midpointCount_le N z
  rw [abs_le]
  constructor
  · by_cases h : midpointCount N z<N
    · let j : Fin N := ⟨midpointCount N z,h⟩
      have hj : ¬(j:ℝ)+(1/2:ℝ)≤z := by
        rw [← lt_midpointCount_iff z j]
        exact lt_irrefl _
      change ¬(midpointCount N z : ℝ)+(1/2:ℝ)≤z at hj
      linarith
    · have he : midpointCount N z=N := by omega
      rw [he]
      linarith
  · by_cases h : midpointCount N z=0
    · rw [h]
      norm_num
      linarith
    · have hpos : 0<midpointCount N z := Nat.pos_of_ne_zero h
      let j : Fin N := ⟨midpointCount N z-1,by omega⟩
      have hj : (j:ℝ)+(1/2:ℝ)≤z := (lt_midpointCount_iff z j).mp (by dsimp [j]; omega)
      have he : (j:ℝ)=(midpointCount N z : ℝ)-1 := by
        dsimp [j]
        rw [Nat.cast_sub (by omega : 1≤midpointCount N z)]
        simp
      rw [he] at hj
      linarith

theorem quantile_exists {a b : ℝ} {q : ℝ → ℝ} (hab : a≤b)
    (hq : ContinuousOn q (Icc a b)) (hqa : q a=0) {Q : ℝ} (hqb : q b=Q)
    {N : ℕ} (hN : (N:ℝ)≤Q) (i : Fin N) :
    ∃ t ∈ Icc a b, q t=(i:ℝ)+(1/2:ℝ) := by
  apply intermediate_value_Icc hab hq
  rw [hqa,hqb]
  have hi : (i:ℝ)+1≤N := by exact_mod_cast i.isLt
  constructor
  · positivity
  · linarith


structure QuantileMesh (a b : ℝ) (q : ℝ → ℝ) (N : ℕ) where
  node : Fin N → ℝ
  node_mem : ∀ i, node i ∈ Icc a b
  node_level : ∀ i, q (node i)=(i:ℝ)+(1/2:ℝ)

theorem exists_quantileMesh {a b : ℝ} {q : ℝ → ℝ} (hab : a≤b)
    (hq : ContinuousOn q (Icc a b)) (hqa : q a=0) {Q : ℝ} (hqb : q b=Q)
    {N : ℕ} (hN : (N:ℝ)≤Q) : Nonempty (QuantileMesh a b q N) := by
  classical
  choose t ht hlevel using (fun i : Fin N => quantile_exists hab hq hqa hqb hN i)
  exact ⟨⟨t,ht,hlevel⟩⟩

theorem QuantileMesh.strictMono {a b : ℝ} {q : ℝ → ℝ} {N : ℕ}
    (mesh : QuantileMesh a b q N) (hq : StrictMonoOn q (Icc a b)) : StrictMono mesh.node := by
  intro i j hij
  apply (hq.lt_iff_lt (mesh.node_mem i) (mesh.node_mem j)).mp
  rw [mesh.node_level,mesh.node_level]
  have hc : (i:ℝ)<(j:ℝ) := by exact_mod_cast hij
  linarith

theorem QuantileMesh.separation {a b M : ℝ} {q : ℝ → ℝ} {N : ℕ}
    (mesh : QuantileMesh a b q N) (hq : StrictMonoOn q (Icc a b)) (hM : 0<M)
    (hLip : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x≤y → q y-q x≤M*(y-x)) :
    ∀ i j : Fin N, i<j → ((j:ℝ)-(i:ℝ))/M ≤ mesh.node j-mesh.node i := by
  intro i j hij
  have h := hLip _ (mesh.node_mem i) _ (mesh.node_mem j) ((mesh.strictMono hq hij).le)
  rw [mesh.node_level,mesh.node_level] at h
  apply (div_le_iff₀ hM).mpr
  nlinarith

theorem QuantileMesh.count_eq {a b : ℝ} {q : ℝ → ℝ} {N : ℕ}
    (mesh : QuantileMesh a b q N) (hq : StrictMonoOn q (Icc a b))
    {s : ℝ} (hs : s ∈ Icc a b) :
    (Finset.univ.filter (fun i : Fin N => mesh.node i≤s)).card = midpointCount N (q s) := by
  classical
  unfold midpointCount
  congr 1
  apply Finset.filter_congr
  intro i _
  rw [← hq.le_iff_le (mesh.node_mem i) hs,mesh.node_level]

theorem QuantileMesh.count_discrepancy {a b Q : ℝ} {q : ℝ → ℝ} {N : ℕ}
    (mesh : QuantileMesh a b q N) (hq : StrictMonoOn q (Icc a b))
    (hab : a≤b) (hqa : q a=0) (hqb : q b=Q) (hQ : Q≤(N:ℝ)+1)
    {s : ℝ} (hs : s ∈ Icc a b) :
    |((Finset.univ.filter (fun i : Fin N => mesh.node i≤s)).card : ℝ)-q s|≤1 := by
  classical
  rw [mesh.count_eq hq hs]
  apply midpointCount_discrepancy
  · have h := hq.monotoneOn (left_mem_Icc.mpr hab) hs hs.1
    rwa [hqa] at h
  · have h := hq.monotoneOn hs (right_mem_Icc.mpr hab) hs.2
    rw [hqb] at h
    exact h.trans hQ

end Erdos524.QuantileCounting
