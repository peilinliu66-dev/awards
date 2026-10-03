import Erdos1017.WeightedSteps

/-!
The classical weighted clique-partition upper bound, with a complete finite
induction and no assumed extremal theorem. The mathematical argument is the
upper-bound part of Győri–Kostochka (1979), simplified using nonneighbor budgets.
UNCOMPILED. No kernel verification is claimed.
-/

namespace Erdos1017

private theorem floor_square_one_step (n : ℕ) :
    n ^ 2 / 2 + n ≤ (n + 1) ^ 2 / 2 := by
  have h : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
  rw [h]
  omega

private theorem floor_square_two_step (n : ℕ) :
    n ^ 2 / 2 + 2 * (n + 1) = (n + 2) ^ 2 / 2 := by
  have h : (n + 2) ^ 2 = n ^ 2 + 4 * n + 4 := by ring
  rw [h]
  omega

theorem floor_square_half_eq_twice_quarter (n : ℕ) :
    n ^ 2 / 2 = 2 * (n ^ 2 / 4) := by
  have hmod := Nat.mod_lt n (by decide : 0 < 2)
  have hdiv := Nat.mod_add_div n 2
  let m := n / 2
  have hn : n = 2 * m ∨ n = 2 * m + 1 := by
    dsimp [m]
    omega
  rcases hn with hn | hn
  · rw [hn]
    have h : (2 * m) ^ 2 = 4 * m ^ 2 := by ring
    rw [h]
    omega
  · rw [hn]
    have h : (2 * m + 1) ^ 2 = 4 * m ^ 2 + 4 * m + 1 := by ring
    rw [h]
    omega

variable {V : Type*} [DecidableEq V]

/-- The weighted theorem for any finite active set. Vertices outside S are
isolated. This form permits induction without changing the ambient vertex type.
-/
theorem exists_weighted_partition_on (G : SimpleGraph V) (S : Finset V)
    (hS : SupportedOn G S) :
    ∃ P : CliquePartition G, P.weight ≤ S.card ^ 2 / 2 := by
  classical
  suffices h : ∀ n : ℕ, ∀ S : Finset V, S.card = n →
      ∀ G : SimpleGraph V, SupportedOn G S →
        ∃ P : CliquePartition G, P.weight ≤ n ^ 2 / 2 by
    exact h S.card S rfl G hS
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro S hcard G hS
    by_cases hempty : S = ∅
    · subst S
      let P : CliquePartition G := {
        blocks := ∅
        nontrivial := by simp
        clique := by simp
        owns := by
          intro u v huv
          have hu := (hS u v huv).1
          simp at hu }
      exact ⟨P, by simp [P, CliquePartition.weight]⟩
    · have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
      obtain ⟨x, hx, hmax⟩ := exists_max_nonneighbors G S hSne
      let k := (nonneighborsOn G S x).card
      by_cases hequal : ∃ y ∈ neighborsOn G S x,
          (nonneighborsOn G S y).card = k
      · obtain ⟨y, hyN, hky⟩ := hequal
        obtain ⟨hy, hxy⟩ := Finset.mem_filter.mp hyN
        obtain ⟨P, hweight, hrem⟩ := two_vertex_weighted_step hx hy hxy hS rfl hky hmax
        let T := (S.erase x).erase y
        have hyerase : y ∈ S.erase x := Finset.mem_erase.mpr ⟨hxy.ne.symm, hy⟩
        have hfirst := Finset.card_erase_add_one hx
        have hsecond := Finset.card_erase_add_one hyerase
        have hT : T.card + 2 = n := by dsimp [T]; omega
        have hlt : T.card < n := by omega
        obtain ⟨Q, hQ⟩ := ih T.card hlt T rfl P.remainder hrem
        refine ⟨P.complete Q, ?_⟩
        rw [CliquePacking.complete_weight]
        have hstep := floor_square_two_step T.card
        have hn : n = T.card + 2 := hT.symm
        rw [hn] at hcard ⊢
        omega
      · have hstrict : ∀ u ∈ neighborsOn G S x,
            (nonneighborsOn G S u).card < (nonneighborsOn G S x).card := by
          intro u hu
          have hle := hmax u (neighborsOn_subset G S x hu)
          have hne : (nonneighborsOn G S u).card ≠ k := by
            intro heq
            exact hequal ⟨u, hu, heq⟩
          change (nonneighborsOn G S u).card ≠ (nonneighborsOn G S x).card at hne
          omega
        obtain ⟨P, hweight, hrem⟩ := one_vertex_weighted_step hx hS hstrict
        let T := S.erase x
        have hT : T.card + 1 = n := by
          have h := Finset.card_erase_add_one hx
          dsimp [T]
          omega
        have hlt : T.card < n := by omega
        obtain ⟨Q, hQ⟩ := ih T.card hlt T rfl P.remainder hrem
        refine ⟨P.complete Q, ?_⟩
        rw [CliquePacking.complete_weight]
        have hstep := floor_square_one_step T.card
        have hn : n = T.card + 1 := hT.symm
        rw [hn] at hcard ⊢
        omega

/-- Unconditional weighted clique-partition theorem, including both parities. -/
theorem exists_weighted_partition [Fintype V] (G : SimpleGraph V) :
    ∃ P : CliquePartition G,
      P.weight ≤ 2 * balancedThreshold (Fintype.card V) := by
  obtain ⟨P, hP⟩ := exists_weighted_partition_on G Finset.univ
    (fun _ _ _ => ⟨Finset.mem_univ _, Finset.mem_univ _⟩)
  refine ⟨P, ?_⟩
  simpa [Finset.card_univ, floor_square_half_eq_twice_quarter, balancedThreshold] using hP

theorem partitionNumber_le_balancedThreshold [Fintype V] (G : SimpleGraph V) :
    partitionNumber G ≤ balancedThreshold (Fintype.card V) := by
  obtain ⟨P, hP⟩ := exists_weighted_partition G
  have hcount := P.two_mul_count_le_weight
  have hmin := partitionNumber_le P
  omega

end Erdos1017
