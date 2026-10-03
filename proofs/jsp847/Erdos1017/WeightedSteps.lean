import Erdos1017.CommonClique

/-!
The one-vertex and adjacent two-vertex steps in the upper-bound part of
Győri–Kostochka (1979), Theorem2. The implementation counts other nonneighbors
and allows an empty maximum common clique. UNCOMPILED.
-/

namespace Erdos1017

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

theorem support_remainder_erase (P : CliquePacking G) {S : Finset V} {x : V}
    (hS : SupportedOn G S)
    (hstar : ∀ u, G.Adj x u → P.OwnsEdge x u) :
    SupportedOn P.remainder (S.erase x) := by
  intro u v huv
  obtain ⟨huS, hvS⟩ := hS u v huv.1
  have hux : u ≠ x := by
    intro h
    subst u
    exact huv.2 (hstar v huv.1)
  have hvx : v ≠ x := by
    intro h
    subst v
    exact huv.2 (P.ownsEdge_symm (hstar u huv.1.symm))
  exact ⟨Finset.mem_erase.mpr ⟨hux, huS⟩, Finset.mem_erase.mpr ⟨hvx, hvS⟩⟩

theorem one_vertex_weighted_step {S : Finset V} {x : V} (hx : x ∈ S)
    (hS : SupportedOn G S)
    (hstrict : ∀ u ∈ neighborsOn G S x,
      (nonneighborsOn G S u).card < (nonneighborsOn G S x).card) :
    ∃ P : CliquePacking G,
      P.weight ≤ S.card - 1 ∧ SupportedOn P.remainder (S.erase x) := by
  classical
  let N := neighborsOn G S x
  let k := (nonneighborsOn G S x).card
  have hbad : ∀ u ∈ N, (nonneighborsOn G N u).card < k := by
    intro u hu
    exact lt_of_le_of_lt
      (Finset.card_le_card (nonneighborsOn_mono G (neighborsOn_subset G S x) u))
      (hstrict u hu)
  obtain ⟨P, hweight, hstar, _⟩ := exists_conePacking_weight_le G x N k
    (not_mem_own_neighbors G S x)
    (fun u hu => (Finset.mem_filter.mp hu).2) hbad
  refine ⟨P, ?_, support_remainder_erase P hS ?_⟩
  · have hcard := neighbor_nonneighbor_card G S hx
    change P.weight ≤ S.card - 1
    change P.weight ≤ (neighborsOn G S x).card + (nonneighborsOn G S x).card at hweight
    omega
  · intro u hxu
    exact hstar u (Finset.mem_filter.mpr ⟨(hS x u hxu).2, hxu⟩)

theorem two_vertex_weighted_step {S : Finset V} {x y : V} {k : ℕ}
    (hx : x ∈ S) (hy : y ∈ S) (hxy : G.Adj x y) (hS : SupportedOn G S)
    (hkx : (nonneighborsOn G S x).card = k)
    (hky : (nonneighborsOn G S y).card = k)
    (hbudget : ∀ u ∈ S, (nonneighborsOn G S u).card ≤ k) :
    ∃ P : CliquePacking G,
      P.weight ≤ 2 * (S.card - 1) ∧
      SupportedOn P.remainder ((S.erase x).erase y) := by
  classical
  obtain ⟨Z, hZ, hZcl, hZmax⟩ := exists_maximum_clique G (commonNeighbors G S x y)
  let t := Z.card
  let C := insert x (insert y Z)
  let R := residualNeighbors G S x y Z
  let B := residualNeighbors G S y x Z
  have hZswap : Z ⊆ commonNeighbors G S y x := by
    simpa only [commonNeighbors_comm] using hZ
  have hZmaxSwap : ∀ D : Finset V, D ⊆ commonNeighbors G S y x →
      IsClique G D → D.card ≤ Z.card := by
    intro D hD hcl
    exact hZmax D (by simpa only [commonNeighbors_comm] using hD) hcl
  have hCcard : C.card = t + 2 := commonClique_with_apices_card hxy hZ
  have hCcl : IsClique G C := commonClique_with_apices hxy hZ hZcl
  let P₀ := CliquePacking.singleton G C (by omega) hCcl
  let G₀ := P₀.remainder
  have hP₀sub : ∀ D ∈ P₀.blocks, D ⊆ C := by
    intro D hD
    obtain rfl := Finset.mem_singleton.mp hD
    exact Finset.Subset.refl _
  have hRout : ∀ u ∈ R, u ∉ C := by
    intro u hu huc
    rcases Finset.mem_insert.mp huc with hux | huc
    · subst u
      exact residualNeighbors_not_left G S x y Z hu
    · exact (Finset.mem_sdiff.mp hu).2 huc
  have hBout : ∀ u ∈ B, u ∉ C := by
    intro u hu huc
    rcases Finset.mem_insert.mp huc with hux | huc
    · subst u
      exact residualNeighbors_not_right G S y x Z hu
    · rcases Finset.mem_insert.mp huc with huy | huc
      · subst u
        exact residualNeighbors_not_left G S y x Z hu
      · exact residualNeighbors_not_clique G S y x Z huc hu
  have hRbadG := residualNeighbors_nonneighbors_lt hy hZ hZcl hZmax hbudget
  have hBbadG := residualNeighbors_nonneighbors_lt hx hZswap hZcl hZmaxSwap hbudget
  have hRbad : ∀ u ∈ R, (nonneighborsOn G₀ R u).card < k := by
    intro u hu
    have heq : nonneighborsOn G₀ R u = nonneighborsOn G R u := by
      ext v
      simp only [nonneighborsOn, Finset.mem_filter]
      rw [P₀.remainder_adj_of_outside hP₀sub (hRout u hu)]
    rw [heq]
    exact hRbadG u hu
  have hBbad : ∀ u ∈ B, (nonneighborsOn G₀ B u).card < k := by
    intro u hu
    have heq : nonneighborsOn G₀ B u = nonneighborsOn G B u := by
      ext v
      simp only [nonneighborsOn, Finset.mem_filter]
      rw [P₀.remainder_adj_of_outside hP₀sub (hBout u hu)]
    rw [heq]
    exact hBbadG u hu
  have hRadj : ∀ u ∈ R, G₀.Adj x u := by
    intro u hu
    apply SimpleGraph.Adj.symm
    apply (P₀.remainder_adj_of_outside hP₀sub (hRout u hu)).mpr
    exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hu).1).2.symm
  obtain ⟨P₁, hP₁weight, hP₁star, hP₁blocks⟩ := exists_conePacking_weight_le G₀ x R k
    (residualNeighbors_not_left G S x y Z) hRadj hRbad
  have hxB : x ∉ B := residualNeighbors_not_right G S y x Z
  have hyP₁ : y ∉ insert x R := by
    simp only [Finset.mem_insert]
    rintro (hyx | hyR)
    · exact hxy.ne hyx.symm
    · exact residualNeighbors_not_right G S x y Z hyR
  have hP₁size : ∀ D ∈ P₁.blocks, (D ∩ B).card ≤ t := by
    intro D hD
    apply hZmax
    · intro u hu
      obtain ⟨huD, huB⟩ := Finset.mem_inter.mp hu
      have hux : u ≠ x := by intro h; subst u; exact hxB huB
      have huR : u ∈ R :=
        (Finset.mem_insert.mp ((hP₁blocks D hD).2 huD)).resolve_left hux
      exact Finset.mem_inter.mpr
        ⟨(Finset.mem_sdiff.mp huR).1, (Finset.mem_sdiff.mp huB).1⟩
    · intro u hu v hv huv
      exact (P₁.clique D hD u (Finset.mem_inter.mp hu).1
        v (Finset.mem_inter.mp hv).1 huv).1
  have hBbad₁ : ∀ u ∈ B,
      (nonneighborsOn P₁.remainder B u).card < k + (t - 1) :=
    P₁.nonneighbors_remainder_lt B x k t hxB
      (fun D hD => (hP₁blocks D hD).1) hP₁size hBbad
  have hBadj : ∀ u ∈ B, P₁.remainder.Adj y u := by
    intro u hu
    apply (P₁.remainder_adj_of_outside (fun D hD => (hP₁blocks D hD).2) hyP₁).mpr
    apply SimpleGraph.Adj.symm
    apply (P₀.remainder_adj_of_outside hP₀sub (hBout u hu)).mpr
    exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hu).1).2.symm
  obtain ⟨P₂, hP₂weight, hP₂star, _⟩ :=
    exists_conePacking_weight_le P₁.remainder y B (k + (t - 1))
      (residualNeighbors_not_left G S y x Z) hBadj hBbad₁
  let P := P₀.append (P₁.append P₂)
  have hstarX : ∀ u, G.Adj x u → P.OwnsEdge x u := by
    intro u hxu
    by_cases huC : u ∈ C
    · exact ⟨C, Finset.mem_union_left _ (Finset.mem_singleton_self C),
        Finset.mem_insert_self _ _, huC⟩
    · have huR : u ∈ R := by
        apply Finset.mem_sdiff.mpr
        refine ⟨Finset.mem_filter.mpr ⟨(hS x u hxu).2, hxu⟩, ?_⟩
        intro hu
        exact huC (Finset.mem_insert_of_mem hu)
      obtain ⟨D, hD, hxD, huD⟩ := hP₁star u huR
      exact ⟨D, Finset.mem_union_right _ (Finset.mem_union_left _ hD), hxD, huD⟩
  have hstarY : ∀ u, G.Adj y u → P.OwnsEdge y u := by
    intro u hyu
    by_cases huC : u ∈ C
    · exact ⟨C, Finset.mem_union_left _ (Finset.mem_singleton_self C),
        Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), huC⟩
    · have huB : u ∈ B := by
        apply Finset.mem_sdiff.mpr
        refine ⟨Finset.mem_filter.mpr ⟨(hS y u hyu).2, hyu⟩, ?_⟩
        intro hu
        rcases Finset.mem_insert.mp hu with rfl | hu
        · exact huC (Finset.mem_insert_self _ _)
        · exact huC (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu))
      obtain ⟨D, hD, hyD, huD⟩ := hP₂star u huB
      exact ⟨D, Finset.mem_union_right _ (Finset.mem_union_right _ hD), hyD, huD⟩
  refine ⟨P, ?_, ?_⟩
  · have hRcard := residualNeighbors_card hy hxy hZ
    have hBcard := residualNeighbors_card hx hxy.symm hZswap
    have hNx := neighbor_nonneighbor_card G S hx
    have hNy := neighbor_nonneighbor_card G S hy
    rw [hkx] at hNx
    rw [hky] at hNy
    have hP₀weight : P₀.weight = t + 2 := by
      simpa [P₀, CliquePacking.weight, CliquePacking.singleton] using hCcard
    have hPweight : P.weight = P₀.weight + (P₁.weight + P₂.weight) := by
      simp only [P, CliquePacking.append_weight]
    change P₁.weight ≤ (residualNeighbors G S x y Z).card + k at hP₁weight
    change P₂.weight ≤ (residualNeighbors G S y x Z).card + (k + (Z.card - 1)) at hP₂weight
    change P₀.weight = Z.card + 2 at hP₀weight
    omega
  · have hxSupport := support_remainder_erase P hS hstarX
    intro u v huv
    obtain ⟨huS, hvS⟩ := hxSupport u v huv
    have huy : u ≠ y := by intro h; subst u; exact huv.2 (hstarY v huv.1)
    have hvy : v ≠ y := by
      intro h
      subst v
      exact huv.2 (P.ownsEdge_symm (hstarY u huv.1.symm))
    exact ⟨Finset.mem_erase.mpr ⟨huy, huS⟩, Finset.mem_erase.mpr ⟨hvy, hvS⟩⟩

end Erdos1017
