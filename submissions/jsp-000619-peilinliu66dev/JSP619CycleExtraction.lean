import JSP619Layers

/-!
# A long path in a BFS band gives many distinct genuine cycle lengths

Verified against the pinned Lean and Mathlib. All branch selection, return paths, simple-cycle
construction, and length injectivity are proved in this dependency chain.
No theorem about theta graphs, consecutive lengths, or circumference is used.
-/
noncomputable section
open Finset Function
namespace JSP619
attribute [local instance] Classical.propDecidable
universe u
variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- At least m low-level vertices on a band path yield m/4 distinct cycle lengths.
There is no claim that every path in an arbitrary graph has this property:
the two level conditions are exactly those supplied by the band construction. -/
theorem cycle_count_of_band_path (T : LayerTree G) (m i : ℕ) (hm : 2 ≤ m)
    {x y : V} (p : G.Walk x y) (hp : p.IsPath) (hlen : 2 * m ≤ p.length)
    (hhigh : ∀ v ∈ p.support, i ≤ T.level v)
    (hstep : ∀ j : ℕ, j < p.length →
      min (T.level (p.getVert j)) (T.level (p.getVert (j + 1))) = i) :
    m ≤ 4 * (cycleLengths G).card := by
  classical
  let idx : ℕ → ℕ := fun j =>
    if T.level (p.getVert (2 * j)) = i then 2 * j else 2 * j + 1
  have idx_bounds (j : ℕ) : 2 * j ≤ idx j ∧ idx j ≤ 2 * j + 1 := by
    dsimp [idx]
    split_ifs <;> omega
  have idx_length (j : ℕ) (hj : j < m) : idx j ≤ p.length := by
    have := idx_bounds j
    omega
  have idx_low (j : ℕ) (hj : j < m) : T.level (p.getVert (idx j)) = i := by
    have h := hstep (2 * j) (by omega)
    dsimp [idx]
    split_ifs with he
    · exact he
    · omega
  have idx_inj : Set.InjOn idx (↑(Finset.range m) : Set ℕ) := by
    intro j hj k hk he
    have h1 := idx_bounds j
    have h2 := idx_bounds k
    omega
  let W : Finset ℕ := (Finset.range m).image idx
  have hWcard : W.card = m := by
    rw [Finset.card_image_iff.mpr idx_inj]
    exact Finset.card_range m
  have hWlength : ∀ a ∈ W, a ≤ p.length := by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
    exact idx_length j (Finset.mem_range.mp hj)
  have hWlow : ∀ a ∈ W, T.level (p.getVert a) = i := by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
    exact idx_low j (Finset.mem_range.mp hj)
  have hWinj : Set.InjOn p.getVert (↑W : Set ℕ) := by
    intro a ha b hb he
    exact hp.getVert_injOn (hWlength a ha) (hWlength b hb) he
  obtain ⟨a, B, r, ha, hBsub, haB, hr, hcard, hbranches⟩ :=
    T.branch_partition W p.getVert i (by omega) hWlow hWinj
  have hB : ∀ b ∈ B, b ≠ a ∧ b ≤ p.length := by
    intro b hb
    refine ⟨?_, hWlength b (hBsub hb)⟩
    rintro rfl
    exact haB hb
  have hreturn : ∀ b ∈ B, ∃ q : G.Walk (p.getVert b) (p.getVert a),
      q.IsPath ∧ q.length = 2 * (i - r) ∧
        ∀ v ∈ q.support, v ≠ p.getVert a → v ≠ p.getVert b → T.level v < i := by
    intro b hb
    exact T.equal_length_return (hWlow a ha) (hWlow b (hBsub hb)) hr
      (hbranches b hb).1 (hbranches b hb).2
  have hcount := fan_count p hp T.level i a (2 * (i - r))
    (hWlength a ha) (by omega) B hB hhigh hreturn
  omega

#print axioms JSP619.cycle_count_of_band_path
end JSP619
end
