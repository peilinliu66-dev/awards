import Erdos524.BlockMeshMoments
import Erdos524.SeparatedFiniteSet

namespace Erdos524.CauchyKernel
open scoped BigOperators

noncomputable def blockPointSet {K : ℕ} (center r : Fin K → ℝ) (count : Fin K → ℕ) : Finset ℝ := by
  classical
  exact Finset.univ.image (fun p : Sigma (fun j : Fin K => Fin (count j)) => blockPoint (center p.1) (r p.1) p.2)

theorem block_family_cross_gap {K : ℕ} (center r : Fin K → ℝ) (count : Fin K → ℕ)
    {width gap : ℝ} (hr : ∀ j, 0 < r j) (hcount : ∀ j, (count j : ℝ) ≤ r j*width)
    (hcenters : ∀ j k : Fin K, j < k → width+gap ≤ center k-center j)
    {j k : Fin K} (hjk : j < k) (a : Fin (count j)) (b : Fin (count k)) :
    gap ≤ blockPoint (center k) (r k) b - blockPoint (center j) (r j) a := by
  have ha := (abs_le.mp (blockPoint_within (center j) (hr j) (hcount j) a)).2
  have hb := (abs_le.mp (blockPoint_within (center k) (hr k) (hcount k) b)).1
  have hc := hcenters j k hjk
  linarith

theorem blockPointSet_separated {K : ℕ} (center r : Fin K → ℝ) (count : Fin K → ℕ)
    {width gap R : ℝ} (hr : ∀ j, 0 < r j) (hR : 0 < R) (hmax : ∀ j, r j ≤ R)
    (hcount : ∀ j, (count j : ℝ) ≤ r j*width)
    (hcenters : ∀ j k : Fin K, j < k → width+gap ≤ center k-center j)
    (hgap : 1/R ≤ gap) :
    ∀ x ∈ blockPointSet center r count, ∀ y ∈ blockPointSet center r count,
      x < y → 1/R ≤ y-x := by
  classical
  intro x hx y hy hxy
  obtain ⟨⟨j,a⟩, _, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨⟨k,b⟩, _, rfl⟩ := Finset.mem_image.mp hy
  rcases lt_trichotomy j k with hjk | hjk | hjk
  · exact hgap.trans (block_family_cross_gap center r count hr hcount hcenters hjk a b)
  · subst k
    have hab : a < b := (blockPoint_strictMono (center j) (hr j) (count j)).lt_iff_lt.mp hxy
    have hc : (a : ℝ)+1 ≤ (b : ℝ) := by exact_mod_cast hab
    rw [blockPoint_gap]
    calc
      1/R ≤ 1/r j := one_div_le_one_div_of_le (hr j) (hmax j)
      _ ≤ ((b:ℝ)-(a:ℝ))/r j := by
        apply (div_le_div_iff_of_pos_right (hr j)).mpr
        linarith
  · have hg := block_family_cross_gap center r count hr hcount hcenters hjk b a
    have hpos : 0 < 1/R := by positivity
    linarith

theorem blockPointSet_card_le {K : ℕ} (center r : Fin K → ℝ) (count : Fin K → ℕ) :
    (blockPointSet center r count).card ≤ ∑ j, count j := by
  classical
  unfold blockPointSet
  convert Finset.card_image_le using 1
  simp


theorem block_family_injective {K : ℕ} (center r : Fin K → ℝ) (count : Fin K → ℕ)
    {width gap : ℝ} (hr : ∀ j, 0 < r j) (hcount : ∀ j, (count j : ℝ) ≤ r j*width)
    (hcenters : ∀ j k : Fin K, j < k → width+gap ≤ center k-center j)
    (hgap : 0 < gap) :
    Function.Injective (fun p : Sigma (fun j : Fin K => Fin (count j)) =>
      blockPoint (center p.1) (r p.1) p.2) := by
  intro p q he
  obtain ⟨j,a⟩ := p
  obtain ⟨k,b⟩ := q
  dsimp only at he
  have hjk : j = k := by
    rcases lt_trichotomy j k with h | h | h
    · have hh := block_family_cross_gap center r count hr hcount hcenters h a b
      rw [he] at hh
      linarith
    · exact h
    · have hh := block_family_cross_gap center r count hr hcount hcenters h b a
      rw [he] at hh
      linarith
  subst k
  have hab := (blockPoint_strictMono (center j) (hr j) (count j)).injective he
  subst b
  rfl

theorem blockPointSet_card_eq {K : ℕ} (center r : Fin K → ℝ) (count : Fin K → ℕ)
    {width gap : ℝ} (hr : ∀ j, 0 < r j) (hcount : ∀ j, (count j : ℝ) ≤ r j*width)
    (hcenters : ∀ j k : Fin K, j < k → width+gap ≤ center k-center j)
    (hgap : 0 < gap) :
    (blockPointSet center r count).card = ∑ j, count j := by
  classical
  unfold blockPointSet
  rw [Finset.card_image_of_injective _ (block_family_injective center r count hr hcount hcenters hgap)]
  simp

theorem blockPointSet_deficit_sum {K : ℕ} (center r : Fin K → ℝ) (count : Fin K → ℕ)
    {width gap : ℝ} (hr : ∀ j, 0 < r j) (hcount : ∀ j, (count j : ℝ) ≤ r j*width)
    (hcenters : ∀ j k : Fin K, j < k → width+gap ≤ center k-center j)
    (hgap : 0 < gap) (L : ℝ) :
    (∑ x ∈ blockPointSet center r count, (L-x/2)) =
      ∑ j, (count j : ℝ)*(L-center j/2) := by
  classical
  unfold blockPointSet
  rw [Finset.sum_image]
  · rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro j _
    exact sum_block_deficit (center j) (r j) L (count j)
  · intro p _ q _ he
    exact block_family_injective center r count hr hcount hcenters hgap he

end Erdos524.CauchyKernel
