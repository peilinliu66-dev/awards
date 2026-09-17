/-
Reused under MIT from CollinYuanjieRen/awards, commit
b8bb4f7803f921a7970abc880291ad9372111360, JSP-000198 small-k submission.
Original module: EmptyPentagon/FourOuter.lean
Source/permission records: EmptyPentagon/UPSTREAM.md and LICENSE.
Local target: Lean 4.33.1 / pinned Mathlib 0df444a36.
-/
import EmptyPentagon.Definitions
import EmptyPentagon.Beam
import EmptyPentagon.Chord
import EmptyPentagon.Interp
import EmptyPentagon.TriangleInterior

noncomputable section
namespace Horton

/-- A nonzero orientation forces its three points to be pairwise distinct. -/
theorem ne_of_orient_ne_zero (a b c : Point) (h : orient a b c ≠ 0) :
    a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  refine ⟨?_, ?_, ?_⟩ <;> intro h' <;> subst h' <;> apply h <;> unfold orient <;> ring

/-- Five pairwise distinct points give an injective `Fin 5`-indexed family. -/
theorem injective_vec5 (a b c d e : Point) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hae : a ≠ e) (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e)
    (hde : d ≠ e) : Function.Injective ![a, b, c, d, e] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; simp at hij; tauto)

/-- General position of `S` restricts to indexed general position of any injective family
of five points of `S`. -/
theorem indexedGP_of_injective (S : Finset Point) (hgp : GeneralPosition S) (p : Fin 5 → Point)
    (hp : ∀ i : Fin 5, p i ∈ S) (hinj : Function.Injective p) : IndexedGP p :=
  fun i j k hij hik hjk ↦
    hgp _ (hp i) _ (hp j) _ (hp k) (hinj.ne hij) (hinj.ne hik) (hinj.ne hjk)

/-- Two hull vertices `ya ≠ yb` of `H` lying in the same cone at `z` through the ccw edge
`va → vb`, strictly beyond that edge, together with `z, va, vb` form a convex pentagon. -/
theorem beam_of_same_cone (S : Finset Point) (hgp : GeneralPosition S) (H : Finset Point)
    (hHS : H ⊆ S) (hH : ConvexIndependent ℝ (fun x : (H : Set Point) => (x : Point)))
    (va vb z ya yb : Point) (hva : va ∈ S) (hvb : vb ∈ S) (hzS : z ∈ S)
    (hya : ya ∈ H) (hyb : yb ∈ H) (hne : ya ≠ yb) (hz : 0 < orient va vb z)
    (hva' : va ∈ convexHull ℝ (H : Set Point)) (hvb' : vb ∈ convexHull ℝ (H : Set Point))
    (hz' : z ∈ convexHull ℝ (H : Set Point))
    (ha : 0 < orient z va ya ∧ 0 < orient z ya vb ∧ orient va vb ya < 0)
    (hb : 0 < orient z va yb ∧ 0 < orient z yb vb ∧ orient va vb yb < 0) :
    ∃ V : Finset Point, V ⊆ S ∧ V.card = 5 ∧
      ConvexIndependent ℝ (fun x : (V : Set Point) => (x : Point)) := by
  obtain ⟨hvavb, hvaz, hvbz⟩ := ne_of_orient_ne_zero va vb z hz.ne'
  obtain ⟨hzva, hzya, hvaya⟩ := ne_of_orient_ne_zero z va ya ha.1.ne'
  obtain ⟨-, hzvb', hyavb⟩ := ne_of_orient_ne_zero z ya vb ha.2.1.ne'
  obtain ⟨-, hzyb, hvayb⟩ := ne_of_orient_ne_zero z va yb hb.1.ne'
  obtain ⟨-, -, hybvb⟩ := ne_of_orient_ne_zero z yb vb hb.2.1.ne'
  set p : Fin 5 → Point := ![z, va, vb, ya, yb] with hp_def
  have hinj : Function.Injective p :=
    injective_vec5 z va vb ya yb hzva hzvb' hzya hzyb hvavb hvaya hvayb hyavb.symm hybvb.symm
      hne
  have hpS : ∀ i : Fin 5, p i ∈ S := by
    intro i
    fin_cases i
    · exact hzS
    · exact hva
    · exact hvb
    · exact hHS hya
    · exact hHS hyb
  have hgp' : IndexedGP p := indexedGP_of_injective S hgp p hpS hinj
  have hzab : orient z va vb = orient va vb z := by unfold orient; ring
  have hyaS : ya ∈ S := hHS hya
  have hybS : yb ∈ S := hHS hyb
  have hl1 : 0 < orient ya yb z * orient ya yb va :=
    same_side_of_hull_chord H hH ya yb hya hyb hne va vb ha.2.2 hb.2.2 z va hz' hva' hz.le
      (le_of_eq (orient_left_self va vb).symm)
      (hgp ya hyaS yb hybS z hzS hne hzya.symm hzyb.symm)
      (hgp ya hyaS yb hybS va hva hne hvaya.symm hvayb.symm)
  have hl2 : 0 < orient ya yb z * orient ya yb vb :=
    same_side_of_hull_chord H hH ya yb hya hyb hne va vb ha.2.2 hb.2.2 z vb hz' hvb' hz.le
      (le_of_eq (orient_right_self va vb).symm)
      (hgp ya hyaS yb hybS z hzS hne hzya.symm hzyb.symm)
      (hgp ya hyaS yb hybS vb hvb hne hyavb hybvb)
  refine ⟨Finset.univ.image p, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact hpS i
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  · exact convexIndependent_beam p hgp' hinj (by show 0 < orient z va vb; rw [hzab]; exact hz)
      ha.1 ha.2.1 ha.2.2 hb.1 hb.2.1 hb.2.2 hl1 hl2

/-- Bonnice's `(4,3,1)` argument: at least four hull vertices `H` of `S`, an inner
counterclockwise triangle `v1 v2 v3` with a point `z` strictly inside, all four points inside the
hull of `H` and no vertex of `H` in the closed inner triangle. Then `S` contains five points in
convex position. -/
theorem convex_pentagon_of_four_outer (S : Finset Point) (hgp : GeneralPosition S)
    (H : Finset Point) (hHS : H ⊆ S)
    (hH : ConvexIndependent ℝ (fun x : (H : Set Point) => (x : Point))) (h4 : 4 ≤ H.card)
    (v1 v2 v3 z : Point) (hv1 : v1 ∈ S) (hv2 : v2 ∈ S) (hv3 : v3 ∈ S) (hzS : z ∈ S)
    (ht : 0 < orient v1 v2 v3)
    (hz : 0 < orient v1 v2 z ∧ 0 < orient v2 v3 z ∧ 0 < orient v3 v1 z)
    (hout : ∀ y ∈ H, y ∉ convexHull ℝ ({v1, v2, v3} : Set Point))
    (hin : ({v1, v2, v3, z} : Set Point) ⊆ convexHull ℝ (H : Set Point)) :
    ∃ V : Finset Point, V ⊆ S ∧ V.card = 5 ∧
      ConvexIndependent ℝ (fun x : (V : Set Point) => (x : Point)) := by
  classical
  obtain ⟨h12, h13, h23⟩ := ne_of_orient_ne_zero v1 v2 v3 ht.ne'
  obtain ⟨-, h1z, h2z⟩ := ne_of_orient_ne_zero v1 v2 z hz.1.ne'
  obtain ⟨-, -, h3z⟩ := ne_of_orient_ne_zero v2 v3 z hz.2.1.ne'
  have hzT : z ∈ convexHull ℝ ({v1, v2, v3} : Set Point) :=
    interior_subset (mem_interior_triangle_of_orient_pos v1 v2 v3 z ht hz.1 hz.2.1 hz.2.2)
  have hv1T : v1 ∈ convexHull ℝ ({v1, v2, v3} : Set Point) := subset_convexHull ℝ _ (by simp)
  have hv2T : v2 ∈ convexHull ℝ ({v1, v2, v3} : Set Point) := subset_convexHull ℝ _ (by simp)
  have hv3T : v3 ∈ convexHull ℝ ({v1, v2, v3} : Set Point) := subset_convexHull ℝ _ (by simp)
  have hcov : ∀ y ∈ H,
      (0 < orient z v1 y ∧ 0 < orient z y v2 ∧ orient v1 v2 y < 0) ∨
      (0 < orient z v2 y ∧ 0 < orient z y v3 ∧ orient v2 v3 y < 0) ∨
      (0 < orient z v3 y ∧ 0 < orient z y v1 ∧ orient v3 v1 y < 0) := by
    intro y hy
    have hyS : y ∈ S := hHS hy
    have hy1 : v1 ≠ y := fun h ↦ hout y hy (h ▸ hv1T)
    have hy2 : v2 ≠ y := fun h ↦ hout y hy (h ▸ hv2T)
    have hy3 : v3 ≠ y := fun h ↦ hout y hy (h ▸ hv3T)
    have hyz : z ≠ y := fun h ↦ hout y hy (h ▸ hzT)
    have hinj : Function.Injective ![v1, v2, v3, z, y] :=
      injective_vec5 v1 v2 v3 z y h12 h13 h1z hy1 h23 h2z hy2 h3z hy3 hyz
    have hpS : ∀ i : Fin 5, ![v1, v2, v3, z, y] i ∈ S := by
      intro i
      fin_cases i
      · exact hv1
      · exact hv2
      · exact hv3
      · exact hzS
      · exact hyS
    have hgp' : IndexedGP ![v1, v2, v3, z, y] := indexedGP_of_injective S hgp _ hpS hinj
    have hy' : orient v1 v2 y < 0 ∨ orient v2 v3 y < 0 ∨ orient v3 v1 y < 0 := by
      by_contra hcon
      push Not at hcon
      have e1 : 0 < orient v1 v2 y :=
        lt_of_le_of_ne hcon.1 (hgp v1 hv1 v2 hv2 y hyS h12 hy1 hy2).symm
      have e2 : 0 < orient v2 v3 y :=
        lt_of_le_of_ne hcon.2.1 (hgp v2 hv2 v3 hv3 y hyS h23 hy2 hy3).symm
      have e3 : 0 < orient v3 v1 y :=
        lt_of_le_of_ne hcon.2.2 (hgp v3 hv3 v1 hv1 y hyS h13.symm hy3 hy1).symm
      exact hout y hy
        (interior_subset (mem_interior_triangle_of_orient_pos v1 v2 v3 y ht e1 e2 e3))
    exact cone_cover ![v1, v2, v3, z, y] hgp' ht hz.1 hz.2.1 hz.2.2 hy'
  let f : Point → Fin 3 := fun y ↦
    if 0 < orient z v1 y ∧ 0 < orient z y v2 ∧ orient v1 v2 y < 0 then 0
    else if 0 < orient z v2 y ∧ 0 < orient z y v3 ∧ orient v2 v3 y < 0 then 1 else 2
  have hc : (Finset.univ : Finset (Fin 3)).card < H.card := by
    rw [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨ya, hya, yb, hyb, hne, hf⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hc (f := f) (fun a _ ↦ Finset.mem_univ _)
  have hv1H : v1 ∈ convexHull ℝ (H : Set Point) := hin (by simp)
  have hv2H : v2 ∈ convexHull ℝ (H : Set Point) := hin (by simp)
  have hv3H : v3 ∈ convexHull ℝ (H : Set Point) := hin (by simp)
  have hzH : z ∈ convexHull ℝ (H : Set Point) := hin (by simp)
  have hzz1 : 0 < orient v3 v1 z := hz.2.2
  by_cases c1 : 0 < orient z v1 ya ∧ 0 < orient z ya v2 ∧ orient v1 v2 ya < 0
  · have d1 : 0 < orient z v1 yb ∧ 0 < orient z yb v2 ∧ orient v1 v2 yb < 0 := by
      by_contra d1
      have hfa : f ya = 0 := by simp only [f, if_pos c1]
      have hfb : f yb = if 0 < orient z v2 yb ∧ 0 < orient z yb v3 ∧ orient v2 v3 yb < 0
          then 1 else 2 := by simp only [f, if_neg d1]
      rw [hfa, hfb] at hf
      split_ifs at hf <;> exact absurd hf (by decide)
    exact beam_of_same_cone S hgp H hHS hH v1 v2 z ya yb hv1 hv2 hzS hya hyb hne hz.1 hv1H
      hv2H hzH c1 d1
  by_cases c2 : 0 < orient z v2 ya ∧ 0 < orient z ya v3 ∧ orient v2 v3 ya < 0
  · have d2 : 0 < orient z v2 yb ∧ 0 < orient z yb v3 ∧ orient v2 v3 yb < 0 := by
      by_contra d2
      have hfa : f ya = 1 := by simp only [f, if_neg c1, if_pos c2]
      have hfb : f yb = if 0 < orient z v1 yb ∧ 0 < orient z yb v2 ∧ orient v1 v2 yb < 0
          then 0 else 2 := by simp only [f, if_neg d2]
      rw [hfa, hfb] at hf
      split_ifs at hf <;> exact absurd hf (by decide)
    exact beam_of_same_cone S hgp H hHS hH v2 v3 z ya yb hv2 hv3 hzS hya hyb hne hz.2.1 hv2H
      hv3H hzH c2 d2
  have c3 : 0 < orient z v3 ya ∧ 0 < orient z ya v1 ∧ orient v3 v1 ya < 0 := by
    rcases hcov ya hya with h | h | h
    · exact absurd h c1
    · exact absurd h c2
    · exact h
  have hfa : f ya = 2 := by simp only [f, if_neg c1, if_neg c2]
  have d3 : 0 < orient z v3 yb ∧ 0 < orient z yb v1 ∧ orient v3 v1 yb < 0 := by
    rcases hcov yb hyb with h | h | h
    · have hfb : f yb = 0 := by simp only [f, if_pos h]
      rw [hfa, hfb] at hf
      exact absurd hf (by decide)
    · by_cases e : 0 < orient z v1 yb ∧ 0 < orient z yb v2 ∧ orient v1 v2 yb < 0
      · have hfb : f yb = 0 := by simp only [f, if_pos e]
        rw [hfa, hfb] at hf
        exact absurd hf (by decide)
      · have hfb : f yb = 1 := by simp only [f, if_neg e, if_pos h]
        rw [hfa, hfb] at hf
        exact absurd hf (by decide)
    · exact h
  exact beam_of_same_cone S hgp H hHS hH v3 v1 z ya yb hv3 hv1 hzS hya hyb hne hzz1 hv3H hv1H
    hzH c3 d3

end Horton
