/-
Reused under MIT from CollinYuanjieRen/awards, commit
b8bb4f7803f921a7970abc880291ad9372111360, JSP-000198 small-k submission.
Original module: EmptyPentagon/Chord.lean
Source/permission records: EmptyPentagon/UPSTREAM.md and LICENSE.
Local target: Lean 4.33.1 / pinned Mathlib 0df444a36.
-/
import EmptyPentagon.Definitions
import EmptyPentagon.ExtremeHull
import EmptyPentagon.Certificate

noncomputable section
namespace Horton

/-- Let `ya, yb` be two vertices of a convex-independent finite set `H` lying strictly beyond a
reference line `v → w`, and let `u, z` be points of the hull of `H` on the closed near side of
that line and off the line `ya yb`. Then `u` and `z` lie strictly on the same side of the line
`ya yb` (the line through two hull vertices meets the hull only in their segment, which is
strictly beyond the reference line). -/
theorem same_side_of_hull_chord (H : Finset Point)
    (hH : ConvexIndependent ℝ (fun x : (H : Set Point) => (x : Point)))
    (ya yb : Point) (hya : ya ∈ H) (hyb : yb ∈ H) (hne : ya ≠ yb) (v w : Point)
    (hya' : orient v w ya < 0) (hyb' : orient v w yb < 0) (u z : Point)
    (hu : u ∈ convexHull ℝ (H : Set Point)) (hz : z ∈ convexHull ℝ (H : Set Point))
    (hu' : 0 ≤ orient v w u) (hz' : 0 ≤ orient v w z)
    (hu0 : orient ya yb u ≠ 0) (hz0 : orient ya yb z ≠ 0) :
    0 < orient ya yb u * orient ya yb z := by
  by_contra hcon
  have hneg : orient ya yb u * orient ya yb z < 0 :=
    lt_of_le_of_ne (not_lt.mp hcon) (mul_ne_zero hu0 hz0)
  have hpos : 0 < |orient ya yb u| + |orient ya yb z| :=
    add_pos (abs_pos.mpr hu0) (abs_pos.mpr hz0)
  set a : ℝ := |orient ya yb z| / (|orient ya yb u| + |orient ya yb z|) with ha_def
  set b : ℝ := |orient ya yb u| / (|orient ya yb u| + |orient ya yb z|) with hb_def
  have ha : 0 ≤ a := div_nonneg (abs_nonneg _) hpos.le
  have hb : 0 ≤ b := div_nonneg (abs_nonneg _) hpos.le
  have hab : a + b = 1 := by
    rw [ha_def, hb_def, ← add_div, add_comm]
    exact div_self hpos.ne'
  have hx : a • u + b • z ∈ convexHull ℝ (H : Set Point) :=
    (convex_convexHull ℝ _) hu hz ha hb hab
  have hcol : orient ya yb (a • u + b • z) = 0 := by
    rw [orient_smul_add ya yb u z a b hab, ha_def, hb_def, div_mul_eq_mul_div,
      div_mul_eq_mul_div, ← add_div, div_eq_zero_iff]
    left
    rcases lt_or_gt_of_ne hu0 with h | h
    · have h' : 0 < orient ya yb z := by nlinarith
      rw [abs_of_neg h, abs_of_pos h']
      ring
    · have h' : orient ya yb z < 0 := by nlinarith
      rw [abs_of_pos h, abs_of_neg h']
      ring
  obtain ⟨a', b', ha', hb', hab', hx'⟩ :=
    mem_segment_of_collinear_of_mem_convexHull H hH ya yb hya hyb hne _ hx hcol
  have h1 : orient v w (a' • ya + b' • yb) < 0 := by
    rw [orient_smul_add v w ya yb a' b' hab']
    rcases ha'.eq_or_lt with h0 | h0
    · have hb1 : b' = 1 := by linarith
      rw [← h0, hb1]
      linarith
    · have := mul_neg_of_pos_of_neg h0 hya'
      have := mul_nonpos_of_nonneg_of_nonpos hb' hyb'.le
      linarith
  have h2 : 0 ≤ orient v w (a • u + b • z) := by
    rw [orient_smul_add v w u z a b hab]
    exact add_nonneg (mul_nonneg ha hu') (mul_nonneg hb hz')
  rw [hx'] at h1
  linarith

end Horton
