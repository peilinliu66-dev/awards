/-
Reused under MIT from CollinYuanjieRen/awards, commit
b8bb4f7803f921a7970abc880291ad9372111360, JSP-000198 small-k submission.
Original module: EmptyPentagon/Third.lean
Source/permission records: EmptyPentagon/UPSTREAM.md and LICENSE.
Local target: Lean 4.33.1 / pinned Mathlib 0df444a36.
-/
import EmptyPentagon.Definitions
import EmptyPentagon.Certificate
import EmptyPentagon.Interp
import EmptyPentagon.TriangleInterior
import EmptyPentagon.Pentagon
import EmptyPentagon.Signs
import EmptyPentagon.CyclicLabel
import EmptyPentagon.Final

noncomputable section
open Classical
namespace Horton

/-- Reversing the three arguments of an orientation negates it. -/
theorem orient_rev (a b c : Point) : orient c b a = -orient a b c := by
  unfold orient; ring

/-- The three-term Grassmann–Plücker product identity for orientations sharing a base point. -/
theorem orient_mul_add (p w x y z : Point) :
    orient p x z * orient p w y = orient p x y * orient p w z + orient p w x * orient p y z := by
  unfold orient; ring

/-- The four-point cocycle identity for orientations. -/
theorem orient_cocycle (a b c d : Point) :
    orient a c d = orient b c d - orient a b c + orient a b d := by
  unfold orient; ring

/-- Among finitely many points strictly left of the directed line `p → w`, one comes first in
the counterclockwise angular order around `p`. -/
theorem exists_angular_first (S : Finset Point) (hgp : GeneralPosition S) (p w : Point)
    (hpS : p ∈ S) (C : Finset Point) (hCS : C ⊆ S) (hCne : C.Nonempty)
    (hleft : ∀ z ∈ C, 0 < orient p w z) :
    ∃ u ∈ C, ∀ z ∈ C, z ≠ u → 0 < orient p u z := by
  classical
  have hne : ∀ z ∈ C, p ≠ z := by
    intro z hz h
    have hz' := hleft z hz
    rw [← h, orient_self_left] at hz'
    exact lt_irrefl _ hz'
  have htr : ∀ a ∈ C, ∀ b ∈ C, ∀ c ∈ C, 0 < orient p a b → 0 < orient p b c →
      0 < orient p a c := by
    intro a ha b hb c hc h1 h2
    have key := orient_mul_add p w a b c
    have hprod : 0 < orient p a c * orient p w b := by
      rw [key]
      exact add_pos (mul_pos h1 (hleft c hc)) (mul_pos (hleft a ha) h2)
    by_contra hcon
    have hle : orient p a c ≤ 0 := not_lt.mp hcon
    nlinarith [hprod, hleft b hb, hle]
  have hlt : ∀ a ∈ C, ∀ b ∈ C, 0 < orient p a b →
      (C.filter fun r => 0 < orient p r a).card < (C.filter fun r => 0 < orient p r b).card := by
    intro a ha b hb h
    apply Finset.card_lt_card
    have hsub : (C.filter fun r => 0 < orient p r a) ⊆ C.filter fun r => 0 < orient p r b := by
      intro x hx
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, htr x hx.1 a ha b hb hx.2 h⟩
    rw [Finset.ssubset_iff_of_subset hsub]
    refine ⟨a, Finset.mem_filter.mpr ⟨ha, h⟩, fun hmem => ?_⟩
    have hbad := (Finset.mem_filter.mp hmem).2
    rw [orient_self_right] at hbad
    exact lt_irrefl _ hbad
  obtain ⟨u, huC, hmin⟩ :=
    Finset.exists_min_image C (fun q => (C.filter fun r => 0 < orient p r q).card) hCne
  refine ⟨u, huC, fun z hz hzu => ?_⟩
  have hnz : orient p u z ≠ 0 :=
    hgp p hpS u (hCS huC) z (hCS hz) (hne u huC) (hne z hz) (Ne.symm hzu)
  rcases lt_or_gt_of_ne hnz with hneg | hpos
  · exfalso
    have hzu' : 0 < orient p z u := by linarith [orient_swap p u z]
    have h1 := hlt z hz u huC hzu'
    have h2 := hmin z hz
    omega
  · exact hpos

/-- A counterclockwise pentagon each of whose outside points is cut off by some line yields an
empty convex pentagon. -/
theorem emptyPentagon_of_data (S : Finset Point) (W : Fin 5 → Point)
    (hinj : Function.Injective W) (hWS : ∀ k, W k ∈ S)
    (hccw : ∀ k j : Fin 5, j ≠ k → j ≠ k + 1 → 0 < orient (W k) (W (k + 1)) (W j))
    (hsep : ∀ q ∈ S, (∀ k, q ≠ W k) → ∃ u v : Point, u ≠ v ∧
      (∀ k, 0 ≤ orient u v (W k)) ∧ orient u v q ≤ 0) :
    ∃ V : Finset Point, V.card = 5 ∧ EmptyConvexPolygon S V := by
  classical
  refine ⟨Finset.univ.image W, ?_, emptyConvexPolygon_of_ccw S W hinj hWS hccw ?_⟩
  · rw [Finset.card_image_of_injective _ hinj]; simp
  · intro q hqS hqW
    have hqne : ∀ k, q ≠ W k := fun k h =>
      hqW (by rw [h]; exact Finset.mem_image_of_mem W (Finset.mem_univ k))
    obtain ⟨u, v, huv, hV, hq⟩ := hsep q hqS hqne
    refine not_mem_interior_convexHull_of_halfplane _ u v q huv ?_ hq
    intro x hx
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hx
    exact hV k


set_option maxHeartbeats 1000000 in
/-- Harborth's third-point configuration around edge `A → B`: `Q`, `R`, `T` are the three
points of `S` closest to the line `A B` inside the wedge of that edge (all wedge points behind
the neighbouring edge lines and, apart from `Q`, beyond the tent `A, Q, B`), and `T` lies
strictly right of `Q → R`.  Then `S` contains the counterclockwise empty pentagon
`T, R, Q, A, U`, where `U` is the first point of the wedge of the previous edge met when the
ray `T → A` turns counterclockwise about `T`. -/
theorem third_pentagon (S : Finset Point) (hgp : GeneralPosition S) (M A B Am Q R T : Point)
    (hMS : M ∈ S) (hAS : A ∈ S) (hBS : B ∈ S) (hAmS : Am ∈ S) (hQS : Q ∈ S) (hRS : R ∈ S)
    (hTS : T ∈ S)
    (cMAB : 0 < orient M A B) (cMAmA : 0 < orient M Am A) (cMAmB : 0 < orient M Am B)
    (cABAm : 0 < orient A B Am)
    (wQ1 : 0 < orient M A Q) (wQ2 : orient M B Q < 0) (wQ3 : orient A B Q < 0)
    (wQ4 : orient Am A Q < 0)
    (wR1 : 0 < orient M A R) (wR2 : orient M B R < 0)
    (wR4 : orient Am A R < 0)
    (wT1 : 0 < orient M A T) (wT2 : orient M B T < 0) (wT3 : orient A B T < 0)
    (wT4 : orient Am A T < 0)
    (tR : 0 < orient Q A R) (tT : 0 < orient Q A T) (hcase : orient Q R T < 0)
    (dTR : orient A B T ≤ orient A B R) (dRQ : orient A B R ≤ orient A B Q)
    (hfar : ∀ q ∈ S, 0 < orient M A q → orient M B q < 0 → orient A B q < 0 → q ≠ Q → q ≠ R →
      q ≠ T → orient A B q ≤ orient A B T)
    (hMuniq : ∀ q ∈ S, 0 < orient M A q → 0 < orient A B q → 0 < orient B M q → q = M) :
    ∃ W : Fin 5 → Point, Function.Injective W ∧ (∀ k, W k ∈ S) ∧
      (∀ k j : Fin 5, j ≠ k → j ≠ k + 1 → 0 < orient (W k) (W (k + 1)) (W j)) ∧
      ∀ q ∈ S, (∀ k, q ≠ W k) → ∃ u v : Point, u ≠ v ∧
        (∀ k, 0 ≤ orient u v (W k)) ∧ orient u v q ≤ 0 := by
  classical
  -- (0) elementary distinctness and rotations
  obtain ⟨nMA, nMB, hAB⟩ := ne_of_orient_pos M A B cMAB
  obtain ⟨nMAm, -, nAmA⟩ := ne_of_orient_pos M Am A cMAmA
  have hTAAm : 0 < orient T A Am := by linarith [orient_rev Am A T]
  have hMAAm : orient M A Am < 0 := by linarith [orient_swap M Am A]
  -- (1) the candidate set and the angularly first candidate `U`
  set Cand : Finset Point := (S.filter fun z => 0 < orient T A z ∧ orient M A z < 0 ∧
    orient Am A z < 0 ∧ 0 < orient M Am z) ∪ {Am} with hCandDef
  have hAmCand : Am ∈ Cand := by
    rw [hCandDef]
    exact Finset.mem_union_right _ (Finset.mem_singleton_self Am)
  have hCS : Cand ⊆ S := by
    rw [hCandDef]
    exact Finset.union_subset (Finset.filter_subset _ _) (Finset.singleton_subset_iff.mpr hAmS)
  have hleft : ∀ z ∈ Cand, 0 < orient T A z := by
    intro z hz
    rw [hCandDef] at hz
    rcases Finset.mem_union.mp hz with h | h
    · exact (Finset.mem_filter.mp h).2.1
    · rw [Finset.mem_singleton.mp h]; exact hTAAm
  obtain ⟨U, hUC, hfirst⟩ :=
    exists_angular_first S hgp T A hTS Cand hCS ⟨Am, hAmCand⟩ hleft
  have hUS : U ∈ S := hCS hUC
  have u1 : 0 < orient T A U := hleft U hUC
  have hUcases : (orient M A U < 0 ∧ orient Am A U < 0 ∧ 0 < orient M Am U) ∨ U = Am := by
    rw [hCandDef] at hUC
    rcases Finset.mem_union.mp hUC with h | h
    · obtain ⟨-, -, h2, h3, h4⟩ := Finset.mem_filter.mp h
      exact Or.inl ⟨h2, h3, h4⟩
    · exact Or.inr (Finset.mem_singleton.mp h)
  have u2 : orient M A U < 0 := by
    rcases hUcases with ⟨h, -, -⟩ | h
    · exact h
    · rw [h]; exact hMAAm
  have u3 : orient Am A U ≤ 0 := by
    rcases hUcases with ⟨-, h, -⟩ | h
    · exact h.le
    · rw [h, orient_self_left]
  have u4 : 0 ≤ orient M Am U := by
    rcases hUcases with ⟨-, -, h⟩ | h
    · exact h.le
    · rw [h, orient_self_right]
  have u5 : 0 ≤ orient T U Am := by
    by_cases h : U = Am
    · rw [h, orient_self_right]
    · exact (hfirst Am hAmCand (fun hx => h hx.symm)).le
  -- (2) the pentagon `U` is not too far from the edge line
  have hgA : 0 < 0 - orient A B T := by linarith
  have hgAm : 0 < orient A B Am - orient A B T := by linarith
  have hgR : 0 ≤ orient A B R - orient A B T := by linarith
  have hgQ : 0 ≤ orient A B Q - orient A B T := by linarith
  have hgU : 0 < orient A B U - orient A B T := by
    have hid : orient T A Am * (orient A B U - orient A B T)
        = orient T A U * (orient A B Am - orient A B T)
          + (0 - orient A B T) * orient T U Am := by
      unfold orient; ring
    have hrhs : 0 < orient T A U * (orient A B Am - orient A B T)
        + (0 - orient A B T) * orient T U Am :=
      add_pos_of_pos_of_nonneg (mul_pos u1 hgAm) (mul_nonneg hgA.le u5)
    nlinarith [hid, hrhs, hTAAm]
  -- (3) the ten counterclockwise facts of the pentagon `T, R, Q, A, U`
  have o1 : 0 < orient T R Q := by linarith [orient_rev Q R T]
  have o4 : 0 < orient Q A R := tR
  have o7 : 0 < orient Q A T := tT
  have o8 : 0 < orient A U T := by linarith [orient_cyc T A U]
  have o2 : 0 < orient T R A := by
    have sAQT : orient A Q T < 0 := by linarith [orient_swap_left Q A T]
    have sAQR : orient A Q R < 0 := by linarith [orient_swap_left Q A R]
    have id1 : orient A Q T * orient A B R
        = orient A Q R * orient A B T + orient A B Q * orient A R T := by
      unfold orient; ring
    have id2 : orient A R T = orient Q R T - orient A Q R + orient A Q T :=
      orient_cocycle A Q R T
    have hg : orient A R T < 0 := by
      rcases le_or_gt (orient A Q T) (orient A Q R) with hpr | hpr
      · linarith
      · exfalso
        have hX : 0 ≤ orient A B Q - orient A B R := by linarith
        have hXY : orient A B Q - orient A B R ≤ orient A B Q - orient A B T := by linarith
        have hec : 0 < orient A B Q * orient Q R T := mul_pos_of_neg_of_neg wQ3 hcase
        have key : orient A Q R * (orient A B Q - orient A B T)
            - orient A Q T * (orient A B Q - orient A B R)
            = orient A B Q * orient Q R T := by linear_combination id1 + orient A B Q * id2
        nlinarith [key, hec, hX, hXY, sAQR, hpr,
          mul_nonneg hX (sub_nonneg.mpr hpr.le),
          mul_le_mul_of_nonpos_left hXY sAQR.le]
    linarith [orient_rev A R T]
  have o3 : 0 < orient T R U := by
    have hid : orient T R U * (0 - orient A B T)
        = orient T R A * (orient A B U - orient A B T)
          + (orient A B R - orient A B T) * orient T A U := by
      unfold orient; ring
    have hrhs : 0 < orient T R A * (orient A B U - orient A B T)
        + (orient A B R - orient A B T) * orient T A U :=
      add_pos_of_pos_of_nonneg (mul_pos o2 hgU) (mul_nonneg hgR u1.le)
    nlinarith [hid, hrhs, hgA]
  have o10 : 0 < orient T Q U := by
    have hTQA : 0 < orient T Q A := by linarith [orient_cyc Q A T, orient_cyc A T Q]
    have hid : orient T Q U * (0 - orient A B T)
        = orient T Q A * (orient A B U - orient A B T)
          + (orient A B Q - orient A B T) * orient T A U := by
      unfold orient; ring
    have hrhs : 0 < orient T Q A * (orient A B U - orient A B T)
        + (orient A B Q - orient A B T) * orient T A U :=
      add_pos_of_pos_of_nonneg (mul_pos hTQA hgU) (mul_nonneg hgQ u1.le)
    nlinarith [hid, hrhs, hgA]
  have o6 : 0 < orient A U Q := by
    have hAAmT : 0 < orient A Am T := by linarith [orient_swap_left Am A T]
    have hAAmQ : 0 < orient A Am Q := by linarith [orient_swap_left Am A Q]
    have hAAmU : 0 ≤ orient A Am U := by linarith [orient_swap_left Am A U]
    have hATQ : 0 < orient A T Q := by linarith [orient_cyc Q A T, orient_cyc A T Q]
    have hid : orient A U Q * orient A Am T
        = orient A U T * orient A Am Q + orient A Am U * orient A T Q := by
      unfold orient; ring
    have hrhs : 0 < orient A U T * orient A Am Q + orient A Am U * orient A T Q :=
      add_pos_of_pos_of_nonneg (mul_pos o8 hAAmQ) (mul_nonneg hAAmU hATQ.le)
    nlinarith [hid, hrhs, hAAmT]
  have o9 : 0 < orient A U R := by
    have sAQT : orient A Q T < 0 := by linarith [orient_swap_left Q A T]
    have sAQR : orient A Q R < 0 := by linarith [orient_swap_left Q A R]
    have sAQU : orient A Q U < 0 := by linarith [orient_swap_left Q A U, orient_cyc Q A U]
    have hATR : 0 < orient A T R := by linarith [orient_cyc T R A, orient_cyc R A T]
    have hid : orient A U R * orient A Q T
        = orient A U T * orient A Q R + orient A Q U * orient A T R := by
      unfold orient; ring
    have hrhs : orient A U T * orient A Q R + orient A Q U * orient A T R < 0 := by
      have t1 := mul_neg_of_pos_of_neg o8 sAQR
      have t2 := mul_neg_of_neg_of_pos sAQU hATR
      linarith
    nlinarith [hid, hrhs, sAQT]
  have o5 : 0 < orient R Q U := by
    have sRTA : orient R T A < 0 := by linarith [orient_swap_left T R A]
    have hRQA : 0 < orient R Q A := by linarith [orient_cyc Q A R, orient_cyc A R Q]
    have sRTU : orient R T U < 0 := by linarith [orient_swap_left T R U]
    have sRTQ : orient R T Q < 0 := by linarith [orient_swap_left T R Q]
    have hRAU : 0 < orient R A U := by linarith [orient_cyc A U R, orient_cyc U R A]
    have hid : orient R Q U * orient R T A
        = orient R Q A * orient R T U + orient R T Q * orient R A U := by
      unfold orient; ring
    have hrhs : orient R Q A * orient R T U + orient R T Q * orient R A U < 0 := by
      have t1 := mul_neg_of_pos_of_neg hRQA sRTU
      have t2 := mul_neg_of_neg_of_pos sRTQ hRAU
      linarith
    nlinarith [hid, hrhs, sRTA]
  -- (4) two further sign facts used to cut off the outside points
  have hMUB : 0 < orient M U B := by
    have hMUA : 0 < orient M U A := by linarith [orient_swap M A U]
    have hid : orient M U B * orient M Am A
        = orient M U A * orient M Am B + orient M Am U * orient M A B := by
      unfold orient; ring
    have hrhs : 0 < orient M U A * orient M Am B + orient M Am U * orient M A B :=
      add_pos_of_pos_of_nonneg (mul_pos hMUA cMAmB) (mul_nonneg u4 cMAB.le)
    nlinarith [hid, hrhs, cMAmA]
  have hMAmX : ∀ X : Point, orient M B X < 0 → 0 < orient M A X → 0 < orient M Am X := by
    intro X hX2 hX1
    have sMBA : orient M B A < 0 := by linarith [orient_swap M A B]
    have sMBAm : orient M B Am < 0 := by linarith [orient_swap M Am B]
    have hid : orient M Am X * orient M B A
        = orient M Am A * orient M B X + orient M B Am * orient M A X := by
      unfold orient; ring
    have hrhs : orient M Am A * orient M B X + orient M B Am * orient M A X < 0 := by
      have t1 := mul_neg_of_pos_of_neg cMAmA hX2
      have t2 := mul_neg_of_neg_of_pos sMBAm hX1
      linarith
    nlinarith [hid, hrhs, sMBA]
  have gQ : 0 < orient M Am Q := hMAmX Q wQ2 wQ1
  have gR : 0 < orient M Am R := hMAmX R wR2 wR1
  have gT : 0 < orient M Am T := hMAmX T wT2 wT1
  -- (5) the pentagon and its vertex data
  obtain ⟨nTR, nTQ, nRQ⟩ := ne_of_orient_pos T R Q o1
  obtain ⟨-, nTA, nRA⟩ := ne_of_orient_pos T R A o2
  obtain ⟨-, nTU, nRU⟩ := ne_of_orient_pos T R U o3
  obtain ⟨nAU, nAQ, nUQ⟩ := ne_of_orient_pos A U Q o6
  set W : Fin 5 → Point := ![T, R, Q, A, U] with hW
  have hWinj : Function.Injective W := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;>
      simp [hW, nTR, nTQ, nTA, nTU, nRQ, nRA, nRU, nAQ, nAU, nUQ, nTR.symm, nTQ.symm, nTA.symm,
        nTU.symm, nRQ.symm, nRA.symm, nRU.symm, nAQ.symm, nAU.symm, nUQ.symm] at hxy ⊢
  have hWmem : ∀ k : Fin 5, W k ∈ S := by
    intro k
    fin_cases k <;> simp [hW, hTS, hRS, hQS, hAS, hUS]
  have hWccw : ∀ k j : Fin 5, j ≠ k → j ≠ k + 1 → 0 < orient (W k) (W (k + 1)) (W j) := by
    have e02 : 0 < orient T R Q := o1
    have e03 : 0 < orient T R A := o2
    have e04 : 0 < orient T R U := o3
    have e13 : 0 < orient R Q A := by rw [orient_cyc]; exact o4
    have e14 : 0 < orient R Q U := o5
    have e10 : 0 < orient R Q T := by rw [orient_cyc, orient_cyc]; exact o1
    have e24 : 0 < orient Q A U := by rw [orient_cyc]; exact o6
    have e20 : 0 < orient Q A T := o7
    have e21 : 0 < orient Q A R := o4
    have e30 : 0 < orient A U T := o8
    have e31 : 0 < orient A U R := o9
    have e32 : 0 < orient A U Q := o6
    have e41 : 0 < orient U T R := by rw [orient_cyc]; exact o3
    have e42 : 0 < orient U T Q := by rw [orient_cyc]; exact o10
    have e43 : 0 < orient U T A := by rw [orient_cyc, orient_cyc]; exact o8
    intro k j hjk hjk1
    fin_cases k <;> fin_cases j <;> simp [hW] at hjk hjk1 ⊢ <;> assumption
  refine ⟨W, hWinj, hWmem, hWccw, ?_⟩
  -- (6) every other point of `S` is cut off by one of six lines
  intro q hqS hqW
  have hqT : q ≠ T := by have h := hqW 0; simpa [hW] using h
  have hqR : q ≠ R := by have h := hqW 1; simpa [hW] using h
  have hqQ : q ≠ Q := by have h := hqW 2; simpa [hW] using h
  have hqA : q ≠ A := by have h := hqW 3; simpa [hW] using h
  have hqU : q ≠ U := by have h := hqW 4; simpa [hW] using h
  have nBM : B ≠ M := Ne.symm nMB
  have hLBM : ∀ k : Fin 5, 0 ≤ orient B M (W k) := by
    have b0 : 0 ≤ orient B M T := by linarith [orient_swap_left M B T]
    have b1 : 0 ≤ orient B M R := by linarith [orient_swap_left M B R]
    have b2 : 0 ≤ orient B M Q := by linarith [orient_swap_left M B Q]
    have b3 : 0 ≤ orient B M A := by linarith [orient_cyc M A B, orient_cyc A B M]
    have b4 : 0 ≤ orient B M U := by linarith [orient_cyc M U B, orient_cyc U B M]
    intro k
    fin_cases k
    · simpa [hW] using b0
    · simpa [hW] using b1
    · simpa [hW] using b2
    · simpa [hW] using b3
    · simpa [hW] using b4
  rcases le_or_gt (orient B M q) 0 with h4 | h4
  · exact ⟨B, M, nBM, hLBM, h4⟩
  have hLAAm : ∀ k : Fin 5, 0 ≤ orient A Am (W k) := by
    have b0 : 0 ≤ orient A Am T := by linarith [orient_swap_left Am A T]
    have b1 : 0 ≤ orient A Am R := by linarith [orient_swap_left Am A R]
    have b2 : 0 ≤ orient A Am Q := by linarith [orient_swap_left Am A Q]
    have b3 : 0 ≤ orient A Am A := by rw [orient_self_left]
    have b4 : 0 ≤ orient A Am U := by linarith [orient_swap_left Am A U]
    intro k
    fin_cases k
    · simpa [hW] using b0
    · simpa [hW] using b1
    · simpa [hW] using b2
    · simpa [hW] using b3
    · simpa [hW] using b4
  rcases le_or_gt (orient A Am q) 0 with h9 | h9
  · exact ⟨A, Am, Ne.symm nAmA, hLAAm, h9⟩
  have hLMAm : ∀ k : Fin 5, 0 ≤ orient M Am (W k) := by
    have b3 : 0 ≤ orient M Am A := cMAmA.le
    intro k
    fin_cases k
    · simpa [hW] using gT.le
    · simpa [hW] using gR.le
    · simpa [hW] using gQ.le
    · simpa [hW] using b3
    · simpa [hW] using u4
  rcases le_or_gt (orient M Am q) 0 with h10 | h10
  · exact ⟨M, Am, nMAm, hLMAm, h10⟩
  have hLAU : ∀ k : Fin 5, 0 ≤ orient A U (W k) := by
    have b3 : 0 ≤ orient A U A := by rw [orient_self_left]
    have b4 : 0 ≤ orient A U U := by rw [orient_self_right]
    intro k
    fin_cases k
    · simpa [hW] using o8.le
    · simpa [hW] using o9.le
    · simpa [hW] using o6.le
    · simpa [hW] using b3
    · simpa [hW] using b4
  rcases le_or_gt (orient A U q) 0 with h8 | h8
  · exact ⟨A, U, nAU, hLAU, h8⟩
  obtain ⟨Tp, hTp1, hTp2⟩ : ∃ p : Point, p.1 = T.1 + B.1 - A.1 ∧ p.2 = T.2 + B.2 - A.2 :=
    ⟨(T.1 + B.1 - A.1, T.2 + B.2 - A.2), rfl, rfl⟩
  have hTpx : ∀ x : Point, orient T Tp x = orient A B x - orient A B T := by
    intro x
    unfold orient
    rw [hTp1, hTp2]
    ring
  have hTTp : T ≠ Tp := by
    intro h
    refine hAB (Prod.ext ?_ ?_)
    · have h1 : T.1 = Tp.1 := by rw [h]
      rw [hTp1] at h1; linarith
    · have h2 : T.2 = Tp.2 := by rw [h]
      rw [hTp2] at h2; linarith
  have hLTp : ∀ k : Fin 5, 0 ≤ orient T Tp (W k) := by
    have b0 : 0 ≤ orient T Tp T := by rw [hTpx]; ring_nf; rfl
    have b1 : 0 ≤ orient T Tp R := by rw [hTpx]; linarith
    have b2 : 0 ≤ orient T Tp Q := by rw [hTpx]; linarith
    have b3 : 0 ≤ orient T Tp A := by rw [hTpx, orient_self_left]; linarith
    have b4 : 0 ≤ orient T Tp U := by rw [hTpx]; linarith
    intro k
    fin_cases k
    · simpa [hW] using b0
    · simpa [hW] using b1
    · simpa [hW] using b2
    · simpa [hW] using b3
    · simpa [hW] using b4
  rcases le_or_gt (orient T Tp q) 0 with h1 | h1
  · exact ⟨T, Tp, hTTp, hLTp, h1⟩
  have hLUT : ∀ k : Fin 5, 0 ≤ orient U T (W k) := by
    have b0 : 0 ≤ orient U T T := by rw [orient_self_right]
    have b1 : 0 ≤ orient U T R := by rw [orient_cyc]; exact o3.le
    have b2 : 0 ≤ orient U T Q := by rw [orient_cyc]; exact o10.le
    have b3 : 0 ≤ orient U T A := by rw [orient_cyc, orient_cyc]; exact o8.le
    have b4 : 0 ≤ orient U T U := by rw [orient_self_left]
    intro k
    fin_cases k
    · simpa [hW] using b0
    · simpa [hW] using b1
    · simpa [hW] using b2
    · simpa [hW] using b3
    · simpa [hW] using b4
  rcases le_or_gt (orient U T q) 0 with h2 | h2
  · exact ⟨U, T, Ne.symm nTU, hLUT, h2⟩
  -- (7) no point survives all six cuts
  exfalso
  rw [hTpx] at h1
  have hMBq : orient M B q < 0 := by linarith [orient_swap_left M B q]
  have hqM : q ≠ M := by
    intro h
    rw [h, orient_self_right] at h4
    exact lt_irrefl _ h4
  have hqB : q ≠ B := by
    intro h
    rw [h, orient_self_left] at h4
    exact lt_irrefl _ h4
  rcases lt_trichotomy (orient M A q) 0 with hma | hma | hma
  · have hAUM : orient A U M < 0 := by linarith [orient_cyc M A U]
    have hATM : 0 < orient A T M := by linarith [orient_cyc M A T]
    have hAMq : 0 < orient A M q := by linarith [orient_swap_left M A q]
    have hidb : orient A T q * orient A U M
        = orient A T M * orient A U q + orient A U T * orient A M q := by
      unfold orient; ring
    have hrhs : 0 < orient A T M * orient A U q + orient A U T * orient A M q :=
      add_pos (mul_pos hATM h8) (mul_pos o8 hAMq)
    have hATq : orient A T q < 0 := by nlinarith [hidb, hrhs, hAUM]
    have hTAq : 0 < orient T A q := by linarith [orient_swap_left T A q]
    have hAmAq : orient Am A q < 0 := by linarith [orient_swap_left Am A q]
    have hqCand : q ∈ Cand := by
      rw [hCandDef]
      exact Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hqS, hTAq, hma, hAmAq, h10⟩)
    have hlast := hfirst q hqCand hqU
    linarith [orient_swap_left T U q]
  · exact hgp M hMS A hAS q hqS nMA (Ne.symm hqM) (Ne.symm hqA) hma
  · rcases lt_trichotomy (orient A B q) 0 with hab | hab | hab
    · have := hfar q hqS hma hMBq hab hqQ hqR hqT
      linarith
    · exact hgp A hAS B hBS q hqS hAB (Ne.symm hqA) (Ne.symm hqB) hab
    · exact hqM (hMuniq q hqS hma hab h4)

/-- Swapping the two coordinates reverses every orientation. -/
theorem orient_swapCoords (a b c : Point) :
    orient (Prod.swap a) (Prod.swap b) (Prod.swap c) = -orient a b c := by
  simp only [orient, Prod.fst_swap, Prod.snd_swap]
  ring

/-- Membership in the coordinate-swapped image of a finite set. -/
theorem mem_image_swap (S : Finset Point) (z : Point) :
    z ∈ S.image Prod.swap ↔ Prod.swap z ∈ S := by
  constructor
  · intro h
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp h
    rwa [Prod.swap_swap]
  · intro h
    exact Finset.mem_image.mpr ⟨Prod.swap z, h, Prod.swap_swap z⟩

/-- General position is preserved by swapping the two coordinates. -/
theorem generalPosition_image_swap (S : Finset Point) (hgp : GeneralPosition S) :
    GeneralPosition (S.image Prod.swap) := by
  intro a ha b hb c hc hab hac hbc
  have ha' : Prod.swap a ∈ S := (mem_image_swap S a).mp ha
  have hb' : Prod.swap b ∈ S := (mem_image_swap S b).mp hb
  have hc' : Prod.swap c ∈ S := (mem_image_swap S c).mp hc
  have key : orient a b c = -orient (Prod.swap a) (Prod.swap b) (Prod.swap c) := by
    rw [orient_swapCoords, neg_neg]
  rw [key, neg_ne_zero]
  exact hgp _ ha' _ hb' _ hc' (fun h => hab (Prod.swap_injective h))
    (fun h => hac (Prod.swap_injective h)) (fun h => hbc (Prod.swap_injective h))

set_option maxHeartbeats 1000000 in
/-- Harborth's third-point case (corrected): `Q, S3, T` are the closest, second-closest and
third-closest points of `S` in the wedge beyond edge `i` (all wedge points lie behind the
neighbouring edge lines and, apart from `Q`, beyond the tent `P i, Q, P (i+1)`). Then `S` has an
empty convex pentagon: `{T, S3, Q, P i, U}` with `U` the first point of `B (i-1) ∪ {P (i-1)}` met
when the ray `T → P i` rotates counterclockwise about `T`, if `T` is strictly right of `Q → S3`;
mirror otherwise. -/
theorem third_case (S : Finset Point) (hgp : GeneralPosition S) (P : Fin 5 → Point)
    (_hinj : Function.Injective P) (hPS : ∀ i, P i ∈ S)
    (hccw : ∀ i j : Fin 5, j ≠ i → j ≠ i + 1 → 0 < orient (P i) (P (i + 1)) (P j))
    (M : Point) (hMS : M ∈ S)
    (hM : M ∈ interior (convexHull ℝ ((Finset.univ.image P : Finset Point) : Set Point)))
    (huniq : ∀ q ∈ S, q ∈ interior (convexHull ℝ ((Finset.univ.image P : Finset Point) : Set Point))
      → q = M)
    (hcore : ∀ i, 0 < orient (P i) (P (i + 2)) M) (i : Fin 5)
    (hnofront : ∀ q ∈ S, 0 < orient M (P i) q → orient M (P (i + 1)) q < 0 →
      orient (P i) (P (i + 1)) q < 0 →
      orient (P (i - 1)) (P i) q < 0 ∧ orient (P (i + 1)) (P (i + 2)) q < 0)
    (Q S3 T : Point) (hQS : Q ∈ S) (hS3S : S3 ∈ S) (hTS : T ∈ S)
    (hQA : 0 < orient M (P i) Q ∧ orient M (P (i + 1)) Q < 0 ∧ orient (P i) (P (i + 1)) Q < 0)
    (hS3A : 0 < orient M (P i) S3 ∧ orient M (P (i + 1)) S3 < 0 ∧ orient (P i) (P (i + 1)) S3 < 0)
    (hTA : 0 < orient M (P i) T ∧ orient M (P (i + 1)) T < 0 ∧ orient (P i) (P (i + 1)) T < 0)
    (hQS3 : Q ≠ S3) (hQT : Q ≠ T) (hS3T : S3 ≠ T)
    (hQmin : ∀ q ∈ S, 0 < orient M (P i) q → orient M (P (i + 1)) q < 0 →
      orient (P i) (P (i + 1)) q < 0 → -orient (P i) (P (i + 1)) Q ≤ -orient (P i) (P (i + 1)) q)
    (hS3min : ∀ q ∈ S, 0 < orient M (P i) q → orient M (P (i + 1)) q < 0 →
      orient (P i) (P (i + 1)) q < 0 → q ≠ Q →
      -orient (P i) (P (i + 1)) S3 ≤ -orient (P i) (P (i + 1)) q)
    (hTmin : ∀ q ∈ S, 0 < orient M (P i) q → orient M (P (i + 1)) q < 0 →
      orient (P i) (P (i + 1)) q < 0 → q ≠ Q → q ≠ S3 →
      -orient (P i) (P (i + 1)) T ≤ -orient (P i) (P (i + 1)) q)
    (hC : ∀ q ∈ S, 0 < orient M (P i) q → orient M (P (i + 1)) q < 0 →
      orient (P i) (P (i + 1)) q < 0 → q ≠ Q →
      0 < orient Q (P i) q ∧ 0 < orient (P (i + 1)) Q q) :
    ∃ V : Finset Point, V.card = 5 ∧ EmptyConvexPolygon S V := by
  classical
  -- (A) index arithmetic in `Fin 5`
  have f1 : ∀ j : Fin 5, j - 1 + 1 = j := by decide
  have f2 : ∀ j : Fin 5, j - 1 + 2 = j + 1 := by decide
  have f3 : ∀ j : Fin 5, j + 1 + 1 = j + 2 := by decide
  have d1 : ∀ j : Fin 5, j - 1 ≠ j := by decide
  have d2 : ∀ j : Fin 5, j - 1 ≠ j + 1 := by decide
  have d3 : ∀ j : Fin 5, j + 2 ≠ j := by decide
  have d4 : ∀ j : Fin 5, j + 2 ≠ j + 1 := by decide
  -- (B) the pentagon data around `M`
  have hE := orient_edge_pos_of_mem_interior P M hM hccw
  have hEi : 0 < orient (P i) (P (i + 1)) M := hE i
  have hEm : 0 < orient (P (i - 1)) (P i) M := by have h := hE (i - 1); rwa [f1 i] at h
  have hEi1 : 0 < orient (P (i + 1)) (P (i + 2)) M := by have h := hE (i + 1); rwa [f3 i] at h
  have hCm : 0 < orient (P (i - 1)) (P (i + 1)) M := by have h := hcore (i - 1); rwa [f2 i] at h
  have cMAB : 0 < orient M (P i) (P (i + 1)) := by rw [orient_cyc]; exact hEi
  have cMAmA : 0 < orient M (P (i - 1)) (P i) := by rw [orient_cyc]; exact hEm
  have cMAmB : 0 < orient M (P (i - 1)) (P (i + 1)) := by rw [orient_cyc]; exact hCm
  have cABAm : 0 < orient (P i) (P (i + 1)) (P (i - 1)) := hccw i (i - 1) (d1 i) (d2 i)
  have cABC : 0 < orient (P i) (P (i + 1)) (P (i + 2)) := hccw i (i + 2) (d3 i) (d4 i)
  -- (C) the wedge and tent literals of the three closest points
  obtain ⟨nfQ1, nfQ2⟩ := hnofront Q hQS hQA.1 hQA.2.1 hQA.2.2
  obtain ⟨nfS1, nfS2⟩ := hnofront S3 hS3S hS3A.1 hS3A.2.1 hS3A.2.2
  obtain ⟨nfT1, nfT2⟩ := hnofront T hTS hTA.1 hTA.2.1 hTA.2.2
  obtain ⟨tS1, tS2⟩ := hC S3 hS3S hS3A.1 hS3A.2.1 hS3A.2.2 (Ne.symm hQS3)
  obtain ⟨tT1, tT2⟩ := hC T hTS hTA.1 hTA.2.1 hTA.2.2 (Ne.symm hQT)
  have dTR : orient (P i) (P (i + 1)) T ≤ orient (P i) (P (i + 1)) S3 := by
    have h := hS3min T hTS hTA.1 hTA.2.1 hTA.2.2 (Ne.symm hQT)
    linarith
  have dRQ : orient (P i) (P (i + 1)) S3 ≤ orient (P i) (P (i + 1)) Q := by
    have h := hQmin S3 hS3S hS3A.1 hS3A.2.1 hS3A.2.2
    linarith
  -- (D) the only point of `S` strictly inside the triangle `M, P i, P (i+1)` is `M`
  have hMuniqR : ∀ q ∈ S, 0 < orient M (P i) q → 0 < orient (P i) (P (i + 1)) q →
      0 < orient (P (i + 1)) M q → q = M := by
    intro q hqS h1 h2 h3
    refine huniq q hqS ?_
    have htri := mem_interior_triangle_of_orient_pos M (P i) (P (i + 1)) q cMAB h1 h2 h3
    have hsub : convexHull ℝ ({M, P i, P (i + 1)} : Set Point) ⊆
        convexHull ℝ ((Finset.univ.image P : Finset Point) : Set Point) := by
      refine convexHull_min ?_ (convex_convexHull ℝ _)
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact interior_subset hM
      · exact subset_convexHull ℝ _
          (Finset.mem_coe.mpr (Finset.mem_image_of_mem P (Finset.mem_univ i)))
      · exact subset_convexHull ℝ _
          (Finset.mem_coe.mpr (Finset.mem_image_of_mem P (Finset.mem_univ (i + 1))))
    exact interior_mono hsub htri
  -- (E) the residual points of the wedge are farther from the edge line than `T`
  have hfarR : ∀ q ∈ S, 0 < orient M (P i) q → orient M (P (i + 1)) q < 0 →
      orient (P i) (P (i + 1)) q < 0 → q ≠ Q → q ≠ S3 → q ≠ T →
      orient (P i) (P (i + 1)) q ≤ orient (P i) (P (i + 1)) T := by
    rintro q hqS h1 h2 h3 hq1 hq2 -
    have h := hTmin q hqS h1 h2 h3 hq1 hq2
    linarith
  -- (F) the two mirror-symmetric cases
  rcases lt_trichotomy (orient Q S3 T) 0 with hcase | hcase | hcase
  · -- CASE R: the counterclockwise pentagon `T, S3, Q, P i, U`
    obtain ⟨W, hWinj, hWS, hWccw, hWsep⟩ :=
      third_pentagon S hgp M (P i) (P (i + 1)) (P (i - 1)) Q S3 T hMS (hPS i) (hPS (i + 1))
        (hPS (i - 1)) hQS hS3S hTS cMAB cMAmA cMAmB cABAm hQA.1 hQA.2.1 hQA.2.2 nfQ1
        hS3A.1 hS3A.2.1 nfS1 hTA.1 hTA.2.1 hTA.2.2 nfT1 tS1 tT1 hcase dTR dRQ hfarR hMuniqR
    exact emptyPentagon_of_data S W hWinj hWS hWccw hWsep
  · exact absurd hcase (hgp Q hQS S3 hS3S T hTS hQS3 hQT hS3T)
  · -- CASE L: the mirror image of CASE R across the diagonal
    suffices h : ∃ W : Fin 5 → Point, Function.Injective W ∧
        (∀ k, W k ∈ S.image Prod.swap) ∧
        (∀ k j : Fin 5, j ≠ k → j ≠ k + 1 → 0 < orient (W k) (W (k + 1)) (W j)) ∧
        ∀ q ∈ S.image Prod.swap, (∀ k, q ≠ W k) → ∃ u v : Point, u ≠ v ∧
          (∀ k, 0 ≤ orient u v (W k)) ∧ orient u v q ≤ 0 by
      obtain ⟨W', hWinj', hWS', hWccw', hWsep'⟩ := h
      have hneg : ∀ k : Fin 5, -(k + 1) + 1 = -k := by decide
      refine emptyPentagon_of_data S (fun k => Prod.swap (W' (-k))) ?_ ?_ ?_ ?_
      · intro x y hxy
        exact neg_injective (hWinj' (Prod.swap_injective hxy))
      · intro k
        exact (mem_image_swap S (W' (-k))).mp (hWS' (-k))
      · intro k j hjk hjk1
        have hne1 : (-j : Fin 5) ≠ -(k + 1) := fun h => hjk1 (neg_injective h)
        have hne2 : (-j : Fin 5) ≠ -(k + 1) + 1 := by
          rw [hneg k]
          exact fun h => hjk (neg_injective h)
        have hcc := hWccw' (-(k + 1)) (-j) hne1 hne2
        rw [hneg k] at hcc
        rw [orient_swapCoords]
        linarith [orient_swap_left (W' (-(k + 1))) (W' (-k)) (W' (-j))]
      · intro q hqS hqW
        have hqW' : ∀ k, Prod.swap q ≠ W' k := by
          intro k hk
          refine hqW (-k) ?_
          show q = Prod.swap (W' (- -k))
          rw [neg_neg, ← hk, Prod.swap_swap]
        obtain ⟨u, v, huv, hV, hq⟩ :=
          hWsep' (Prod.swap q) (Finset.mem_image_of_mem _ hqS) hqW'
        refine ⟨Prod.swap v, Prod.swap u, fun hs => huv (Prod.swap_injective hs).symm, ?_, ?_⟩
        · intro k
          rw [orient_swapCoords]
          linarith [hV (-k), orient_swap_left u v (W' (-k))]
        · have e : orient (Prod.swap v) (Prod.swap u) q
              = orient (Prod.swap v) (Prod.swap u) (Prod.swap (Prod.swap q)) := by
            rw [Prod.swap_swap]
          rw [e, orient_swapCoords]
          linarith [orient_swap_left u v (Prod.swap q)]
    refine third_pentagon (S.image Prod.swap) (generalPosition_image_swap S hgp) (Prod.swap M)
      (Prod.swap (P (i + 1))) (Prod.swap (P i)) (Prod.swap (P (i + 2))) (Prod.swap Q)
      (Prod.swap S3) (Prod.swap T) (Finset.mem_image_of_mem _ hMS)
      (Finset.mem_image_of_mem _ (hPS (i + 1))) (Finset.mem_image_of_mem _ (hPS i))
      (Finset.mem_image_of_mem _ (hPS (i + 2))) (Finset.mem_image_of_mem _ hQS)
      (Finset.mem_image_of_mem _ hS3S) (Finset.mem_image_of_mem _ hTS) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [orient_swapCoords]; linarith [orient_swap M (P i) (P (i + 1))]
    · rw [orient_swapCoords]
      linarith [orient_swap M (P (i + 1)) (P (i + 2)), orient_cyc M (P (i + 1)) (P (i + 2)),
        orient_cyc (P (i + 1)) (P (i + 2)) M]
    · rw [orient_swapCoords]
      linarith [orient_swap M (P i) (P (i + 2)), orient_cyc M (P i) (P (i + 2)),
        orient_cyc (P i) (P (i + 2)) M, hcore i]
    · rw [orient_swapCoords]
      linarith [orient_swap_left (P i) (P (i + 1)) (P (i + 2))]
    · rw [orient_swapCoords]; linarith [hQA.2.1]
    · rw [orient_swapCoords]; linarith [hQA.1]
    · rw [orient_swapCoords]; linarith [orient_swap_left (P i) (P (i + 1)) Q]
    · rw [orient_swapCoords]; linarith [orient_swap_left (P (i + 1)) (P (i + 2)) Q]
    · rw [orient_swapCoords]; linarith [hS3A.2.1]
    · rw [orient_swapCoords]; linarith [hS3A.1]
    · rw [orient_swapCoords]; linarith [orient_swap_left (P (i + 1)) (P (i + 2)) S3]
    · rw [orient_swapCoords]; linarith [hTA.2.1]
    · rw [orient_swapCoords]; linarith [hTA.1]
    · rw [orient_swapCoords]; linarith [orient_swap_left (P i) (P (i + 1)) T]
    · rw [orient_swapCoords]; linarith [orient_swap_left (P (i + 1)) (P (i + 2)) T]
    · rw [orient_swapCoords]; linarith [orient_swap_left (P (i + 1)) Q S3]
    · rw [orient_swapCoords]; linarith [orient_swap_left (P (i + 1)) Q T]
    · rw [orient_swapCoords]; linarith
    · simp only [orient_swapCoords]
      linarith [orient_swap_left (P i) (P (i + 1)) T, orient_swap_left (P i) (P (i + 1)) S3]
    · simp only [orient_swapCoords]
      linarith [orient_swap_left (P i) (P (i + 1)) S3, orient_swap_left (P i) (P (i + 1)) Q]
    · rintro q hqS h1 h2 h3 hq1 hq2 -
      obtain ⟨z, hzS, rfl⟩ := Finset.mem_image.mp hqS
      simp only [orient_swapCoords] at h1 h2 h3 ⊢
      have e1 : 0 < orient M (P i) z := by linarith [orient_swap_left (P i) M z]
      have e2 : orient M (P (i + 1)) z < 0 := by linarith
      have e3 : orient (P i) (P (i + 1)) z < 0 := by
        linarith [orient_swap_left (P i) (P (i + 1)) z]
      have h := hTmin z hzS e1 e2 e3 (fun hx => hq1 (by rw [hx]))
        (fun hx => hq2 (by rw [hx]))
      linarith [orient_swap_left (P i) (P (i + 1)) z, orient_swap_left (P i) (P (i + 1)) T]
    · intro q hqS h1 h2 h3
      obtain ⟨z, hzS, rfl⟩ := Finset.mem_image.mp hqS
      simp only [orient_swapCoords] at h1 h2 h3
      have e1 : 0 < orient M (P i) z := by linarith [orient_swap_left (P i) M z]
      have e2 : 0 < orient (P i) (P (i + 1)) z := by
        linarith [orient_swap_left (P i) (P (i + 1)) z]
      have e3 : 0 < orient (P (i + 1)) M z := by linarith [orient_swap_left M (P (i + 1)) z]
      rw [hMuniqR z hzS e1 e2 e3]

end Horton
