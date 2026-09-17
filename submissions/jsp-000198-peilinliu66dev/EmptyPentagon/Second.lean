/-
Reused under MIT from CollinYuanjieRen/awards, commit
b8bb4f7803f921a7970abc880291ad9372111360, JSP-000198 small-k submission.
Original module: EmptyPentagon/Second.lean
Source/permission records: EmptyPentagon/UPSTREAM.md and LICENSE.
Local target: Lean 4.33.1 / pinned Mathlib 0df444a36.
-/
import EmptyPentagon.Definitions
import EmptyPentagon.Certificate
import EmptyPentagon.Interp
import EmptyPentagon.TriangleInterior
import EmptyPentagon.Pentagon
import EmptyPentagon.Signs
import EmptyPentagon.Identities

noncomputable section
open Classical
namespace Horton

/-! ### Elementary orientation tools -/

/-- The three-term Grassmann–Plücker product identity for orientations sharing a base point. -/
theorem second_mul_add (p w x y z : Point) :
    orient p x z * orient p w y = orient p x y * orient p w z + orient p w x * orient p y z := by
  unfold orient; ring

/-- A positive orientation forces its three arguments to be pairwise distinct. -/
theorem second_ne_of_orient_pos (a b c : Point) (h : 0 < orient a b c) :
    a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  refine ⟨?_, ?_, ?_⟩ <;> rintro rfl
  · simp [orient_self_pair] at h
  · simp [orient_self_left] at h
  · simp [orient_self_right] at h

/-! ### Angular extremes around a pivot -/

/-- Among finitely many points strictly left of the directed line `p → w`, one comes first in
the counterclockwise angular order around `p`. -/
theorem second_angular_first (S : Finset Point) (hgp : GeneralPosition S) (p w : Point)
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
    have key := second_mul_add p w a b c
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

/-- Among finitely many points strictly right of the directed line `p → w`, one comes last in
the counterclockwise angular order around `p`. -/
theorem second_angular_last (S : Finset Point) (hgp : GeneralPosition S) (p w : Point)
    (hpS : p ∈ S) (C : Finset Point) (hCS : C ⊆ S) (hCne : C.Nonempty)
    (hright : ∀ z ∈ C, orient p w z < 0) :
    ∃ u ∈ C, ∀ z ∈ C, z ≠ u → orient p u z < 0 := by
  classical
  have hne : ∀ z ∈ C, p ≠ z := by
    intro z hz h
    have hz' := hright z hz
    rw [← h, orient_self_left] at hz'
    exact lt_irrefl _ hz'
  have htr : ∀ a ∈ C, ∀ b ∈ C, ∀ c ∈ C, orient p a b < 0 → orient p b c < 0 →
      orient p a c < 0 := by
    intro a ha b hb c hc h1 h2
    have key := second_mul_add p w a b c
    have hprod : 0 < orient p a c * orient p w b := by
      rw [key]
      exact add_pos (mul_pos_of_neg_of_neg h1 (hright c hc))
        (mul_pos_of_neg_of_neg (hright a ha) h2)
    by_contra hcon
    have hle : 0 ≤ orient p a c := not_lt.mp hcon
    nlinarith [hprod, hright b hb, hle]
  have hlt : ∀ a ∈ C, ∀ b ∈ C, orient p a b < 0 →
      (C.filter fun r => orient p r a < 0).card < (C.filter fun r => orient p r b < 0).card := by
    intro a ha b hb h
    apply Finset.card_lt_card
    have hsub : (C.filter fun r => orient p r a < 0) ⊆ C.filter fun r => orient p r b < 0 := by
      intro x hx
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, htr x hx.1 a ha b hb hx.2 h⟩
    rw [Finset.ssubset_iff_of_subset hsub]
    refine ⟨a, Finset.mem_filter.mpr ⟨ha, h⟩, fun hmem => ?_⟩
    have hbad := (Finset.mem_filter.mp hmem).2
    rw [orient_self_right] at hbad
    exact lt_irrefl _ hbad
  obtain ⟨u, huC, hmin⟩ :=
    Finset.exists_min_image C (fun q => (C.filter fun r => orient p r q < 0).card) hCne
  refine ⟨u, huC, fun z hz hzu => ?_⟩
  have hnz : orient p u z ≠ 0 :=
    hgp p hpS u (hCS huC) z (hCS hz) (hne u huC) (hne z hz) (Ne.symm hzu)
  rcases lt_or_gt_of_ne hnz with hneg | hpos
  · exact hneg
  · exfalso
    have hzu' : orient p z u < 0 := by linarith [orient_swap p u z]
    have h1 := hlt z hz u huC hzu'
    have h2 := hmin z hz
    omega

/-- A counterclockwise pentagon each of whose outside points is cut off by some line yields an
empty convex pentagon of `S`. -/
theorem second_emptyPentagon_of_data (S : Finset Point) (W : Fin 5 → Point)
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

/-! ### The two key sign facts for the closest wedge point -/

/-- A wedge point `z` no closer to the line `A B` than `Q` and strictly right of `Q → A` lies
strictly left of `B → Q`. -/
theorem second_key_right (A B Q z : Point) (hzQ : orient A B z ≤ orient A B Q)
    (hz : orient Q A z < 0) : 0 < orient B Q z := by
  have h4 := orient_four_identity A B Q z
  have h1 : 0 < orient A Q z := by linarith [orient_cyc A Q z, orient_swap Q A z]
  linarith

/-- A wedge point `z` no closer to the line `A B` than `Q` and strictly right of `B → Q` lies
strictly right of `A → Q`. -/
theorem second_key_left (A B Q z : Point) (hzQ : orient A B z ≤ orient A B Q)
    (hz : orient B Q z < 0) : orient A Q z < 0 := by
  have h4 := orient_four_identity A B Q z
  linarith

/-! ### The two pentagons -/

/-- The counterclockwise empty pentagon `A, Q, R, B, M` of Harborth's second-point case, where
`R` is the angularly first wedge point right of `Q → A` as seen from `B`. -/
theorem second_pentagon_right (S : Finset Point) (hgp : GeneralPosition S) (M A B Q R : Point)
    (hMS : M ∈ S) (hAS : A ∈ S) (hBS : B ∈ S) (hQS : Q ∈ S) (hRS : R ∈ S)
    (cMAB : 0 < orient M A B)
    (wQ1 : 0 < orient M A Q) (wQ2 : orient M B Q < 0) (wQ3 : orient A B Q < 0)
    (wR1 : 0 < orient M A R) (wR2 : orient M B R < 0) (wR3 : orient A B R < 0)
    (hQmin : ∀ q ∈ S, 0 < orient M A q → orient M B q < 0 → orient A B q < 0 →
      orient A B q ≤ orient A B Q)
    (tR : orient Q A R < 0)
    (hfirst : ∀ z ∈ S, 0 < orient M A z → orient M B z < 0 → orient A B z < 0 →
      orient Q A z < 0 → z ≠ R → 0 < orient B R z)
    (hMuniq : ∀ q ∈ S, 0 < orient M A q → 0 < orient A B q → 0 < orient B M q → q = M) :
    ∃ V : Finset Point, V.card = 5 ∧ EmptyConvexPolygon S V := by
  classical
  -- (1) the ten counterclockwise facts of the pentagon `A, Q, R, B, M`
  have o034 : 0 < orient A B M := by linarith [orient_cyc M A B]
  have o012 : 0 < orient A Q R := by linarith [orient_cyc A Q R, orient_swap Q A R]
  have o013 : 0 < orient A Q B := by linarith [orient_swap A B Q]
  have o014 : 0 < orient A Q M := by linarith [orient_cyc M A Q]
  have o023 : 0 < orient A R B := by linarith [orient_swap A B R]
  have o024 : 0 < orient A R M := by linarith [orient_cyc M A R]
  have key : 0 < orient B Q R :=
    second_key_right A B Q R (hQmin R hRS wR1 wR2 wR3) tR
  have o123 : 0 < orient Q R B := by linarith [orient_cyc B Q R]
  have o134 : 0 < orient Q B M := by linarith [orient_cyc M Q B, orient_swap M B Q]
  have o234 : 0 < orient R B M := by linarith [orient_cyc M R B, orient_swap M B R]
  have o124 : 0 < orient Q R M := by
    have hid := second_mul_add Q A R B M
    have hQAB : orient Q A B < 0 := by linarith [orient_swap_left A Q B]
    have hQAM : orient Q A M < 0 := by linarith [orient_swap_left A Q M]
    have hrhs : orient Q R B * orient Q A M + orient Q A R * orient Q B M < 0 := by
      have t1 := mul_neg_of_pos_of_neg o123 hQAM
      have t2 := mul_neg_of_neg_of_pos tR o134
      linarith
    nlinarith [hid, hrhs, hQAB]
  -- (2) the five vertices are pairwise distinct
  obtain ⟨nMA, nMB, nAB⟩ := second_ne_of_orient_pos M A B cMAB
  obtain ⟨nAQ, nAR, nQR⟩ := second_ne_of_orient_pos A Q R o012
  obtain ⟨nQB, nQM, nBM⟩ := second_ne_of_orient_pos Q B M o134
  obtain ⟨nRB, nRM, -⟩ := second_ne_of_orient_pos R B M o234
  have nAM : A ≠ M := Ne.symm nMA
  -- (3) the pentagon
  set W : Fin 5 → Point := ![A, Q, R, B, M] with hW
  have hWinj : Function.Injective W := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;>
      simp [hW, nAQ, nAR, nAB, nAM, nQR, nQB, nQM, nRB, nRM, nBM, nAQ.symm, nAR.symm, nAB.symm,
        nAM.symm, nQR.symm, nQB.symm, nQM.symm, nRB.symm, nRM.symm, nBM.symm] at hxy ⊢
  have hWmem : ∀ k : Fin 5, W k ∈ S := by
    intro k
    fin_cases k <;> simp [hW, hAS, hQS, hRS, hBS, hMS]
  have hWccw : ∀ k j : Fin 5, j ≠ k → j ≠ k + 1 → 0 < orient (W k) (W (k + 1)) (W j) := by
    have e02 : 0 < orient A Q R := o012
    have e03 : 0 < orient A Q B := o013
    have e04 : 0 < orient A Q M := o014
    have e13 : 0 < orient Q R B := o123
    have e14 : 0 < orient Q R M := o124
    have e10 : 0 < orient Q R A := by rw [orient_cyc, orient_cyc]; exact o012
    have e24 : 0 < orient R B M := o234
    have e20 : 0 < orient R B A := by rw [orient_cyc, orient_cyc]; exact o023
    have e21 : 0 < orient R B Q := by rw [orient_cyc, orient_cyc]; exact o123
    have e30 : 0 < orient B M A := by rw [orient_cyc]; exact cMAB
    have e31 : 0 < orient B M Q := by rw [orient_cyc, orient_cyc]; exact o134
    have e32 : 0 < orient B M R := by rw [orient_cyc, orient_cyc]; exact o234
    have e41 : 0 < orient M A Q := wQ1
    have e42 : 0 < orient M A R := wR1
    have e43 : 0 < orient M A B := cMAB
    intro k j hjk hjk1
    fin_cases k <;> fin_cases j <;> simp [hW] at hjk hjk1 ⊢ <;> assumption
  refine second_emptyPentagon_of_data S W hWinj hWmem hWccw ?_
  -- (4) every other point of `S` is cut off by one of four edge lines
  intro q hqS hqW
  have hqA : q ≠ A := by have h := hqW 0; simpa [hW] using h
  have hqQ : q ≠ Q := by have h := hqW 1; simpa [hW] using h
  have hqR : q ≠ R := by have h := hqW 2; simpa [hW] using h
  have hqB : q ≠ B := by have h := hqW 3; simpa [hW] using h
  have hqM : q ≠ M := by have h := hqW 4; simpa [hW] using h
  have hLMA : ∀ k : Fin 5, 0 ≤ orient M A (W k) := by
    have b0 : (0 : ℝ) ≤ orient M A A := by rw [orient_self_right]
    have b4 : (0 : ℝ) ≤ orient M A M := by rw [orient_self_left]
    intro k
    fin_cases k
    · simpa [hW] using b0
    · simpa [hW] using wQ1.le
    · simpa [hW] using wR1.le
    · simpa [hW] using cMAB.le
    · simpa [hW] using b4
  rcases le_or_gt (orient M A q) 0 with h1 | h1
  · exact ⟨M, A, nMA, hLMA, h1⟩
  have hLBM : ∀ k : Fin 5, 0 ≤ orient B M (W k) := by
    have b0 : (0 : ℝ) ≤ orient B M A := by rw [orient_cyc]; exact cMAB.le
    have b1 : (0 : ℝ) ≤ orient B M Q := by rw [orient_cyc, orient_cyc]; exact o134.le
    have b2 : (0 : ℝ) ≤ orient B M R := by rw [orient_cyc, orient_cyc]; exact o234.le
    have b3 : (0 : ℝ) ≤ orient B M B := by rw [orient_self_left]
    have b4 : (0 : ℝ) ≤ orient B M M := by rw [orient_self_right]
    intro k
    fin_cases k
    · simpa [hW] using b0
    · simpa [hW] using b1
    · simpa [hW] using b2
    · simpa [hW] using b3
    · simpa [hW] using b4
  rcases le_or_gt (orient B M q) 0 with h2 | h2
  · exact ⟨B, M, nBM, hLBM, h2⟩
  have hMBq : orient M B q < 0 := by linarith [orient_swap_left M B q]
  rcases lt_trichotomy (orient A B q) 0 with hab | hab | hab
  · -- `q` is a wedge point other than `Q` and `R`
    rcases lt_trichotomy (orient Q A q) 0 with hq | hq | hq
    · have hBRq := hfirst q hqS h1 hMBq hab hq hqR
      have hLRB : ∀ k : Fin 5, 0 ≤ orient R B (W k) := by
        have b0 : (0 : ℝ) ≤ orient R B A := by rw [orient_cyc, orient_cyc]; exact o023.le
        have b1 : (0 : ℝ) ≤ orient R B Q := by rw [orient_cyc, orient_cyc]; exact o123.le
        have b2 : (0 : ℝ) ≤ orient R B R := by rw [orient_self_left]
        have b3 : (0 : ℝ) ≤ orient R B B := by rw [orient_self_right]
        intro k
        fin_cases k
        · simpa [hW] using b0
        · simpa [hW] using b1
        · simpa [hW] using b2
        · simpa [hW] using b3
        · simpa [hW] using o234.le
      exact ⟨R, B, nRB, hLRB, by linarith [orient_swap_left B R q]⟩
    · exact absurd hq
        (hgp Q hQS A hAS q hqS (Ne.symm nAQ) (Ne.symm hqQ) (Ne.symm hqA))
    · have hLAQ : ∀ k : Fin 5, 0 ≤ orient A Q (W k) := by
        have b0 : (0 : ℝ) ≤ orient A Q A := by rw [orient_self_left]
        have b1 : (0 : ℝ) ≤ orient A Q Q := by rw [orient_self_right]
        intro k
        fin_cases k
        · simpa [hW] using b0
        · simpa [hW] using b1
        · simpa [hW] using o012.le
        · simpa [hW] using o013.le
        · simpa [hW] using o014.le
      exact ⟨A, Q, nAQ, hLAQ, by linarith [orient_swap_left Q A q]⟩
  · exact absurd hab (hgp A hAS B hBS q hqS nAB (Ne.symm hqA) (Ne.symm hqB))
  · exact absurd (hMuniq q hqS h1 hab h2) hqM

/-- The counterclockwise empty pentagon `A, R, Q, B, M` of Harborth's second-point case, where
`R` is the angularly last wedge point right of `B → Q` as seen from `A`. -/
theorem second_pentagon_left (S : Finset Point) (hgp : GeneralPosition S) (M A B Q R : Point)
    (hMS : M ∈ S) (hAS : A ∈ S) (hBS : B ∈ S) (hQS : Q ∈ S) (hRS : R ∈ S)
    (cMAB : 0 < orient M A B)
    (wQ1 : 0 < orient M A Q) (wQ2 : orient M B Q < 0) (wQ3 : orient A B Q < 0)
    (wR1 : 0 < orient M A R) (wR2 : orient M B R < 0) (wR3 : orient A B R < 0)
    (hQmin : ∀ q ∈ S, 0 < orient M A q → orient M B q < 0 → orient A B q < 0 →
      orient A B q ≤ orient A B Q)
    (tR : orient B Q R < 0)
    (hlast : ∀ z ∈ S, 0 < orient M A z → orient M B z < 0 → orient A B z < 0 →
      orient B Q z < 0 → z ≠ R → orient A R z < 0)
    (hMuniq : ∀ q ∈ S, 0 < orient M A q → 0 < orient A B q → 0 < orient B M q → q = M) :
    ∃ V : Finset Point, V.card = 5 ∧ EmptyConvexPolygon S V := by
  classical
  -- (1) the ten counterclockwise facts of the pentagon `A, R, Q, B, M`
  have o034 : 0 < orient A B M := by linarith [orient_cyc M A B]
  have key : orient A Q R < 0 :=
    second_key_left A B Q R (hQmin R hRS wR1 wR2 wR3) tR
  have o012 : 0 < orient A R Q := by linarith [orient_swap A Q R]
  have o013 : 0 < orient A R B := by linarith [orient_swap A B R]
  have o014 : 0 < orient A R M := by linarith [orient_cyc M A R]
  have o023 : 0 < orient A Q B := by linarith [orient_swap A B Q]
  have o024 : 0 < orient A Q M := by linarith [orient_cyc M A Q]
  have o123 : 0 < orient R Q B := by
    linarith [orient_swap R B Q, orient_cyc B Q R, orient_cyc Q R B]
  have o134 : 0 < orient R B M := by linarith [orient_cyc M R B, orient_swap M B R]
  have o234 : 0 < orient Q B M := by linarith [orient_cyc M Q B, orient_swap M B Q]
  have o124 : 0 < orient R Q M := by
    have hid := second_mul_add R A Q B M
    have hRAB : orient R A B < 0 := by linarith [orient_swap_left A R B]
    have hRAM : orient R A M < 0 := by linarith [orient_swap_left A R M]
    have hRAQ : orient R A Q < 0 := by linarith [orient_swap_left A R Q]
    have hrhs : orient R Q B * orient R A M + orient R A Q * orient R B M < 0 := by
      have t1 := mul_neg_of_pos_of_neg o123 hRAM
      have t2 := mul_neg_of_neg_of_pos hRAQ o134
      linarith
    nlinarith [hid, hrhs, hRAB]
  -- (2) the five vertices are pairwise distinct
  obtain ⟨nMA, nMB, nAB⟩ := second_ne_of_orient_pos M A B cMAB
  obtain ⟨nAR, nAQ, nRQ⟩ := second_ne_of_orient_pos A R Q o012
  obtain ⟨nRB, nRM, nBM⟩ := second_ne_of_orient_pos R B M o134
  obtain ⟨nQB, nQM, -⟩ := second_ne_of_orient_pos Q B M o234
  have nAM : A ≠ M := Ne.symm nMA
  -- (3) the pentagon
  set W : Fin 5 → Point := ![A, R, Q, B, M] with hW
  have hWinj : Function.Injective W := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;>
      simp [hW, nAQ, nAR, nAB, nAM, nRQ, nQB, nQM, nRB, nRM, nBM, nAQ.symm, nAR.symm, nAB.symm,
        nAM.symm, nRQ.symm, nQB.symm, nQM.symm, nRB.symm, nRM.symm, nBM.symm] at hxy ⊢
  have hWmem : ∀ k : Fin 5, W k ∈ S := by
    intro k
    fin_cases k <;> simp [hW, hAS, hQS, hRS, hBS, hMS]
  have hWccw : ∀ k j : Fin 5, j ≠ k → j ≠ k + 1 → 0 < orient (W k) (W (k + 1)) (W j) := by
    have e02 : 0 < orient A R Q := o012
    have e03 : 0 < orient A R B := o013
    have e04 : 0 < orient A R M := o014
    have e13 : 0 < orient R Q B := o123
    have e14 : 0 < orient R Q M := o124
    have e10 : 0 < orient R Q A := by rw [orient_cyc, orient_cyc]; exact o012
    have e24 : 0 < orient Q B M := o234
    have e20 : 0 < orient Q B A := by rw [orient_cyc, orient_cyc]; exact o023
    have e21 : 0 < orient Q B R := by rw [orient_cyc, orient_cyc]; exact o123
    have e30 : 0 < orient B M A := by rw [orient_cyc]; exact cMAB
    have e31 : 0 < orient B M R := by rw [orient_cyc, orient_cyc]; exact o134
    have e32 : 0 < orient B M Q := by rw [orient_cyc, orient_cyc]; exact o234
    have e41 : 0 < orient M A R := wR1
    have e42 : 0 < orient M A Q := wQ1
    have e43 : 0 < orient M A B := cMAB
    intro k j hjk hjk1
    fin_cases k <;> fin_cases j <;> simp [hW] at hjk hjk1 ⊢ <;> assumption
  refine second_emptyPentagon_of_data S W hWinj hWmem hWccw ?_
  -- (4) every other point of `S` is cut off by one of four edge lines
  intro q hqS hqW
  have hqA : q ≠ A := by have h := hqW 0; simpa [hW] using h
  have hqR : q ≠ R := by have h := hqW 1; simpa [hW] using h
  have hqQ : q ≠ Q := by have h := hqW 2; simpa [hW] using h
  have hqB : q ≠ B := by have h := hqW 3; simpa [hW] using h
  have hqM : q ≠ M := by have h := hqW 4; simpa [hW] using h
  have hLMA : ∀ k : Fin 5, 0 ≤ orient M A (W k) := by
    have b0 : (0 : ℝ) ≤ orient M A A := by rw [orient_self_right]
    have b4 : (0 : ℝ) ≤ orient M A M := by rw [orient_self_left]
    intro k
    fin_cases k
    · simpa [hW] using b0
    · simpa [hW] using wR1.le
    · simpa [hW] using wQ1.le
    · simpa [hW] using cMAB.le
    · simpa [hW] using b4
  rcases le_or_gt (orient M A q) 0 with h1 | h1
  · exact ⟨M, A, nMA, hLMA, h1⟩
  have hLBM : ∀ k : Fin 5, 0 ≤ orient B M (W k) := by
    have b0 : (0 : ℝ) ≤ orient B M A := by rw [orient_cyc]; exact cMAB.le
    have b1 : (0 : ℝ) ≤ orient B M R := by rw [orient_cyc, orient_cyc]; exact o134.le
    have b2 : (0 : ℝ) ≤ orient B M Q := by rw [orient_cyc, orient_cyc]; exact o234.le
    have b3 : (0 : ℝ) ≤ orient B M B := by rw [orient_self_left]
    have b4 : (0 : ℝ) ≤ orient B M M := by rw [orient_self_right]
    intro k
    fin_cases k
    · simpa [hW] using b0
    · simpa [hW] using b1
    · simpa [hW] using b2
    · simpa [hW] using b3
    · simpa [hW] using b4
  rcases le_or_gt (orient B M q) 0 with h2 | h2
  · exact ⟨B, M, nBM, hLBM, h2⟩
  have hMBq : orient M B q < 0 := by linarith [orient_swap_left M B q]
  rcases lt_trichotomy (orient A B q) 0 with hab | hab | hab
  · -- `q` is a wedge point other than `Q` and `R`
    rcases lt_trichotomy (orient B Q q) 0 with hq | hq | hq
    · have hARq := hlast q hqS h1 hMBq hab hq hqR
      have hLAR : ∀ k : Fin 5, 0 ≤ orient A R (W k) := by
        have b0 : (0 : ℝ) ≤ orient A R A := by rw [orient_self_left]
        have b1 : (0 : ℝ) ≤ orient A R R := by rw [orient_self_right]
        intro k
        fin_cases k
        · simpa [hW] using b0
        · simpa [hW] using b1
        · simpa [hW] using o012.le
        · simpa [hW] using o013.le
        · simpa [hW] using o014.le
      exact ⟨A, R, nAR, hLAR, hARq.le⟩
    · exact absurd hq
        (hgp B hBS Q hQS q hqS (Ne.symm nQB) (Ne.symm hqB) (Ne.symm hqQ))
    · have hLQB : ∀ k : Fin 5, 0 ≤ orient Q B (W k) := by
        have b0 : (0 : ℝ) ≤ orient Q B A := by rw [orient_cyc, orient_cyc]; exact o023.le
        have b1 : (0 : ℝ) ≤ orient Q B R := by rw [orient_cyc, orient_cyc]; exact o123.le
        have b2 : (0 : ℝ) ≤ orient Q B Q := by rw [orient_self_left]
        have b3 : (0 : ℝ) ≤ orient Q B B := by rw [orient_self_right]
        intro k
        fin_cases k
        · simpa [hW] using b0
        · simpa [hW] using b1
        · simpa [hW] using b2
        · simpa [hW] using b3
        · simpa [hW] using o234.le
      exact ⟨Q, B, nQB, hLQB, by linarith [orient_swap_left B Q q]⟩
  · exact absurd hab (hgp A hAS B hBS q hqS nAB (Ne.symm hqA) (Ne.symm hqB))
  · exact absurd (hMuniq q hqS h1 hab h2) hqM

/-- Harborth's second-point case. All points of `S` in the wedge beyond edge `i` lie behind the
two neighbouring edge lines (no front point); `Q` is a wedge point closest to the edge line;
another wedge point `R` lies strictly right of `Q → P i` or strictly right of `P (i+1) → Q`.
Then `S` has an empty convex pentagon (`{P i, Q, R', P (i+1), M}` or `{P i, R', Q, P (i+1), M}`
for a closest such `R'`). -/
theorem second_case (S : Finset Point) (hgp : GeneralPosition S) (P : Fin 5 → Point)
    (hinj : Function.Injective P) (hPS : ∀ i, P i ∈ S)
    (hccw : ∀ i j : Fin 5, j ≠ i → j ≠ i + 1 → 0 < orient (P i) (P (i + 1)) (P j))
    (M : Point) (hMS : M ∈ S)
    (hM : M ∈ interior (convexHull ℝ ((Finset.univ.image P : Finset Point) : Set Point)))
    (huniq : ∀ q ∈ S, q ∈ interior (convexHull ℝ ((Finset.univ.image P : Finset Point) : Set Point))
      → q = M)
    (hcore : ∀ i, 0 < orient (P i) (P (i + 2)) M) (i : Fin 5)
    (hnofront : ∀ q ∈ S, 0 < orient M (P i) q → orient M (P (i + 1)) q < 0 →
      orient (P i) (P (i + 1)) q < 0 →
      orient (P (i - 1)) (P i) q < 0 ∧ orient (P (i + 1)) (P (i + 2)) q < 0)
    (Q : Point) (hQS : Q ∈ S)
    (hQA : 0 < orient M (P i) Q ∧ orient M (P (i + 1)) Q < 0 ∧ orient (P i) (P (i + 1)) Q < 0)
    (hQmin : ∀ q ∈ S, 0 < orient M (P i) q → orient M (P (i + 1)) q < 0 →
      orient (P i) (P (i + 1)) q < 0 → -orient (P i) (P (i + 1)) Q ≤ -orient (P i) (P (i + 1)) q)
    (R : Point) (hRS : R ∈ S)
    (hRA : 0 < orient M (P i) R ∧ orient M (P (i + 1)) R < 0 ∧ orient (P i) (P (i + 1)) R < 0)
    (hRQ : orient Q (P i) R < 0 ∨ orient (P (i + 1)) Q R < 0) :
    ∃ V : Finset Point, V.card = 5 ∧ EmptyConvexPolygon S V := by
  classical
  -- (A) the edge `i` of the pentagon sees `M` on its left
  have hEi : 0 < orient (P i) (P (i + 1)) M := orient_edge_pos_of_mem_interior P M hM hccw i
  have cMAB : 0 < orient M (P i) (P (i + 1)) := by rw [orient_cyc]; exact hEi
  -- (B) the only point of `S` strictly inside the triangle `M, P i, P (i+1)` is `M`
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
  -- (C) the closest-point condition in additive form
  have hQmin' : ∀ q ∈ S, 0 < orient M (P i) q → orient M (P (i + 1)) q < 0 →
      orient (P i) (P (i + 1)) q < 0 →
      orient (P i) (P (i + 1)) q ≤ orient (P i) (P (i + 1)) Q := by
    intro q hqS h1 h2 h3
    have h := hQmin q hqS h1 h2 h3
    linarith
  -- (D) the two cases
  rcases hRQ with hR | hR
  · -- `R` is right of `Q → P i`: take the angularly first such wedge point seen from `P (i+1)`
    set C : Finset Point := S.filter (fun z => 0 < orient M (P i) z ∧
      orient M (P (i + 1)) z < 0 ∧ orient (P i) (P (i + 1)) z < 0 ∧ orient Q (P i) z < 0)
      with hCdef
    have hCS : C ⊆ S := by rw [hCdef]; exact Finset.filter_subset _ _
    have hRC : R ∈ C := by
      rw [hCdef]
      exact Finset.mem_filter.mpr ⟨hRS, hRA.1, hRA.2.1, hRA.2.2, hR⟩
    have hmemC : ∀ z ∈ C, z ∈ S ∧ 0 < orient M (P i) z ∧ orient M (P (i + 1)) z < 0 ∧
        orient (P i) (P (i + 1)) z < 0 ∧ orient Q (P i) z < 0 := by
      intro z hz
      rw [hCdef] at hz
      obtain ⟨hzS, hz1, hz2, hz3, hz4⟩ := Finset.mem_filter.mp hz
      exact ⟨hzS, hz1, hz2, hz3, hz4⟩
    have hleft : ∀ z ∈ C, 0 < orient (P (i + 1)) Q z := by
      intro z hz
      obtain ⟨hzS, hz1, hz2, hz3, hz4⟩ := hmemC z hz
      exact second_key_right (P i) (P (i + 1)) Q z (hQmin' z hzS hz1 hz2 hz3) hz4
    obtain ⟨R', hR'C, hR'first⟩ :=
      second_angular_first S hgp (P (i + 1)) Q (hPS (i + 1)) C hCS ⟨R, hRC⟩ hleft
    obtain ⟨hR'S, hR'1, hR'2, hR'3, hR'4⟩ := hmemC R' hR'C
    refine second_pentagon_right S hgp M (P i) (P (i + 1)) Q R' hMS (hPS i) (hPS (i + 1)) hQS
      hR'S cMAB hQA.1 hQA.2.1 hQA.2.2 hR'1 hR'2 hR'3 hQmin' hR'4 ?_ hMuniqR
    intro z hzS hz1 hz2 hz3 hz4 hzR
    refine hR'first z ?_ hzR
    rw [hCdef]
    exact Finset.mem_filter.mpr ⟨hzS, hz1, hz2, hz3, hz4⟩
  · -- `R` is right of `P (i+1) → Q`: take the angularly last such wedge point seen from `P i`
    set C : Finset Point := S.filter (fun z => 0 < orient M (P i) z ∧
      orient M (P (i + 1)) z < 0 ∧ orient (P i) (P (i + 1)) z < 0 ∧
      orient (P (i + 1)) Q z < 0) with hCdef
    have hCS : C ⊆ S := by rw [hCdef]; exact Finset.filter_subset _ _
    have hRC : R ∈ C := by
      rw [hCdef]
      exact Finset.mem_filter.mpr ⟨hRS, hRA.1, hRA.2.1, hRA.2.2, hR⟩
    have hmemC : ∀ z ∈ C, z ∈ S ∧ 0 < orient M (P i) z ∧ orient M (P (i + 1)) z < 0 ∧
        orient (P i) (P (i + 1)) z < 0 ∧ orient (P (i + 1)) Q z < 0 := by
      intro z hz
      rw [hCdef] at hz
      obtain ⟨hzS, hz1, hz2, hz3, hz4⟩ := Finset.mem_filter.mp hz
      exact ⟨hzS, hz1, hz2, hz3, hz4⟩
    have hright : ∀ z ∈ C, orient (P i) Q z < 0 := by
      intro z hz
      obtain ⟨hzS, hz1, hz2, hz3, hz4⟩ := hmemC z hz
      exact second_key_left (P i) (P (i + 1)) Q z (hQmin' z hzS hz1 hz2 hz3) hz4
    obtain ⟨R', hR'C, hR'last⟩ :=
      second_angular_last S hgp (P i) Q (hPS i) C hCS ⟨R, hRC⟩ hright
    obtain ⟨hR'S, hR'1, hR'2, hR'3, hR'4⟩ := hmemC R' hR'C
    refine second_pentagon_left S hgp M (P i) (P (i + 1)) Q R' hMS (hPS i) (hPS (i + 1)) hQS
      hR'S cMAB hQA.1 hQA.2.1 hQA.2.2 hR'1 hR'2 hR'3 hQmin' hR'4 ?_ hMuniqR
    intro z hzS hz1 hz2 hz3 hz4 hzR
    refine hR'last z ?_ hzR
    rw [hCdef]
    exact Finset.mem_filter.mpr ⟨hzS, hz1, hz2, hz3, hz4⟩

end Horton
