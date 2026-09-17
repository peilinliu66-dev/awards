/-
Reused under MIT from CollinYuanjieRen/awards, commit
b8bb4f7803f921a7970abc880291ad9372111360, JSP-000198 small-k submission.
Original module: EmptyPentagon/Final.lean
Source/permission records: EmptyPentagon/UPSTREAM.md and LICENSE.
Local target: Lean 4.33.1 / pinned Mathlib 0df444a36.
-/
import EmptyPentagon.Definitions
import EmptyPentagon.Certificate
import EmptyPentagon.Interp
import EmptyPentagon.TriangleInterior
import EmptyPentagon.Pentagon
import EmptyPentagon.Signs

noncomputable section
open Classical
namespace Horton

/-- Membership in the region `B j`: beyond edge `j`, between the rays from `M` through `P j`
and `P (j+1)`, and behind the two neighbouring edge lines. -/
def InB (P : Fin 5 → Point) (M : Point) (j : Fin 5) (q : Point) : Prop :=
  0 < orient M (P j) q ∧ orient M (P (j + 1)) q < 0 ∧ orient (P j) (P (j + 1)) q < 0 ∧
    orient (P (j - 1)) (P j) q < 0 ∧ orient (P (j + 1)) (P (j + 2)) q < 0

/-- Indexed general position for a five-point family of `S` with pairwise distinct entries. -/
theorem indexedGP_vec5 (S : Finset Point) (hgp : GeneralPosition S) (a b c d e : Point)
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hd : d ∈ S) (he : e ∈ S) (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hae : a ≠ e) (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hcd : c ≠ d)
    (hce : c ≠ e) (hde : d ≠ e) : IndexedGP ![a, b, c, d, e] := by
  have hinj : Function.Injective ![a, b, c, d, e] := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;>
      simp [hab, hac, had, hae, hbc, hbd, hbe, hcd, hce, hde, hab.symm, hac.symm, had.symm,
        hae.symm, hbc.symm, hbd.symm, hbe.symm, hcd.symm, hce.symm, hde.symm] at hxy ⊢
  have hmem : ∀ k : Fin 5, ![a, b, c, d, e] k ∈ S := by
    intro k
    fin_cases k <;> simp [ha, hb, hc, hd, he]
  exact fun x y z hxy hxz hyz =>
    hgp _ (hmem x) _ (hmem y) _ (hmem z) (hinj.ne hxy) (hinj.ne hxz) (hinj.ne hyz)

/-- A point of the region `B j` is none of the five pentagon vertices. -/
theorem ne_vertex_of_inB (P : Fin 5 → Point)
    (hccw : ∀ a b : Fin 5, b ≠ a → b ≠ a + 1 → 0 < orient (P a) (P (a + 1)) (P b))
    (M : Point) (j : Fin 5) (q : Point) (h : InB P M j q) (k : Fin 5) : q ≠ P k := by
  have e1 : ∀ a : Fin 5, a - 1 + 1 = a := by decide
  have e2 : ∀ a : Fin 5, a + 1 + 1 = a + 2 := by decide
  have e3 : ∀ a : Fin 5, a - 1 ≠ a + 1 := by decide
  have e4 : ∀ a : Fin 5, a - 1 ≠ a + 1 + 1 := by decide
  have e5 : ∀ a : Fin 5, a ≠ a + 1 := by decide
  have e6 : ∀ a : Fin 5, a ≠ a + 1 + 1 := by decide
  intro hq
  by_cases hk : k = j - 1 ∨ k = j
  · have h5 := h.2.2.2.2
    rw [hq] at h5
    have hne1 : k ≠ j + 1 := by
      rcases hk with h' | h'
      · rw [h']; exact e3 j
      · rw [h']; exact e5 j
    have hne2 : k ≠ j + 1 + 1 := by
      rcases hk with h' | h'
      · rw [h']; exact e4 j
      · rw [h']; exact e6 j
    have hpos := hccw (j + 1) k hne1 hne2
    rw [e2 j] at hpos
    linarith
  · have hk' := not_or.mp hk
    have h4 := h.2.2.2.1
    rw [hq] at h4
    have hpos := hccw (j - 1) k hk'.1 (by rw [e1 j]; exact hk'.2)
    rw [e1 j] at hpos
    linarith

/-- Five points `M, U, V, A, B, C` with `A, B, C` beyond the edge `U → V`, seen from `M` in the
order "before `U`", "between `U` and `V`", "past `V`", and with `A` strictly left of `B → C`,
give the counterclockwise pentagon `V, U, A, B, C`; if every other point of `S` is strictly left
of `U → V`, that pentagon is an empty convex polygon of `S`. -/
theorem empty_pentagon_of_wedge_triple (S : Finset Point) (hgp : GeneralPosition S)
    (M U V A B C : Point) (hMS : M ∈ S) (hUS : U ∈ S) (hVS : V ∈ S) (hAS : A ∈ S) (hBS : B ∈ S)
    (hCS : C ∈ S) (h1 : 0 < orient U V M) (h2 : orient M U A < 0) (h3 : orient U V A < 0)
    (h4 : 0 < orient M U B) (h5 : orient M V B < 0) (h6 : orient U V B < 0)
    (h7 : 0 < orient M V C) (h8 : orient U V C < 0) (h9 : 0 < orient B C A)
    (hrest : ∀ q ∈ S, q ≠ U → q ≠ V → q ≠ A → q ≠ B → q ≠ C → 0 < orient U V q) :
    ∃ W : Finset Point, W.card = 5 ∧ EmptyConvexPolygon S W := by
  classical
  -- (D) the six points are pairwise distinct
  have nMU : M ≠ U := by intro h; rw [h, orient_self_left] at h1; exact lt_irrefl _ h1
  have nMV : M ≠ V := by intro h; rw [h, orient_self_right] at h1; exact lt_irrefl _ h1
  have nUV : U ≠ V := by intro h; rw [h, orient_self_pair] at h1; exact lt_irrefl _ h1
  have nMA : M ≠ A := by intro h; rw [← h, orient_self_left] at h2; exact lt_irrefl _ h2
  have nUA : U ≠ A := by intro h; rw [← h, orient_self_right] at h2; exact lt_irrefl _ h2
  have nVA : V ≠ A := by intro h; rw [← h, orient_self_right] at h3; exact lt_irrefl _ h3
  have nMB : M ≠ B := by intro h; rw [← h, orient_self_left] at h4; exact lt_irrefl _ h4
  have nUB : U ≠ B := by intro h; rw [← h, orient_self_right] at h4; exact lt_irrefl _ h4
  have nVB : V ≠ B := by intro h; rw [← h, orient_self_right] at h5; exact lt_irrefl _ h5
  have nMC : M ≠ C := by intro h; rw [← h, orient_self_left] at h7; exact lt_irrefl _ h7
  have nVC : V ≠ C := by intro h; rw [← h, orient_self_right] at h7; exact lt_irrefl _ h7
  have nUC : U ≠ C := by intro h; rw [← h, orient_self_left] at h8; exact lt_irrefl _ h8
  have nAB : A ≠ B := by intro h; rw [h] at h2; linarith
  have nAC : A ≠ C := by intro h; rw [h, orient_self_right] at h9; exact lt_irrefl _ h9
  have nBC : B ≠ C := by intro h; rw [h, orient_self_pair] at h9; exact lt_irrefl _ h9
  -- (R) two rotations of the given literals
  have mUV : 0 < orient M U V := by
    linarith [orient_cyc U V M, orient_cyc V M U]
  have hABC : 0 < orient A B C := by
    linarith [orient_cyc B C A, orient_cyc C A B]
  -- (K1) the subfamily `M, U, V, A, B`
  set p1 : Fin 5 → Point := ![M, U, V, A, B] with hp1
  have g1 : IndexedGP p1 :=
    indexedGP_vec5 S hgp M U V A B hMS hUS hVS hAS hBS nMU nMV nMA nMB nUV nUA nUB nVA nVB nAB
  have hUAB : 0 < orient U A B := by
    have h := sign_imp_pos [(0, 1, 2, true), (0, 1, 3, false), (0, 1, 4, true), (1, 2, 3, false),
      (1, 2, 4, false)] 1 3 4 (by decide +kernel) p1 g1
      (litHolds_cons (litHolds_pos p1 0 1 2 (by simpa [hp1] using mUV))
        (litHolds_cons (litHolds_neg p1 0 1 3 (by simpa [hp1] using h2))
          (litHolds_cons (litHolds_pos p1 0 1 4 (by simpa [hp1] using h4))
            (litHolds_cons (litHolds_neg p1 1 2 3 (by simpa [hp1] using h3))
              (litHolds_cons (litHolds_neg p1 1 2 4 (by simpa [hp1] using h6))
                (litHolds_nil p1))))))
    simpa [hp1] using h
  have hMAB : 0 < orient M A B := by
    have h := sign_imp_pos [(0, 1, 2, true), (0, 1, 3, false), (0, 1, 4, true), (1, 2, 3, false),
      (1, 2, 4, false)] 0 3 4 (by decide +kernel) p1 g1
      (litHolds_cons (litHolds_pos p1 0 1 2 (by simpa [hp1] using mUV))
        (litHolds_cons (litHolds_neg p1 0 1 3 (by simpa [hp1] using h2))
          (litHolds_cons (litHolds_pos p1 0 1 4 (by simpa [hp1] using h4))
            (litHolds_cons (litHolds_neg p1 1 2 3 (by simpa [hp1] using h3))
              (litHolds_cons (litHolds_neg p1 1 2 4 (by simpa [hp1] using h6))
                (litHolds_nil p1))))))
    simpa [hp1] using h
  -- (K2) the subfamily `M, U, V, A, C`
  set p2 : Fin 5 → Point := ![M, U, V, A, C] with hp2
  have g2 : IndexedGP p2 :=
    indexedGP_vec5 S hgp M U V A C hMS hUS hVS hAS hCS nMU nMV nMA nMC nUV nUA nUC nVA nVC nAC
  have hMUC : 0 < orient M U C := by
    have h := sign_imp_pos [(0, 1, 2, true), (0, 2, 4, true), (1, 2, 4, false)] 0 1 4
      (by decide +kernel) p2 g2
      (litHolds_cons (litHolds_pos p2 0 1 2 (by simpa [hp2] using mUV))
        (litHolds_cons (litHolds_pos p2 0 2 4 (by simpa [hp2] using h7))
          (litHolds_cons (litHolds_neg p2 1 2 4 (by simpa [hp2] using h8))
            (litHolds_nil p2))))
    simpa [hp2] using h
  have hUAC : 0 < orient U A C := by
    have h := sign_imp_pos [(0, 1, 2, true), (0, 1, 3, false), (0, 2, 4, true), (1, 2, 3, false),
      (1, 2, 4, false)] 1 3 4 (by decide +kernel) p2 g2
      (litHolds_cons (litHolds_pos p2 0 1 2 (by simpa [hp2] using mUV))
        (litHolds_cons (litHolds_neg p2 0 1 3 (by simpa [hp2] using h2))
          (litHolds_cons (litHolds_pos p2 0 2 4 (by simpa [hp2] using h7))
            (litHolds_cons (litHolds_neg p2 1 2 3 (by simpa [hp2] using h3))
              (litHolds_cons (litHolds_neg p2 1 2 4 (by simpa [hp2] using h8))
                (litHolds_nil p2))))))
    simpa [hp2] using h
  have hMAC : 0 < orient M A C := by
    have h := sign_imp_pos [(0, 1, 2, true), (0, 1, 3, false), (0, 2, 4, true), (1, 2, 3, false),
      (1, 2, 4, false)] 0 3 4 (by decide +kernel) p2 g2
      (litHolds_cons (litHolds_pos p2 0 1 2 (by simpa [hp2] using mUV))
        (litHolds_cons (litHolds_neg p2 0 1 3 (by simpa [hp2] using h2))
          (litHolds_cons (litHolds_pos p2 0 2 4 (by simpa [hp2] using h7))
            (litHolds_cons (litHolds_neg p2 1 2 3 (by simpa [hp2] using h3))
              (litHolds_cons (litHolds_neg p2 1 2 4 (by simpa [hp2] using h8))
                (litHolds_nil p2))))))
    simpa [hp2] using h
  have hVAC : 0 < orient V A C := by
    have h := sign_imp_pos [(0, 1, 2, true), (0, 1, 3, false), (0, 2, 4, true), (1, 2, 3, false),
      (1, 2, 4, false)] 2 3 4 (by decide +kernel) p2 g2
      (litHolds_cons (litHolds_pos p2 0 1 2 (by simpa [hp2] using mUV))
        (litHolds_cons (litHolds_neg p2 0 1 3 (by simpa [hp2] using h2))
          (litHolds_cons (litHolds_pos p2 0 2 4 (by simpa [hp2] using h7))
            (litHolds_cons (litHolds_neg p2 1 2 3 (by simpa [hp2] using h3))
              (litHolds_cons (litHolds_neg p2 1 2 4 (by simpa [hp2] using h8))
                (litHolds_nil p2))))))
    simpa [hp2] using h
  -- (K3) the subfamily `M, U, V, B, C`
  set p3 : Fin 5 → Point := ![M, U, V, B, C] with hp3
  have g3 : IndexedGP p3 :=
    indexedGP_vec5 S hgp M U V B C hMS hUS hVS hBS hCS nMU nMV nMB nMC nUV nUB nUC nVB nVC nBC
  have hMBC : 0 < orient M B C := by
    have h := sign_imp_pos [(0, 1, 2, true), (0, 2, 3, false), (0, 2, 4, true), (1, 2, 3, false),
      (1, 2, 4, false)] 0 3 4 (by decide +kernel) p3 g3
      (litHolds_cons (litHolds_pos p3 0 1 2 (by simpa [hp3] using mUV))
        (litHolds_cons (litHolds_neg p3 0 2 3 (by simpa [hp3] using h5))
          (litHolds_cons (litHolds_pos p3 0 2 4 (by simpa [hp3] using h7))
            (litHolds_cons (litHolds_neg p3 1 2 3 (by simpa [hp3] using h6))
              (litHolds_cons (litHolds_neg p3 1 2 4 (by simpa [hp3] using h8))
                (litHolds_nil p3))))))
    simpa [hp3] using h
  have hVBC : 0 < orient V B C := by
    have h := sign_imp_pos [(0, 1, 2, true), (0, 2, 3, false), (0, 2, 4, true), (1, 2, 3, false),
      (1, 2, 4, false)] 2 3 4 (by decide +kernel) p3 g3
      (litHolds_cons (litHolds_pos p3 0 1 2 (by simpa [hp3] using mUV))
        (litHolds_cons (litHolds_neg p3 0 2 3 (by simpa [hp3] using h5))
          (litHolds_cons (litHolds_pos p3 0 2 4 (by simpa [hp3] using h7))
            (litHolds_cons (litHolds_neg p3 1 2 3 (by simpa [hp3] using h6))
              (litHolds_cons (litHolds_neg p3 1 2 4 (by simpa [hp3] using h8))
                (litHolds_nil p3))))))
    simpa [hp3] using h
  -- (K4) the subfamily `M, V, A, B, C`
  set p4 : Fin 5 → Point := ![M, V, A, B, C] with hp4
  have g4 : IndexedGP p4 :=
    indexedGP_vec5 S hgp M V A B C hMS hVS hAS hBS hCS nMV nMA nMB nMC nVA nVB nVC nAB nAC nBC
  have hVAB : 0 < orient V A B := by
    have h := sign_imp_pos [(0, 1, 3, false), (0, 2, 3, true), (0, 3, 4, true), (1, 3, 4, true),
      (2, 3, 4, true)] 1 2 3 (by decide +kernel) p4 g4
      (litHolds_cons (litHolds_neg p4 0 1 3 (by simpa [hp4] using h5))
        (litHolds_cons (litHolds_pos p4 0 2 3 (by simpa [hp4] using hMAB))
          (litHolds_cons (litHolds_pos p4 0 3 4 (by simpa [hp4] using hMBC))
            (litHolds_cons (litHolds_pos p4 1 3 4 (by simpa [hp4] using hVBC))
              (litHolds_cons (litHolds_pos p4 2 3 4 (by simpa [hp4] using hABC))
                (litHolds_nil p4))))))
    simpa [hp4] using h
  -- (K5) the subfamily `M, U, A, B, C`
  set p5 : Fin 5 → Point := ![M, U, A, B, C] with hp5
  have g5 : IndexedGP p5 :=
    indexedGP_vec5 S hgp M U A B C hMS hUS hAS hBS hCS nMU nMA nMB nMC nUA nUB nUC nAB nAC nBC
  have hUBC : 0 < orient U B C := by
    have h := sign_imp_pos [(0, 1, 4, true), (0, 2, 4, true), (0, 3, 4, true), (1, 2, 4, true),
      (2, 3, 4, true)] 1 3 4 (by decide +kernel) p5 g5
      (litHolds_cons (litHolds_pos p5 0 1 4 (by simpa [hp5] using hMUC))
        (litHolds_cons (litHolds_pos p5 0 2 4 (by simpa [hp5] using hMAC))
          (litHolds_cons (litHolds_pos p5 0 3 4 (by simpa [hp5] using hMBC))
            (litHolds_cons (litHolds_pos p5 1 2 4 (by simpa [hp5] using hUAC))
              (litHolds_cons (litHolds_pos p5 2 3 4 (by simpa [hp5] using hABC))
                (litHolds_nil p5))))))
    simpa [hp5] using h
  -- (W) the counterclockwise pentagon `V, U, A, B, C`
  set W : Fin 5 → Point := ![V, U, A, B, C] with hW
  have hWinj : Function.Injective W := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;>
      simp [hW, nUV, nUA, nUB, nUC, nVA, nVB, nVC, nAB, nAC, nBC, nUV.symm, nUA.symm, nUB.symm,
        nUC.symm, nVA.symm, nVB.symm, nVC.symm, nAB.symm, nAC.symm, nBC.symm] at hxy ⊢
  have hWS : ∀ k : Fin 5, W k ∈ S := by
    intro k
    fin_cases k <;> simp [hW, hUS, hVS, hAS, hBS, hCS]
  have e02 : 0 < orient V U A := by linarith [orient_swap_left U V A]
  have e03 : 0 < orient V U B := by linarith [orient_swap_left U V B]
  have e04 : 0 < orient V U C := by linarith [orient_swap_left U V C]
  have hWccw : ∀ k j : Fin 5, j ≠ k → j ≠ k + 1 → 0 < orient (W k) (W (k + 1)) (W j) := by
    have e10 : 0 < orient U A V := by linarith [orient_cyc V U A]
    have e13 : 0 < orient U A B := hUAB
    have e14 : 0 < orient U A C := hUAC
    have e20 : 0 < orient A B V := by linarith [orient_cyc V A B]
    have e21 : 0 < orient A B U := by linarith [orient_cyc U A B]
    have e24 : 0 < orient A B C := hABC
    have e30 : 0 < orient B C V := by linarith [orient_cyc V B C]
    have e31 : 0 < orient B C U := by linarith [orient_cyc U B C]
    have e32 : 0 < orient B C A := h9
    have e41 : 0 < orient C V U := by linarith [orient_cyc C V U]
    have e42 : 0 < orient C V A := by linarith [orient_cyc C V A]
    have e43 : 0 < orient C V B := by linarith [orient_cyc V B C, orient_cyc B C V]
    intro k j hjk hjk1
    fin_cases k <;> fin_cases j <;> simp [hW] at hjk hjk1 ⊢ <;> assumption
  refine ⟨Finset.univ.image W, ?_, emptyConvexPolygon_of_ccw S W hWinj hWS hWccw ?_⟩
  · rw [Finset.card_image_of_injective _ hWinj]; simp
  · intro q hqS hqW
    have hqne : ∀ k : Fin 5, q ≠ W k := by
      intro k h
      exact hqW (by rw [h]; exact Finset.mem_image_of_mem W (Finset.mem_univ k))
    have hqV : q ≠ V := by have h := hqne 0; simpa [hW] using h
    have hqU : q ≠ U := by have h := hqne 1; simpa [hW] using h
    have hqA : q ≠ A := by have h := hqne 2; simpa [hW] using h
    have hqB : q ≠ B := by have h := hqne 3; simpa [hW] using h
    have hqC : q ≠ C := by have h := hqne 4; simpa [hW] using h
    refine not_mem_interior_convexHull_of_halfplane _ V U q (Ne.symm nUV) ?_ ?_
    · intro x hx
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hx
      fin_cases k
      · simp [hW, orient_self_left]
      · simp [hW, orient_self_right]
      · simpa [hW] using e02.le
      · simpa [hW] using e03.le
      · simpa [hW] using e04.le
    · have hq := hrest q hqS hqU hqV hqA hqB hqC
      linarith [orient_swap_left U V q]

/-- Harborth's final case: the four points of `S` outside the pentagon lie one each in the four
consecutive regions `B (i-1), B i, B (i+1), B (i+2)`. Then `{Q (i-1), Q i, Q (i+1), P i, P (i+1)}`
(if `Q (i-1)` is strictly left of `Q i → Q (i+1)`) or `{Q i, Q (i+1), Q (i+2), P (i+1), P (i+2)}`
(otherwise) is an empty convex pentagon. -/
theorem final_case (S : Finset Point) (hgp : GeneralPosition S) (P : Fin 5 → Point)
    (hinj : Function.Injective P) (hPS : ∀ i, P i ∈ S)
    (hccw : ∀ i j : Fin 5, j ≠ i → j ≠ i + 1 → 0 < orient (P i) (P (i + 1)) (P j))
    (M : Point) (hMS : M ∈ S)
    (hM : M ∈ interior (convexHull ℝ ((Finset.univ.image P : Finset Point) : Set Point)))
    (_hcore : ∀ i, 0 < orient (P i) (P (i + 2)) M) (i : Fin 5)
    (Qm Q0 Q1 Q2 : Point)
    (hQm : InB P M (i - 1) Qm) (hQ0 : InB P M i Q0) (hQ1 : InB P M (i + 1) Q1)
    (hQ2 : InB P M (i + 2) Q2)
    (hS : ∀ q, q ∈ S ↔ (∃ j, q = P j) ∨ q = M ∨ q = Qm ∨ q = Q0 ∨ q = Q1 ∨ q = Q2) :
    ∃ V : Finset Point, V.card = 5 ∧ EmptyConvexPolygon S V := by
  classical
  -- (A) index arithmetic in `Fin 5`
  have f1 : ∀ a : Fin 5, a - 1 = a + 4 := by decide
  have f2 : ∀ a : Fin 5, a - 1 + 1 = a := by decide
  have f3 : ∀ a : Fin 5, a - 1 - 1 = a + 3 := by decide
  have f4 : ∀ a : Fin 5, a - 1 + 2 = a + 1 := by decide
  have f5 : ∀ a : Fin 5, a + 1 + 1 = a + 2 := by decide
  have f6 : ∀ a : Fin 5, a + 1 - 1 = a := by decide
  have f7 : ∀ a : Fin 5, a + 1 + 2 = a + 3 := by decide
  have f8 : ∀ a : Fin 5, a + 2 + 1 = a + 3 := by decide
  have f9 : ∀ a : Fin 5, a + 2 - 1 = a + 1 := by decide
  have f10 : ∀ a : Fin 5, a + 2 + 2 = a + 4 := by decide
  have f11 : ∀ a : Fin 5, a + 3 + 1 = a + 4 := by decide
  have d01 : ∀ a : Fin 5, a ≠ a + 1 := by decide
  have d02 : ∀ a : Fin 5, a ≠ a + 2 := by decide
  have d03 : ∀ a : Fin 5, a ≠ a + 3 := by decide
  have d04 : ∀ a : Fin 5, a ≠ a + 4 := by decide
  have d12 : ∀ a : Fin 5, a + 1 ≠ a + 2 := by decide
  have d13 : ∀ a : Fin 5, a + 1 ≠ a + 3 := by decide
  have d14 : ∀ a : Fin 5, a + 1 ≠ a + 4 := by decide
  have d23 : ∀ a : Fin 5, a + 2 ≠ a + 3 := by decide
  have d24 : ∀ a : Fin 5, a + 2 ≠ a + 4 := by decide
  have d34 : ∀ a : Fin 5, a + 3 ≠ a + 4 := by decide
  -- (B) `M` is strictly left of every edge and is not a vertex
  have hE := orient_edge_pos_of_mem_interior P M hM hccw
  have hEi : 0 < orient (P i) (P (i + 1)) M := hE i
  have hEi1 : 0 < orient (P (i + 1)) (P (i + 2)) M := by have h := hE (i + 1); rwa [f5 i] at h
  have hEi3 : 0 < orient (P (i + 3)) (P (i + 4)) M := by have h := hE (i + 3); rwa [f11 i] at h
  have mA : 0 < orient M (P i) (P (i + 1)) := by
    linarith [orient_cyc (P i) (P (i + 1)) M, orient_cyc (P (i + 1)) M (P i)]
  have mB : 0 < orient M (P (i + 1)) (P (i + 2)) := by
    linarith [orient_cyc (P (i + 1)) (P (i + 2)) M, orient_cyc (P (i + 2)) M (P (i + 1))]
  have mC : 0 < orient M (P (i + 3)) (P (i + 4)) := by
    linarith [orient_cyc (P (i + 3)) (P (i + 4)) M, orient_cyc (P (i + 4)) M (P (i + 3))]
  have hMP : ∀ k, M ≠ P k := by
    intro k h
    have h' := hE k
    rw [h, orient_self_left] at h'
    exact lt_irrefl _ h'
  -- (C) the region literals of the four outer points
  have qm1 : 0 < orient M (P (i + 4)) Qm := by have h := hQm.1; rwa [f1 i] at h
  have qm2 : orient M (P i) Qm < 0 := by have h := hQm.2.1; rwa [f2 i] at h
  have qm4 : orient (P (i + 3)) (P (i + 4)) Qm < 0 := by
    have h := hQm.2.2.2.1; rwa [f3 i, f1 i] at h
  have qm5 : orient (P i) (P (i + 1)) Qm < 0 := by have h := hQm.2.2.2.2; rwa [f2 i, f4 i] at h
  have q01 : 0 < orient M (P i) Q0 := hQ0.1
  have q02 : orient M (P (i + 1)) Q0 < 0 := hQ0.2.1
  have q03 : orient (P i) (P (i + 1)) Q0 < 0 := hQ0.2.2.1
  have q05 : orient (P (i + 1)) (P (i + 2)) Q0 < 0 := hQ0.2.2.2.2
  have q11 : 0 < orient M (P (i + 1)) Q1 := hQ1.1
  have q12 : orient M (P (i + 2)) Q1 < 0 := by have h := hQ1.2.1; rwa [f5 i] at h
  have q13 : orient (P (i + 1)) (P (i + 2)) Q1 < 0 := by have h := hQ1.2.2.1; rwa [f5 i] at h
  have q14 : orient (P i) (P (i + 1)) Q1 < 0 := by have h := hQ1.2.2.2.1; rwa [f6 i] at h
  have q21 : 0 < orient M (P (i + 2)) Q2 := hQ2.1
  have q22 : orient M (P (i + 3)) Q2 < 0 := by have h := hQ2.2.1; rwa [f8 i] at h
  have q24 : orient (P (i + 1)) (P (i + 2)) Q2 < 0 := by have h := hQ2.2.2.2.1; rwa [f9 i] at h
  have q25 : orient (P (i + 3)) (P (i + 4)) Q2 < 0 := by
    have h := hQ2.2.2.2.2; rwa [f8 i, f10 i] at h
  -- (D) membership and distinctness of the ten points
  have hQmS : Qm ∈ S := (hS Qm).2 (Or.inr (Or.inr (Or.inl rfl)))
  have hQ0S : Q0 ∈ S := (hS Q0).2 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have hQ1S : Q1 ∈ S := (hS Q1).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have hQ2S : Q2 ∈ S := (hS Q2).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  have nQmP : ∀ k, Qm ≠ P k := ne_vertex_of_inB P hccw M (i - 1) Qm hQm
  have nQ0P : ∀ k, Q0 ≠ P k := ne_vertex_of_inB P hccw M i Q0 hQ0
  have nQ1P : ∀ k, Q1 ≠ P k := ne_vertex_of_inB P hccw M (i + 1) Q1 hQ1
  have nQ2P : ∀ k, Q2 ≠ P k := ne_vertex_of_inB P hccw M (i + 2) Q2 hQ2
  have nMQm : M ≠ Qm := by intro h; rw [← h, orient_self_left] at qm1; exact lt_irrefl _ qm1
  have nMQ0 : M ≠ Q0 := by intro h; rw [← h, orient_self_left] at q01; exact lt_irrefl _ q01
  have nMQ1 : M ≠ Q1 := by intro h; rw [← h, orient_self_left] at q11; exact lt_irrefl _ q11
  have nMQ2 : M ≠ Q2 := by intro h; rw [← h, orient_self_left] at q21; exact lt_irrefl _ q21
  have nQmQ0 : Qm ≠ Q0 := by intro h; rw [h] at qm2; linarith
  have nQ0Q1 : Q0 ≠ Q1 := by intro h; rw [h] at q02; linarith
  have nQ1Q2 : Q1 ≠ Q2 := by intro h; rw [h] at q12; linarith
  -- (E) the three sign facts needed in both cases
  set r1 : Fin 5 → Point := ![M, P i, P (i + 1), Qm, P (i + 2)] with hr1
  have gr1 : IndexedGP r1 :=
    indexedGP_vec5 S hgp M (P i) (P (i + 1)) Qm (P (i + 2)) hMS (hPS i) (hPS (i + 1)) hQmS
      (hPS (i + 2)) (hMP i) (hMP (i + 1)) nMQm (hMP (i + 2)) (hinj.ne (d01 i))
      (Ne.symm (nQmP i)) (hinj.ne (d02 i)) (Ne.symm (nQmP (i + 1))) (hinj.ne (d12 i))
      (nQmP (i + 2))
  have o1 : orient M (P (i + 1)) Qm < 0 := by
    have h := sign_imp_neg [(0, 1, 2, true), (0, 1, 3, false), (1, 2, 3, false)] 0 2 3
      (by decide +kernel) r1 gr1
      (litHolds_cons (litHolds_pos r1 0 1 2 (by simpa [hr1] using mA))
        (litHolds_cons (litHolds_neg r1 0 1 3 (by simpa [hr1] using qm2))
          (litHolds_cons (litHolds_neg r1 1 2 3 (by simpa [hr1] using qm5))
            (litHolds_nil r1))))
    simpa [hr1] using h
  set r2 : Fin 5 → Point := ![M, P (i + 1), P (i + 2), P (i + 3), Q2] with hr2
  have gr2 : IndexedGP r2 :=
    indexedGP_vec5 S hgp M (P (i + 1)) (P (i + 2)) (P (i + 3)) Q2 hMS (hPS (i + 1)) (hPS (i + 2))
      (hPS (i + 3)) hQ2S (hMP (i + 1)) (hMP (i + 2)) (hMP (i + 3)) nMQ2 (hinj.ne (d12 i))
      (hinj.ne (d13 i)) (Ne.symm (nQ2P (i + 1))) (hinj.ne (d23 i)) (Ne.symm (nQ2P (i + 2)))
      (Ne.symm (nQ2P (i + 3)))
  have o2 : 0 < orient M (P (i + 1)) Q2 := by
    have h := sign_imp_pos [(0, 1, 2, true), (0, 2, 4, true), (1, 2, 4, false)] 0 1 4
      (by decide +kernel) r2 gr2
      (litHolds_cons (litHolds_pos r2 0 1 2 (by simpa [hr2] using mB))
        (litHolds_cons (litHolds_pos r2 0 2 4 (by simpa [hr2] using q21))
          (litHolds_cons (litHolds_neg r2 1 2 4 (by simpa [hr2] using q24))
            (litHolds_nil r2))))
    simpa [hr2] using h
  have nQmQ1 : Qm ≠ Q1 := by intro h; rw [h] at o1; linarith
  have nQmQ2 : Qm ≠ Q2 := by intro h; rw [h] at o1; linarith
  have nQ0Q2 : Q0 ≠ Q2 := by intro h; rw [h] at q02; linarith
  set r3 : Fin 5 → Point := ![M, P (i + 3), P (i + 4), Qm, Q2] with hr3
  have gr3 : IndexedGP r3 :=
    indexedGP_vec5 S hgp M (P (i + 3)) (P (i + 4)) Qm Q2 hMS (hPS (i + 3)) (hPS (i + 4)) hQmS
      hQ2S (hMP (i + 3)) (hMP (i + 4)) nMQm nMQ2 (hinj.ne (d34 i)) (Ne.symm (nQmP (i + 3)))
      (Ne.symm (nQ2P (i + 3))) (Ne.symm (nQmP (i + 4))) (Ne.symm (nQ2P (i + 4))) nQmQ2
  have o3 : orient M Qm Q2 < 0 := by
    have h := sign_imp_neg [(0, 1, 2, true), (0, 1, 4, false), (0, 2, 3, true), (1, 2, 3, false),
      (1, 2, 4, false)] 0 3 4 (by decide +kernel) r3 gr3
      (litHolds_cons (litHolds_pos r3 0 1 2 (by simpa [hr3] using mC))
        (litHolds_cons (litHolds_neg r3 0 1 4 (by simpa [hr3] using q22))
          (litHolds_cons (litHolds_pos r3 0 2 3 (by simpa [hr3] using qm1))
            (litHolds_cons (litHolds_neg r3 1 2 3 (by simpa [hr3] using qm4))
              (litHolds_cons (litHolds_neg r3 1 2 4 (by simpa [hr3] using q25))
                (litHolds_nil r3))))))
    simpa [hr3] using h
  -- (F) the case distinction on the side of `Q0 → Q1` carrying `Qm`
  have hnz : orient Q0 Q1 Qm ≠ 0 :=
    hgp Q0 hQ0S Q1 hQ1S Qm hQmS nQ0Q1 (Ne.symm nQmQ0) (Ne.symm nQmQ1)
  rcases lt_or_gt_of_ne hnz with hcase | hcase
  · -- CASE B: the pentagon `P (i+2), P (i+1), Q0, Q1, Q2`
    set s1 : Fin 5 → Point := ![M, P i, P (i + 1), Qm, Q1] with hs1
    have gs1 : IndexedGP s1 :=
      indexedGP_vec5 S hgp M (P i) (P (i + 1)) Qm Q1 hMS (hPS i) (hPS (i + 1)) hQmS hQ1S
        (hMP i) (hMP (i + 1)) nMQm nMQ1 (hinj.ne (d01 i)) (Ne.symm (nQmP i)) (Ne.symm (nQ1P i))
        (Ne.symm (nQmP (i + 1))) (Ne.symm (nQ1P (i + 1))) nQmQ1
    have o5 : 0 < orient M Qm Q1 := by
      have h := sign_imp_pos [(0, 1, 2, true), (0, 1, 3, false), (0, 2, 4, true), (1, 2, 3, false),
        (1, 2, 4, false)] 0 3 4 (by decide +kernel) s1 gs1
        (litHolds_cons (litHolds_pos s1 0 1 2 (by simpa [hs1] using mA))
          (litHolds_cons (litHolds_neg s1 0 1 3 (by simpa [hs1] using qm2))
            (litHolds_cons (litHolds_pos s1 0 2 4 (by simpa [hs1] using q11))
              (litHolds_cons (litHolds_neg s1 1 2 3 (by simpa [hs1] using qm5))
                (litHolds_cons (litHolds_neg s1 1 2 4 (by simpa [hs1] using q14))
                  (litHolds_nil s1))))))
      simpa [hs1] using h
    set s2 : Fin 5 → Point := ![M, P i, P (i + 1), Q0, Q1] with hs2
    have gs2 : IndexedGP s2 :=
      indexedGP_vec5 S hgp M (P i) (P (i + 1)) Q0 Q1 hMS (hPS i) (hPS (i + 1)) hQ0S hQ1S
        (hMP i) (hMP (i + 1)) nMQ0 nMQ1 (hinj.ne (d01 i)) (Ne.symm (nQ0P i)) (Ne.symm (nQ1P i))
        (Ne.symm (nQ0P (i + 1))) (Ne.symm (nQ1P (i + 1))) nQ0Q1
    have o6 : 0 < orient M Q0 Q1 := by
      have h := sign_imp_pos [(0, 1, 2, true), (0, 2, 3, false), (0, 2, 4, true), (1, 2, 3, false),
        (1, 2, 4, false)] 0 3 4 (by decide +kernel) s2 gs2
        (litHolds_cons (litHolds_pos s2 0 1 2 (by simpa [hs2] using mA))
          (litHolds_cons (litHolds_neg s2 0 2 3 (by simpa [hs2] using q02))
            (litHolds_cons (litHolds_pos s2 0 2 4 (by simpa [hs2] using q11))
              (litHolds_cons (litHolds_neg s2 1 2 3 (by simpa [hs2] using q03))
                (litHolds_cons (litHolds_neg s2 1 2 4 (by simpa [hs2] using q14))
                  (litHolds_nil s2))))))
      simpa [hs2] using h
    set s3 : Fin 5 → Point := ![M, P (i + 1), P (i + 2), Q1, Q2] with hs3
    have gs3 : IndexedGP s3 :=
      indexedGP_vec5 S hgp M (P (i + 1)) (P (i + 2)) Q1 Q2 hMS (hPS (i + 1)) (hPS (i + 2)) hQ1S
        hQ2S (hMP (i + 1)) (hMP (i + 2)) nMQ1 nMQ2 (hinj.ne (d12 i)) (Ne.symm (nQ1P (i + 1)))
        (Ne.symm (nQ2P (i + 1))) (Ne.symm (nQ1P (i + 2))) (Ne.symm (nQ2P (i + 2))) nQ1Q2
    have o7 : 0 < orient M Q1 Q2 := by
      have h := sign_imp_pos [(0, 1, 2, true), (0, 2, 3, false), (0, 2, 4, true), (1, 2, 3, false),
        (1, 2, 4, false)] 0 3 4 (by decide +kernel) s3 gs3
        (litHolds_cons (litHolds_pos s3 0 1 2 (by simpa [hs3] using mB))
          (litHolds_cons (litHolds_neg s3 0 2 3 (by simpa [hs3] using q12))
            (litHolds_cons (litHolds_pos s3 0 2 4 (by simpa [hs3] using q21))
              (litHolds_cons (litHolds_neg s3 1 2 3 (by simpa [hs3] using q13))
                (litHolds_cons (litHolds_neg s3 1 2 4 (by simpa [hs3] using q24))
                  (litHolds_nil s3))))))
      simpa [hs3] using h
    have hcase' : orient Qm Q0 Q1 < 0 := by
      linarith [orient_cyc Q0 Q1 Qm, orient_cyc Q1 Qm Q0]
    set s4 : Fin 5 → Point := ![M, Qm, Q0, Q1, Q2] with hs4
    have gs4 : IndexedGP s4 :=
      indexedGP_vec5 S hgp M Qm Q0 Q1 Q2 hMS hQmS hQ0S hQ1S hQ2S nMQm nMQ0 nMQ1 nMQ2 nQmQ0
        nQmQ1 nQmQ2 nQ0Q1 nQ0Q2 nQ1Q2
    have o8 : 0 < orient Q0 Q1 Q2 := by
      have h := sign_imp_pos [(0, 1, 3, true), (0, 1, 4, false), (0, 2, 3, true), (0, 3, 4, true),
        (1, 2, 3, false)] 2 3 4 (by decide +kernel) s4 gs4
        (litHolds_cons (litHolds_pos s4 0 1 3 (by simpa [hs4] using o5))
          (litHolds_cons (litHolds_neg s4 0 1 4 (by simpa [hs4] using o3))
            (litHolds_cons (litHolds_pos s4 0 2 3 (by simpa [hs4] using o6))
              (litHolds_cons (litHolds_pos s4 0 3 4 (by simpa [hs4] using o7))
                (litHolds_cons (litHolds_neg s4 1 2 3 (by simpa [hs4] using hcase'))
                  (litHolds_nil s4))))))
      simpa [hs4] using h
    set s5 : Fin 5 → Point := ![M, P (i + 1), P (i + 2), Qm, Q2] with hs5
    have gs5 : IndexedGP s5 :=
      indexedGP_vec5 S hgp M (P (i + 1)) (P (i + 2)) Qm Q2 hMS (hPS (i + 1)) (hPS (i + 2)) hQmS
        hQ2S (hMP (i + 1)) (hMP (i + 2)) nMQm nMQ2 (hinj.ne (d12 i)) (Ne.symm (nQmP (i + 1)))
        (Ne.symm (nQ2P (i + 1))) (Ne.symm (nQmP (i + 2))) (Ne.symm (nQ2P (i + 2))) nQmQ2
    have o9 : 0 < orient (P (i + 1)) (P (i + 2)) Qm := by
      have h := sign_imp_pos [(0, 1, 2, true), (0, 1, 3, false), (0, 2, 4, true), (0, 3, 4, false),
        (1, 2, 4, false)] 1 2 3 (by decide +kernel) s5 gs5
        (litHolds_cons (litHolds_pos s5 0 1 2 (by simpa [hs5] using mB))
          (litHolds_cons (litHolds_neg s5 0 1 3 (by simpa [hs5] using o1))
            (litHolds_cons (litHolds_pos s5 0 2 4 (by simpa [hs5] using q21))
              (litHolds_cons (litHolds_neg s5 0 3 4 (by simpa [hs5] using o3))
                (litHolds_cons (litHolds_neg s5 1 2 4 (by simpa [hs5] using q24))
                  (litHolds_nil s5))))))
      simpa [hs5] using h
    refine empty_pentagon_of_wedge_triple S hgp M (P (i + 1)) (P (i + 2)) Q0 Q1 Q2 hMS
      (hPS (i + 1)) (hPS (i + 2)) hQ0S hQ1S hQ2S hEi1 q02 q05 q11 q12 q13 q21 q24 ?_ ?_
    · linarith [orient_cyc Q0 Q1 Q2, orient_cyc Q1 Q2 Q0]
    · intro q hqS hqU hqV hqA hqB hqC
      rcases (hS q).1 hqS with ⟨j, rfl⟩ | rfl | rfl | rfl | rfl | rfl
      · have h := hccw (i + 1) j (fun h => hqU (by rw [h])) (fun h => hqV (by rw [h, f5 i]))
        rwa [f5 i] at h
      · exact hEi1
      · exact o9
      · exact absurd rfl hqA
      · exact absurd rfl hqB
      · exact absurd rfl hqC
  · -- CASE A: the pentagon `P (i+1), P i, Qm, Q0, Q1`
    set t1 : Fin 5 → Point := ![M, P i, P (i + 1), Qm, Q2] with ht1
    have gt1 : IndexedGP t1 :=
      indexedGP_vec5 S hgp M (P i) (P (i + 1)) Qm Q2 hMS (hPS i) (hPS (i + 1)) hQmS hQ2S
        (hMP i) (hMP (i + 1)) nMQm nMQ2 (hinj.ne (d01 i)) (Ne.symm (nQmP i)) (Ne.symm (nQ2P i))
        (Ne.symm (nQmP (i + 1))) (Ne.symm (nQ2P (i + 1))) nQmQ2
    have o4 : 0 < orient (P i) (P (i + 1)) Q2 := by
      have h := sign_imp_pos [(0, 1, 2, true), (0, 2, 3, false), (0, 2, 4, true), (0, 3, 4, false),
        (1, 2, 3, false)] 1 2 4 (by decide +kernel) t1 gt1
        (litHolds_cons (litHolds_pos t1 0 1 2 (by simpa [ht1] using mA))
          (litHolds_cons (litHolds_neg t1 0 2 3 (by simpa [ht1] using o1))
            (litHolds_cons (litHolds_pos t1 0 2 4 (by simpa [ht1] using o2))
              (litHolds_cons (litHolds_neg t1 0 3 4 (by simpa [ht1] using o3))
                (litHolds_cons (litHolds_neg t1 1 2 3 (by simpa [ht1] using qm5))
                  (litHolds_nil t1))))))
      simpa [ht1] using h
    refine empty_pentagon_of_wedge_triple S hgp M (P i) (P (i + 1)) Qm Q0 Q1 hMS (hPS i)
      (hPS (i + 1)) hQmS hQ0S hQ1S hEi qm2 qm5 q01 q02 q03 q11 q14 hcase ?_
    intro q hqS hqU hqV hqA hqB hqC
    rcases (hS q).1 hqS with ⟨j, rfl⟩ | rfl | rfl | rfl | rfl | rfl
    · exact hccw i j (fun h => hqU (by rw [h])) (fun h => hqV (by rw [h]))
    · exact hEi
    · exact absurd rfl hqA
    · exact absurd rfl hqB
    · exact absurd rfl hqC
    · exact o4

end Horton
