/-
Reused under MIT from CollinYuanjieRen/awards, commit
b8bb4f7803f921a7970abc880291ad9372111360, JSP-000198 small-k submission.
Original module: EmptyPentagon/Front2.lean
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

/-- Harborth's second front case: some point of `S` lies in the wedge beyond edge `i` and
strictly left of the next edge line `P (i+1) → P (i+2)`.  Taking such a point closest to the
edge line `i` yields the empty convex pentagon `{P i, R, P (i+1), P (i+2), M}`. -/
theorem front_case2 (S : Finset Point) (hgp : GeneralPosition S) (P : Fin 5 → Point)
    (hinj : Function.Injective P) (hPS : ∀ i, P i ∈ S)
    (hccw : ∀ i j : Fin 5, j ≠ i → j ≠ i + 1 → 0 < orient (P i) (P (i + 1)) (P j))
    (M : Point) (hMS : M ∈ S)
    (hM : M ∈ interior (convexHull ℝ ((Finset.univ.image P : Finset Point) : Set Point)))
    (huniq : ∀ q ∈ S, q ∈ interior (convexHull ℝ ((Finset.univ.image P : Finset Point) : Set Point))
      → q = M)
    (hcore : ∀ i, 0 < orient (P i) (P (i + 2)) M)
    (i : Fin 5) (R : Point) (hRS : R ∈ S)
    (hA : 0 < orient M (P i) R ∧ orient M (P (i + 1)) R < 0 ∧ orient (P i) (P (i + 1)) R < 0)
    (hfront : 0 < orient (P (i + 1)) (P (i + 2)) R) :
    ∃ V : Finset Point, V.card = 5 ∧ EmptyConvexPolygon S V := by
  classical
  -- index arithmetic in `Fin 5`
  have a1 : ∀ j : Fin 5, j + 1 + 1 = j + 2 := by decide
  have a2 : ∀ j : Fin 5, j + 1 ≠ j := by decide
  have a3 : ∀ j : Fin 5, j + 2 ≠ j := by decide
  have a4 : ∀ j : Fin 5, j + 2 ≠ j + 1 := by decide
  -- (F1) `M` is strictly left of every edge of `P`, and it is not a vertex
  have hE := orient_edge_pos_of_mem_interior P M hM hccw
  have hEi : 0 < orient (P i) (P (i + 1)) M := hE i
  have hEn : 0 < orient (P (i + 1)) (P (i + 2)) M := by have h := hE (i + 1); rwa [a1 i] at h
  have hdg : 0 < orient (P i) (P (i + 2)) M := hcore i
  have hccw3 : 0 < orient (P i) (P (i + 1)) (P (i + 2)) := hccw i (i + 2) (a3 i) (a4 i)
  have hMP : ∀ j, M ≠ P j := by
    intro j hj
    have h := hE j
    rw [hj, orient_self_left] at h
    exact lt_irrefl _ h
  -- (F2) a wedge point beyond edge `i` and left of the next edge, closest to edge `i`
  obtain ⟨R0, hR0, hmin⟩ := Finset.exists_min_image
    (S.filter fun q => 0 < orient M (P i) q ∧ orient M (P (i + 1)) q < 0 ∧
      orient (P i) (P (i + 1)) q < 0 ∧ 0 < orient (P (i + 1)) (P (i + 2)) q)
    (fun q => -orient (P i) (P (i + 1)) q)
    ⟨R, Finset.mem_filter.mpr ⟨hRS, hA.1, hA.2.1, hA.2.2, hfront⟩⟩
  obtain ⟨hR0S, hw1, hw2, hw3, hw4⟩ := Finset.mem_filter.mp hR0
  -- (F3) the five new vertices are pairwise distinct
  have hR0M : R0 ≠ M := by
    intro h; rw [h, orient_self_left] at hw1; exact lt_irrefl _ hw1
  have hR0A : R0 ≠ P i := by
    intro h; rw [h, orient_self_left] at hw3; exact lt_irrefl _ hw3
  have hR0B : R0 ≠ P (i + 1) := by
    intro h; rw [h, orient_self_right] at hw3; exact lt_irrefl _ hw3
  have hR0C : R0 ≠ P (i + 2) := by
    intro h; rw [h, orient_self_right] at hw4; exact lt_irrefl _ hw4
  have hAB : P i ≠ P (i + 1) := hinj.ne (Ne.symm (a2 i))
  have hAC : P i ≠ P (i + 2) := hinj.ne (Ne.symm (a3 i))
  have hBC : P (i + 1) ≠ P (i + 2) := hinj.ne (Ne.symm (a4 i))
  -- (F4) the two nonobvious sign facts, from the kernel-checked five-point tool
  set p : Fin 5 → Point := ![M, P i, P (i + 1), P (i + 2), R0] with hp
  have hpinj : Function.Injective p := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;>
      simp [hp, hMP i, hMP (i + 1), hMP (i + 2), hR0M, hR0A, hR0B, hR0C, hAB, hAC, hBC,
        (hMP i).symm, (hMP (i + 1)).symm, (hMP (i + 2)).symm, hR0M.symm, hR0A.symm, hR0B.symm,
        hR0C.symm, hAB.symm, hAC.symm, hBC.symm] at hxy ⊢
  have hpS : ∀ k : Fin 5, p k ∈ S := by
    intro k; fin_cases k <;> simp [hp, hMS, hPS, hR0S]
  have hpgp : IndexedGP p := fun x y z hxy hxz hyz =>
    hgp _ (hpS x) _ (hpS y) _ (hpS z) (hpinj.ne hxy) (hpinj.ne hxz) (hpinj.ne hyz)
  have htool1 : orient M (P (i + 2)) R0 < 0 := by
    have h := sign_imp_neg [(1, 2, 0, true), (2, 3, 0, true), (1, 3, 0, true), (0, 1, 4, true),
      (0, 2, 4, false)] 0 3 4 (by decide +kernel) p hpgp
      (litHolds_cons (litHolds_pos p 1 2 0 (by simpa [hp] using hEi))
        (litHolds_cons (litHolds_pos p 2 3 0 (by simpa [hp] using hEn))
          (litHolds_cons (litHolds_pos p 1 3 0 (by simpa [hp] using hdg))
            (litHolds_cons (litHolds_pos p 0 1 4 (by simpa [hp] using hw1))
              (litHolds_cons (litHolds_neg p 0 2 4 (by simpa [hp] using hw2))
                (litHolds_nil p))))))
    simpa [hp] using h
  have htool2 : orient (P i) (P (i + 2)) R0 < 0 := by
    have h := sign_imp_neg [(1, 2, 3, true), (1, 2, 0, true), (1, 3, 0, true), (0, 1, 4, true),
      (1, 2, 4, false)] 1 3 4 (by decide +kernel) p hpgp
      (litHolds_cons (litHolds_pos p 1 2 3 (by simpa [hp] using hccw3))
        (litHolds_cons (litHolds_pos p 1 2 0 (by simpa [hp] using hEi))
          (litHolds_cons (litHolds_pos p 1 3 0 (by simpa [hp] using hdg))
            (litHolds_cons (litHolds_pos p 0 1 4 (by simpa [hp] using hw1))
              (litHolds_cons (litHolds_neg p 1 2 4 (by simpa [hp] using hw3))
                (litHolds_nil p))))))
    simpa [hp] using h
  -- (F5) the new pentagon `Q = (P i, R0, P (i+1), P (i+2), M)`
  set Q : Fin 5 → Point := ![P i, R0, P (i + 1), P (i + 2), M] with hQ
  have hQinj : Function.Injective Q := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;>
      simp [hQ, hMP i, hMP (i + 1), hMP (i + 2), hR0M, hR0A, hR0B, hR0C, hAB, hAC, hBC,
        (hMP i).symm, (hMP (i + 1)).symm, (hMP (i + 2)).symm, hR0M.symm, hR0A.symm, hR0B.symm,
        hR0C.symm, hAB.symm, hAC.symm, hBC.symm] at hxy ⊢
  have hQS : ∀ k : Fin 5, Q k ∈ S := by
    intro k; fin_cases k <;> simp [hQ, hMS, hPS, hR0S]
  have hQccw : ∀ k j : Fin 5, j ≠ k → j ≠ k + 1 → 0 < orient (Q k) (Q (k + 1)) (Q j) := by
    have h02 : 0 < orient (P i) R0 (P (i + 1)) := by
      rw [show orient (P i) R0 (P (i + 1)) = -orient (P i) (P (i + 1)) R0 from by
        unfold orient; ring]
      linarith
    have h03 : 0 < orient (P i) R0 (P (i + 2)) := by
      rw [show orient (P i) R0 (P (i + 2)) = -orient (P i) (P (i + 2)) R0 from by
        unfold orient; ring]
      linarith
    have h04 : 0 < orient (P i) R0 M := by
      rw [show orient (P i) R0 M = orient M (P i) R0 from by unfold orient; ring]
      exact hw1
    have h10 : 0 < orient R0 (P (i + 1)) (P i) := by
      rw [show orient R0 (P (i + 1)) (P i) = -orient (P i) (P (i + 1)) R0 from by
        unfold orient; ring]
      linarith
    have h13 : 0 < orient R0 (P (i + 1)) (P (i + 2)) := by
      rw [show orient R0 (P (i + 1)) (P (i + 2)) = orient (P (i + 1)) (P (i + 2)) R0 from by
        unfold orient; ring]
      exact hw4
    have h14 : 0 < orient R0 (P (i + 1)) M := by
      rw [show orient R0 (P (i + 1)) M = -orient M (P (i + 1)) R0 from by unfold orient; ring]
      linarith
    have h20 : 0 < orient (P (i + 1)) (P (i + 2)) (P i) := by
      rw [show orient (P (i + 1)) (P (i + 2)) (P i) = orient (P i) (P (i + 1)) (P (i + 2)) from by
        unfold orient; ring]
      exact hccw3
    have h21 : 0 < orient (P (i + 1)) (P (i + 2)) R0 := hw4
    have h24 : 0 < orient (P (i + 1)) (P (i + 2)) M := hEn
    have h30 : 0 < orient (P (i + 2)) M (P i) := by
      rw [show orient (P (i + 2)) M (P i) = orient (P i) (P (i + 2)) M from by unfold orient; ring]
      exact hdg
    have h31 : 0 < orient (P (i + 2)) M R0 := by
      rw [show orient (P (i + 2)) M R0 = -orient M (P (i + 2)) R0 from by unfold orient; ring]
      linarith
    have h32 : 0 < orient (P (i + 2)) M (P (i + 1)) := by
      rw [show orient (P (i + 2)) M (P (i + 1)) = orient (P (i + 1)) (P (i + 2)) M from by
        unfold orient; ring]
      exact hEn
    have h41 : 0 < orient M (P i) R0 := hw1
    have h42 : 0 < orient M (P i) (P (i + 1)) := by
      rw [show orient M (P i) (P (i + 1)) = orient (P i) (P (i + 1)) M from by unfold orient; ring]
      exact hEi
    have h43 : 0 < orient M (P i) (P (i + 2)) := by
      rw [show orient M (P i) (P (i + 2)) = orient (P i) (P (i + 2)) M from by unfold orient; ring]
      exact hdg
    intro k j hjk hjk1
    fin_cases k <;> fin_cases j <;> simp [hQ] at hjk hjk1 ⊢ <;> assumption
  -- (F6) emptiness of the new pentagon
  have hFmem : ∀ j : Fin 5,
      P j ∈ convexHull ℝ ((Finset.univ.image P : Finset Point) : Set Point) := fun j =>
    subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem P (Finset.mem_univ j)))
  have hCH : ∀ a b c : Point,
      a ∈ convexHull ℝ ((Finset.univ.image P : Finset Point) : Set Point) →
      b ∈ convexHull ℝ ((Finset.univ.image P : Finset Point) : Set Point) →
      c ∈ convexHull ℝ ((Finset.univ.image P : Finset Point) : Set Point) →
      interior (convexHull ℝ ({a, b, c} : Set Point)) ⊆
        interior (convexHull ℝ ((Finset.univ.image P : Finset Point) : Set Point)) := by
    intro a b c ha hb hc
    refine interior_mono (convexHull_min ?_ (convex_convexHull ℝ _))
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
  refine ⟨Finset.univ.image Q, ?_, emptyConvexPolygon_of_ccw S Q hQinj hQS hQccw ?_⟩
  · rw [Finset.card_image_of_injective _ hQinj]; simp
  · intro q hqS hqV hqI
    have hqne : ∀ k : Fin 5, q ≠ Q k := by
      intro k h
      exact hqV (by rw [h]; exact Finset.mem_image_of_mem Q (Finset.mem_univ k))
    have hqA : q ≠ P i := by have h := hqne 0; simpa [hQ] using h
    have hqB : q ≠ P (i + 1) := by have h := hqne 2; simpa [hQ] using h
    have hqM : q ≠ M := by have h := hqne 4; simpa [hQ] using h
    have hed := orient_edge_pos_of_mem_interior Q q hqI hQccw
    have ed0 : 0 < orient (P i) R0 q := by have h := hed 0; simpa [hQ] using h
    have ed1 : 0 < orient R0 (P (i + 1)) q := by have h := hed 1; simpa [hQ] using h
    have ed2 : 0 < orient (P (i + 1)) (P (i + 2)) q := by have h := hed 2; simpa [hQ] using h
    have ed3 : 0 < orient (P (i + 2)) M q := by have h := hed 3; simpa [hQ] using h
    have ed4 : 0 < orient M (P i) q := by have h := hed 4; simpa [hQ] using h
    have hbcnz : orient (P i) (P (i + 1)) q ≠ 0 :=
      hgp _ (hPS i) _ (hPS (i + 1)) _ hqS hAB (Ne.symm hqA) (Ne.symm hqB)
    rcases lt_or_gt_of_ne hbcnz with hneg | hpos
    · -- `q` is strictly inside the triangle `P i, R0, P (i+1)`, contradicting minimality of `R0`
      have htri : 0 < orient (P i) R0 (P (i + 1)) := by
        rw [show orient (P i) R0 (P (i + 1)) = -orient (P i) (P (i + 1)) R0 from by
          unfold orient; ring]
        linarith
      have edBA : 0 < orient (P (i + 1)) (P i) q := by
        rw [show orient (P (i + 1)) (P i) q = -orient (P i) (P (i + 1)) q from by
          unfold orient; ring]
        linarith
      obtain ⟨α, β, γ, hα, hβ, hγ, hsum, hqeq⟩ :=
        barycentric_of_orient_pos (P i) R0 (P (i + 1)) q htri ed0 ed1 edBA
      have hMAB : 0 < orient M (P i) (P (i + 1)) := by
        rw [show orient M (P i) (P (i + 1)) = orient (P i) (P (i + 1)) M from by
          unfold orient; ring]
        exact hEi
      have hMBA : orient M (P (i + 1)) (P i) < 0 := by
        rw [show orient M (P (i + 1)) (P i) = -orient M (P i) (P (i + 1)) from by
          unfold orient; ring]
        linarith
      have c1 : 0 < orient M (P i) q := by
        rw [hqeq, orient_affine_comb _ _ _ _ _ _ _ _ hsum, orient_self_right]
        have t1 := mul_pos hβ hw1
        have t2 := mul_pos hγ hMAB
        linarith
      have c2 : orient M (P (i + 1)) q < 0 := by
        rw [hqeq, orient_affine_comb _ _ _ _ _ _ _ _ hsum, orient_self_right]
        have t1 := mul_neg_of_pos_of_neg hα hMBA
        have t2 := mul_neg_of_pos_of_neg hβ hw2
        linarith
      have hval : orient (P i) (P (i + 1)) q = β * orient (P i) (P (i + 1)) R0 := by
        rw [hqeq, orient_affine_comb _ _ _ _ _ _ _ _ hsum, orient_self_left, orient_self_right]
        ring
      have c3 : orient (P i) (P (i + 1)) q < 0 := by
        rw [hval]; exact mul_neg_of_pos_of_neg hβ hw3
      have hle : -orient (P i) (P (i + 1)) R0 ≤ -orient (P i) (P (i + 1)) q :=
        hmin q (Finset.mem_filter.mpr ⟨hqS, c1, c2, c3, ed2⟩)
      rw [hval] at hle
      have hkey : 0 < (1 - β) * -orient (P i) (P (i + 1)) R0 :=
        mul_pos (by linarith) (by linarith)
      nlinarith
    · -- `q` is strictly inside `F`, so `q = M`, contradicting `q ∉ Q`
      have hnz2 : orient (P (i + 1)) M q ≠ 0 :=
        hgp _ (hPS (i + 1)) _ hMS _ hqS (Ne.symm (hMP (i + 1))) (Ne.symm hqB) (Ne.symm hqM)
      have hMhull : M ∈ convexHull ℝ ((Finset.univ.image P : Finset Point) : Set Point) :=
        interior_subset hM
      have hqF : q ∈
          interior (convexHull ℝ ((Finset.univ.image P : Finset Point) : Set Point)) := by
        rcases lt_or_gt_of_ne hnz2 with h2 | h2
        · refine hCH (P (i + 1)) (P (i + 2)) M (hFmem (i + 1)) (hFmem (i + 2)) hMhull ?_
          refine mem_interior_triangle_of_orient_pos _ _ _ _ hEn ed2 ed3 ?_
          rw [show orient M (P (i + 1)) q = -orient (P (i + 1)) M q from by unfold orient; ring]
          linarith
        · exact hCH (P i) (P (i + 1)) M (hFmem i) (hFmem (i + 1)) hMhull
            (mem_interior_triangle_of_orient_pos _ _ _ _ hEi hpos h2 ed4)
      exact hqM (huniq q hqS hqF)

end Horton
