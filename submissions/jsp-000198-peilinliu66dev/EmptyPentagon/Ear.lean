/-
Reused under MIT from CollinYuanjieRen/awards, commit
b8bb4f7803f921a7970abc880291ad9372111360, JSP-000198 small-k submission.
Original module: EmptyPentagon/Ear.lean
Source/permission records: EmptyPentagon/UPSTREAM.md and LICENSE.
Local target: Lean 4.33.1 / pinned Mathlib 0df444a36.
-/
import EmptyPentagon.Definitions
import EmptyPentagon.Certificate
import EmptyPentagon.Interp
import EmptyPentagon.Pentagon
import EmptyPentagon.Signs

noncomputable section
namespace Horton

/-- The orientation is invariant under the reverse cyclic rotation of its arguments. -/
theorem orient_rot (a b c : Point) : orient a b c = orient c a b := by
  unfold orient; ring

/-- Harborth's ear case: if the unique interior point `M` of a counterclockwise pentagon lies in
the ear triangle `P i, P (i+1), P (i+2)`, then `{P i, M, P (i+2), P (i+3), P (i+4)}` is an empty
convex pentagon of `S`. -/
theorem ear_case (S : Finset Point) (P : Fin 5 → Point) (hinj : Function.Injective P)
    (hPS : ∀ i, P i ∈ S)
    (hccw : ∀ i j : Fin 5, j ≠ i → j ≠ i + 1 → 0 < orient (P i) (P (i + 1)) (P j))
    (M : Point) (hMS : M ∈ S)
    (hM : M ∈ interior (convexHull ℝ ((Finset.univ.image P : Finset Point) : Set Point)))
    (huniq : ∀ q ∈ S, q ∈ interior (convexHull ℝ ((Finset.univ.image P : Finset Point) : Set Point))
      → q = M)
    (i : Fin 5) (hear : 0 < orient (P (i + 2)) (P i) M) :
    ∃ V : Finset Point, V.card = 5 ∧ EmptyConvexPolygon S V := by
  -- index arithmetic in `Fin 5`
  have e11 : i + 1 + 1 = i + 2 := by omega
  have e21 : i + 2 + 1 = i + 3 := by omega
  have e31 : i + 3 + 1 = i + 4 := by omega
  have e41 : i + 4 + 1 = i := by omega
  -- (F1) `M` is strictly left of every edge
  have hE := orient_edge_pos_of_mem_interior P M hM hccw
  have hE0 : 0 < orient (P i) (P (i + 1)) M := hE i
  have hE1 : 0 < orient (P (i + 1)) (P (i + 2)) M := by have h := hE (i + 1); rwa [e11] at h
  have hE2 : 0 < orient (P (i + 2)) (P (i + 3)) M := by have h := hE (i + 2); rwa [e21] at h
  have hE3 : 0 < orient (P (i + 3)) (P (i + 4)) M := by have h := hE (i + 3); rwa [e31] at h
  have hE4 : 0 < orient (P (i + 4)) (P i) M := by have h := hE (i + 4); rwa [e41] at h
  -- (F2) `M` is not a vertex
  have hMP : ∀ j, M ≠ P j := by
    intro j hj
    have h := hE j
    rw [hj, orient_self_left] at h
    exact lt_irrefl _ h
  -- (F3) orientation facts of the pentagon itself
  have p02 : 0 < orient (P i) (P (i + 1)) (P (i + 2)) := hccw i (i + 2) (by omega) (by omega)
  have p03 : 0 < orient (P i) (P (i + 1)) (P (i + 3)) := hccw i (i + 3) (by omega) (by omega)
  have p20 : 0 < orient (P (i + 2)) (P (i + 3)) (P i) := by
    have h := hccw (i + 2) i (by omega) (by omega); rwa [e21] at h
  have p24 : 0 < orient (P (i + 2)) (P (i + 3)) (P (i + 4)) := by
    have h := hccw (i + 2) (i + 4) (by omega) (by omega); rwa [e21] at h
  have p30 : 0 < orient (P (i + 3)) (P (i + 4)) (P i) := by
    have h := hccw (i + 3) i (by omega) (by omega); rwa [e31] at h
  have p32 : 0 < orient (P (i + 3)) (P (i + 4)) (P (i + 2)) := by
    have h := hccw (i + 3) (i + 2) (by omega) (by omega); rwa [e31] at h
  have p42 : 0 < orient (P (i + 4)) (P i) (P (i + 2)) := by
    have h := hccw (i + 4) (i + 2) (by omega) (by omega); rwa [e41] at h
  have p43 : 0 < orient (P (i + 4)) (P i) (P (i + 3)) := by
    have h := hccw (i + 4) (i + 3) (by omega) (by omega); rwa [e41] at h
  have p14 : 0 < orient (P (i + 1)) (P (i + 2)) (P (i + 4)) := by
    have h := hccw (i + 1) (i + 4) (by omega) (by omega); rwa [e11] at h
  -- (F4) `M` lies strictly inside the ear triangle; chord facts through `M`
  obtain ⟨α, β, γ, hα, hβ, hγ, hsum, hMeq⟩ :=
    barycentric_of_orient_pos (P i) (P (i + 1)) (P (i + 2)) M p02 hE0 hE1 hear
  have hF1 : 0 < orient (P (i + 3)) (P i) M := by
    rw [hMeq, orient_affine_comb _ _ _ _ _ _ _ _ hsum, orient_self_right, mul_zero, zero_add,
      orient_cyc (P (i + 3)) (P i) (P (i + 1)), orient_cyc (P (i + 3)) (P i) (P (i + 2)),
      orient_cyc (P i) (P (i + 2)) (P (i + 3))]
    exact add_pos (mul_pos hβ p03) (mul_pos hγ p20)
  have hF2 : 0 < orient (P (i + 2)) (P (i + 4)) M := by
    rw [hMeq, orient_affine_comb _ _ _ _ _ _ _ _ hsum, orient_self_left, mul_zero, add_zero,
      orient_cyc (P (i + 2)) (P (i + 4)) (P i), orient_rot (P (i + 2)) (P (i + 4)) (P (i + 1))]
    exact add_pos (mul_pos hα p42) (mul_pos hβ p14)
  -- the new pentagon `Q = (P i, M, P (i+2), P (i+3), P (i+4))`
  set Q : Fin 5 → Point := ![P i, M, P (i + 2), P (i + 3), P (i + 4)] with hQ
  have hQinj : Function.Injective Q := by
    have hAM := (hMP i).symm
    have hMB := hMP (i + 2)
    have hMC := hMP (i + 3)
    have hMD := hMP (i + 4)
    have hAB : P i ≠ P (i + 2) := hinj.ne (by omega)
    have hAC : P i ≠ P (i + 3) := hinj.ne (by omega)
    have hAD : P i ≠ P (i + 4) := hinj.ne (by omega)
    have hBC : P (i + 2) ≠ P (i + 3) := hinj.ne (by omega)
    have hBD : P (i + 2) ≠ P (i + 4) := hinj.ne (by omega)
    have hCD : P (i + 3) ≠ P (i + 4) := hinj.ne (by omega)
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp [hQ, hAM, hAB, hAC, hAD, hMB, hMC, hMD, hBC, hBD, hCD,
      hAM.symm, hAB.symm, hAC.symm, hAD.symm, hMB.symm, hMC.symm, hMD.symm, hBC.symm, hBD.symm,
      hCD.symm] at hab ⊢
  have hQS : ∀ k, Q k ∈ S := by
    intro k
    fin_cases k <;> simp [hQ, hPS, hMS]
  have hQccw : ∀ k j : Fin 5, j ≠ k → j ≠ k + 1 → 0 < orient (Q k) (Q (k + 1)) (Q j) := by
    have h02 : 0 < orient (P i) M (P (i + 2)) := by rw [orient_rot]; exact hear
    have h03 : 0 < orient (P i) M (P (i + 3)) := by rw [orient_rot]; exact hF1
    have h04 : 0 < orient (P i) M (P (i + 4)) := by rw [orient_rot]; exact hE4
    have h10 : 0 < orient M (P (i + 2)) (P i) := by rw [orient_cyc]; exact hear
    have h13 : 0 < orient M (P (i + 2)) (P (i + 3)) := by rw [orient_cyc]; exact hE2
    have h14 : 0 < orient M (P (i + 2)) (P (i + 4)) := by rw [orient_cyc]; exact hF2
    have h20 : 0 < orient (P (i + 2)) (P (i + 3)) (P i) := p20
    have h21 : 0 < orient (P (i + 2)) (P (i + 3)) M := hE2
    have h24 : 0 < orient (P (i + 2)) (P (i + 3)) (P (i + 4)) := p24
    have h30 : 0 < orient (P (i + 3)) (P (i + 4)) (P i) := p30
    have h31 : 0 < orient (P (i + 3)) (P (i + 4)) M := hE3
    have h32 : 0 < orient (P (i + 3)) (P (i + 4)) (P (i + 2)) := p32
    have h41 : 0 < orient (P (i + 4)) (P i) M := hE4
    have h42 : 0 < orient (P (i + 4)) (P i) (P (i + 2)) := p42
    have h43 : 0 < orient (P (i + 4)) (P i) (P (i + 3)) := p43
    intro k j hjk hjk1
    fin_cases k <;> fin_cases j <;> simp [hQ] at hjk hjk1 ⊢ <;> assumption
  -- (F6) emptiness: the new hull lies inside the old one, whose only interior point is `M`
  have hsub : convexHull ℝ ((Finset.univ.image Q : Finset Point) : Set Point) ⊆
      convexHull ℝ ((Finset.univ.image P : Finset Point) : Set Point) := by
    refine convexHull_min ?_ (convex_convexHull ℝ _)
    intro x hx
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
    have hP : ∀ j, P j ∈ convexHull ℝ ((Finset.univ.image P : Finset Point) : Set Point) :=
      fun j => subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem P (Finset.mem_univ j)))
    fin_cases k <;> simp only [hQ] <;> first | exact hP _ | exact interior_subset hM
  refine ⟨Finset.univ.image Q, ?_, emptyConvexPolygon_of_ccw S Q hQinj hQS hQccw ?_⟩
  · rw [Finset.card_image_of_injective _ hQinj]; simp
  · intro q hqS hqV hqI
    have hqM := huniq q hqS (interior_mono hsub hqI)
    apply hqV
    rw [hqM]
    exact Finset.mem_image_of_mem Q (Finset.mem_univ 1)

end Horton
