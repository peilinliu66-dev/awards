import Erdos776.Combinatorics.DiagonalTransfer
import Erdos776.Combinatorics.ProfileCriterion
import Erdos776.L4.Profile

/-!
# The symbolic diagonal-shell obstruction

This file formalizes the non-computational transfer argument from Section 16
of `UNIFORM_THEOREM.md`.  It first extracts a ground-independent consequence
of L4 and then transports the upper part of the long constant-profile
recurrence through a diagonal binomial shell.
-/

namespace Erdos776.Uniform

open Erdos776.KruskalKatona
open Erdos776.L4

/-- The ground-independent version of the canonical L4 recurrence. -/
def canonicalL4Chain (r : ℕ) : ℕ → ℕ :=
  l4ProfileChain canonicalShadow r

/-- The finite L4 recurrence is pointwise bounded by the canonical recurrence. -/
theorem l4ProfileChain_le_canonicalL4Chain (r : ℕ) :
    ∀ i, 2 ≤ i → i ≤ r + 1 →
      l4ProfileChain (l4Shadow r) r i ≤ canonicalL4Chain r i := by
  intro i hi hir
  let d := l4ProfileChain (l4Shadow r) r
  let c := canonicalL4Chain r
  have hd : IsL4Chain (l4Shadow r) r d :=
    isL4Chain_l4ProfileChain (l4Shadow r) r
  have hc : IsL4Chain canonicalShadow r c :=
    isL4Chain_l4ProfileChain canonicalShadow r
  change d i ≤ c i
  apply Nat.decreasingInduction'
      (P := fun k => d k ≤ c k) (m := i) (n := r + 1) ?_ hir
  · rw [hd.1, hc.1]
  · intro k hkr hik ih
    have hk2 : 2 ≤ k := hi.trans hik
    have hkle : k ≤ r := by omega
    rw [hd.2 k hk2 hkle, hc.2 k hk2 hkle]
    apply Nat.add_le_add_left
    exact (kkShadow_le_canonicalShadow (r + 4) (k + 1)
      (d (k + 1)) (by omega)).trans
        (canonicalShadow_mono (k + 1) (by omega) ih)

/-- L4 forces the bottom of its canonical numerical recurrence over capacity. -/
theorem canonicalL4Chain_bottom_gt (r : ℕ) (hr : 29 ≤ r) :
    (r + 4).choose 2 < canonicalL4Chain r 2 := by
  by_contra h
  have hcap : canonicalL4Chain r 2 ≤ (r + 4).choose 2 := by omega
  apply l4_no_recurrence r hr
  refine ⟨l4ProfileChain (l4Shadow r) r,
    isL4Chain_l4ProfileChain (l4Shadow r) r, ?_⟩
  exact (l4ProfileChain_le_canonicalL4Chain r 2 le_rfl (by omega)).trans hcap

/-- The upper residual recurrence after removing the diagonal shell. -/
def IsUpperCoreRecurrence (r : ℕ) (x : ℕ → ℕ) : Prop :=
  x (r + 3) = 0 ∧
    (∀ b, 3 ≤ b → b ≤ r + 2 →
      x b = r + canonicalShadow (b + 1) (x (b + 1))) ∧
    ∀ b, 4 ≤ b → b ≤ r + 2 → x b < (r + 4).choose b

/-- The canonical recurrence for the upper core on levels `3,...,r+2`. -/
def upperCoreChain (r : ℕ) : ℕ → ℕ :=
  profileChain (fun _ => r) (r + 2)

@[simp] theorem upperCoreChain_above_top (r : ℕ) :
    upperCoreChain r (r + 3) = 0 := by
  exact profileChain_top (fun _ => r) (r + 2)

theorem upperCoreChain_step (r b : ℕ) (hb : b ≤ r + 2) :
    upperCoreChain r b =
      r + canonicalShadow (b + 1) (upperCoreChain r (b + 1)) := by
  exact profileChain_step (fun _ => r) hb

/-- The computational upper-core input only needs to provide strict fit. -/
theorem upperCoreChain_isUpperCoreRecurrence (r : ℕ)
    (hstrict : ∀ b, 4 ≤ b → b ≤ r + 2 →
      upperCoreChain r b < (r + 4).choose b) :
    IsUpperCoreRecurrence r (upperCoreChain r) := by
  exact ⟨upperCoreChain_above_top r,
    (fun b _ hb => upperCoreChain_step r b hb), hstrict⟩

/--
Non-strict upper-core capacity, together with a carry smaller than the
positive prescribed load, implies the strict no-carry inequalities (16.0).
-/
theorem upperCoreChain_strict_of_fit
    (r : ℕ) (hr : 2 ≤ r) {e : ℕ}
    (hfit : ∀ b, 4 ≤ b → b ≤ r + 2 →
      upperCoreChain r b ≤ (r + 4).choose b)
    (hexcess : upperCoreChain r 3 = (r + 4).choose 3 + e)
    (her : e < r) :
    ∀ b, 4 ≤ b → b ≤ r + 2 →
      upperCoreChain r b < (r + 4).choose b := by
  intro b hb4 hbr
  have hle := hfit b hb4 hbr
  apply lt_of_le_of_ne hle
  intro heq'
  have heq : upperCoreChain r b = (r + 4).choose b :=
    heq'
  have hshadow : canonicalShadow b ((r + 4).choose b) =
      (r + 4).choose (b - 1) :=
    canonicalShadow_choose (by omega) (by omega)
  by_cases hb : b = 4
  · subst b
    have hstep := upperCoreChain_step r 3 (by omega)
    rw [heq, hshadow] at hstep
    simp only [show 4 - 1 = 3 by omega] at hstep
    omega
  · have hb5 : 5 ≤ b := by omega
    have hstep := upperCoreChain_step r (b - 1) (by omega)
    rw [show b - 1 + 1 = b by omega, heq, hshadow] at hstep
    have hfitLower := hfit (b - 1) (by omega) (by omega)
    omega

/-- The full constant-profile recurrence, with `r` sets on each occupied level. -/
def fullProfileChain (r : ℕ) : ℕ → ℕ :=
  profileChain (fun _ => r) (2 * r + 3)

@[simp] theorem fullProfileChain_above_top (r : ℕ) :
    fullProfileChain r (2 * r + 4) = 0 := by
  simp [fullProfileChain, show 2 * r + 4 = (2 * r + 3) + 1 by omega]

@[simp] theorem fullProfileChain_top (r : ℕ) :
    fullProfileChain r (2 * r + 3) = r := by
  rw [fullProfileChain, profileChain_step (fun _ => r) (by omega)]
  simp

theorem fullProfileChain_step (r i : ℕ) (hi : i ≤ 2 * r + 3) :
    fullProfileChain r i =
      r + canonicalShadow (i + 1) (fullProfileChain r (i + 1)) := by
  exact profileChain_step (fun _ => r) hi

/--
The upper-shell formula (16.2a): while the residual remains strictly below
the next shell, the full recurrence is the diagonal shell plus that residual.
-/
theorem fullProfileChain_diagonal_transfer
    {r : ℕ} {x : ℕ → ℕ} (hx : IsUpperCoreRecurrence r x) :
    ∀ b, 3 ≤ b → b ≤ r + 3 →
      fullProfileChain r (b + r) =
        (2 * r + 4).choose (b + r) - (r + 4).choose b + x b := by
  intro b hb hbr
  apply Nat.decreasingInduction'
      (P := fun k => fullProfileChain r (k + r) =
        (2 * r + 4).choose (k + r) - (r + 4).choose k + x k)
      (m := b) (n := r + 3) ?_ hbr
  · rw [show r + 3 + r = 2 * r + 3 by omega,
      fullProfileChain_top, hx.1]
    have hB : (2 * r + 4).choose (2 * r + 3) = 2 * r + 4 := by
      simpa only [show 2 * r + 4 = (2 * r + 3) + 1 by omega] using
        Nat.choose_succ_self_right (2 * r + 3)
    have hA : (r + 4).choose (r + 3) = r + 4 := by
      simpa only [show r + 4 = (r + 3) + 1 by omega] using
        Nat.choose_succ_self_right (r + 3)
    rw [hB, hA]
    omega
  · intro k hkr hbk ih
    have hk3 : 3 ≤ k := hb.trans hbk
    have hkupper : k ≤ r + 2 := by omega
    have hres : x (k + 1) < (r + 4).choose (k + 1) := by
      by_cases htop : k + 1 = r + 3
      · rw [htop, hx.1]
        have : 0 < (r + 4).choose (r + 3) := by
          rw [show r + 4 = (r + 3) + 1 by omega,
            Nat.choose_succ_self_right]
          omega
        exact this
      · exact hx.2.2 (k + 1) (by omega) (by omega)
    have htransfer := canonicalShadow_diagonal_transfer
      (A := r + 4) (b := k + 1) (t := r) (x := x (k + 1))
      (by omega) (by omega) hres
    have htransfer' :
        canonicalShadow (k + r + 1)
            ((2 * r + 4).choose (k + r + 1) -
              (r + 4).choose (k + 1) + x (k + 1)) =
          (2 * r + 4).choose (k + r) - (r + 4).choose k +
            canonicalShadow (k + 1) (x (k + 1)) := by
      simpa only [Nat.add_sub_cancel, show k + 1 + r = k + r + 1 by omega,
        show r + 4 + r = 2 * r + 4 by omega,
        show k + 1 + r - 1 = k + r by omega,
        show k + 1 - 1 = k by omega] using htransfer
    have ih' : fullProfileChain r (k + r + 1) =
        (2 * r + 4).choose (k + r + 1) -
          (r + 4).choose (k + 1) + x (k + 1) := by
      simpa only [show k + 1 + r = k + r + 1 by omega] using ih
    rw [fullProfileChain_step r (k + r) (by omega), ih', htransfer']
    rw [hx.2.1 k hk3 hkupper]
    omega

/-- A positive core excess at level three becomes a residual above the shell. -/
theorem fullProfileChain_level_r_add_three
    {r e : ℕ} {x : ℕ → ℕ} (hx : IsUpperCoreRecurrence r x)
    (hx3 : x 3 = (r + 4).choose 3 + e) :
    fullProfileChain r (r + 3) =
      (2 * r + 4).choose (r + 3) + e := by
  have hformula := fullProfileChain_diagonal_transfer hx 3 (by omega) (by omega)
  have hmono : (r + 4).choose 3 ≤
      (2 * r + 4).choose (r + 3) := by
    simpa only [show r + 4 + r = 2 * r + 4 by omega,
      show 3 + r = r + 3 by omega] using
        choose_diagonal_mono (r + 4) 3 r
  rw [show 3 + r = r + 3 by omega, hx3] at hformula
  omega

/-- The residual recurrence (16.3), indexed by distance below its top. -/
def residualDescending (r : ℕ) : ℕ → ℕ
  | 0 => 1
  | d + 1 =>
      r + canonicalShadow (r + 2 - d) (residualDescending r d)

/-- The same residual recurrence indexed by set-size level. -/
def residualChain (r i : ℕ) : ℕ :=
  residualDescending r (r + 3 - i)

@[simp] theorem residualChain_top (r : ℕ) :
    residualChain r (r + 3) = 1 := by
  simp [residualChain, residualDescending]

theorem residualChain_step (r i : ℕ) (hi : 3 ≤ i) (hir : i ≤ r + 2) :
    residualChain r i =
      r + canonicalShadow i (residualChain r (i + 1)) := by
  have hdist : r + 3 - i = (r + 2 - i) + 1 := by omega
  have hlevel : r + 2 - (r + 2 - i) = i := by omega
  have hnext : r + 3 - (i + 1) = r + 2 - i := by omega
  rw [residualChain, hdist, residualDescending, hlevel]
  rw [residualChain, hnext]

theorem residualChain_next_to_top (r : ℕ) (hr : 1 ≤ r) :
    residualChain r (r + 2) = 2 * r + 2 := by
  rw [residualChain_step r (r + 2) (by omega) (by omega),
    residualChain_top, canonicalShadow_one (r + 2) (by omega)]
  omega

/-- The residual recurrence dominates the canonical L4 recurrence one level over. -/
theorem canonicalL4Chain_le_residualChain (r : ℕ) (hr : 1 ≤ r) :
    ∀ i, 2 ≤ i → i ≤ r + 1 →
      canonicalL4Chain r i ≤ residualChain r (i + 1) := by
  intro i hi hir
  have hc : IsL4Chain canonicalShadow r (canonicalL4Chain r) :=
    isL4Chain_l4ProfileChain canonicalShadow r
  apply Nat.decreasingInduction'
      (P := fun k => canonicalL4Chain r k ≤ residualChain r (k + 1))
      (m := i) (n := r + 1) ?_ hir
  · rw [hc.1, residualChain_next_to_top r hr]
    omega
  · intro k hkr hik ih
    have hk2 : 2 ≤ k := hi.trans hik
    have hkle : k ≤ r := by omega
    rw [hc.2 k hk2 hkle,
      residualChain_step r (k + 1) (by omega) (by omega)]
    exact Nat.add_le_add_left
      (canonicalShadow_mono (k + 1) (by omega) ih) r

/-- The bottom residual exceeds the two-level capacity inherited from L4. -/
theorem residualChain_three_gt (r : ℕ) (hr : 29 ≤ r) :
    (r + 4).choose 2 < residualChain r 3 := by
  exact (canonicalL4Chain_bottom_gt r hr).trans_le
    (canonicalL4Chain_le_residualChain r (by omega) 2 le_rfl (by omega))

/--
The full constant-profile recurrence exceeds a level of `Fin (2*r+5)`.
The hypotheses on `x` are precisely the non-computational interface to the
upper-core calculation: strict fit above level three and a positive excess at
level three.
-/
theorem fullProfileChain_overflows
    (r : ℕ) (hr : 29 ≤ r) {x : ℕ → ℕ} {e : ℕ}
    (hx : IsUpperCoreRecurrence r x)
    (hx3 : x 3 = (r + 4).choose 3 + e) (he : 1 ≤ e) :
    ∃ i, 2 ≤ i ∧ i ≤ 2 * r + 3 ∧
      (2 * r + 5).choose i < fullProfileChain r i := by
  by_contra hnot
  have hcap : ∀ i, 2 ≤ i → i ≤ 2 * r + 3 →
      fullProfileChain r i ≤ (2 * r + 5).choose i := by
    intro i hi hii
    by_contra hfail
    apply hnot
    exact ⟨i, hi, hii, by omega⟩
  have hstart : (2 * r + 4).choose (r + 3) + residualChain r (r + 3) ≤
      fullProfileChain r (r + 3) := by
    rw [residualChain_top,
      fullProfileChain_level_r_add_three hx hx3]
    omega
  have noCarry : ∀ k, 3 ≤ k → k ≤ r + 3 →
      (2 * r + 4).choose k + residualChain r k ≤ fullProfileChain r k →
      residualChain r k < (2 * r + 4).choose (k - 1) := by
    intro k hk3 hkr hlower
    by_contra hnotlt
    have hreslarge : (2 * r + 4).choose (k - 1) ≤
        residualChain r k := by omega
    have hp : (2 * r + 5).choose k =
        (2 * r + 4).choose (k - 1) + (2 * r + 4).choose k := by
      simpa only [Nat.succ_eq_add_one,
        show 2 * r + 4 + 1 = 2 * r + 5 by omega,
        show k - 1 + 1 = k by omega] using
          Nat.choose_succ_succ (2 * r + 4) (k - 1)
    have hfull : (2 * r + 5).choose k ≤ fullProfileChain r k := by
      rw [hp]
      omega
    have heq : fullProfileChain r k = (2 * r + 5).choose k := by
      exact Nat.le_antisymm (hcap k (by omega) (by omega)) hfull
    have hstep := fullProfileChain_step r (k - 1) (by omega)
    have hshadow : canonicalShadow k ((2 * r + 5).choose k) =
        (2 * r + 5).choose (k - 1) := by
      exact canonicalShadow_choose (by omega) (by omega)
    rw [show k - 1 + 1 = k by omega, heq, hshadow] at hstep
    have hcapLower := hcap (k - 1) (by omega) (by omega)
    omega
  have hlower3 : (2 * r + 4).choose 3 + residualChain r 3 ≤
      fullProfileChain r 3 := by
    refine Nat.decreasingInduction'
        (P := fun k => (2 * r + 4).choose k + residualChain r k ≤
          fullProfileChain r k)
        (m := 3) (n := r + 3) ?_ (by omega) hstart
    intro k hkr hk3 ih
    have hkupper : k ≤ r + 2 := by omega
    have hnc := noCarry (k + 1) (by omega) (by omega) ih
    have hmono := canonicalShadow_mono (k + 1) (by omega) ih
    have hshell := canonicalShadow_add_shell
      (B := 2 * r + 4) (k := k + 1) (x := residualChain r (k + 1))
      (by omega) (by omega) hnc
    have hstep := fullProfileChain_step r k (by omega)
    have hresstep := residualChain_step r k hk3 hkupper
    rw [hstep]
    calc
      (2 * r + 4).choose k + residualChain r k =
          r + ((2 * r + 4).choose k +
            canonicalShadow k (residualChain r (k + 1))) := by
              rw [hresstep]
              omega
      _ = r + canonicalShadow (k + 1)
          ((2 * r + 4).choose (k + 1) + residualChain r (k + 1)) := by
            rw [hshell]
            simp only [show k + 1 - 1 = k by omega]
      _ ≤ r + canonicalShadow (k + 1) (fullProfileChain r (k + 1)) :=
        Nat.add_le_add_left hmono r
  have hnc3 := noCarry 3 (by omega) (by omega) hlower3
  have hmono3 := canonicalShadow_mono 3 (by omega) hlower3
  have hshell3 := canonicalShadow_add_shell
    (B := 2 * r + 4) (k := 3) (x := residualChain r 3)
    (by omega) (by omega) hnc3
  have hspecial : canonicalShadow 2 ((r + 4).choose 2 + 1) = r + 5 := by
    have hs := canonicalShadow_add_shell
      (B := r + 4) (k := 2) (x := 1) (by omega) (by omega)
        (by simp [Nat.choose_one_right])
    simpa [Nat.choose_one_right, canonicalShadow_one] using hs
  have hresLower : (r + 4).choose 2 + 1 ≤ residualChain r 3 := by
    have := residualChain_three_gt r hr
    omega
  have hshadowLower : r + 5 ≤ canonicalShadow 2 (residualChain r 3) := by
    have hm := canonicalShadow_mono 2 (by omega) hresLower
    rw [hspecial] at hm
    exact hm
  have hM2 : r + (2 * r + 4).choose 2 + (r + 5) ≤
      fullProfileChain r 2 := by
    rw [fullProfileChain_step r 2 (by omega)]
    calc
      r + (2 * r + 4).choose 2 + (r + 5) ≤
          r + ((2 * r + 4).choose 2 +
            canonicalShadow 2 (residualChain r 3)) := by omega
      _ = r + canonicalShadow 3
          ((2 * r + 4).choose 3 + residualChain r 3) := by
            rw [hshell3]
      _ ≤ r + canonicalShadow 3 (fullProfileChain r 3) :=
        Nat.add_le_add_left hmono3 r
  have hp2 : (2 * r + 5).choose 2 =
      (2 * r + 4).choose 1 + (2 * r + 4).choose 2 := by
    simpa only [Nat.succ_eq_add_one,
      show 2 * r + 4 + 1 = 2 * r + 5 by omega] using
        Nat.choose_succ_succ (2 * r + 4) 1
  have hcap2 := hcap 2 le_rfl (by omega)
  rw [hp2, Nat.choose_one_right] at hcap2
  omega

/--
Semantic endpoint: under the upper-core interface, no antichain on
`2*r+5` points can carry `r` members on every level `2,...,2*r+3`.
-/
theorem full_multiplicity_profile_infeasible
    (r : ℕ) (hr : 29 ≤ r) {x : ℕ → ℕ} {e : ℕ}
    (hx : IsUpperCoreRecurrence r x)
    (hx3 : x 3 = (r + 4).choose 3 + e) (he : 1 ≤ e) :
    ¬ ∃ F : Erdos776.Antichain.Family (Fin (2 * r + 5)),
      Erdos776.Antichain.IsSperner F ∧
        ∀ i, 2 ≤ i → i ≤ 2 * r + 3 →
          r ≤ (Erdos776.Antichain.level F i).card := by
  rintro ⟨F, hanti, hprofile⟩
  have hrec := profileChain_isProfileRecurrence_of_antichain
    (n := 2 * r + 5) (lo := 2) (hi := 2 * r + 3)
    (f := fun _ => r) (F := F) hanti hprofile
  obtain ⟨i, hi2, hii, hover⟩ :=
    fullProfileChain_overflows r hr hx hx3 he
  have hcap := hrec.2.2 i hi2 (by omega)
  change fullProfileChain r i ≤ (2 * r + 5).choose i at hcap
  omega

/--
The same semantic endpoint stated directly with the two facts supplied by the
upper-core computation in the research package.
-/
theorem upperCore_full_multiplicity_profile_infeasible
    (r : ℕ) (hr : 29 ≤ r) {e : ℕ}
    (hstrict : ∀ b, 4 ≤ b → b ≤ r + 2 →
      upperCoreChain r b < (r + 4).choose b)
    (hexcess : upperCoreChain r 3 = (r + 4).choose 3 + e)
    (he : 1 ≤ e) :
    ¬ ∃ F : Erdos776.Antichain.Family (Fin (2 * r + 5)),
      Erdos776.Antichain.IsSperner F ∧
        ∀ i, 2 ≤ i → i ≤ 2 * r + 3 →
          r ≤ (Erdos776.Antichain.level F i).card := by
  exact full_multiplicity_profile_infeasible r hr
    (upperCoreChain_isUpperCoreRecurrence r hstrict) hexcess he

/--
Certificate-facing form: ordinary upper-core feasibility and the manuscript's
bound `1 ≤ e ≤ 6` supply every hypothesis of the symbolic obstruction.
-/
theorem upperCore_fit_full_multiplicity_profile_infeasible
    (r : ℕ) (hr : 29 ≤ r) {e : ℕ}
    (hfit : ∀ b, 4 ≤ b → b ≤ r + 2 →
      upperCoreChain r b ≤ (r + 4).choose b)
    (hexcess : upperCoreChain r 3 = (r + 4).choose 3 + e)
    (heLower : 1 ≤ e) (heUpper : e ≤ 6) :
    ¬ ∃ F : Erdos776.Antichain.Family (Fin (2 * r + 5)),
      Erdos776.Antichain.IsSperner F ∧
        ∀ i, 2 ≤ i → i ≤ 2 * r + 3 →
          r ≤ (Erdos776.Antichain.level F i).card := by
  apply upperCore_full_multiplicity_profile_infeasible r hr
      (e := e) ?_ hexcess heLower
  exact upperCoreChain_strict_of_fit r (by omega) hfit hexcess (by omega)

end Erdos776.Uniform
