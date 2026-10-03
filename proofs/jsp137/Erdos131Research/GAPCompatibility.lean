/-
Copyright (c) 2026. Released under Apache 2.0.
Original conversions between two separately obtained GAP interfaces.
The Nondividing dependency is Theofil Xeff's erdos_131 repository at
aeafec6479cf23b584a65fce6cb6dc1005be3b1f. Its source is not included here.
The Erdos186 dependency is plby/lean-proofs at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e.
Compiled and audited; Lean 4.33.0 / Mathlib db584cd6d46c92f209a44c0f1c829460d327499d.
-/
import Nondividing.GAP
import ErdosProblems.Erdos186.DiscreteJohn
import ErdosProblems.Erdos186.CFP.SymmetricGAP

open scoped BigOperators

namespace Erdos131Research

noncomputable section
open Nondividing

theorem centered_eq_symmetricGAP {d r : ℕ} (P : Erdos186.GAP d r)
    (radii : Fin r → ℕ) (hP : P.Centered radii) :
    P = Erdos186.DiscreteJohn.symmetricGAP P.steps radii := by
  cases P with
  | mk offset steps widths hwidth =>
    obtain ⟨hw, ho⟩ := hP
    dsimp at hw ho
    subst widths
    subst offset
    rfl

/-- Centering one-sided coordinates gives the literal signed coefficient box. -/
theorem mem_symmetricGAP_iff {d r : ℕ}
    (steps : Fin r → Fin d → ℤ) (radii : Fin r → ℕ) (v : Fin d → ℤ) :
    v ∈ (Erdos186.DiscreteJohn.symmetricGAP steps radii).carrier ↔
      ∃ z ∈ coordinateBox radii,
        Erdos186.DiscreteJohn.integerCombination steps z = v := by
  classical
  constructor
  · intro hv
    obtain ⟨n, hn⟩ := Erdos186.GAP.mem_carrier_iff.mp hv
    refine ⟨fun i => (n i : ℤ) - radii i, ?_, ?_⟩
    · rw [mem_coordinateBox]
      intro i
      have hi := (n i).isLt
      change (n i : ℕ) < 2 * radii i + 1 at hi
      constructor <;> omega
    · rwa [Erdos186.DiscreteJohn.symmetricGAP_coordPoint] at hn
  · rintro ⟨z, hz, hval⟩
    have hz' := mem_coordinateBox.mp hz
    let n : (Erdos186.DiscreteJohn.symmetricGAP steps radii).Coord :=
      fun i => ⟨(z i + (radii i : ℤ)).toNat, by
        have := hz' i
        change (z i + (radii i : ℤ)).toNat < 2 * radii i + 1
        omega⟩
    refine Erdos186.GAP.mem_carrier_iff.mpr ⟨n, ?_⟩
    rw [Erdos186.DiscreteJohn.symmetricGAP_coordPoint]
    have hcoeff : (fun i => (n i : ℤ) - (radii i : ℤ)) = z := by
      funext i
      have := hz' i
      dsimp [n]
      omega
    rw [hcoeff]
    exact hval

/-- The signed image and the one-sided centered carrier are exactly equal. -/
theorem symmetricGAP_carrier_eq_image {d r : ℕ}
    (steps : Fin r → Fin d → ℤ) (radii : Fin r → ℕ) :
    (Erdos186.DiscreteJohn.symmetricGAP steps radii).carrier =
      (coordinateBox radii).image (Erdos186.DiscreteJohn.integerCombination steps) := by
  classical
  ext v
  rw [mem_symmetricGAP_iff]
  exact Finset.mem_image.symm

/-- Properness in the existing finite API implies injectivity on signed coordinates. -/
theorem signed_injOn_of_symmetricGAP_proper {d r : ℕ}
    (steps : Fin r → Fin d → ℤ) (radii : Fin r → ℕ)
    (hproper : (Erdos186.DiscreteJohn.symmetricGAP steps radii).Proper) :
    Set.InjOn (Erdos186.DiscreteJohn.integerCombination steps)
      (coordinateBox radii : Set (Fin r → ℤ)) := by
  classical
  apply Finset.card_image_iff.mp
  rw [← symmetricGAP_carrier_eq_image,
    Erdos186.GAP.card_carrier_eq_volume _ hproper,
    Erdos186.DiscreteJohn.symmetricGAP_volume, card_coordinateBox]

/-- Construct the positive-radius display used in the projective argument. -/
def positiveGAP {d r : ℕ} (steps : Fin r → Fin d → ℤ)
    (radii : Fin r → ℕ) (hpos : ∀ i, 0 < radii i) : Nondividing.GAP d r :=
  ⟨steps, radii, hpos⟩

theorem positiveGAP_carrier {d r : ℕ} (steps : Fin r → Fin d → ℤ)
    (radii : Fin r → ℕ) (hpos : ∀ i, 0 < radii i) :
    (positiveGAP steps radii hpos).carrier =
      (Erdos186.DiscreteJohn.symmetricGAP steps radii).carrier := by
  classical
  rw [symmetricGAP_carrier_eq_image]
  rfl

theorem positiveGAP_proper {d r : ℕ} (steps : Fin r → Fin d → ℤ)
    (radii : Fin r → ℕ) (hpos : ∀ i, 0 < radii i)
    (hproper : (Erdos186.DiscreteJohn.symmetricGAP steps radii).Proper) :
    (positiveGAP steps radii hpos).Proper :=
  signed_injOn_of_symmetricGAP_proper steps radii hproper

/-- Real dilates retain the same signed coefficient interpretation, including floor. -/
theorem positiveGAP_dilatedCarrier {d r : ℕ} (steps : Fin r → Fin d → ℤ)
    (radii : Fin r → ℕ) (hpos : ∀ i, 0 < radii i) (t : ℝ) :
    (positiveGAP steps radii hpos).dilatedCarrier t =
      (Erdos186.DiscreteJohn.symmetricGAP steps
        (fun i => ⌊t * (radii i : ℝ)⌋₊)).carrier := by
  rw [symmetricGAP_carrier_eq_image]
  rfl

theorem symmetricGAP_carrier_mono {d r : ℕ}
    (steps : Fin r → Fin d → ℤ) {a b : Fin r → ℕ}
    (hab : ∀ i, a i ≤ b i) :
    (Erdos186.DiscreteJohn.symmetricGAP steps a).carrier ⊆
      (Erdos186.DiscreteJohn.symmetricGAP steps b).carrier := by
  intro v hv
  obtain ⟨z, hz, hval⟩ := (mem_symmetricGAP_iff steps a v).mp hv
  refine (mem_symmetricGAP_iff steps b v).mpr ⟨z, ?_, hval⟩
  rw [mem_coordinateBox] at hz ⊢
  intro i
  have h := hz i
  have h' := hab i
  constructor <;> omega

end
end Erdos131Research
