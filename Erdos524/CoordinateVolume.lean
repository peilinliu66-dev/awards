import Erdos524.CoordinateSymmetrization
import Erdos524.ProductFiberVolume
import Mathlib.MeasureTheory.Constructions.Pi

/-!
Coordinate volume transport for the finite symmetrization argument.
This module is under active compilation; it is not the final probability theorem.
-/

namespace Erdos524.CoordinateVolume

open Set MeasureTheory
open Erdos524.CoordinateSymmetrization
open Erdos524.ProductFiberVolume

variable {n : ℕ}

def splitCoord (i : Fin (n + 1)) :
    (Fin (n + 1) → ℝ) ≃ᵐ ℝ × (Fin n → ℝ) :=
  MeasurableEquiv.piFinSuccAbove (fun _ ↦ ℝ) i

@[simp] theorem splitCoord_apply (i : Fin (n + 1)) (x : Fin (n + 1) → ℝ) :
    splitCoord i x = (x i, fun j ↦ x (i.succAbove j)) := rfl

def splitLinear (i : Fin (n + 1)) :
    (Fin (n + 1) → ℝ) →ₗ[ℝ] ℝ × (Fin n → ℝ) where
  toFun := splitCoord i
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

theorem continuous_splitCoord (i : Fin (n + 1)) : Continuous (splitCoord i) := by
  change Continuous (fun x : Fin (n + 1) → ℝ ↦ (x i, fun j ↦ x (i.succAbove j)))
  fun_prop

theorem volume_splitCoord_image (i : Fin (n + 1))
    (A : Set (Fin (n + 1) → ℝ)) :
    volume (splitCoord i '' A) = volume A := by
  have he : MeasurePreserving (splitCoord i) :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) i
  have h := he.measure_preimage_equiv (splitCoord i '' A)
  simpa only [Set.preimage_image_eq _ (splitCoord i).injective] using h.symm

theorem splitCoord_centerFiber (i : Fin (n + 1)) (p q : Fin (n + 1) → ℝ) :
    splitCoord i (centerFiber i p q) =
      ((p i - q i) / 2, (splitCoord i p).2) := by
  apply Prod.ext
  · simp [centerFiber]
  · funext j
    simp [centerFiber, Fin.succAbove_ne]

theorem splitCoord_symm_image (i : Fin (n + 1))
    (A : Set (Fin (n + 1) → ℝ)) :
    splitCoord i '' symm i A = fiberSymm (splitCoord i '' A) := by
  ext y
  constructor
  · rintro ⟨x, ⟨p, hp, q, hq, hpq, rfl⟩, rfl⟩
    rw [splitCoord_centerFiber]
    change ∃ u, (u, (splitCoord i p).2) ∈ splitCoord i '' A ∧
      ∃ v, (v, (splitCoord i p).2) ∈ splitCoord i '' A ∧ (u - v) / 2 = (p i - q i) / 2
    refine ⟨p i, ⟨p, hp, rfl⟩, q i, ⟨q, hq, ?_⟩, rfl⟩
    apply Prod.ext
    · rfl
    · funext j
      exact (hpq (i.succAbove j) (Fin.succAbove_ne i j)).symm
  · rcases y with ⟨t, z⟩
    rintro ⟨u, ⟨p, hp, hpu⟩, v, ⟨q, hq, hqv⟩, huv⟩
    have hp0 : p i = u := congrArg Prod.fst hpu
    have hq0 : q i = v := congrArg Prod.fst hqv
    have hpz : (splitCoord i p).2 = z := congrArg Prod.snd hpu
    have hqz : (splitCoord i q).2 = z := congrArg Prod.snd hqv
    refine ⟨centerFiber i p q, ⟨p, hp, q, hq, ?_, rfl⟩, ?_⟩
    · intro j hji
      obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hji
      exact (congrFun hpz k).trans (congrFun hqz k).symm
    · rw [splitCoord_centerFiber, hp0, hq0, hpz, huv]

theorem volume_symm (i : Fin (n + 1))
    {A : Set (Fin (n + 1) → ℝ)} (hcompact : IsCompact A)
    (hconvex : Convex ℝ A) : volume (symm i A) = volume A := by
  have hc : IsCompact (splitCoord i '' A) := hcompact.image (continuous_splitCoord i)
  have hv : Convex ℝ (splitCoord i '' A) := hconvex.linear_image (splitLinear i)
  calc
    volume (symm i A) = volume (splitCoord i '' symm i A) :=
      (volume_splitCoord_image i _).symm
    _ = volume (fiberSymm (splitCoord i '' A)) := by rw [splitCoord_symm_image]
    _ = volume (splitCoord i '' A) := prod_measure_fiberSymm volume hc hv
    _ = volume A := volume_splitCoord_image i A

theorem volume_symmList (is : List (Fin (n + 1)))
    {A : Set (Fin (n + 1) → ℝ)} (hcompact : IsCompact A)
    (hconvex : Convex ℝ A) : volume (symmList is A) = volume A := by
  induction is generalizing A with
  | nil => rfl
  | cons i is ih =>
    change volume (symmList is (symm i A)) = volume A
    exact (ih (isCompact_symm i hcompact) (convex_symm i hconvex)).trans
      (volume_symm i hcompact hconvex)

end Erdos524.CoordinateVolume
