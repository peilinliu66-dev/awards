import Erdos524.OneDimensionalFibers
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Product-fiber symmetrization preserves product measure

This compiled module supplies the Fubini step on
`ℝ × E`; transport to a chosen coordinate of `Fin n → ℝ` is separate.
-/

namespace Erdos524.ProductFiberVolume

open Set MeasureTheory
open Erdos524.OneDimensionalFibers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

def fiber (A : Set (ℝ × E)) (y : E) : Set ℝ :=
  {t | (t, y) ∈ A}

def fiberSymm (A : Set (ℝ × E)) : Set (ℝ × E) :=
  {z | z.1 ∈ halfDifference (fiber A z.2)}

theorem fiber_eq_image (A : Set (ℝ × E)) (y : E) :
    fiber A y = Prod.fst '' (A ∩ Prod.snd ⁻¹' {y}) := by
  ext t
  constructor
  · intro ht
    exact ⟨(t, y), ⟨ht, rfl⟩, rfl⟩
  · rintro ⟨⟨s, z⟩, ⟨hsz, hz⟩, hst⟩
    change z = y at hz
    change s = t at hst
    simpa [fiber, hz, hst] using hsz

theorem isCompact_fiber {A : Set (ℝ × E)} (hA : IsCompact A) (y : E) :
    IsCompact (fiber A y) := by
  rw [fiber_eq_image]
  exact (hA.inter_right (isClosed_singleton.preimage continuous_snd)).image
    continuous_fst

theorem convex_fiber {A : Set (ℝ × E)} (hA : Convex ℝ A) (y : E) :
    Convex ℝ (fiber A y) := by
  intro u hu v hv a b ha hb hab
  have hmem := hA hu hv ha hb hab
  have hy : a • y + b • y = y := by rw [← add_smul, hab, one_smul]
  simpa only [fiber, Set.mem_setOf_eq, Prod.smul_mk, Prod.mk_add_mk,
    smul_eq_mul, hy] using hmem

theorem fiberSymm_eq_image (A : Set (ℝ × E)) :
    fiberSymm A =
      (fun z : (ℝ × E) × (ℝ × E) ↦ ((z.1.1 - z.2.1) / 2, z.1.2)) ''
        ((A ×ˢ A) ∩ {z | z.1.2 = z.2.2}) := by
  ext x
  constructor
  · rintro ⟨u, hu, v, hv, huv⟩
    refine ⟨((u, x.2), (v, x.2)), ⟨⟨hu, hv⟩, rfl⟩, ?_⟩
    exact Prod.ext huv rfl
  · rintro ⟨⟨⟨u, y⟩, ⟨v, z⟩⟩, ⟨⟨huy, hvz⟩, hyz⟩, rfl⟩
    change y = z at hyz
    subst z
    exact ⟨u, huy, v, hvz, rfl⟩

theorem isCompact_fiberSymm {A : Set (ℝ × E)} (hA : IsCompact A) :
    IsCompact (fiberSymm A) := by
  rw [fiberSymm_eq_image]
  apply ((hA.prod hA).inter_right (isClosed_eq (by fun_prop) (by fun_prop))).image
  fun_prop

/-- Fiber length equality is integrated directly. There is no measurable
choice of endpoints, and the measure on the other coordinates is arbitrary. -/
theorem prod_measure_fiberSymm (ν : Measure E) [SFinite ν]
    {A : Set (ℝ × E)} (hcompact : IsCompact A) (hconvex : Convex ℝ A) :
    (volume.prod ν) (fiberSymm A) = (volume.prod ν) A := by
  rw [Measure.prod_apply_symm (isCompact_fiberSymm hcompact).measurableSet,
    Measure.prod_apply_symm hcompact.measurableSet]
  apply lintegral_congr_ae
  exact Filter.Eventually.of_forall fun y ↦
    volume_halfDifference (isCompact_fiber hcompact y) (convex_fiber hconvex y)

end Erdos524.ProductFiberVolume
