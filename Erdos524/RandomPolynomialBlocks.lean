import Erdos524.RandomPolynomialFinite
import Erdos524.FactorialSparseMesh

/-! Actual independence of disjoint fresh coefficient blocks in the infinite sign model. -/

namespace Erdos524.RandomPolynomialModel

open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
open Erdos524.SignGaussianMoments

variable (len : ℕ → ℕ) (f : (j : ℕ) × Fin (len j) → ℕ)

theorem grouped_coordinate_law (hf : Function.Injective f) :
    P.map (fun ω : Ω ↦ fun j i ↦ ω (f ⟨j, i⟩)) =
      Measure.infinitePi (fun j ↦ Measure.pi (fun _ : Fin (len j) ↦ signLaw)) := by
  have hflat := Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ ↦ signLaw) hf
  let c := MeasurableEquiv.piCurry (fun (j : ℕ) (_ : Fin (len j)) ↦ ℝ)
  have h := congrArg (fun μ : Measure ((p : (j : ℕ) × Fin (len j)) → ℝ) ↦ μ.map c) hflat
  rw [Measure.map_map c.measurable (by fun_prop)] at h
  rw [Measure.infinitePi_map_piCurry (fun (j : ℕ) (_ : Fin (len j)) ↦ signLaw)] at h
  simp only [Measure.infinitePi_eq_pi] at h
  exact h

theorem grouped_coordinates_independent (hf : Function.Injective f) :
    iIndepFun (fun j ↦ fun ω : Ω ↦ fun i ↦ ω (f ⟨j, i⟩)) P := by
  apply (iIndepFun_iff_map_fun_eq_infinitePi_map (fun _ ↦ by fun_prop)).mpr
  rw [grouped_coordinate_law len f hf]
  congr 1
  funext j
  symm
  apply finite_marginal_law
  intro i k hik
  have he := hf hik
  exact Sigma.mk.inj_iff.mp he |>.2 |> eq_of_heq

theorem consecutive_block_coordinate_injective (g : ℕ → ℕ) (hg : StrictMono g) :
    Function.Injective (fun p : (j : ℕ) × Fin (g (j + 1) - g j) ↦ g p.1 + p.2.val) := by
  rintro ⟨j, i⟩ ⟨k, l⟩ he
  have hi := i.isLt
  have hl := l.isLt
  have hij : g j ≤ g (j + 1) := hg.monotone (Nat.le_succ j)
  have hkl : g k ≤ g (k + 1) := hg.monotone (Nat.le_succ k)
  have hjk : j = k := by
    rcases lt_trichotomy j k with h | h | h
    · have hmono := hg.monotone (show j + 1 ≤ k by omega)
      dsimp at he
      omega
    · exact h
    · have hmono := hg.monotone (show k + 1 ≤ j by omega)
      dsimp at he
      omega
  subst k
  have hil : i = l := by apply Fin.ext; dsimp at he; omega
  subst l
  rfl

theorem consecutive_blocks_independent (g : ℕ → ℕ) (hg : StrictMono g) :
    iIndepFun (fun j ↦ finiteBlock (g j) (g (j + 1) - g j)) P :=
  grouped_coordinates_independent (fun j ↦ g (j + 1) - g j)
    (fun p ↦ g p.1 + p.2.val) (consecutive_block_coordinate_injective g hg)

theorem freshNorms_independent (g : ℕ → ℕ) (hg : StrictMono g) :
    iIndepFun (fun j ↦ freshNorm (g j) (g (j + 1) - g j)) P := by
  exact (consecutive_blocks_independent g hg).comp (fun j ↦ finiteNorm)
    (fun j ↦ measurable_finiteNorm _)

theorem freshNorm_events_independent (g : ℕ → ℕ) (hg : StrictMono g) (R : ℕ → ℝ) :
    iIndepSet (fun j ↦ {ω | freshNorm (g j) (g (j + 1) - g j) ω ≤ R j}) P := by
  have hmeas (j : ℕ) : MeasurableSet {ω | freshNorm (g j) (g (j + 1) - g j) ω ≤ R j} :=
    measurableSet_le (measurable_freshNorm _ _) measurable_const
  apply (iIndepSet_iff_meas_biInter hmeas).mpr
  intro s
  apply (freshNorms_independent g hg).meas_biInter
  intro j hj
  exact measurableSet_Iic.preimage (comap_measurable (freshNorm (g j) (g (j + 1) - g j)))

theorem factorial_fresh_events_independent (R : ℕ → ℝ) :
    iIndepSet (fun j ↦ {ω | freshNorm (Erdos524.FactorialSparseMesh.endpoint j)
      (Erdos524.FactorialSparseMesh.blockLength j) ω ≤ R j}) P :=
  freshNorm_events_independent _ Erdos524.FactorialSparseMesh.endpoint_strictMono R

end Erdos524.RandomPolynomialModel
