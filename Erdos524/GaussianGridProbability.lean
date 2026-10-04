import Erdos524.GaussianGridOscillation
import Erdos524.PolynomialFullProbability
import Erdos524.FiniteGaussianCubes

namespace Erdos524.GaussianGridProbability
open MeasureTheory ProbabilityTheory Matrix WithLp Set Filter
open Erdos524.GaussianGridOscillation Erdos524.LaplaceKernelComparison
open Erdos524.GaussianCoordinateProjection Erdos524.FiniteCouplingComparison
open Erdos524.GramGaussianCoupling

noncomputable def kernelProbability {m : ℕ} (u : Fin m → ℝ) (r : ℝ) : ℝ :=
  gramBoxProbability (fun i => laplace (u i)) intervalMeasure r

theorem kernel_projection_measure {n m : ℕ} (u : Fin n → ℝ) (hu : ∀ i, 0≤u i)
    (f : Fin m → Fin n) (B : Set (Fin m → ℝ)) (hB : MeasurableSet B) :
    (multivariateGaussian 0 (finiteKernel u)) ((fun z => fun i => z (f i)) ⁻¹' B)=
      (multivariateGaussian 0 (finiteKernel (fun i => u (f i)))) (ofLp ⁻¹' B) := by
  have h := gaussian_coordinate_projection (finiteKernel_posSemidef u hu) f
  have he : (finiteKernel u).submatrix f f=finiteKernel (fun i => u (f i)) := by ext i j; rfl
  rw [he] at h
  have hm := congrArg (fun μ : Measure (Fin m → ℝ) => μ B) h
  rw [Measure.map_apply (by fun_prop) hB,Measure.map_apply (by fun_prop) hB] at hm
  exact hm

theorem kernel_projection_probability {n m : ℕ} (u : Fin n → ℝ) (hu : ∀ i, 0≤u i)
    (f : Fin m → Fin n) (r : ℝ) :
    (multivariateGaussian 0 (finiteKernel u)).real {z | ∀ i, |z (f i)|≤r}=kernelProbability (fun i => u (f i)) r := by
  have h := kernel_projection_measure u hu f (box id r) (box_measurable id (by intro i; fun_prop) r)
  exact congrArg ENNReal.toReal h

theorem grid_probability_le_core {m : ℕ} (J : ℕ) {h η : ℝ} (hh : 0<h) (hη : 0<η)
    (u : Fin m → ℝ) (hu : ∀ i, 0≤u i) (hub : ∀ i, u i≤(J:ℝ)*h) (r : ℝ) :
    kernelProbability (gridPoints J h) r≤kernelProbability u (r+η)+Real.sqrt (2*(Real.exp 1)^2*h)/η := by
  obtain ⟨W,hWm,hWi,hW0,hWb,hWE⟩ := exists_grid_oscillation J hh u hu hub
  let P := jointMeasure J h u
  let A : Set (EuclideanSpace ℝ (Fin ((J+1)+m))) := {z | ∀ j : Fin (J+1), |z (Fin.castAdd m j)|≤r}
  let B : Set (EuclideanSpace ℝ (Fin ((J+1)+m))) := {z | ∀ i : Fin m, |z (Fin.natAdd (J+1) i)|≤r+η}
  let D := {z | η≤W z}
  have hs : A⊆B∪D := by
    intro z hz
    by_cases hd : z∈D
    · exact Or.inr hd
    · left
      intro i
      obtain ⟨j,hj⟩ := hWb z i
      have hw : W z<η := lt_of_not_ge hd
      have ht := abs_add_le (z (Fin.natAdd (J+1) i)-z (Fin.castAdd m j)) (z (Fin.castAdd m j))
      rw [sub_add_cancel] at ht
      exact ht.trans (by linarith [hz j])
  have hbad := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall hW0) hWi η
  have hDb : P.real D≤Real.sqrt (2*(Real.exp 1)^2*h)/η := by
    apply (le_div_iff₀ hη).mpr
    change η*P.real D≤_ at hbad
    nlinarith
  have hAp := kernel_projection_probability (jointPoints J h u) (jointPoints_nonneg J hh.le u hu) (Fin.castAdd m) r
  have hBp := kernel_projection_probability (jointPoints J h u) (jointPoints_nonneg J hh.le u hu) (Fin.natAdd (J+1)) (r+η)
  have hfa : (fun j => jointPoints J h u (Fin.castAdd m j))=gridPoints J h := by funext j; simp only [jointPoints,Fin.addCases_left]
  have hfb : (fun i => jointPoints J h u (Fin.natAdd (J+1) i))=u := by funext i; simp only [jointPoints,Fin.addCases_right]
  rw [hfa] at hAp
  rw [hfb] at hBp
  change P.real A=kernelProbability (gridPoints J h) r at hAp
  change P.real B=kernelProbability u (r+η) at hBp
  rw [← hAp,← hBp]
  exact (measureReal_mono hs).trans ((measureReal_union_le B D).trans (add_le_add le_rfl hDb))

theorem kernel_projection_complement_probability {n m : ℕ} (u : Fin n → ℝ) (hu : ∀ i, 0≤u i)
    (f : Fin m → Fin n) (r : ℝ) :
    (multivariateGaussian 0 (finiteKernel u)).real {z | ¬∀ i, |z (f i)|≤r}=
      (multivariateGaussian 0 (finiteKernel (fun i => u (f i)))).real {z | ¬∀ i, |z i|≤r} := by
  have h := kernel_projection_measure u hu f (box id r)ᶜ (box_measurable id (by intro i; fun_prop) r).compl
  exact congrArg ENNReal.toReal h

theorem kernel_tail_complement_probability {m : ℕ} (u : Fin m → ℝ) {T r : ℝ}
    (hT : 0≤T) (hu : ∀ i, T≤u i) (hr : 0<r) :
    (multivariateGaussian 0 (finiteKernel u)).real {z | ¬∀ i, |z i|≤r}≤Real.exp 1/(r*Real.sqrt (T+1)) := by
  have h := Erdos524.FiniteGaussianCubes.finiteKernel_cube_compl_tail u hT hu hr
  have he : {z : EuclideanSpace ℝ (Fin m) | ¬∀ i, |z i|≤r}=(ofLp ⁻¹' Erdos524.FiniteGaussianCubes.cube m r)ᶜ := by
    ext z
    simp only [Set.mem_setOf_eq,Set.mem_compl_iff,Set.mem_preimage,Erdos524.FiniteGaussianCubes.cube,
      Set.mem_pi,Set.mem_univ,true_implies,Set.mem_Icc,abs_le]
  have ht := ENNReal.toReal_mono (by finiteness) h
  rw [ENNReal.toReal_ofReal (by positivity : 0≤Real.exp 1/(r*Real.sqrt (T+1)))] at ht
  unfold Measure.real
  rw [he]
  exact ht

theorem grid_probability_le_arbitrary {m : ℕ} (J : ℕ) {h η r : ℝ} (hh : 0<h) (hη : 0<η)
    (hrη : 0<r+η) (u : Fin m → ℝ) (hu : ∀ i, 0≤u i) :
    kernelProbability (gridPoints J h) r≤kernelProbability u (r+η)+Real.sqrt (2*(Real.exp 1)^2*h)/η+
      Real.exp 1/((r+η)*Real.sqrt ((J:ℝ)*h+1)) := by
  classical
  let s : Finset (Fin m) := Finset.univ.filter (fun i => u i≤(J:ℝ)*h)
  let f : Fin s.card → Fin m := fun k => (s.equivFin.symm k).val
  let g : Fin sᶜ.card → Fin m := fun k => (sᶜ.equivFin.symm k).val
  have hf (k : Fin s.card) : u (f k)≤(J:ℝ)*h := (Finset.mem_filter.mp (s.equivFin.symm k).property).2
  have hg (k : Fin sᶜ.card) : (J:ℝ)*h≤u (g k) := by
    have hn : g k∉s := Finset.mem_compl.mp (sᶜ.equivFin.symm k).property
    by_contra h
    exact hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _,(lt_of_not_ge h).le⟩)
  have hc := grid_probability_le_core J hh hη (fun i => u (f i)) (fun i => hu (f i)) hf r
  let P := multivariateGaussian 0 (finiteKernel u)
  let A : Set (EuclideanSpace ℝ (Fin m)) := {z | ∀ i, |z (f i)|≤r+η}
  let B : Set (EuclideanSpace ℝ (Fin m)) := {z | ¬∀ i, |z (g i)|≤r+η}
  let C : Set (EuclideanSpace ℝ (Fin m)) := {z | ∀ i, |z i|≤r+η}
  have hs : A⊆C∪B := by
    intro z hz
    by_cases hb : z∈B
    · exact Or.inr hb
    · left
      have htail : ∀ i, |z (g i)|≤r+η := Classical.not_not.mp hb
      intro i
      by_cases hi : i∈s
      · let k := s.equivFin ⟨i,hi⟩
        have he : f k=i := congrArg Subtype.val (s.equivFin.symm_apply_apply ⟨i,hi⟩)
        simpa only [he] using hz k
      · have hi' : i∈sᶜ := Finset.mem_compl.mpr hi
        let k := sᶜ.equivFin ⟨i,hi'⟩
        have he : g k=i := congrArg Subtype.val (sᶜ.equivFin.symm_apply_apply ⟨i,hi'⟩)
        simpa only [he] using htail k
  have hAp := kernel_projection_probability u hu f (r+η)
  have hBp := kernel_projection_complement_probability u hu g (r+η)
  have hBt := kernel_tail_complement_probability (fun i => u (g i)) (by positivity : (0:ℝ)≤(J:ℝ)*h) hg hrη
  change P.real A=kernelProbability (fun i => u (f i)) (r+η) at hAp
  change P.real B=_ at hBp
  rw [← hBp] at hBt
  have hbound := (measureReal_mono (μ := P) hs).trans (measureReal_union_le C B)
  rw [hAp] at hbound
  change kernelProbability (fun i => u (f i)) (r+η)≤kernelProbability u (r+η)+P.real B at hbound
  linarith

end Erdos524.GaussianGridProbability
