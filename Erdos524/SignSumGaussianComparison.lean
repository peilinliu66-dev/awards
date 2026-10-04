import Erdos524.GaussianPolynomialLaw
import Erdos524.FiniteCDFReplacement
import Erdos524.PolynomialFiniteComparison
import Erdos524.GaussianTailLower

namespace Erdos524.SignSumGaussianComparison
open MeasureTheory ProbabilityTheory Matrix WithLp Set
open Erdos524.GaussianPolynomialLaw Erdos524.FiniteCDFReplacement Erdos524.PolynomialFiniteComparison
open Erdos524.SignGaussianMoments Erdos524.SmoothCutoff Erdos524.SmoothedCDFSandwich Erdos524.LinearStatistic

noncomputable def normalizedSum {N : ℕ} (z : Fin N → ℝ) : ℝ := (∑ i, z i)/Real.sqrt (N:ℝ)

theorem normalizedSum_measurable (N : ℕ) : Measurable (normalizedSum (N := N)) := by unfold normalizedSum; fun_prop

theorem gaussian_normalizedSum_law {N : ℕ} (hN : 0<N) :
    (Measure.pi (fun _ : Fin N => gaussianReal 0 1)).map normalizedSum=gaussianReal 0 1 := by
  let A : Matrix (Fin 1) (Fin N) ℝ := fun _ _ => 1/Real.sqrt (N:ℝ)
  have hNp : (0:ℝ)<N := by exact_mod_cast hN
  have hs := Real.sq_sqrt hNp.le
  have hGram : A*Aᵀ=(1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    ext i j
    fin_cases i
    fin_cases j
    change (∑ _k : Fin N, (1/Real.sqrt (N:ℝ))*(1/Real.sqrt (N:ℝ)))=1
    simp only [div_mul_div_comm,one_mul,← pow_two,hs,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp
    exact hs.symm
  have h := gaussian_pi_linear_map A
  rw [hGram] at h
  have hh := congrArg (fun μ : Measure (Fin 1 → ℝ) => μ.map (fun z => z 0)) h
  rw [Measure.map_map (by fun_prop) (by fun_prop),Measure.map_map (by fun_prop) (by fun_prop)] at hh
  have hEval := (measurePreserving_eval_multivariateGaussian (μ := (0 : EuclideanSpace ℝ (Fin 1))) (S := (1 : Matrix (Fin 1) (Fin 1) ℝ)) Matrix.PosSemidef.one (i := 0)).map_eq
  simp only [Pi.zero_apply,Matrix.one_apply,ite_true,Real.toNNReal_one] at hEval
  change (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) (1 : Matrix (Fin 1) (Fin 1) ℝ)).map (fun x => x 0)=gaussianReal 0 1 at hEval
  simp only [Function.comp_def] at hh
  rw [hEval] at hh
  have he : (fun z : Fin N → ℝ => (A*ᵥz) 0)=normalizedSum := by
    funext z
    simp only [Matrix.mulVec,dotProduct,A,normalizedSum]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rwa [he] at hh

theorem normalizedSum_cdf_compare {n : ℕ} {C η : ℝ} (hC : 0≤C) (hη : 0<η)
    (hcut : ∀ j : Fin 4, ∀ x : ℝ, ‖iteratedDeriv (j.val+1) cutoff x‖≤C) (x : ℝ) :
    (Measure.pi (fun _ : Fin (n+1) => signLaw)).real {z | normalizedSum z≤x}≤
      (gaussianReal 0 1).real (Iic (x+2*η))+((75/6:ℝ)*C)/((n+1:ℝ)*η^4) := by
  let c : Fin (n+1) → Fin 1 → ℝ := fun _ _ => 1/Real.sqrt ((n+1:ℕ):ℝ)
  let a : Fin (n+1) → ℝ := fun _ => 1/Real.sqrt ((n+1:ℕ):ℝ)
  have h := finite_cdf_replacement (by norm_num : 0<1) (b := 1) le_rfl hη hC (by norm_num) hcut x c a
    (by intro i; dsimp [a]; positivity) (by intro i j; dsimp [c,a]; rw [abs_of_nonneg (by positivity)])
  dsimp only at h
  have he (r : ℝ) : coordBox c r={z | normalizedSum z≤r} := by
    ext z
    simp only [coordBox,Set.mem_setOf_eq,Fin.forall_fin_one,linearStatistic,c,normalizedSum,mul_one_div,← Finset.sum_div]
  simp_rw [he] at h
  have ha : (∑ i, (a i)^4)=1/((n+1:ℕ):ℝ) := constant_fourth_sum (by omega)
  rw [ha] at h
  have hg := congrArg (fun μ : Measure ℝ => μ.real (Iic (x+2*η))) (gaussian_normalizedSum_law (by omega : 0<n+1))
  unfold Measure.real at hg
  rw [Measure.map_apply (normalizedSum_measurable _) measurableSet_Iic] at hg
  change (Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)).real {z | normalizedSum z≤x+2*η}=_ at hg
  rw [hg] at h
  have hE : ((75/6:ℝ)*C*1^3/η^4)*(1/((n+1:ℕ):ℝ))=((75/6:ℝ)*C)/((n+1:ℝ)*η^4) := by push_cast; field_simp
  simpa only [hE,Measure.real] using h.2

theorem normalizedSum_tail_compare {n : ℕ} {C η : ℝ} (hC : 0≤C) (hη : 0<η)
    (hcut : ∀ j : Fin 4, ∀ x : ℝ, ‖iteratedDeriv (j.val+1) cutoff x‖≤C) (x : ℝ) :
    (gaussianReal 0 1).real (Ioi (x+2*η))-((75/6:ℝ)*C)/((n+1:ℝ)*η^4)≤
      (Measure.pi (fun _ : Fin (n+1) => signLaw)).real {z | x<normalizedSum z} := by
  have h := normalizedSum_cdf_compare (n := n) hC hη hcut x
  have he : {z : Fin (n+1) → ℝ | x<normalizedSum z}={z | normalizedSum z≤x}ᶜ := by ext z; simp
  rw [he,measureReal_compl (measurableSet_le (normalizedSum_measurable _) measurable_const),probReal_univ,
    ← compl_Iic,measureReal_compl measurableSet_Iic,probReal_univ]
  linarith

theorem exists_universal_sum_tail_constant : ∃ D : ℝ, 0<D ∧ ∀ {N : ℕ}, 0<N → ∀ {η : ℝ}, 0<η → ∀ x : ℝ,
    (gaussianReal 0 1).real (Ioi (x+2*η))-D/((N:ℝ)*η^4)≤
      (Measure.pi (fun _ : Fin N => signLaw)).real {z | x<normalizedSum z} := by
  obtain ⟨C,hC,hcut⟩ := exists_cutoff_derivative_bound
  refine ⟨(75/6:ℝ)*C,by positivity,?_⟩
  intro N hN η hη x
  cases N with
  | zero => omega
  | succ n => simpa only [Nat.cast_add,Nat.cast_one] using normalizedSum_tail_compare (by linarith) hη hcut x

theorem exists_exponential_sum_tail_constant : ∃ D : ℝ, 0<D ∧ ∀ {N : ℕ}, 0<N → ∀ x : ℝ,
    (gaussianReal 0 1).real (Ioi (x+2*Real.exp (-Real.log (N:ℝ)/8)))-D*Real.exp (-Real.log (N:ℝ)/2)≤
      (Measure.pi (fun _ : Fin N => signLaw)).real {z | x<normalizedSum z} := by
  obtain ⟨D,hD,h⟩ := exists_universal_sum_tail_constant
  refine ⟨D,hD,?_⟩
  intro N hN x
  have hNp : (0:ℝ)<N := by exact_mod_cast hN
  have hh := h hN (Real.exp_pos (-Real.log (N:ℝ)/8)) x
  have hpow : (Real.exp (-Real.log (N:ℝ)/8))^4=Real.exp (-Real.log (N:ℝ)/2) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  have he : (N:ℝ)*Real.exp (-Real.log (N:ℝ)/2)=Real.exp (Real.log (N:ℝ)/2) := by
    conv_lhs => lhs; rw [← Real.exp_log hNp]
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hpow,he] at hh
  have hDexp : D/Real.exp (Real.log (N:ℝ)/2)=D*Real.exp (-Real.log (N:ℝ)/2) := by rw [div_eq_mul_inv,← Real.exp_neg]; congr 2; ring
  rw [hDexp] at hh
  exact hh

end Erdos524.SignSumGaussianComparison
