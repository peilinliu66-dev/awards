import Erdos524.FiniteChaining
import Mathlib.Analysis.Real.Pi.Bounds
import Erdos524.SignWalkMaximal
import Erdos524.LayercakeDiscrepancy
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

namespace Erdos524.FiniteSignWalk
open MeasureTheory ProbabilityTheory Set Filter
open Erdos524.SignGaussianMoments Erdos524.SignConcentration

noncomputable def walkMax {N : ℕ} (z : Fin N → ℝ) : ℝ := ‖fun k : Fin (N+1) => walkPrefix z k.val‖

theorem walkMax_continuous (N : ℕ) : Continuous (walkMax (N := N)) := by
  apply Continuous.norm
  apply continuous_pi
  intro k
  unfold walkPrefix
  apply continuous_finset_sum
  intro i hi
  split_ifs <;> fun_prop

theorem coordinate_memLp_two {N : ℕ} (i : Fin N) :
    MemLp (fun z : Fin N → ℝ => z i) 2 (Measure.pi (fun _ : Fin N => signLaw)) := by
  have hi : MemLp (id : ℝ → ℝ) 2 signLaw := by
    apply MemLp.of_bound measurable_id.aestronglyMeasurable 1
    filter_upwards [signLaw_ae_interval] with x hx
    exact abs_le.mpr hx
  have h := hi.comp_measurePreserving (measurePreserving_eval (fun _ : Fin N => signLaw) i)
  simpa only [Function.comp_def,id_eq,Function.eval] using h

theorem walkMax_integrable (N : ℕ) : Integrable (walkMax (N := N)) (Measure.pi (fun _ : Fin N => signLaw)) := by
  have hp (k : Fin (N+1)) : MemLp (fun z : Fin N → ℝ => walkPrefix z k.val) 2 (Measure.pi (fun _ : Fin N => signLaw)) := by
    apply memLp_finsetSum Finset.univ
    intro i hi
    by_cases h : i.val<k.val
    · simpa only [if_pos h] using coordinate_memLp_two i
    · simp only [if_neg h]
      exact MemLp.zero
  exact (memLp_pi_iff.mpr hp).integrable (by norm_num) |>.norm

theorem walkMax_level_eq {N : ℕ} {t : ℝ} (ht : 0<t) :
    {z : Fin N → ℝ | t≤walkMax z}=absHitEvent N t := by
  ext z
  have he : t≤walkMax z ↔ ∃ k : Fin (N+1), t≤|walkPrefix z k.val| := by
    rw [← not_lt]
    change ¬‖fun k : Fin (N+1) => walkPrefix z k.val‖<t ↔ _
    rw [pi_norm_lt_iff ht]
    simp only [not_forall,not_lt,Real.norm_eq_abs]
  change t≤walkMax z ↔ ∃ k≤N, t≤|walkPrefix z k|
  rw [he]
  constructor
  · rintro ⟨k,hk⟩
    exact ⟨k.val,by omega,hk⟩
  · rintro ⟨k,hk,hh⟩
    exact ⟨⟨k,by omega⟩,hh⟩

theorem integral_walkMax_le {N : ℕ} (hN : 0<N) :
    (∫ z, walkMax z ∂Measure.pi (fun _ : Fin N => signLaw))≤3*Real.sqrt (N:ℝ) := by
  let P := Measure.pi (fun _ : Fin N => signLaw)
  let f : ℝ → ℝ := fun t => P.real {z | t≤walkMax z}
  let g : ℝ → ℝ := fun t => 2*Real.exp (-(1/(2*(N:ℝ)))*t^2)
  have hNp : (0:ℝ)<N := by exact_mod_cast hN
  have hfmeas : Measurable f := by
    have ha : Antitone f := by intro s t hst; exact measureReal_mono (fun z hz => hst.trans hz)
    exact ha.measurable
  have hg : IntegrableOn g (Ioi 0) := ((integrable_exp_neg_mul_sq (by positivity : (0:ℝ)<1/(2*(N:ℝ)))).const_mul 2).integrableOn
  have hfg : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0), f t≤g t := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    dsimp only [f,g,P]
    rw [walkMax_level_eq ht]
    have h := abs_maximal_hoeffding hN ht.le
    convert h using 1 <;> congr 2 <;> ring
  have hfi : IntegrableOn f (Ioi 0) := hg.mono' hfmeas.aestronglyMeasurable (by
    filter_upwards [hfg] with t ht
    rw [Real.norm_eq_abs,abs_of_nonneg (show 0≤f t from measureReal_nonneg)]
    exact ht)
  rw [(walkMax_integrable N).integral_eq_integral_meas_le (Eventually.of_forall (fun z => norm_nonneg _))]
  change (∫ t in Ioi 0, f t)≤_
  calc
    _ ≤ ∫ t in Ioi 0, g t := integral_mono_ae hfi hg hfg
    _ = Real.sqrt (2*Real.pi*(N:ℝ)) := by
      dsimp only [g]
      rw [integral_const_mul,integral_gaussian_Ioi]
      have he : Real.pi/(1/(2*(N:ℝ)))=2*Real.pi*(N:ℝ) := by field_simp
      rw [he]
      ring
    _ ≤ Real.sqrt (9*(N:ℝ)) := Real.sqrt_le_sqrt (by nlinarith [Real.pi_lt_four])
    _ = 3*Real.sqrt (N:ℝ) := by rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤9)]; norm_num

end Erdos524.FiniteSignWalk
