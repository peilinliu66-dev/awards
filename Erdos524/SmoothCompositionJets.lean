import Erdos524.SmoothCutoff

namespace Erdos524.SmoothCompositionJets
open Erdos524.SmoothCutoff

noncomputable def cutoffJet (n : ℕ) (q : ℝ → ℝ) (t : ℝ) : ℝ := iteratedDeriv n cutoff (q t)

theorem cutoff_iterated_hasDerivAt (n : ℕ) (x : ℝ) :
    HasDerivAt (iteratedDeriv n cutoff) (iteratedDeriv (n+1) cutoff x) x := by
  rw [iteratedDeriv_succ]
  exact ((cutoff_contDiff (n+1)).differentiable_iteratedDeriv' n x).hasDerivAt

theorem cutoffJet_hasDerivAt (n : ℕ) (q q1 : ℝ → ℝ) (t : ℝ) (hq : HasDerivAt q (q1 t) t) :
    HasDerivAt (cutoffJet n q) (cutoffJet (n+1) q t*q1 t) t :=
  (cutoff_iterated_hasDerivAt n (q t)).comp t hq

noncomputable def compositionFirst (q q1 : ℝ → ℝ) (t : ℝ) : ℝ := cutoffJet 1 q t*q1 t
noncomputable def compositionSecond (q q1 q2 : ℝ → ℝ) (t : ℝ) : ℝ :=
  cutoffJet 2 q t*(q1 t)^2+cutoffJet 1 q t*q2 t
noncomputable def compositionThird (q q1 q2 q3 : ℝ → ℝ) (t : ℝ) : ℝ :=
  cutoffJet 3 q t*(q1 t)^3+3*cutoffJet 2 q t*q1 t*q2 t+cutoffJet 1 q t*q3 t
noncomputable def compositionFourth (q q1 q2 q3 q4 : ℝ → ℝ) (t : ℝ) : ℝ :=
  cutoffJet 4 q t*(q1 t)^4+6*cutoffJet 3 q t*(q1 t)^2*q2 t+
    3*cutoffJet 2 q t*(q2 t)^2+4*cutoffJet 2 q t*q1 t*q3 t+cutoffJet 1 q t*q4 t

theorem composition_hasDerivAt (q q1 : ℝ → ℝ) (t : ℝ) (hq : HasDerivAt q (q1 t) t) :
    HasDerivAt (fun s => cutoff (q s)) (compositionFirst q q1 t) t := by
  convert cutoffJet_hasDerivAt 0 q q1 t hq using 1
  · funext s
    simp only [cutoffJet,iteratedDeriv_zero]
  · rfl

theorem compositionFirst_hasDerivAt (q q1 q2 : ℝ → ℝ) (t : ℝ)
    (hq : HasDerivAt q (q1 t) t) (h1 : HasDerivAt q1 (q2 t) t) :
    HasDerivAt (compositionFirst q q1) (compositionSecond q q1 q2 t) t := by
  convert (cutoffJet_hasDerivAt 1 q q1 t hq).mul h1 using 1
  · funext s; rfl
  · unfold compositionSecond
    ring

theorem compositionSecond_hasDerivAt (q q1 q2 q3 : ℝ → ℝ) (t : ℝ)
    (hq : HasDerivAt q (q1 t) t) (h1 : HasDerivAt q1 (q2 t) t) (h2 : HasDerivAt q2 (q3 t) t) :
    HasDerivAt (compositionSecond q q1 q2) (compositionThird q q1 q2 q3 t) t := by
  have hj1 := cutoffJet_hasDerivAt 1 q q1 t hq
  have hj2 := cutoffJet_hasDerivAt 2 q q1 t hq
  convert ((hj2.mul (h1.pow 2)).add (hj1.mul h2)) using 1
  · funext s; rfl
  · unfold compositionThird
    simp only [Pi.pow_apply,Pi.mul_apply,Pi.add_apply,Pi.sub_apply]
    ring

theorem compositionThird_hasDerivAt (q q1 q2 q3 q4 : ℝ → ℝ) (t : ℝ)
    (hq : HasDerivAt q (q1 t) t) (h1 : HasDerivAt q1 (q2 t) t)
    (h2 : HasDerivAt q2 (q3 t) t) (h3 : HasDerivAt q3 (q4 t) t) :
    HasDerivAt (compositionThird q q1 q2 q3) (compositionFourth q q1 q2 q3 q4 t) t := by
  have hj1 := cutoffJet_hasDerivAt 1 q q1 t hq
  have hj2 := cutoffJet_hasDerivAt 2 q q1 t hq
  have hj3 := cutoffJet_hasDerivAt 3 q q1 t hq
  convert (((hj3.mul (h1.pow 3)).add (((hj2.mul h1).mul h2).const_mul 3)).add (hj1.mul h3)) using 1
  · funext s
    dsimp only [compositionThird,Pi.add_apply,Pi.mul_apply,Pi.pow_apply]
    ring
  · unfold compositionFourth
    simp only [Pi.pow_apply,Pi.mul_apply,Pi.add_apply,Pi.sub_apply]
    ring

theorem composition_iteratedDeriv_four (q q1 q2 q3 q4 : ℝ → ℝ)
    (hq : ∀ t, HasDerivAt q (q1 t) t) (h1 : ∀ t, HasDerivAt q1 (q2 t) t)
    (h2 : ∀ t, HasDerivAt q2 (q3 t) t) (h3 : ∀ t, HasDerivAt q3 (q4 t) t) :
    iteratedDeriv 4 (fun t => cutoff (q t))=compositionFourth q q1 q2 q3 q4 := by
  have e1 : deriv (fun t => cutoff (q t))=compositionFirst q q1 :=
    funext (fun t => (composition_hasDerivAt q q1 t (hq t)).deriv)
  have e2 : deriv (compositionFirst q q1)=compositionSecond q q1 q2 :=
    funext (fun t => (compositionFirst_hasDerivAt q q1 q2 t (hq t) (h1 t)).deriv)
  have e3 : deriv (compositionSecond q q1 q2)=compositionThird q q1 q2 q3 :=
    funext (fun t => (compositionSecond_hasDerivAt q q1 q2 q3 t (hq t) (h1 t) (h2 t)).deriv)
  have e4 : deriv (compositionThird q q1 q2 q3)=compositionFourth q q1 q2 q3 q4 :=
    funext (fun t => (compositionThird_hasDerivAt q q1 q2 q3 q4 t (hq t) (h1 t) (h2 t) (h3 t)).deriv)
  rw [show 4=3+1 by rfl,iteratedDeriv_succ,show 3=2+1 by rfl,iteratedDeriv_succ,
    show 2=1+1 by rfl,iteratedDeriv_succ,iteratedDeriv_one,e1,e2,e3,e4]

end Erdos524.SmoothCompositionJets
