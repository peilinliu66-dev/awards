import Erdos524.FiniteSmallBallStrict

/-! The unique inverse of the finite small-ball distribution on (0,1). -/

namespace Erdos524.FiniteSmallBallInverse

open Set Filter
open Erdos524.FiniteSmallBallBasic Erdos524.FiniteSmallBallTail Erdos524.FiniteSmallBallZero
open Erdos524.FiniteSmallBallStrict

theorem exists_smallBall_inverse (p : ℝ) (hp : 0 < p ∧ p < 1) :
    ∃ δ : ℝ, 0 < δ ∧ smallBallReal δ = p := by
  have hlarge : ∀ᶠ x : ℝ in atTop, p < smallBallReal x :=
    (tendsto_order.mp smallBallReal_tendsto_one).1 p hp.2
  obtain ⟨M, hM0, hMp⟩ := ((eventually_ge_atTop (0 : ℝ)).and hlarge).exists
  have hmem : p ∈ Icc (smallBallReal 0) (smallBallReal M) := by
    rw [smallBallReal_nonpos le_rfl]
    exact ⟨hp.1.le, hMp.le⟩
  obtain ⟨δ, hδ, he⟩ := intermediate_value_Icc hM0 smallBallReal_continuous.continuousOn hmem
  have hδpos : 0 < δ := by
    by_contra hn
    have hz := smallBallReal_nonpos (le_of_not_gt hn)
    linarith [hp.1]
  exact ⟨δ, hδpos, he⟩

noncomputable def smallBallInverse (p : ℝ) : ℝ :=
  if hp : 0 < p ∧ p < 1 then Classical.choose (exists_smallBall_inverse p hp) else 0

theorem smallBallInverse_spec {p : ℝ} (hp : 0 < p ∧ p < 1) :
    0 < smallBallInverse p ∧ smallBallReal (smallBallInverse p) = p := by
  unfold smallBallInverse
  rw [dif_pos hp]
  exact Classical.choose_spec (exists_smallBall_inverse p hp)

theorem smallBallInverse_nonneg (p : ℝ) : 0 ≤ smallBallInverse p := by
  by_cases hp : 0 < p ∧ p < 1
  · exact (smallBallInverse_spec hp).1.le
  · simp [smallBallInverse, hp]

theorem smallBallInverse_unique {p δ : ℝ} (hp : 0 < p ∧ p < 1) (hδ : 0 ≤ δ)
    (he : smallBallReal δ = p) : δ = smallBallInverse p :=
  smallBallReal_strictMono.injOn hδ (smallBallInverse_spec hp).1.le
    (he.trans (smallBallInverse_spec hp).2.symm)

theorem smallBallInverse_left_inverse {δ : ℝ} (hδ : 0 < δ) :
    smallBallInverse (smallBallReal δ) = δ := by
  exact (smallBallInverse_unique ⟨smallBallReal_pos hδ, smallBallReal_lt_one hδ.le⟩ hδ.le rfl).symm

theorem smallBallInverse_strictMono : StrictMonoOn smallBallInverse (Ioo 0 1) := by
  intro p hp q hq hpq
  apply lt_of_not_ge
  intro h
  have he := smallBallReal_mono h
  rw [(smallBallInverse_spec hq).2, (smallBallInverse_spec hp).2] at he
  linarith

theorem smallBallInverse_continuousAt {p : ℝ} (hp : 0 < p ∧ p < 1) :
    ContinuousAt smallBallInverse p := by
  apply Metric.continuousAt_iff.mpr
  intro ε heps
  let d := smallBallInverse p
  let a := max 0 (d - ε / 2)
  let b := d + ε / 2
  have hd : 0 < d := (smallBallInverse_spec hp).1
  have hdp : smallBallReal d = p := (smallBallInverse_spec hp).2
  have ha0 : 0 ≤ a := le_max_left _ _
  have had : a < d := max_lt hd (by linarith)
  have hdb : d < b := by dsimp [b]; linarith
  have hb0 : 0 ≤ b := hd.le.trans hdb.le
  have hFa : smallBallReal a < p := by
    rw [← hdp]
    exact smallBallReal_strictMono ha0 hd.le had
  have hFb : p < smallBallReal b := by
    rw [← hdp]
    exact smallBallReal_strictMono hd.le hb0 hdb
  let η := min (min (p - smallBallReal a) (smallBallReal b - p)) (min p (1 - p))
  have hη : 0 < η := lt_min (lt_min (sub_pos.mpr hFa) (sub_pos.mpr hFb))
    (lt_min hp.1 (sub_pos.mpr hp.2))
  refine ⟨η, hη, ?_⟩
  intro q hq
  have hclose : |q - p| < η := by simpa only [Real.dist_eq] using hq
  have hleft := (abs_lt.mp (hclose.trans_le ((min_le_left _ _).trans (min_le_left _ _)))).1
  have hright := (abs_lt.mp (hclose.trans_le ((min_le_left _ _).trans (min_le_right _ _)))).2
  have hq0 := (abs_lt.mp (hclose.trans_le ((min_le_right _ _).trans (min_le_left _ _)))).1
  have hq1 := (abs_lt.mp (hclose.trans_le ((min_le_right _ _).trans (min_le_right _ _)))).2
  have hqin : 0 < q ∧ q < 1 := by constructor <;> linarith
  have hfq := (smallBallInverse_spec hqin).2
  have haInv : a < smallBallInverse q := by
    apply lt_of_not_ge
    intro h
    have he := smallBallReal_mono h
    rw [hfq] at he
    linarith
  have hInvb : smallBallInverse q < b := by
    apply lt_of_not_ge
    intro h
    have he := smallBallReal_mono h
    rw [hfq] at he
    linarith
  have haLower : d - ε / 2 ≤ a := le_max_right _ _
  rw [Real.dist_eq, abs_lt]
  change -ε < smallBallInverse q - d ∧ smallBallInverse q - d < ε
  dsimp only [b] at hInvb
  constructor <;> linarith

theorem smallBallInverse_zero : smallBallInverse 0 = 0 := by simp [smallBallInverse]

theorem smallBallInverse_continuousAt_zero : ContinuousAt smallBallInverse 0 := by
  apply Metric.continuousAt_iff.mpr
  intro ε heps
  have hpε : 0 < smallBallReal ε ∧ smallBallReal ε < 1 :=
    ⟨smallBallReal_pos heps, smallBallReal_lt_one heps.le⟩
  refine ⟨min (smallBallReal ε) (1 / 2), lt_min hpε.1 (by norm_num), ?_⟩
  intro p hp
  have habs : |p| < min (smallBallReal ε) (1 / 2) := by simpa only [Real.dist_eq, sub_zero] using hp
  rw [smallBallInverse_zero, Real.dist_eq, sub_zero, abs_of_nonneg (smallBallInverse_nonneg p)]
  by_cases hpin : 0 < p ∧ p < 1
  · have hpq : p < smallBallReal ε := (le_abs_self p).trans_lt (habs.trans_le (min_le_left _ _))
    have h := smallBallInverse_strictMono hpin hpε hpq
    rwa [smallBallInverse_left_inverse heps] at h
  · simp only [smallBallInverse, dif_neg hpin]
    exact heps

theorem smallBallInverse_tendsto_zero : Tendsto smallBallInverse (nhds 0) (nhds 0) := by
  simpa only [smallBallInverse_zero] using smallBallInverse_continuousAt_zero.tendsto

end Erdos524.FiniteSmallBallInverse
