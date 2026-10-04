import Erdos524.FiniteSmallBallTail

/-! Dimension-free Gaussian band control for affine coordinates with positive slopes. -/

namespace Erdos524.AffineGaussianBand

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

variable {n : ℕ}

theorem standardGaussian_density_le_one (x : ℝ) : gaussianPDFReal 0 1 x ≤ 1 := by
  have hspos : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hs : 1 ≤ Real.sqrt (2 * Real.pi) := by
    nlinarith [Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi), Real.pi_gt_three]
  have hc : (Real.sqrt (2 * Real.pi))⁻¹ ≤ 1 := by
    simpa only [one_div, inv_one] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hs
  have he : Real.exp (-x ^ 2 / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
  unfold gaussianPDFReal
  simp only [NNReal.coe_one, mul_one, sub_zero]
  exact (mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hspos.le)).trans (by simpa using hc)

theorem standardGaussian_le_volume (s : Set ℝ) : (gaussianReal 0 1) s ≤ volume s := by
  rw [gaussianReal_apply 0 (by norm_num)]
  calc
    _ ≤ ∫⁻ _ in s, (1 : ℝ≥0∞) := by
      apply lintegral_mono
      intro x
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (standardGaussian_density_le_one x)
    _ = _ := setLIntegral_one s

noncomputable def fiberLower (a r : Fin (n + 1) → ℝ) (δ : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i ↦ (-δ - r i) / a i)
noncomputable def fiberUpper (a r : Fin (n + 1) → ℝ) (δ : ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i ↦ (δ - r i) / a i)

theorem affine_cube_fiber (a r : Fin (n + 1) → ℝ) (ha : ∀ i, 0 < a i) (δ : ℝ) :
    {x : ℝ | ∀ i, |a i * x + r i| ≤ δ} = Icc (fiberLower a r δ) (fiberUpper a r δ) := by
  ext x
  constructor
  · intro hx
    constructor
    · apply (Finset.sup'_le_iff _ _).mpr
      intro i hi
      apply (div_le_iff₀ (ha i)).mpr
      have h := (abs_le.mp (hx i)).1
      nlinarith
    · apply (Finset.le_inf'_iff _ _).mpr
      intro i hi
      apply (le_div_iff₀ (ha i)).mpr
      have h := (abs_le.mp (hx i)).2
      nlinarith
  · intro hx i
    have hl : (-δ - r i) / a i ≤ x :=
      (Finset.le_sup' _ (Finset.mem_univ i)).trans hx.1
    have hu : x ≤ (δ - r i) / a i := hx.2.trans (Finset.inf'_le _ (Finset.mem_univ i))
    have h1 := (div_le_iff₀ (ha i)).mp hl
    have h2 := (le_div_iff₀ (ha i)).mp hu
    rw [abs_le]
    constructor <;> nlinarith

theorem fiberLower_shift (a r : Fin (n + 1) → ℝ) {c ε : ℝ}
    (hc : 0 < c) (ha : ∀ i, c ≤ a i) (hε : 0 ≤ ε) (δ : ℝ) :
    fiberLower a r δ - ε / c ≤ fiberLower a r (δ + ε) := by
  have h : fiberLower a r δ ≤ fiberLower a r (δ + ε) + ε / c := by
    apply (Finset.sup'_le_iff _ _).mpr
    intro i hi
    have hq : ε / a i ≤ ε / c := by gcongr; exact ha i
    have hs : (-(δ + ε) - r i) / a i ≤ fiberLower a r (δ + ε) := Finset.le_sup' (fun j ↦ (-(δ + ε) - r j) / a j) hi
    have he : (-δ - r i) / a i = (-(δ + ε) - r i) / a i + ε / a i := by ring
    linarith
  linarith

theorem fiberUpper_shift (a r : Fin (n + 1) → ℝ) {c ε : ℝ}
    (hc : 0 < c) (ha : ∀ i, c ≤ a i) (hε : 0 ≤ ε) (δ : ℝ) :
    fiberUpper a r (δ + ε) ≤ fiberUpper a r δ + ε / c := by
  have h : fiberUpper a r (δ + ε) - ε / c ≤ fiberUpper a r δ := by
    apply (Finset.le_inf'_iff _ _).mpr
    intro i hi
    have hq : ε / a i ≤ ε / c := by gcongr; exact ha i
    have hs : fiberUpper a r (δ + ε) ≤ (δ + ε - r i) / a i := Finset.inf'_le _ hi
    have he : (δ + ε - r i) / a i = (δ - r i) / a i + ε / a i := by ring
    linarith
  linarith

theorem affine_gaussian_cube_increment (a r : Fin (n + 1) → ℝ) {c ε : ℝ}
    (hc : 0 < c) (ha : ∀ i, c ≤ a i) (hε : 0 ≤ ε) (δ : ℝ) :
    (gaussianReal 0 1) {x : ℝ | ∀ i, |a i * x + r i| ≤ δ + ε} ≤
      (gaussianReal 0 1) {x : ℝ | ∀ i, |a i * x + r i| ≤ δ} +
        ENNReal.ofReal (2 * ε / c) := by
  rw [affine_cube_fiber a r (fun i ↦ hc.trans_le (ha i)),
    affine_cube_fiber a r (fun i ↦ hc.trans_le (ha i))]
  let lo := fiberLower a r δ
  let hi := fiberUpper a r δ
  let h := ε / c
  have hnonneg : 0 ≤ h := div_nonneg hε hc.le
  have hsub : Icc (fiberLower a r (δ + ε)) (fiberUpper a r (δ + ε)) ⊆
      Icc lo hi ∪ (Icc (lo - h) lo ∪ Icc hi (hi + h)) := by
    intro x hx
    by_cases hlo : lo ≤ x
    · by_cases hhi : x ≤ hi
      · exact Or.inl ⟨hlo, hhi⟩
      · right; right
        exact ⟨(lt_of_not_ge hhi).le, hx.2.trans (fiberUpper_shift a r hc ha hε δ)⟩
    · right; left
      exact ⟨(fiberLower_shift a r hc ha hε δ).trans hx.1, (lt_of_not_ge hlo).le⟩
  have hleft : (gaussianReal 0 1) (Icc (lo - h) lo) ≤ ENNReal.ofReal h := by
    have hp := standardGaussian_le_volume (Icc (lo - h) lo)
    rw [Real.volume_Icc] at hp
    convert hp using 1 <;> congr 1 <;> ring
  have hright : (gaussianReal 0 1) (Icc hi (hi + h)) ≤ ENNReal.ofReal h := by
    have hp := standardGaussian_le_volume (Icc hi (hi + h))
    rw [Real.volume_Icc] at hp
    convert hp using 1 <;> congr 1 <;> ring
  calc
    _ ≤ (gaussianReal 0 1) (Icc lo hi ∪ (Icc (lo - h) lo ∪ Icc hi (hi + h))) := measure_mono hsub
    _ ≤ (gaussianReal 0 1) (Icc lo hi) +
        ((gaussianReal 0 1) (Icc (lo - h) lo) + (gaussianReal 0 1) (Icc hi (hi + h))) :=
      (measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))
    _ ≤ (gaussianReal 0 1) (Icc lo hi) + (ENNReal.ofReal h + ENNReal.ofReal h) := by gcongr
    _ = _ := by
      rw [← ENNReal.ofReal_add hnonneg hnonneg]
      congr 2
      dsimp [h]
      ring

end Erdos524.AffineGaussianBand
