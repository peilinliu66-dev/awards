import Mathlib.Probability.BorelCantelli
import Mathlib.MeasureTheory.MeasurableSpace.MeasurablyGenerated
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! Abstract lower-envelope blocking. All required event probability estimates are explicit hypotheses. -/

namespace Erdos524.EnvelopeBlocking

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem ae_frequently_of_independent {E : ℕ → Set Ω}
    (hE : ∀ j, MeasurableSet (E j)) (hind : iIndepSet E μ)
    (hdiv : ∑' j, μ (E j) = ⊤) : ∀ᵐ ω ∂μ, ∃ᶠ j in atTop, ω ∈ E j := by
  haveI : IsProbabilityMeasure μ := hind.isProbabilityMeasure
  have hmeasure := measure_limsup_eq_one hE hind hdiv
  have hae : ∀ᵐ ω ∂μ, ω ∈ limsup E atTop := by
    apply (ae_iff_measure_eq (MeasurableSet.measurableSet_limsup hE).nullMeasurableSet).mpr
    change μ (limsup E atTop) = μ univ
    simpa only [measure_univ] using hmeasure
  simpa only [mem_limsup_iff_frequently_mem] using hae

theorem mesh_block_cover {g : ℕ → ℕ} (hg : StrictMono g) {J n : ℕ} (hn : g J ≤ n) :
    ∃ j, J ≤ j ∧ g j ≤ n ∧ n < g (j + 1) := by
  classical
  have hex : ∃ k, n < g k := ⟨n + 1, lt_of_lt_of_le (Nat.lt_succ_self n) (hg.id_le _)⟩
  let k := Nat.find hex
  have hkn : n < g k := Nat.find_spec hex
  have hk0 : 0 < k := by
    by_contra hh
    have hk : k = 0 := by omega
    have h0 := hg.monotone (Nat.zero_le J)
    rw [hk] at hkn
    omega
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hk0)
  have hmin : g j ≤ n := by
    exact le_of_not_gt (Nat.find_min hex (show j < Nat.find hex by change j < k; omega))
  have hJ : J ≤ j := by
    by_contra hh
    have hmono := hg.monotone (show j + 1 ≤ J by omega)
    rw [show k = j + 1 from hj] at hkn
    omega
  exact ⟨j, hJ, hmin, by simpa only [hj, Nat.succ_eq_add_one] using hkn⟩

theorem ae_eventual_mesh_lower
    (X : ℕ → Ω → ℝ) (b : ℕ → ℝ) (g : ℕ → ℕ) (a e : ℝ)
    (hbad : (∑' j, μ {ω | X (g j) ω ≤ a * b (g j)}) ≠ ⊤)
    (hinc : (∑' j, μ {ω | ¬∀ n, g j ≤ n → n ≤ g (j + 1) →
      |X n ω - X (g j) ω| ≤ e * b (g j)}) ≠ ⊤) :
    ∀ᵐ ω ∂μ, ∀ᶠ j in atTop, ∀ n, g j ≤ n → n ≤ g (j + 1) →
      (a - e) * b (g j) ≤ X n ω := by
  filter_upwards [ae_eventually_notMem hbad, ae_eventually_notMem hinc] with ω hbad hinc
  filter_upwards [hbad, hinc] with j hj hk
  have hj' : a * b (g j) < X (g j) ω := lt_of_not_ge hj
  have hk' : ∀ n, g j ≤ n → n ≤ g (j + 1) → |X n ω - X (g j) ω| ≤ e * b (g j) := by simpa using hk
  intro n hnj hnj1
  have hd := (abs_le.mp (hk' n hnj hnj1)).1
  nlinarith

theorem ae_eventual_full_lower
    (X : ℕ → Ω → ℝ) (b : ℕ → ℝ) (hb : ∀ n, 0 ≤ b n)
    (g : ℕ → ℕ) (hg : StrictMono g) (a e q κ : ℝ) (hq : 0 ≤ q)
    (hslack : q * κ ≤ a - e)
    (hscale : ∀ᶠ j in atTop, ∀ n, g j ≤ n → n ≤ g (j + 1) → b n ≤ κ * b (g j))
    (hbad : (∑' j, μ {ω | X (g j) ω ≤ a * b (g j)}) ≠ ⊤)
    (hinc : (∑' j, μ {ω | ¬∀ n, g j ≤ n → n ≤ g (j + 1) →
      |X n ω - X (g j) ω| ≤ e * b (g j)}) ≠ ⊤) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, q * b n ≤ X n ω := by
  filter_upwards [ae_eventual_mesh_lower X b g a e hbad hinc] with ω hω
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (hω.and hscale)
  filter_upwards [eventually_ge_atTop (g J)] with n hn
  obtain ⟨j, hj, hnj, hnj1⟩ := mesh_block_cover hg hn
  have h := hJ j hj
  calc
    q * b n ≤ q * (κ * b (g j)) := mul_le_mul_of_nonneg_left (h.2 n hnj hnj1.le) hq
    _ = (q * κ) * b (g j) := by ring
    _ ≤ (a - e) * b (g j) := mul_le_mul_of_nonneg_right hslack (hb _)
    _ ≤ X n ω := h.1 n hnj hnj1.le

theorem ae_frequent_sparse_upper
    (X fresh old : ℕ → Ω → ℝ) (b u v : ℕ → ℝ) (g : ℕ → ℕ) (hg : StrictMono g) (q : ℝ)
    (hE : ∀ j, MeasurableSet {ω | fresh j ω ≤ u j})
    (hind : iIndepSet (fun j ↦ {ω | fresh j ω ≤ u j}) μ)
    (hdiv : ∑' j, μ {ω | fresh j ω ≤ u j} = ⊤)
    (hold : ∀ᵐ ω ∂μ, ∀ᶠ j in atTop, old j ω ≤ v j)
    (hsum : ∀ ω j, X (g j) ω ≤ fresh j ω + old j ω)
    (hbudget : ∀ᶠ j in atTop, u j + v j ≤ q * b (g j)) :
    ∀ᵐ ω ∂μ, ∃ᶠ n in atTop, X n ω ≤ q * b n := by
  filter_upwards [ae_frequently_of_independent hE hind hdiv, hold] with ω hf ho
  have hj : ∃ᶠ j in atTop, X (g j) ω ≤ q * b (g j) := by
    apply ((hf.and_eventually ho).and_eventually hbudget).mono
    intro j hj
    exact (hsum ω j).trans ((add_le_add hj.1.1 hj.1.2).trans hj.2)
  apply frequently_atTop.2
  intro N
  obtain ⟨j, hjN, hj⟩ := frequently_atTop.1 hj N
  exact ⟨g j, hjN.trans (hg.id_le j), hj⟩

end Erdos524.EnvelopeBlocking
