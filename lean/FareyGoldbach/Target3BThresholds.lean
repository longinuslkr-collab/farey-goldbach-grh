import FareyGoldbach.Defs

namespace ThresholdEightSeventeenths

def initialCut (x cap : ℚ) : ℚ := (x - cap) / 5
def sixthCut (x cap : ℚ) : ℚ := (3 * x - 2 * cap) / 10
def fourthCut (x cap : ℚ) : ℚ := (2 * x - cap) / 5
def target (x cap : ℚ) : ℚ := (9 * cap - x) / 10

theorem cuts_ordered (x cap : ℚ) (hx : 0 < x) (hc : 0 ≤ cap)
    (hcap : 9 * cap ≤ x) :
    0 < initialCut x cap ∧ initialCut x cap < sixthCut x cap ∧
    sixthCut x cap < fourthCut x cap ∧ fourthCut x cap ≤ x / 2 := by
  unfold initialCut sixthCut fourthCut
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem type_i_rows (x cap j : ℚ) (hc : 0 ≤ cap)
    (hcap : 9 * cap ≤ x) (hj : j ≤ cap) :
    j - x ≤ target x cap ∧
    j + 2 * initialCut x cap - x / 2 ≤ target x cap := by
  unfold initialCut target
  exact ⟨by linarith, by linarith⟩

theorem cauchy_rows (x cap j s : ℚ) (hc : 0 ≤ cap)
    (hcap : 9 * cap ≤ x) (hj : j ≤ cap)
    (hs₁ : initialCut x cap ≤ s) (hs₂ : s ≤ sixthCut x cap) :
    (j - s) / 2 ≤ target x cap ∧
    j - x / 2 ≤ target x cap ∧
    j + s / 2 - x / 4 ≤ target x cap := by
  unfold initialCut at hs₁
  unfold sixthCut at hs₂
  unfold target
  exact ⟨by linarith, by linarith, by linarith⟩

theorem sixth_moment_rows (x cap j s : ℚ) (hc : 0 ≤ cap)
    (hcap : 9 * cap ≤ x) (hj : j ≤ cap)
    (hs₁ : sixthCut x cap ≤ s) (hs₂ : s ≤ fourthCut x cap) :
    (5 * j - 2 * s) / 6 ≤ target x cap ∧
    (5 * j + s - x) / 6 ≤ target x cap ∧
    j - s / 2 ≤ target x cap ∧
    j - x / 6 ≤ target x cap := by
  unfold sixthCut at hs₁
  unfold fourthCut at hs₂
  unfold target
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem fourth_moment_rows (x cap j s : ℚ) (hc : 0 ≤ cap)
    (hcap : 9 * cap ≤ x) (hj : j ≤ cap)
    (hs₁ : fourthCut x cap ≤ s) (hs₂ : s ≤ x / 2) :
    (3 * j + s - x) / 4 ≤ target x cap ∧
    (3 * j - s) / 4 ≤ target x cap ∧
    j + s / 2 - x / 2 ≤ target x cap ∧
    j - x / 4 ≤ target x cap := by
  unfold fourthCut at hs₁
  unfold target
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem attained_at_sixth_cut (x cap : ℚ) :
    cap + sixthCut x cap / 2 - x / 4 = target x cap ∧
    (5 * cap - 2 * sixthCut x cap) / 6 = target x cap := by
  unfold sixthCut target
  exact ⟨by ring, by ring⟩

theorem balanced_threshold (θ : ℚ) (hθ : 8 < 17 * θ) (hhalf : 2 * θ ≤ 1) :
    0 ≤ 1 - 2 * θ ∧ 9 * (1 - 2 * θ) < 1 - θ ∧
    target (1 - θ) (1 - 2 * θ) = (8 - 17 * θ) / 10 ∧
    target (1 - θ) (1 - 2 * θ) < 0 := by
  unfold target
  exact ⟨by linarith, by linarith, by ring, by linarith⟩

theorem shifted_poisson_cap (x cap d extra : ℚ) (hd : 0 ≤ d)
    (hgap : 9 * (cap + extra) < x) (hfreq : 0 ≤ cap - d + extra) :
    0 ≤ cap - d + extra ∧ 9 * (cap - d + extra) < x - d ∧
    target (x - d) (cap - d + extra) =
      target x cap + (9 * extra - 8 * d) / 10 := by
  unfold target
  exact ⟨by linarith, by linarith, by ring⟩

end ThresholdEightSeventeenths

namespace ThresholdSevenFifteenths

open ThresholdEightSeventeenths (initialCut fourthCut)

def sixthCut (x cap : ℚ) : ℚ := (6 * x - 4 * cap) / 17
def target (x cap : ℚ) : ℚ := (8 * cap - x) / 10

theorem cuts_ordered (x cap : ℚ) (hx : 0 < x) (hc : 0 ≤ cap)
    (hcap : 8 * cap ≤ x) :
    cap < initialCut x cap ∧ initialCut x cap < sixthCut x cap ∧
    sixthCut x cap < fourthCut x cap ∧ fourthCut x cap ≤ x / 2 := by
  unfold initialCut sixthCut fourthCut
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem type_i_rows (x cap j : ℚ) (hc : 0 ≤ cap)
    (hcap : 8 * cap ≤ x) (hj : j ≤ cap) :
    j - x ≤ target x cap ∧
    j + 2 * initialCut x cap - x / 2 ≤ target x cap := by
  unfold initialCut target
  exact ⟨by linarith, by linarith⟩

theorem spectral_cauchy_rows (x cap j s : ℚ) (hc : 0 ≤ cap)
    (hcap : 8 * cap ≤ x) (hj : j ≤ cap)
    (hs₁ : initialCut x cap ≤ s) (hs₂ : s ≤ sixthCut x cap) :
    (j - s) / 2 ≤ target x cap ∧
    j - x / 2 ≤ target x cap ∧
    j + 3 * s / 8 - x / 4 ≤ target x cap := by
  unfold initialCut at hs₁
  unfold sixthCut at hs₂
  unfold target
  exact ⟨by linarith, by linarith, by linarith⟩

theorem spectral_length_margin (x cap s : ℚ) (hcap : 8 * cap ≤ x)
    (hs : initialCut x cap ≤ s) : x / 20 ≤ s - cap := by
  unfold initialCut at hs
  linarith

theorem exceptional_factor_exponents (cap s k : ℚ) (hc : cap ≤ s)
    (hk : k ≤ s) :
    k / 2 ≤ s / 2 ∧ k / 2 + (7 / 32) * ((cap - k) / 2) ≤ s / 2 := by
  exact ⟨by linarith, by linarith⟩

theorem normalize_completed_terms (x j s : ℚ) (hx : 0 ≤ x) (hs : s ≤ x / 2) :
    ((x + s / 2 + 2 * (j + s)) + (2 * x - s)) / 2 - 2 * x =
      j + 3 * s / 4 - x / 2 ∧
    ((3 * x / 2 - s / 4 + 2 * (j + s)) + (2 * x - s)) / 2 - 2 * x =
      j + 3 * s / 8 - x / 4 ∧
    j + 3 * s / 4 - x / 2 ≤ j + 3 * s / 8 - x / 4 := by
  exact ⟨by ring, by ring, by linarith⟩

theorem sixth_moment_rows (x cap j s : ℚ) (hc : 0 ≤ cap)
    (hcap : 8 * cap ≤ x) (hj : j ≤ cap)
    (hs₁ : sixthCut x cap ≤ s) (hs₂ : s ≤ fourthCut x cap) :
    (5 * j - 2 * s) / 6 ≤ target x cap ∧
    (5 * j + s - x) / 6 ≤ target x cap ∧
    j - s / 2 ≤ target x cap ∧
    j - x / 6 ≤ target x cap := by
  unfold sixthCut at hs₁
  unfold fourthCut at hs₂
  unfold target
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem fourth_moment_rows (x cap j s : ℚ) (hc : 0 ≤ cap)
    (hcap : 8 * cap ≤ x) (hj : j ≤ cap)
    (hs₁ : fourthCut x cap ≤ s) (hs₂ : s ≤ x / 2) :
    (3 * j + s - x) / 4 ≤ target x cap ∧
    (3 * j - s) / 4 ≤ target x cap ∧
    j + s / 2 - x / 2 ≤ target x cap ∧
    j - x / 4 ≤ target x cap := by
  unfold fourthCut at hs₁
  unfold target
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem attained_at_fourth_cut (x cap : ℚ) :
    (5 * cap + fourthCut x cap - x) / 6 = target x cap ∧
    (3 * cap - fourthCut x cap) / 4 = target x cap := by
  unfold fourthCut target
  exact ⟨by ring, by ring⟩

theorem obstruction_at_three_j (x j : ℚ) (hx : 0 < x) (h : x ≤ 8 * j) :
    0 < j + 3 * (3 * j) / 8 - x / 4 ∧
    0 ≤ (5 * j + 3 * j - x) / 6 ∧
    (3 * j - 3 * j) / 4 = 0 := by
  exact ⟨by linarith, by linarith, by ring⟩

theorem spectral_strictly_improves : (7 : ℚ) / 15 < 8 / 17 := by
  norm_num

theorem balanced_threshold (θ : ℚ) (hθ : 7 < 15 * θ) (hhalf : 2 * θ ≤ 1) :
    0 ≤ 1 - 2 * θ ∧ 8 * (1 - 2 * θ) < 1 - θ ∧
    target (1 - θ) (1 - 2 * θ) = (7 - 15 * θ) / 10 ∧
    target (1 - θ) (1 - 2 * θ) < 0 := by
  unfold target
  exact ⟨by linarith, by linarith, by ring, by linarith⟩

theorem shifted_poisson_cap (x cap d extra : ℚ) (hd : 0 ≤ d)
    (hgap : 8 * (cap + extra) < x) (hfreq : 0 ≤ cap - d + extra) :
    0 ≤ cap - d + extra ∧ 8 * (cap - d + extra) < x - d ∧
    target (x - d) (cap - d + extra) =
      target x cap + (8 * extra - 7 * d) / 10 := by
  unfold target
  exact ⟨by linarith, by linarith, by ring⟩

end ThresholdSevenFifteenths
