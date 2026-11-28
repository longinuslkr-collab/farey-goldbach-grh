import FareyGoldbach.Target3AFoundation

open scoped BigOperators Matrix

namespace Target3A

private theorem gcd_with_prime_eq_one {r : ℕ} (hr : r.Prime) {x : ℤ}
    (hx : ¬ (r : ℤ) ∣ x) : Int.gcd x (r : ℤ) = 1 := by
  have hg := Int.gcd_dvd_right x (r : ℤ)
  rcases (Nat.dvd_prime hr).mp (Int.natCast_dvd_natCast.mp hg) with h | h
  · exact h
  · have h' := Int.gcd_dvd_left x (r : ℤ)
    rw [h] at h'
    exact (hx h').elim

/-- The cofactor and both endpoints are units modulo the second prime.
The returned Bézout coefficient is a common inverse for the two residue formulae. -/
theorem r2_congruence_of_minus_cofactor {r₁ r₂ p : ℕ} {a b m n r s Q₀ : ℤ}
    (hr₁ : r₁.Prime) (hr₂ : r₂.Prime) (hp : p.Prime)
    (h₁₂ : r₁ < r₂) (h₂p : r₂ < p)
    (hn : (r₂ : ℤ) ∣ n) (hs : (r₂ : ℤ) ∣ s)
    (hleft : m * n - ((r₂ : ℤ) - r₁) * p = a * r₁ * Q₀)
    (hright : r * s - ((r₂ : ℤ) - r₁) * p = b * r₁ * Q₀) :
    Int.gcd Q₀ (r₂ : ℤ) = 1 ∧ Int.gcd a (r₂ : ℤ) = 1 ∧
    Int.gcd b (r₂ : ℤ) = 1 ∧ a ≡ b [ZMOD (r₂ : ℤ)] ∧
    ∃ u : ℤ, Q₀ * u ≡ 1 [ZMOD (r₂ : ℤ)] ∧
      a ≡ (p : ℤ) * u [ZMOD (r₂ : ℤ)] ∧
      b ≡ (p : ℤ) * u [ZMOD (r₂ : ℤ)] := by
  have hr₂pos : (0 : ℤ) < r₂ := by exact_mod_cast hr₂.pos
  have hpunit : ¬ (r₂ : ℤ) ∣ (p : ℤ) := by
    intro hd
    rcases (Nat.dvd_prime hp).mp (Int.natCast_dvd_natCast.mp hd) with h | h
    · exact hr₂.ne_one h
    · exact h₂p.ne h
  have hr₁unit : ¬ (r₂ : ℤ) ∣ (r₁ : ℤ) := by
    intro hd
    exact (not_le_of_gt h₁₂) (Nat.le_of_dvd hr₁.pos (Int.natCast_dvd_natCast.mp hd))
  have hg₁ := gcd_with_prime_eq_one hr₂ hr₁unit
  have hproduct (w x y : ℤ) (hy : (r₂ : ℤ) ∣ y)
      (h : x * y - ((r₂ : ℤ) - r₁) * p = w * r₁ * Q₀) :
      w * Q₀ ≡ (p : ℤ) [ZMOD (r₂ : ℤ)] := by
    have hd : (r₂ : ℤ) ∣ x * y - (r₂ : ℤ) * p :=
      dvd_sub (dvd_mul_of_dvd_right hy x) (dvd_mul_right _ _)
    have heq : (r₁ : ℤ) * (w * Q₀) - (r₁ : ℤ) * (p : ℤ) =
        x * y - (r₂ : ℤ) * p := by
      linear_combination -h
    have hh : (r₁ : ℤ) * (w * Q₀) ≡ (r₁ : ℤ) * (p : ℤ) [ZMOD (r₂ : ℤ)] :=
      (Int.modEq_iff_dvd.mpr (heq ▸ hd)).symm
    simpa [Int.gcd_comm (r₂ : ℤ) (r₁ : ℤ), hg₁] using
      Int.ModEq.cancel_left_div_gcd hr₂pos hh
  have hA := hproduct a m n hn hleft
  have hB := hproduct b r s hs hright
  have hgQ : Int.gcd Q₀ (r₂ : ℤ) = 1 :=
    gcd_with_prime_eq_one hr₂ (fun hd => hpunit (hA.dvd_iff.mp (dvd_mul_of_dvd_right hd a)))
  have hgA : Int.gcd a (r₂ : ℤ) = 1 :=
    gcd_with_prime_eq_one hr₂ (fun hd => hpunit (hA.dvd_iff.mp (dvd_mul_of_dvd_left hd Q₀)))
  have hgB : Int.gcd b (r₂ : ℤ) = 1 :=
    gcd_with_prime_eq_one hr₂ (fun hd => hpunit (hB.dvd_iff.mp (dvd_mul_of_dvd_left hd Q₀)))
  let u := Int.gcdA Q₀ (r₂ : ℤ)
  have hu : Q₀ * u ≡ 1 [ZMOD (r₂ : ℤ)] := by
    have hbez := Int.gcd_eq_gcd_ab Q₀ (r₂ : ℤ)
    rw [hgQ, Int.natCast_one] at hbez
    apply Int.modEq_of_dvd
    exact ⟨Int.gcdB Q₀ (r₂ : ℤ), by dsimp [u]; linear_combination hbez⟩
  have hscaled {w : ℤ} (hw : w * Q₀ ≡ (p : ℤ) [ZMOD (r₂ : ℤ)]) :
      w ≡ (p : ℤ) * u [ZMOD (r₂ : ℤ)] := by
    have hwu : w * (Q₀ * u) ≡ w [ZMOD (r₂ : ℤ)] := by
      simpa only [mul_one] using hu.mul_left w
    exact hwu.symm.trans (by simpa only [mul_assoc] using hw.mul_right u)
  exact ⟨hgQ, hgA, hgB, (hscaled hA).trans (hscaled hB).symm, u, hu,
    hscaled hA, hscaled hB⟩

/-- Every physical cofactor pair lies in the determinant congruence modulo `p`. -/
theorem determinant_dvd_of_minus_cofactors {p Δ r₁ Q₀ a b m n r s : ℤ}
    (hleft : m * n - Δ * p = a * r₁ * Q₀)
    (hright : r * s - Δ * p = b * r₁ * Q₀) :
    p ∣ b * (m * n) - a * (r * s) := by
  refine ⟨Δ * (b - a), ?_⟩
  linear_combination b * hleft - a * hright

/-- On a fixed invertible product-coordinate fibre, distinct admissible integer
coordinates are at least one modulus apart. -/
theorem product_fiber_spacing {p x y y' t : ℤ} (hp : 0 < p)
    (hx : Int.gcd p x = 1)
    (hy : x * y ≡ t [ZMOD p]) (hy' : x * y' ≡ t [ZMOD p])
    (h_order : y < y') : p ≤ y' - y := by
  have h : y ≡ y' [ZMOD p] := by
    simpa [hx] using Int.ModEq.cancel_left_div_gcd hp (hy.trans hy'.symm)
  exact Int.le_of_dvd (sub_pos.mpr h_order) (Int.modEq_iff_dvd.mp h)

/-- The row swap followed by the integral branch shear and reversal. -/
def swapMatrixClass (j : ℤ) (C : Matrix (Fin 2) (Fin 2) ℤ) :
    Matrix (Fin 2) (Fin 2) ℤ :=
  !![C 1 0, j * C 1 0 - C 1 1; C 0 0, j * C 0 0 - C 0 1]

theorem swap_matrix_class_formula (j : ℤ) (C : Matrix (Fin 2) (Fin 2) ℤ) :
    swapMatrixClass j C = (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ) *
      C * !![1, j; 0, -1] := by
  ext i h
  fin_cases i <;> fin_cases h <;>
    simp [swapMatrixClass, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
      sub_eq_add_neg, mul_comm]

theorem swap_matrix_class_det_and_r2 (j r₂ : ℤ) (C : Matrix (Fin 2) (Fin 2) ℤ) :
    (swapMatrixClass j C).det = C.det ∧
    ((swapMatrixClass j C) 0 0 ≡ 0 [ZMOD r₂] ↔ C 1 0 ≡ 0 [ZMOD r₂]) := by
  constructor
  · rw [swapMatrixClass, Matrix.det_fin_two_of, Matrix.det_fin_two]
    ring
  · rfl

theorem swap_matrix_class_involutive (j : ℤ) (C : Matrix (Fin 2) (Fin 2) ℤ) :
    swapMatrixClass j (swapMatrixClass j C) = C := by
  ext i h
  fin_cases i <;> fin_cases h <;> simp [swapMatrixClass]

/-- Entrywise congruence is preserved and reflected, so the branch acts bijectively
on matrix classes at every modulus. -/
theorem swap_matrix_class_modEq_iff (j T : ℤ) (C C' : Matrix (Fin 2) (Fin 2) ℤ) :
    (∀ i h, swapMatrixClass j C i h ≡ swapMatrixClass j C' i h [ZMOD T]) ↔
    (∀ i h, C i h ≡ C' i h [ZMOD T]) := by
  have preserves {M N : Matrix (Fin 2) (Fin 2) ℤ}
      (hm : ∀ i h, M i h ≡ N i h [ZMOD T]) :
      ∀ i h, swapMatrixClass j M i h ≡ swapMatrixClass j N i h [ZMOD T] := by
    intro i h
    fin_cases i <;> fin_cases h
    · exact hm 1 0
    · exact ((hm 1 0).mul_left j).sub (hm 1 1)
    · exact hm 0 0
    · exact ((hm 0 0).mul_left j).sub (hm 0 1)
  constructor
  · intro h
    simpa only [swap_matrix_class_involutive] using preserves h
  · exact preserves

/-- Inverse powers encode the probabilities of the ordered auxiliary choices. -/
theorem auxiliary_pairing_weight_identity (J k : ℕ) (V D d : ℚ)
    (hD : D ≠ 0) (hd : d ≠ 0) :
    (((J + 1).factorial : ℚ) ^ k) * (V⁻¹ ^ (J + 1)) *
        ((((J + 1 : ℕ) : ℚ)⁻¹) ^ k) * V⁻¹ * ((D / d) / D) =
      ((J.factorial : ℚ) ^ k) * (V⁻¹ ^ (J + 2)) / d := by
  have hj : ((J + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hslots : (((J + 1).factorial : ℚ) ^ k) *
      ((((J + 1 : ℕ) : ℚ)⁻¹) ^ k) = (J.factorial : ℚ) ^ k := by
    rw [← mul_pow, Nat.factorial_succ, Nat.cast_mul]
    congr 1
    calc
      ((J + 1 : ℕ) : ℚ) * (J.factorial : ℚ) * (((J + 1 : ℕ) : ℚ)⁻¹) =
          (((J + 1 : ℕ) : ℚ) * (((J + 1 : ℕ) : ℚ)⁻¹)) * (J.factorial : ℚ) := by ring
      _ = (J.factorial : ℚ) := by rw [mul_inv_cancel₀ hj, one_mul]
  have hscale : (D / d) / D = d⁻¹ := by field_simp
  rw [hscale, pow_succ (V⁻¹) (J + 1), div_eq_mul_inv]
  calc
    _ = ((((J + 1).factorial : ℚ) ^ k) * ((((J + 1 : ℕ) : ℚ)⁻¹) ^ k)) *
        ((V⁻¹ ^ (J + 1)) * V⁻¹) * d⁻¹ := by ring
    _ = _ := by rw [hslots]

structure MinorArcParameters where
  α : ℚ
  β : ℚ
  jmath : ℚ
  ϱ : ℚ
  k : ℕ
  A₀ : ℚ
  G : ℚ
  C₀ : ℚ
  E₀ : ℚ

def minorArcParameters (A C cStar : ℚ) : MinorArcParameters :=
  let E := A + 4 * max 0 C + 3
  let G := E + 4
  { α := 1 / 1000
    β := 1 / 100
    jmath := 1 / 100
    ϱ := 1 / 4
    k := Nat.ceil (200 * (G + 3))
    A₀ := G + 3
    G := G
    C₀ := 2 * (max 0 cStar + E + 4)
    E₀ := E }

structure MinorArcBudget (A C cStar : ℚ) (P : MinorArcParameters) : Prop where
  alpha_pos : 0 < P.α
  beta_pos : 0 < P.β
  jmath_pos : 0 < P.jmath
  rho_pos : 0 < P.ϱ
  k_pos : 0 < P.k
  major_pos : 0 < P.A₀
  good_pos : 0 < P.G
  crude_pos : 0 < P.C₀
  saving_pos : 0 < P.E₀
  alpha_lt_beta : P.α < P.β
  beta_lt_half : P.β < 1 / 2
  total_lt_one : P.ϱ + P.β + P.jmath < 1
  rho_gt : P.β + P.jmath < P.ϱ
  major_gt : P.G + P.β + 2 < P.A₀
  memory_gt : P.G + 2 < P.jmath * (P.k : ℚ) / 2
  good_gt : P.E₀ + 3 < P.G
  crude_gt : cStar + P.E₀ + 3 < P.C₀ / 2
  saving_gt : A + 4 * C + 2 < P.E₀

theorem minor_arc_parameter_budget (A C cStar : ℚ) (hA : 0 < A) :
    MinorArcBudget A C cStar (minorArcParameters A C cStar) := by
  have hC := le_max_right (0 : ℚ) C
  have hc := le_max_right (0 : ℚ) cStar
  have hC₀ := le_max_left (0 : ℚ) C
  have hc₀ := le_max_left (0 : ℚ) cStar
  have hceil := Nat.le_ceil (200 * (A + 4 * max 0 C + 3 + 4 + 3))
  have hk : 0 < Nat.ceil (200 * (A + 4 * max 0 C + 3 + 4 + 3)) := by
    have hk' : (0 : ℚ) < (Nat.ceil (200 * (A + 4 * max 0 C + 3 + 4 + 3)) : ℚ) := by
      linarith
    exact_mod_cast hk'
  constructor <;> dsimp [minorArcParameters]
  all_goals try exact hk
  all_goals norm_num
  all_goals linarith

/-- Data to which the external physical and moment estimates apply. -/
structure MinorArcBox where
  logP : ℝ
  X : ℝ
  Y : ℝ
  Z : ℝ
  H : ℕ
  scales : Finset ℕ
  minorValue : ℂ
  pairing : ℕ → ℂ
  historyTrace : ℕ → ℝ
  historyMain : ℕ → ℝ
  historyMemoryError : ℕ → ℝ
  historyGridError : ℕ → ℝ
  sharedActiveError : ℂ
  auxiliaryEndpointError : ℂ
  badRootError : ℂ

noncomputable def MinorArcBox.normalizedPairing (B : MinorArcBox) (d : ℕ) : ℂ :=
  ((d : ℝ)⁻¹) • B.pairing d

def MinorArcBox.twiceHistory (B : MinorArcBox) : ℝ := 2 * (B.H : ℝ)

def MinorArcBox.volume (B : MinorArcBox) : ℝ := B.X * B.Y

/-- The history trace divided by the number-of-vertices scale, with the
geometric factor retained for the spectral estimate. -/
noncomputable def MinorArcBox.moment (B : MinorArcBox) (D : ℕ) : ℝ :=
  (B.H : ℝ) * D * B.Z * B.historyTrace D / (D * B.Y * B.X)

noncomputable def MinorArcBox.historyComponentBound (B : MinorArcBox)
    (D : ℕ) (E₀ : ℚ) (K : ℝ) : ℝ :=
  (B.H : ℝ) * D * B.Z * (K * B.logP ^ (-(E₀ : ℝ))) ^ B.twiceHistory

/-- External estimates for the physical pairing and history moment. -/
structure AnalyticMinorArcInputs (B : MinorArcBox) (C : ℚ) (P : MinorArcParameters)
    (K : ℝ) : Prop where
  log_ge_one : 1 ≤ B.logP
  x_pos : 0 < B.X
  y_pos : 0 < B.Y
  z_nonneg : 0 ≤ B.Z
  history_pos : 0 < B.H
  constant_ge_one : 1 ≤ K
  scale_pos : ∀ d ∈ B.scales, 0 < d
  scale_count : (B.scales.card : ℝ) ≤ B.logP
  pairing_expansion :
    B.minorValue = (∑ d ∈ B.scales, B.normalizedPairing d) +
      B.sharedActiveError + B.auxiliaryEndpointError + B.badRootError
  shared_active_bound :
    ‖B.sharedActiveError‖ ≤ K * B.volume * B.logP ^ (4 * (C : ℝ) - (P.E₀ : ℝ))
  auxiliary_endpoint_bound :
    ‖B.auxiliaryEndpointError‖ ≤ K * B.volume * B.logP ^ (4 * (C : ℝ) - (P.E₀ : ℝ))
  bad_root_bound :
    ‖B.badRootError‖ ≤ K * B.volume * B.logP ^ (4 * (C : ℝ) - (P.E₀ : ℝ))
  moment_nonneg : ∀ d ∈ B.scales, 0 ≤ B.moment d
  spectral_holder : ∀ d ∈ B.scales,
    ‖B.normalizedPairing d‖ ≤
      K * B.volume * B.logP ^ (4 * (C : ℝ)) * B.moment d ^ B.twiceHistory⁻¹
  history_expansion : ∀ D ∈ B.scales,
    B.moment D = B.historyMain D + B.historyMemoryError D + B.historyGridError D
  history_main_bound : ∀ D ∈ B.scales,
    |B.historyMain D| ≤ B.historyComponentBound D P.E₀ K
  history_memory_bound : ∀ D ∈ B.scales,
    |B.historyMemoryError D| ≤ B.historyComponentBound D P.E₀ K
  history_grid_bound : ∀ D ∈ B.scales,
    |B.historyGridError D| ≤ B.historyComponentBound D P.E₀ K
  geometry_bound : ∀ d ∈ B.scales,
    (B.H : ℝ) * d * B.Z ≤ B.logP ^ B.twiceHistory

theorem minor_arc_assembled_moment_bound {B : MinorArcBox} {C : ℚ}
    {P : MinorArcParameters} {K : ℝ} (I : AnalyticMinorArcInputs B C P K)
    {D : ℕ} (hD : D ∈ B.scales) :
    B.moment D ≤ (B.H : ℝ) * D * B.Z *
      (3 * K * B.logP ^ (-(P.E₀ : ℝ))) ^ B.twiceHistory := by
  have hL : 0 < B.logP := lt_of_lt_of_le zero_lt_one I.log_ge_one
  have hK : 0 ≤ K := le_trans zero_le_one I.constant_ge_one
  have hZ := I.z_nonneg
  have hHnat : 1 ≤ B.H := I.history_pos
  have hH : (1 : ℝ) ≤ (B.H : ℝ) := by exact_mod_cast hHnat
  have hN : 1 ≤ B.twiceHistory := by unfold MinorArcBox.twiceHistory; linarith
  have hthree : (3 : ℝ) ≤ (3 : ℝ) ^ B.twiceHistory := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hN
  have hmain := (le_abs_self _).trans (I.history_main_bound D hD)
  have hmemory := (le_abs_self _).trans (I.history_memory_bound D hD)
  have hgrid := (le_abs_self _).trans (I.history_grid_bound D hD)
  have hcomponent : 0 ≤ B.historyComponentBound D P.E₀ K := by
    unfold MinorArcBox.historyComponentBound
    positivity
  have hU : 0 ≤ K * B.logP ^ (-(P.E₀ : ℝ)) := by positivity
  calc
    _ = B.historyMain D + B.historyMemoryError D + B.historyGridError D :=
      I.history_expansion D hD
    _ ≤ 3 * B.historyComponentBound D P.E₀ K := by linarith
    _ ≤ (3 : ℝ) ^ B.twiceHistory * B.historyComponentBound D P.E₀ K :=
      mul_le_mul_of_nonneg_right hthree hcomponent
    _ = _ := by
      unfold MinorArcBox.historyComponentBound
      rw [mul_assoc (3 : ℝ) K, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hU]
      ring

theorem minor_arc_normalized_pairing_bound {B : MinorArcBox} {C : ℚ}
    {P : MinorArcParameters} {K : ℝ} (I : AnalyticMinorArcInputs B C P K)
    {d : ℕ} (hd : d ∈ B.scales) :
    ‖B.normalizedPairing d‖ ≤
      (3 * K * K) * B.volume * B.logP ^ (4 * (C : ℝ) - (P.E₀ : ℝ)) *
        ((B.H : ℝ) * d * B.Z) ^ B.twiceHistory⁻¹ := by
  have hL : 0 < B.logP := lt_of_lt_of_le zero_lt_one I.log_ge_one
  have hK : 0 ≤ K := le_trans zero_le_one I.constant_ge_one
  have hX := I.x_pos
  have hY := I.y_pos
  have hZ := I.z_nonneg
  have hVol : 0 ≤ B.volume := mul_nonneg hX.le hY.le
  have hH : (0 : ℝ) < (B.H : ℝ) := by exact_mod_cast I.history_pos
  have hN : 0 < B.twiceHistory := by unfold MinorArcBox.twiceHistory; positivity
  have hmass : 0 ≤ (B.H : ℝ) * d * B.Z := by positivity
  have hpower : 0 ≤ 3 * K * B.logP ^ (-(P.E₀ : ℝ)) := by positivity
  have hroot := Real.rpow_le_rpow (I.moment_nonneg d hd) (minor_arc_assembled_moment_bound I hd)
    (inv_nonneg.mpr hN.le)
  rw [Real.mul_rpow hmass (Real.rpow_nonneg hpower _), ← Real.rpow_mul hpower,
    mul_inv_cancel₀ hN.ne', Real.rpow_one] at hroot
  calc
    _ ≤ K * B.volume * B.logP ^ (4 * (C : ℝ)) * B.moment d ^ B.twiceHistory⁻¹ :=
      I.spectral_holder d hd
    _ ≤ K * B.volume * B.logP ^ (4 * (C : ℝ)) *
        (((B.H : ℝ) * d * B.Z) ^ B.twiceHistory⁻¹ * (3 * K * B.logP ^ (-(P.E₀ : ℝ)))) :=
      mul_le_mul_of_nonneg_left hroot (by positivity)
    _ = _ := by
      rw [sub_eq_add_neg, Real.rpow_add hL]
      ring

theorem minor_arc_physical_pairing_bound {B : MinorArcBox} {C : ℚ}
    {P : MinorArcParameters} {K : ℝ} (I : AnalyticMinorArcInputs B C P K)
    {D : ℕ} (hD : D ∈ B.scales) :
    (D : ℝ)⁻¹ * ‖B.pairing D‖ ≤
      (3 * K * K) * B.volume * B.logP ^ (4 * (C : ℝ) - (P.E₀ : ℝ)) *
        ((B.H : ℝ) * D * B.Z) ^ B.twiceHistory⁻¹ := by
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast I.scale_pos D hD
  simpa only [MinorArcBox.normalizedPairing, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr hDpos.le)] using minor_arc_normalized_pairing_bound I hD

/-- The conditional estimate includes the loss from summing the dyadic scales. -/
theorem minor_arc_arbitrary_log_saving (A C cStar : ℚ) (hA : 0 < A)
    {B : MinorArcBox} {K : ℝ}
    (I : AnalyticMinorArcInputs B C (minorArcParameters A C cStar) K) :
    ‖B.minorValue‖ ≤ (3 * K * K + 3 * K) * B.X * B.Y * B.logP ^ (-(A : ℝ)) := by
  let P := minorArcParameters A C cStar
  let τ : ℝ := 4 * (C : ℝ) - (P.E₀ : ℝ)
  have hbudget := minor_arc_parameter_budget A C cStar hA
  have hsave : (A : ℝ) + 4 * (C : ℝ) + 2 < (P.E₀ : ℝ) := by
    exact_mod_cast hbudget.saving_gt
  have hL : 0 < B.logP := lt_of_lt_of_le zero_lt_one I.log_ge_one
  have hK : 0 ≤ K := le_trans zero_le_one I.constant_ge_one
  have hX := I.x_pos
  have hY := I.y_pos
  have hZ := I.z_nonneg
  have hVol : 0 ≤ B.volume := mul_nonneg hX.le hY.le
  have hH : (0 : ℝ) < (B.H : ℝ) := by exact_mod_cast I.history_pos
  have hN : 0 < B.twiceHistory := by unfold MinorArcBox.twiceHistory; positivity
  have hblock (d : ℕ) (hd : d ∈ B.scales) :
      ‖B.normalizedPairing d‖ ≤ 3 * K * K * B.volume * B.logP ^ (τ + 1) := by
    have hmass : 0 ≤ (B.H : ℝ) * d * B.Z := by positivity
    have hgeo := Real.rpow_le_rpow hmass (I.geometry_bound d hd) (inv_nonneg.mpr hN.le)
    rw [← Real.rpow_mul hL.le, mul_inv_cancel₀ hN.ne', Real.rpow_one] at hgeo
    calc
      _ ≤ _ := minor_arc_normalized_pairing_bound I hd
      _ ≤ 3 * K * K * B.volume * B.logP ^ τ * B.logP :=
        mul_le_mul_of_nonneg_left hgeo (by positivity)
      _ = _ := by rw [Real.rpow_add hL, Real.rpow_one]; ring
  have hsum : ‖∑ d ∈ B.scales, B.normalizedPairing d‖ ≤
      3 * K * K * B.volume * B.logP ^ (-(A : ℝ)) := by
    calc
      _ ≤ ∑ d ∈ B.scales, ‖B.normalizedPairing d‖ := norm_sum_le _ _
      _ ≤ ∑ _d ∈ B.scales, 3 * K * K * B.volume * B.logP ^ (τ + 1) :=
        Finset.sum_le_sum hblock
      _ = (B.scales.card : ℝ) * (3 * K * K * B.volume * B.logP ^ (τ + 1)) := by simp
      _ ≤ B.logP * (3 * K * K * B.volume * B.logP ^ (τ + 1)) :=
        mul_le_mul_of_nonneg_right I.scale_count (by positivity)
      _ = 3 * K * K * B.volume * B.logP ^ (τ + 1 + 1) := by
        rw [Real.rpow_add hL (τ + 1) 1, Real.rpow_one]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le I.log_ge_one (by dsimp [τ]; linarith))
        (by positivity)
  have herrExponent : K * B.volume * B.logP ^ τ ≤
      K * B.volume * B.logP ^ (-(A : ℝ)) := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le I.log_ge_one (by dsimp [τ]; linarith))
    (by positivity)
  rw [I.pairing_expansion]
  calc
    _ ≤ ‖∑ d ∈ B.scales, B.normalizedPairing d‖ +
        ‖B.sharedActiveError‖ + ‖B.auxiliaryEndpointError‖ +
        ‖B.badRootError‖ := by
      refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
      refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
      exact norm_add_le _ _
    _ ≤ 3 * K * K * B.volume * B.logP ^ (-(A : ℝ)) +
        K * B.volume * B.logP ^ (-(A : ℝ)) +
        K * B.volume * B.logP ^ (-(A : ℝ)) +
        K * B.volume * B.logP ^ (-(A : ℝ)) := by
      exact add_le_add (add_le_add (add_le_add hsum
        (I.shared_active_bound.trans herrExponent)) (I.auxiliary_endpoint_bound.trans herrExponent))
          (I.bad_root_bound.trans herrExponent)
    _ = _ := by unfold MinorArcBox.volume; ring

/-- A positive rational target above any prescribed real exponent. -/
noncomputable def rationalLogTarget (A : ℝ) : ℚ := (Nat.ceil A + 1 : ℕ)

theorem minor_arc_arbitrary_real_log_saving (A : ℝ) (C cStar : ℚ)
    {B : MinorArcBox} {K : ℝ}
    (I : AnalyticMinorArcInputs B C (minorArcParameters (rationalLogTarget A) C cStar) K) :
    ‖B.minorValue‖ ≤ (3 * K * K + 3 * K) * B.X * B.Y * B.logP ^ (-A) := by
  have hA : 0 < rationalLogTarget A := by unfold rationalLogTarget; positivity
  have hceil : A ≤ (rationalLogTarget A : ℝ) := by
    have h := Nat.le_ceil A
    dsimp [rationalLogTarget]
    push_cast
    linarith
  have hK : 0 ≤ K := le_trans zero_le_one I.constant_ge_one
  have hX := I.x_pos
  have hY := I.y_pos
  exact (minor_arc_arbitrary_log_saving (rationalLogTarget A) C cStar hA I).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le I.log_ge_one (neg_le_neg hceil)) (by positivity))

end Target3A
