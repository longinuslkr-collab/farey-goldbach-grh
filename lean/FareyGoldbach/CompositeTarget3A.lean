import FareyGoldbach.Defs

open scoped Matrix

/-!
# Integer lattice lemmas for the composite reflected Möbius problem

The first coordinate of a root, and the first coordinate of any transported
physical vertex at which primitiveness is tested, are units modulo the index.
-/

namespace CompositeTarget3A

/-- The completion with first column `(x, y)` and determinant `-N`,
provided that `x ∣ y * u - N`. -/
def latticeMatrix (N x y u : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![x, u; y, (y * u - N) / x]

private theorem completion_eq {N x y u : ℤ} (h : x ∣ y * u - N) :
    x * ((y * u - N) / x) - u * y = -N := by
  have hd := Int.ediv_mul_cancel h
  linear_combination hd

theorem latticeMatrix_det {N x y u : ℤ} (h : x ∣ y * u - N) :
    (latticeMatrix N x y u).det = -N := by
  simpa only [latticeMatrix, Matrix.det_fin_two_of] using completion_eq h

@[simp] theorem latticeMatrix_mulVec_zero (N x y u : ℤ) (w : Fin 2 → ℤ) :
    (latticeMatrix N x y u *ᵥ w) 0 = x * w 0 + u * w 1 := by
  simp [latticeMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

@[simp] theorem latticeMatrix_mulVec_one (N x y u : ℤ) (w : Fin 2 → ℤ) :
    (latticeMatrix N x y u *ᵥ w) 1 = y * w 0 + ((y * u - N) / x) * w 1 := by
  simp [latticeMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Bézout gives an integer determinant completion of every primitive root. -/
theorem exists_lattice_completion {N x y : ℤ} (hxy : IsCoprime x y) :
    ∃ u : ℤ, x ∣ y * u - N := by
  obtain ⟨a, b, hab⟩ := hxy
  refine ⟨N * b, -N * a, ?_⟩
  linear_combination N * hab

/-- In a determinant completion, the first coordinate's being a unit modulo
the index also forces the root to be physically primitive. -/
theorem root_coprime_of_unit {N x y u : ℤ} (h : x ∣ y * u - N)
    (hxN : IsCoprime x N) : IsCoprime x y := by
  obtain ⟨a, b, hab⟩ := hxN
  have hdet := completion_eq h
  refine ⟨a - b * ((y * u - N) / x), b * u, ?_⟩
  linear_combination hab - b * hdet

/-- Exact image of a determinant completion at a primitive root. -/
theorem latticeMatrix_range_of_primitive {N x y u : ℤ} (h : x ∣ y * u - N)
    (hxy : IsCoprime x y) :
    Set.range (fun w => latticeMatrix N x y u *ᵥ w) =
      {z : Fin 2 → ℤ | N ∣ x * z 1 - y * z 0} := by
  let d := (y * u - N) / x
  have hdet : x * d - u * y = -N := completion_eq h
  ext z
  change (∃ w, latticeMatrix N x y u *ᵥ w = z) ↔ N ∣ x * z 1 - y * z 0
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨-w 1, ?_⟩
    simp only [latticeMatrix_mulVec_zero, latticeMatrix_mulVec_one]
    change x * (y * w 0 + d * w 1) - y * (x * w 0 + u * w 1) = N * (-w 1)
    linear_combination (w 1) * hdet
  · rintro ⟨k, hk⟩
    obtain ⟨a, b, hab⟩ := hxy
    let U := z 0 + u * k
    let V := z 1 + d * k
    have hz : x * V - y * U = 0 := by
      dsimp [U, V]
      linear_combination hk + k * hdet
    have hx : x * (a * U + b * V) = U := by
      linear_combination U * hab + b * hz
    have hy : y * (a * U + b * V) = V := by
      linear_combination V * hab - a * hz
    refine ⟨![a * U + b * V, -k], ?_⟩
    ext i
    fin_cases i
    · change (latticeMatrix N x y u *ᵥ ![a * U + b * V, -k]) 0 = z 0
      rw [latticeMatrix_mulVec_zero]
      change x * (a * U + b * V) + u * (-k) = z 0
      rw [hx]
      dsimp [U]
      ring
    · change (latticeMatrix N x y u *ᵥ ![a * U + b * V, -k]) 1 = z 1
      rw [latticeMatrix_mulVec_one]
      change y * (a * U + b * V) + d * (-k) = z 1
      rw [hy]
      dsimp [V]
      ring

theorem latticeMatrix_range {N x y u : ℤ} (h : x ∣ y * u - N)
    (hxN : IsCoprime x N) :
    Set.range (fun w => latticeMatrix N x y u *ᵥ w) =
      {z : Fin 2 → ℤ | N ∣ x * z 1 - y * z 0} :=
  latticeMatrix_range_of_primitive h (root_coprime_of_unit h hxN)

/-- The adjugate forces any new common divisor to divide the index.
The unit condition is on the first coordinate of the transported vertex. -/
theorem latticeMatrix_primitive_in_box {N x y u : ℤ}
    (h : x ∣ y * u - N) {w : Fin 2 → ℤ}
    (hunit : IsCoprime ((latticeMatrix N x y u *ᵥ w) 0) N) :
    IsCoprime ((latticeMatrix N x y u *ᵥ w) 0) ((latticeMatrix N x y u *ᵥ w) 1)
      ↔ IsCoprime (w 0) (w 1) := by
  let d := (y * u - N) / x
  have hdet : x * d - u * y = -N := completion_eq h
  let X := x * w 0 + u * w 1
  let Y := y * w 0 + d * w 1
  simp only [latticeMatrix_mulVec_zero, latticeMatrix_mulVec_one] at hunit ⊢
  change IsCoprime X N at hunit
  change IsCoprime X Y ↔ IsCoprime (w 0) (w 1)
  constructor
  · rintro ⟨a, b, hab⟩
    refine ⟨a * x + b * y, a * u + b * d, ?_⟩
    dsimp [X, Y] at hab
    linear_combination hab
  · rintro ⟨a, b, hab⟩
    obtain ⟨c, e, hce⟩ := hunit
    have hw0 : u * Y - d * X = N * w 0 := by
      dsimp [X, Y]
      linear_combination -(w 0) * hdet
    have hw1 : y * X - x * Y = N * w 1 := by
      dsimp [X, Y]
      linear_combination -(w 1) * hdet
    have hsum : (b * y - a * d) * X + (a * u - b * x) * Y = N := by
      linear_combination a * hw0 + b * hw1 + N * hab
    refine ⟨c + e * (b * y - a * d), e * (a * u - b * x), ?_⟩
    linear_combination hce + e * hsum

/-- Cross-multiplied collinearity is transitive when the middle first
coordinate is a unit, for every integer modulus. -/
theorem collinear_trans {N x₀ y₀ x₁ y₁ x₂ y₂ : ℤ}
    (hx₁ : IsCoprime x₁ N)
    (h₀₁ : N ∣ x₀ * y₁ - y₀ * x₁)
    (h₁₂ : N ∣ x₁ * y₂ - y₁ * x₂) :
    N ∣ x₀ * y₂ - y₀ * x₂ := by
  obtain ⟨a, b, hab⟩ := hx₁
  obtain ⟨j, hj⟩ := h₀₁
  obtain ⟨k, hk⟩ := h₁₂
  refine ⟨a * (x₀ * k + x₂ * j) + b * (x₀ * y₂ - y₀ * x₂), ?_⟩
  linear_combination a * x₂ * hj + a * x₀ * hk - (x₀ * y₂ - y₀ * x₂) * hab

/-- The completion count can use a Kloosterman sum modulo `x * t` if
the first coordinate is a unit modulo the index and `t ∣ x`. -/
theorem kloosterman_rhs_coprime {N x t c : ℤ}
    (hxN : IsCoprime x N) (ht : t ∣ x) : IsCoprime (N + x * c) (x * t) := by
  have hx : IsCoprime (N + x * c) x := by
    simpa only [mul_comm x c] using hxN.symm.add_mul_right_left c
  exact hx.mul_right (hx.of_isCoprime_of_dvd_right ht)

/-- Dividing an integer and its modulus by their exact gcd leaves coprime integers. -/
theorem gcd_strip {n N g n₁ N₁ : ℤ} (hg : g ≠ 0)
    (hN : N = g * N₁) (hn : n = g * n₁) (h : n.gcd N = g.natAbs) :
    n₁.gcd N₁ = 1 := by
  have hgpos : 0 < g.natAbs := Int.natAbs_pos.mpr hg
  rw [hn, hN, Int.gcd_mul_left] at h
  exact Nat.eq_of_mul_eq_mul_left hgpos (h.trans (Nat.mul_one _).symm)

/-- The minus-shift numerator has a common cofactor before exact gcd division
if and only if the quotient numerators have the same reduced cofactor.
No condition on `gcd Δ N` is needed. -/
theorem minus_cofactor_strip {N N₁ g Δ r₁ a b m n n₁ r s s₁ q : ℤ}
    (hg : g ≠ 0) (hN : N = g * N₁) (hn : n = g * n₁) (hs : s = g * s₁) :
    (m * n - Δ * N = a * r₁ * (g * q) ∧
      r * s - Δ * N = b * r₁ * (g * q)) ↔
    (m * n₁ - Δ * N₁ = a * r₁ * q ∧
      r * s₁ - Δ * N₁ = b * r₁ * q) := by
  have strip (x y c : ℤ) :
      x * (g * y) - Δ * (g * N₁) = c * r₁ * (g * q) ↔
        x * y - Δ * N₁ = c * r₁ * q := by
    rw [show x * (g * y) - Δ * (g * N₁) = g * (x * y - Δ * N₁) by ring,
        show c * r₁ * (g * q) = g * (c * r₁ * q) by ring]
    exact ⟨mul_left_cancel₀ hg, congrArg (g * ·)⟩
  rw [hN, hn, hs, strip, strip]

/-- If the label and the first prime are units modulo `g`, the original
cofactor must contain all of `g`, even when `g` and `Δ` have common factors. -/
theorem gcd_dvd_cofactor {N n g Δ r₁ a m q : ℤ}
    (hN : g ∣ N) (hn : g ∣ n) (hunit : g.gcd (a * r₁) = 1)
    (h : m * n - Δ * N = a * r₁ * q) : g ∣ q := by
  apply Int.dvd_of_dvd_mul_right_of_gcd_one _ hunit
  rw [← h]
  obtain ⟨n₁, hn₁⟩ := hn
  obtain ⟨N₁, hN₁⟩ := hN
  exact ⟨m * n₁ - Δ * N₁, by rw [hn₁, hN₁]; ring⟩

/-- Sharing an unrestricted original cofactor is equivalent to sharing a
reduced cofactor. The divisibility of the original cofactor by `g` is derived. -/
theorem minus_cofactor_strip_exists {N N₁ g Δ r₁ a b m n n₁ r s s₁ : ℤ}
    (hg : g ≠ 0) (hN : N = g * N₁) (hn : n = g * n₁) (hs : s = g * s₁)
    (hunit : g.gcd (a * r₁) = 1) :
    (∃ q : ℤ, m * n - Δ * N = a * r₁ * q ∧ r * s - Δ * N = b * r₁ * q) ↔
    (∃ q : ℤ, m * n₁ - Δ * N₁ = a * r₁ * q ∧ r * s₁ - Δ * N₁ = b * r₁ * q) := by
  constructor
  · rintro ⟨q, hleft, hright⟩
    obtain ⟨u, rfl⟩ := gcd_dvd_cofactor ⟨N₁, hN⟩ ⟨n₁, hn⟩ hunit hleft
    exact ⟨u, (minus_cofactor_strip hg hN hn hs).mp ⟨hleft, hright⟩⟩
  · rintro ⟨q, hleft, hright⟩
    exact ⟨g * q, (minus_cofactor_strip hg hN hn hs).mpr ⟨hleft, hright⟩⟩

/-- The integer determinant is equivalent to sharing a reduced cofactor,
once each minus-shift numerator satisfies the first-prime divisibility. -/
theorem minus_cofactor_determinant {Q Δ r₁ a b x y : ℤ}
    (ha : a ≠ 0) (hr : r₁ ≠ 0) (hab : a.gcd b = 1)
    (hx : r₁ ∣ x - Δ * Q) (hy : r₁ ∣ y - Δ * Q) :
    (∃ q : ℤ, x - Δ * Q = a * r₁ * q ∧ y - Δ * Q = b * r₁ * q) ↔
      b * x - a * y = Δ * Q * (b - a) := by
  constructor
  · rintro ⟨q, h₁, h₂⟩
    linear_combination b * h₁ - a * h₂
  · intro h
    obtain ⟨u, hu⟩ := hx
    obtain ⟨v, hv⟩ := hy
    have hscaled : r₁ * (b * u) = r₁ * (a * v) := by
      linear_combination h - b * hu + a * hv
    have heq := mul_left_cancel₀ hr hscaled
    obtain ⟨q, hq⟩ := Int.dvd_of_dvd_mul_right_of_gcd_one (show a ∣ b * u from ⟨v, heq⟩) hab
    have hvq : v = b * q := by
      apply mul_left_cancel₀ ha
      calc
        a * v = b * u := heq.symm
        _ = a * (b * q) := by rw [hq]; ring
    exact ⟨q, by rw [hu, hq]; ring, by rw [hv, hvq]; ring⟩

/-- The modulus `r₂` uses only the coprimality of `r₁` and `r₂`.
In particular, it imposes no coprimality between the large modulus and the gap. -/
theorem minus_cofactor_mod_second_prime {Q r₁ r₂ a m n q : ℤ}
    (hr₂ : 0 < r₂) (hr : r₂.gcd r₁ = 1) (hn : r₂ ∣ n)
    (h : m * n - (r₂ - r₁) * Q = a * r₁ * q) :
    a * q ≡ Q [ZMOD r₂] := by
  have hdiff : r₂ ∣ r₁ * (a * q) - r₁ * Q := by
    rw [show r₁ * (a * q) - r₁ * Q = m * n - r₂ * Q by linear_combination -h]
    obtain ⟨n₀, hn₀⟩ := hn
    exact ⟨m * n₀ - Q, by rw [hn₀]; ring⟩
  have hscaled : r₁ * (a * q) ≡ r₁ * Q [ZMOD r₂] := (Int.modEq_iff_dvd.mpr hdiff).symm
  simpa only [hr, Int.natCast_one, Int.ediv_one] using Int.ModEq.cancel_left_div_gcd hr₂ hscaled

/-- An explicit squared-error budget. The loss permits up to `R^3` from
the second-moment normalization, `R^2` from residue blocks and `R^4`
from squaring the number of Kátai pairs. `C` collects fixed logarithmic losses. -/
theorem log_budget {L R : ℝ} {K C S : ℕ} (hL : 1 ≤ L) (hR₀ : 0 ≤ R)
    (hR : R ≤ L ^ K) :
    R ^ 9 * L ^ C / L ^ (9 * K + C + S) ≤ 1 / L ^ S := by
  have hpos : 0 < L := zero_lt_one.trans_le hL
  have hpow : R ^ 9 ≤ L ^ (9 * K) := by
    rw [Nat.mul_comm 9 K, pow_mul]
    exact pow_le_pow_left₀ hR₀ hR 9
  have hnum : R ^ 9 * L ^ C ≤ L ^ (9 * K + C) := by
    rw [pow_add]
    exact mul_le_mul_of_nonneg_right hpow (pow_nonneg hpos.le _)
  calc
    _ ≤ L ^ (9 * K + C) / L ^ (9 * K + C + S) :=
      div_le_div_of_nonneg_right hnum (pow_nonneg hpos.le _)
    _ = 1 / L ^ S := by
      field_simp [ne_of_gt hpos]
      simp only [pow_add]

end CompositeTarget3A
