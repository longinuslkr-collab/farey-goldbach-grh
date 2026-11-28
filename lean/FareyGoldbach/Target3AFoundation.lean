import FareyGoldbach.Defs

open scoped Matrix

namespace Target3A

/-- Absorbing `r₂` in the product belonging to the first linear form gives a minus shift. -/
theorem physicalShift (p r₁ r₂ s₀ : ℤ) :
    r₂ * (p - r₁ * s₀) - (r₂ - r₁) * p = r₁ * (p - r₂ * s₀) := by
  ring

theorem productBlockModEq {p r₁ r₂ m n i j : ℤ}
    (hm : m ≡ i [ZMOD r₁]) (hn : n ≡ r₂ * p * j [ZMOD r₁])
    (hinv : i * j ≡ 1 [ZMOD r₁]) :
    m * n ≡ r₂ * p [ZMOD r₁] := by
  have h := hinv.mul_left (r₂ * p)
  rw [mul_one, show r₂ * p * (i * j) = i * (r₂ * p * j) by ring] at h
  exact (hm.mul hn).trans h

/-- The positive residue block makes the plus-shift numerator congruent to `2 * r₂ * p`. -/
theorem plusShiftResidue {p r₁ r₂ m n i j : ℤ}
    (hm : m ≡ i [ZMOD r₁]) (hn : n ≡ r₂ * p * j [ZMOD r₁])
    (hinv : i * j ≡ 1 [ZMOD r₁]) :
    m * n + (r₂ - r₁) * p ≡ 2 * r₂ * p [ZMOD r₁] := by
  have hshift := (productBlockModEq hm hn hinv).add_right ((r₂ - r₁) * p)
  exact hshift.trans (Int.modEq_of_dvd ⟨p, by ring⟩)

theorem plusShiftObstruction {p r₁ r₂ m n i j : ℤ}
    (hm : m ≡ i [ZMOD r₁]) (hn : n ≡ r₂ * p * j [ZMOD r₁])
    (hinv : i * j ≡ 1 [ZMOD r₁]) (hodd : ¬ r₁ ∣ 2 * r₂ * p) :
    ¬ r₁ ∣ m * n + (r₂ - r₁) * p := by
  intro h
  exact hodd (Int.modEq_zero_iff_dvd.mp
    ((plusShiftResidue hm hn hinv).symm.trans h.modEq_zero_int))

theorem minusShiftDivisibility {p r₁ r₂ m n i j : ℤ}
    (hm : m ≡ i [ZMOD r₁]) (hn : n ≡ r₂ * p * j [ZMOD r₁])
    (hinv : i * j ≡ 1 [ZMOD r₁]) :
    r₁ ∣ m * n - (r₂ - r₁) * p := by
  have hshift := (productBlockModEq hm hn hinv).sub_right ((r₂ - r₁) * p)
  rw [show r₂ * p - (r₂ - r₁) * p = r₁ * p by ring] at hshift
  exact Int.modEq_zero_iff_dvd.mp (hshift.trans (dvd_mul_right r₁ p).modEq_zero_int)

/-- The determinant identity recovers a common cofactor once both shifted products
are known to be multiples of `r₁`. The signed shift is `t`. -/
theorem cofactorEquiv {a b r₁ x y t : ℤ}
    (ha : a ≠ 0) (hr₁ : r₁ ≠ 0) (hab : Int.gcd a b = 1)
    (hx : r₁ ∣ x + t) (hy : r₁ ∣ y + t) :
    (∃ q : ℤ, x + t = a * r₁ * q ∧ y + t = b * r₁ * q) ↔
      b * x - a * y = t * (a - b) := by
  constructor
  · rintro ⟨q, hq₁, hq₂⟩
    linear_combination b * hq₁ - a * hq₂
  · intro h
    obtain ⟨u, hu⟩ := hx
    obtain ⟨v, hv⟩ := hy
    have hcross : b * (x + t) = a * (y + t) := by
      linear_combination h
    have hscaled : r₁ * (b * u) = r₁ * (a * v) := by
      calc
        r₁ * (b * u) = b * (x + t) := by rw [hu]; ring
        _ = a * (y + t) := hcross
        _ = r₁ * (a * v) := by rw [hv]; ring
    have heq : b * u = a * v := mul_left_cancel₀ hr₁ hscaled
    have hd : a ∣ b * u := ⟨v, heq⟩
    obtain ⟨q, hq⟩ := Int.dvd_of_dvd_mul_right_of_gcd_one hd hab
    have hvq : v = b * q := by
      apply mul_left_cancel₀ ha
      calc
        a * v = b * u := heq.symm
        _ = a * (b * q) := by rw [hq]; ring
    exact ⟨q, by rw [hu, hq]; ring, by rw [hv, hvq]; ring⟩

theorem correctedCofactorEquiv {p r₁ r₂ a b m n r s i j : ℤ}
    (ha : a ≠ 0) (hr₁ : r₁ ≠ 0) (hab : Int.gcd a b = 1)
    (hm : m ≡ i [ZMOD r₁]) (hn : n ≡ r₂ * p * j [ZMOD r₁])
    (hr : r ≡ i [ZMOD r₁]) (hs : s ≡ r₂ * p * j [ZMOD r₁])
    (hinv : i * j ≡ 1 [ZMOD r₁]) :
    (∃ q : ℤ, m * n - (r₂ - r₁) * p = a * r₁ * q ∧
      r * s - (r₂ - r₁) * p = b * r₁ * q) ↔
    b * (m * n) - a * (r * s) = (r₂ - r₁) * p * (b - a) := by
  have hx := minusShiftDivisibility hm hn hinv
  have hy := minusShiftDivisibility hr hs hinv
  have hsign : -((r₂ - r₁) * p) * (a - b) = (r₂ - r₁) * p * (b - a) := by ring
  have h := cofactorEquiv (t := -((r₂ - r₁) * p)) ha hr₁ hab
    (by simpa only [sub_eq_add_neg] using hx)
    (by simpa only [sub_eq_add_neg] using hy)
  rw [hsign] at h
  simpa only [sub_eq_add_neg] using h

/-- Regression: the `p = 101` example fails the `r₁` congruence for the plus shift. -/
theorem originalNumericalRegression :
    (7 : ℤ) * (11 * 4) - 5 * (17 * 6) = 101 * (5 - 7) ∧
    (11 : ℤ) * 4 + 101 = 5 * 29 ∧ (17 : ℤ) * 6 + 101 = 7 * 29 ∧
    ¬ ((11 : ℤ) * 4 ≡ 2 * 101 [ZMOD 3]) ∧
    ¬ ∃ q : ℤ, 11 * 4 + 101 = 5 * 3 * q ∧ 17 * 6 + 101 = 7 * 3 * q := by
  refine ⟨by norm_num, by norm_num, by norm_num, by decide, ?_⟩
  rintro ⟨q, hq, _⟩
  have h : (3 : ℤ) ∣ 11 * 4 + 101 := ⟨5 * q, by linear_combination hq⟩
  norm_num at h

/-- Regression: with literal `r₁ < r₂` and residue block, the plus shift still fails. -/
theorem positiveOrderRegression :
    (3 : ℤ) < 5 ∧ (5 : ℤ) ∣ 10 ∧ (5 : ℤ) ∣ 25 ∧
    (7 : ℤ) ≡ 1 [ZMOD 3] ∧ (22 : ℤ) ≡ 1 [ZMOD 3] ∧
    (10 : ℤ) ≡ 5 * 101 [ZMOD 3] ∧ (25 : ℤ) ≡ 5 * 101 [ZMOD 3] ∧
    Int.gcd 17 47 = 1 ∧
    (47 : ℤ) * (7 * 10) - 17 * (22 * 25) = (5 - 3) * 101 * (17 - 47) ∧
    (7 : ℤ) * 10 + (5 - 3) * 101 = 17 * 16 ∧
    (22 : ℤ) * 25 + (5 - 3) * 101 = 47 * 16 ∧
    ¬ ∃ q : ℤ, 7 * 10 + (5 - 3) * 101 = 17 * 3 * q ∧
      22 * 25 + (5 - 3) * 101 = 47 * 3 * q := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, ?_⟩
  rintro ⟨q, hq, _⟩
  have h : (3 : ℤ) ∣ 7 * 10 + (5 - 3) * 101 := ⟨17 * q, by linear_combination hq⟩
  norm_num at h

private def noDvdFrom (p : ℕ) : ℕ → Bool
  | 0 => true
  | 1 => true
  | k + 1 => decide (p % (k + 1) ≠ 0) && noDvdFrom p k

private theorem noDvdFrom_spec (p B : ℕ) (h : noDvdFrom p B = true) :
    ∀ m, 2 ≤ m → m ≤ B → ¬ m ∣ p := by
  induction B with
  | zero => intro m hm h0; omega
  | succ k ih =>
    cases k with
    | zero => intro m hm h1; omega
    | succ k' =>
      simp only [noDvdFrom, Bool.and_eq_true, decide_eq_true_eq] at h
      intro m hm2 hmle
      by_cases htop : m = k' + 2
      · subst htop; exact fun hd => h.1 (Nat.mod_eq_zero_of_dvd hd)
      · exact ih h.2 m hm2 (by omega)

private theorem nat_prime_of_bound (p B : ℕ) (hp : 2 ≤ p) (hB : p < (B + 1) * (B + 1))
    (h : noDvdFrom p B = true) : Nat.Prime p := by
  have hno := noDvdFrom_spec p B h
  rw [Nat.prime_def_lt']
  refine ⟨hp, fun m hm2 hmp hdvd => ?_⟩
  by_cases hmB : m ≤ B
  · exact hno m hm2 hmB hdvd
  · have hq_dvd : p / m ∣ p := Nat.div_dvd_of_dvd hdvd
    have hmul : m * (p / m) = p := Nat.mul_div_cancel' hdvd
    have hq2 : 2 ≤ p / m := by nlinarith
    have hqB : p / m ≤ B := by nlinarith
    exact hno (p / m) hq2 hqB hq_dvd

/-- Regression: a positive-order example with prime factors and primitive physical box endpoints. -/
theorem physicalBoxRegression :
    Nat.Prime 21599 ∧ Nat.Prime 73 ∧ Nat.Prime 103 ∧ Nat.Prime 109 ∧ Nat.Prime 127 ∧
    (103 : ℤ) < 109 ∧ (103 : ℤ) < 127 ∧
    (109 : ℤ) ≡ 1 [ZMOD 3] ∧ (127 : ℤ) ≡ 1 [ZMOD 3] ∧
    (475 : ℤ) ≡ 5 * 21599 [ZMOD 3] ∧ (715 : ℤ) ≡ 5 * 21599 [ZMOD 3] ∧
    (109 : ℤ) * 475 = 5 * (21599 - 3 * 3748) ∧
    (127 : ℤ) * 715 = 5 * (21599 - 3 * 1146) ∧
    (103 : ℤ) * 109 < 21599 ∧ (73 : ℤ) * 127 < 21599 ∧
    (475 : ℤ) < 21599 ∧ (715 : ℤ) < 21599 ∧
    Int.gcd (103 * 109) 715 = 1 ∧ Int.gcd (73 * 127) 475 = 1 ∧
    (103 : ℤ) * (109 * 475) - 73 * (127 * 715) = (5 - 3) * 21599 * (73 - 103) ∧
    (109 : ℤ) * 475 + (5 - 3) * 21599 = 73 * 1301 ∧
    (127 : ℤ) * 715 + (5 - 3) * 21599 = 103 * 1301 ∧
    ¬ ∃ q : ℤ, 109 * 475 + (5 - 3) * 21599 = 73 * 3 * q ∧
      127 * 715 + (5 - 3) * 21599 = 103 * 3 * q := by
  refine ⟨nat_prime_of_bound 21599 147 (by decide) (by decide) rfl,
    nat_prime_of_bound 73 9 (by decide) (by decide) rfl,
    nat_prime_of_bound 103 10 (by decide) (by decide) rfl,
    nat_prime_of_bound 109 10 (by decide) (by decide) rfl,
    nat_prime_of_bound 127 11 (by decide) (by decide) rfl,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ?_⟩
  rintro ⟨q, hq, _⟩
  have h : (3 : ℤ) ∣ 109 * 475 + (5 - 3) * 21599 := ⟨73 * q, by linear_combination hq⟩
  norm_num at h

/-- The integer completion of the first column `(x, y)` with determinant `-p`. -/
def latticeMatrix (p x y u : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![x, u; y, (y * u - p) / x]

private theorem completion_eq {p x y u : ℤ} (h : x ∣ y * u - p) :
    x * ((y * u - p) / x) - u * y = -p := by
  have hd := Int.ediv_mul_cancel h
  linear_combination hd

theorem latticeMatrix_det {p x y u : ℤ} (h : x ∣ y * u - p) :
    (latticeMatrix p x y u).det = -p := by
  simpa only [latticeMatrix, Matrix.det_fin_two_of] using completion_eq h

@[simp] theorem latticeMatrix_mulVec_zero (p x y u : ℤ) (w : Fin 2 → ℤ) :
    (latticeMatrix p x y u *ᵥ w) 0 = x * w 0 + u * w 1 := by
  simp [latticeMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

@[simp] theorem latticeMatrix_mulVec_one (p x y u : ℤ) (w : Fin 2 → ℤ) :
    (latticeMatrix p x y u *ᵥ w) 1 = y * w 0 + ((y * u - p) / x) * w 1 := by
  simp [latticeMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem latticeMatrix_range {p x y u : ℤ} (h : x ∣ y * u - p)
    (hxy : IsCoprime x y) :
    Set.range (fun w => latticeMatrix p x y u *ᵥ w) =
      {z : Fin 2 → ℤ | p ∣ x * z 1 - y * z 0} := by
  let d := (y * u - p) / x
  have hdet : x * d - u * y = -p := completion_eq h
  ext z
  change (∃ w, latticeMatrix p x y u *ᵥ w = z) ↔ p ∣ x * z 1 - y * z 0
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨-w 1, ?_⟩
    simp only [latticeMatrix_mulVec_zero, latticeMatrix_mulVec_one]
    change x * (y * w 0 + d * w 1) - y * (x * w 0 + u * w 1) = p * (-w 1)
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
    · change (latticeMatrix p x y u *ᵥ ![a * U + b * V, -k]) 0 = z 0
      rw [latticeMatrix_mulVec_zero]
      change x * (a * U + b * V) + u * (-k) = z 0
      rw [hx]
      dsimp [U]
      ring
    · change (latticeMatrix p x y u *ᵥ ![a * U + b * V, -k]) 1 = z 1
      rw [latticeMatrix_mulVec_one]
      change y * (a * U + b * V) + d * (-k) = z 1
      rw [hy]
      dsimp [V]
      ring

/-- Bounding the positive first physical coordinate below `p` excludes the
only prime that the determinant `-p` allows to appear as a new common factor. -/
theorem latticeMatrix_primitive_in_box {p : ℕ} (hp : p.Prime) {x y u : ℤ}
    (h : x ∣ y * u - (p : ℤ)) {w : Fin 2 → ℤ}
    (hpos : 0 < (latticeMatrix p x y u *ᵥ w) 0)
    (hsmall : (latticeMatrix p x y u *ᵥ w) 0 < p) :
    IsCoprime ((latticeMatrix p x y u *ᵥ w) 0) ((latticeMatrix p x y u *ᵥ w) 1)
      ↔ IsCoprime (w 0) (w 1) := by
  let d := (y * u - (p : ℤ)) / x
  have hdet : x * d - u * y = -(p : ℤ) := completion_eq h
  let X := x * w 0 + u * w 1
  let Y := y * w 0 + d * w 1
  simp only [latticeMatrix_mulVec_zero, latticeMatrix_mulVec_one] at hpos hsmall ⊢
  change 0 < X at hpos
  change X < (p : ℤ) at hsmall
  change IsCoprime X Y ↔ IsCoprime (w 0) (w 1)
  constructor
  · rintro ⟨a, b, hab⟩
    refine ⟨a * x + b * y, a * u + b * d, ?_⟩
    dsimp [X, Y] at hab
    linear_combination hab
  · rintro ⟨a, b, hab⟩
    apply Int.isCoprime_iff_gcd_eq_one.mpr
    let g := Int.gcd X Y
    have hgX : (g : ℤ) ∣ X := Int.gcd_dvd_left X Y
    have hgY : (g : ℤ) ∣ Y := Int.gcd_dvd_right X Y
    have hw0 : u * Y - d * X = (p : ℤ) * w 0 := by
      dsimp [X, Y]
      linear_combination -(w 0) * hdet
    have hw1 : y * X - x * Y = (p : ℤ) * w 1 := by
      dsimp [X, Y]
      linear_combination -(w 1) * hdet
    have hd0 : (g : ℤ) ∣ (p : ℤ) * w 0 :=
      hw0 ▸ dvd_sub (dvd_mul_of_dvd_right hgY u) (dvd_mul_of_dvd_right hgX d)
    have hd1 : (g : ℤ) ∣ (p : ℤ) * w 1 :=
      hw1 ▸ dvd_sub (dvd_mul_of_dvd_right hgX y) (dvd_mul_of_dvd_right hgY x)
    have hsum : a * ((p : ℤ) * w 0) + b * ((p : ℤ) * w 1) = p := by
      linear_combination (p : ℤ) * hab
    have hgp : (g : ℤ) ∣ (p : ℤ) :=
      hsum ▸ dvd_add (dvd_mul_of_dvd_right hd0 a) (dvd_mul_of_dvd_right hd1 b)
    rcases (Nat.dvd_prime hp).mp (Int.natCast_dvd_natCast.mp hgp) with hg | hg
    · exact hg
    · have hpX : (p : ℤ) ∣ X := hg ▸ hgX
      exact (not_lt_of_ge (Int.le_of_dvd hpos hpX) hsmall).elim

theorem latticeMatrix_p7_regression :
    (2 : ℤ) ∣ 3 * 1 - 7 ∧ IsCoprime (2 : ℤ) 3 ∧
    IsCoprime (1 : ℤ) (-2) ∧
    latticeMatrix 7 2 3 1 *ᵥ ![(1 : ℤ), -2] = ![(0 : ℤ), 7] ∧
    ¬ IsCoprime (0 : ℤ) 7 := by
  refine ⟨by decide, by decide, by decide, ?_, by decide⟩
  ext i
  fin_cases i <;> norm_num

end Target3A
