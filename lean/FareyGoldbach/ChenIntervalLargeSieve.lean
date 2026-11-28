import FareyGoldbach.CongruenceLargeSieve

/-! Exact binary decomposition of moving intervals and the primitive-character large sieve. -/

open scoped BigOperators Classical
namespace FareyGoldbach

/-- The weighted primitive-character first moment at conductor q. -/
noncomputable def chenPrimitiveNorm (q : ℕ) (F : DirichletCharacter ℂ q → ℂ) : ℝ :=
  if hq : 0 < q then
    letI : NeZero q := ⟨hq.ne'⟩
    (q:ℝ)/q.totient * ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter
      (fun χ => χ.IsPrimitive), ‖F χ‖
  else 0

theorem chenPrimitiveNorm_of_pos {q : ℕ} [NeZero q] (F : DirichletCharacter ℂ q → ℂ) :
    chenPrimitiveNorm q F = (q:ℝ)/q.totient *
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter
        (fun χ => χ.IsPrimitive), ‖F χ‖ := by
  simp [chenPrimitiveNorm, NeZero.pos q]

theorem chenPrimitiveNorm_nonneg (q : ℕ) (F : DirichletCharacter ℂ q → ℂ) :
    0 ≤ chenPrimitiveNorm q F := by
  unfold chenPrimitiveNorm
  split <;> positivity

private def digit (k u : ℕ) : ℕ := u / 2^k

private lemma digit_succ (k u : ℕ) : digit (k+1) u = digit k u / 2 := by
  simp only [digit, pow_succ, Nat.div_div_eq_div_mul]

private lemma binary_prefix (u r d : ℕ) (hr : r < 2^d) :
    (if u < r then (1:ℂ) else 0) = ∑ k ∈ Finset.range d,
      if digit k r % 2 = 1 ∧ digit k u = digit k r - 1 then (1:ℂ) else 0 := by
  have hstep (k : ℕ) :
      (if digit k u < digit k r then (1:ℂ) else 0) =
      (if digit k r % 2 = 1 ∧ digit k u = digit k r - 1 then (1:ℂ) else 0) +
      (if digit (k+1) u < digit (k+1) r then (1:ℂ) else 0) := by
    simp only [digit_succ]
    split_ifs <;> first | omega | norm_num
  have htel (i : ℕ) : (if u < r then (1:ℂ) else 0) =
      (∑ k ∈ Finset.range i,
       if digit k r % 2 = 1 ∧ digit k u = digit k r - 1 then (1:ℂ) else 0) +
      (if digit i u < digit i r then (1:ℂ) else 0) := by
    induction i with
    | zero => simp [digit]
    | succ i ih => rw [ih, hstep i, Finset.sum_range_succ, add_assoc]
  simpa [digit, Nat.div_eq_of_lt hr] using htel d

private noncomputable def cutCoef (f : ℕ → ℂ) (g : ℕ → ℕ) (j : ℕ) (n : ℕ) : ℂ :=
  if g n = j then f n else 0

private noncomputable def primePoly {q : ℕ} (s : Finset ℕ) (v : ℕ → ℂ)
    (χ : DirichletCharacter ℂ q) : ℂ := ∑ n ∈ s, v n * χ (n : ZMod q)

private lemma energy_nonneg (q : ℕ) (s : Finset ℕ) (v : ℕ → ℂ) :
    0 ≤ primitiveCharacterEnergy q s v := by
  unfold primitiveCharacterEnergy
  split <;> positivity

private lemma band_bilinear (r₁ Q : ℕ) (hr₁ : 0<r₁) (s t : Finset ℕ) (v z : ℕ → ℂ) :
    (∑ q ∈ Finset.Ioc Q (2*Q), chenPrimitiveNorm (r₁*q)
      (fun χ => primePoly s v χ * primePoly t z χ)) ≤
    Real.sqrt (∑ q ∈ Finset.Ioc Q (2*Q), primitiveCharacterEnergy (r₁*q) s v) *
    Real.sqrt (∑ q ∈ Finset.Ioc Q (2*Q), primitiveCharacterEnergy (r₁*q) t z) := by
  apply le_trans _ (Real.sum_sqrt_mul_sqrt_le _ (fun i => energy_nonneg (r₁*i) s v)
    (fun i => energy_nonneg (r₁*i) t z))
  apply Finset.sum_le_sum
  intro q hq
  have hp : 0 < r₁*q := Nat.mul_pos hr₁ (lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hq).1)
  let : NeZero (r₁*q) := ⟨hp.ne'⟩
  let T := (Finset.univ : Finset (DirichletCharacter ℂ (r₁*q))).filter (fun χ => χ.IsPrimitive)
  let c := (↑(r₁*q):ℝ)/(r₁*q).totient
  have hc : 0 ≤ c := by dsimp [c]; positivity
  simp only [chenPrimitiveNorm, dite_eq_left hp, primitiveCharacterEnergy_of_pos hp, norm_mul]
  change c * (∑ χ ∈ T, ‖primePoly s v χ‖ * ‖primePoly t z χ‖) ≤
    Real.sqrt (c * ∑ χ ∈ T, ‖primePoly s v χ‖ ^ 2) *
    Real.sqrt (c * ∑ χ ∈ T, ‖primePoly t z χ‖ ^ 2)
  rw [Real.sqrt_mul hc, Real.sqrt_mul hc, mul_mul_mul_comm, Real.mul_self_sqrt hc]
  exact mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt _ _ _) hc

private lemma band_energy (r₁ Q N : ℕ) (hr₁ : 0<r₁) (v : ℕ → ℂ) :
    (∑ q ∈ Finset.Ioc Q (2*Q), primitiveCharacterEnergy (r₁*q) (Finset.Icc 1 N) v) ≤
      200*((N:ℝ)+(r₁:ℝ)*(Q:ℝ)^2) * ∑ n ∈ Finset.Icc 1 N, ‖v n‖^2 := by
  have hs : Finset.Ioc 0 N = Finset.Icc 1 N := by ext n; simp; omega
  have H := primitive_large_sieve_multiple r₁ 0 N (2*Q) hr₁ v
  simp only [zero_add, hs, Nat.cast_mul, Nat.cast_ofNat] at H
  apply le_trans _ (H.trans ?_)
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      simp only [Finset.mem_Ioc, Finset.mem_Icc] at hn ⊢
      omega
    · exact fun i _ _ => energy_nonneg (r₁*i) _ _
  · apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => by positivity)
    nlinarith [Nat.cast_nonneg (α:=ℝ) N]

private lemma cut_energy (N : ℕ) (J : Finset ℕ) (f : ℕ → ℂ) (tag : ℕ → ℕ)
    {E : ℝ} (hf : (∑ n ∈ Finset.Icc 1 N, ‖f n‖^2) ≤ E) :
    (∑ j ∈ J, ∑ n ∈ Finset.Icc 1 N, ‖cutCoef f tag j n‖^2) ≤ E := by
  rw [Finset.sum_comm]
  apply le_trans _ hf
  apply Finset.sum_le_sum
  intro n _
  simp only [cutCoef, apply_ite norm, norm_zero, ite_pow, zero_pow (by decide : 2≠0)]
  rw [Finset.sum_ite_eq]
  split <;> first | rfl | positivity

private lemma level_estimate (r₁ M W Q : ℕ) (hr₁ : 0<r₁) (J : Finset ℕ) (f g : ℕ → ℂ)
    (tagA tagB : ℕ → ℕ) {A B : ℝ}
    (hf : (∑ n∈Finset.Icc 1 M, ‖f n‖^2)≤A) (hg : (∑ n∈Finset.Icc 1 W, ‖g n‖^2)≤B) :
    (∑ j ∈ J, ∑ q ∈ Finset.Ioc Q (2*Q), chenPrimitiveNorm (r₁*q)
      (fun χ => primePoly (Finset.Icc 1 M) (cutCoef f tagA j) χ *
       primePoly (Finset.Icc 1 W) (cutCoef g tagB j) χ)) ≤
      200 * Real.sqrt (((M:ℝ)+(r₁:ℝ)*(Q:ℝ)^2)*A) * Real.sqrt (((W:ℝ)+(r₁:ℝ)*(Q:ℝ)^2)*B) := by
  let EN (N : ℕ) (F : ℕ → ℂ) (t : ℕ → ℕ) (j : ℕ) :=
    ∑ q ∈ Finset.Ioc Q (2*Q), primitiveCharacterEnergy (r₁*q) (Finset.Icc 1 N) (cutCoef F t j)
  have EN0 (N F t j) : 0 ≤ EN N F t j := Finset.sum_nonneg fun q _ => energy_nonneg (r₁*q) _ _
  have el (N : ℕ) (F : ℕ → ℂ) (t : ℕ → ℕ)
      {E : ℝ} (hF : (∑ n∈Finset.Icc 1 N, ‖F n‖^2)≤E) :
      ∑ j ∈ J, EN N F t j ≤ 200 * (((N:ℝ)+(r₁:ℝ)*(Q:ℝ)^2)*E) := by
    calc
      _ ≤ ∑ j ∈ J, (200*((N:ℝ)+(r₁:ℝ)*(Q:ℝ)^2)) * ∑ n ∈ Finset.Icc 1 N, ‖cutCoef F t j n‖^2 :=
        Finset.sum_le_sum fun j _ => band_energy r₁ Q N hr₁ _
      _ = _ := by rw [← Finset.mul_sum]
      _ ≤ _ := by rw [← mul_assoc]; gcongr; exact cut_energy N J F t hF
  calc
    _ ≤ ∑ j ∈ J, Real.sqrt (EN M f tagA j) * Real.sqrt (EN W g tagB j) :=
      Finset.sum_le_sum fun j _ => band_bilinear r₁ Q hr₁ _ _ _ _
    _ ≤ _ := Real.sum_sqrt_mul_sqrt_le J (EN0 M f tagA) (EN0 W g tagB)
    _ ≤ Real.sqrt (200*(((M:ℝ)+(r₁:ℝ)*(Q:ℝ)^2)*A)) * Real.sqrt (200*(((W:ℝ)+(r₁:ℝ)*(Q:ℝ)^2)*B)) := by
      exact mul_le_mul (Real.sqrt_le_sqrt (el M f tagA hf)) (Real.sqrt_le_sqrt (el W g tagB hg))
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := by rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 200), Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 200),
                     mul_mul_mul_comm, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 200), mul_assoc]


private noncomputable def bitCoef (k : ℕ) (r : ℕ → ℕ) (f : ℕ → ℂ) (n : ℕ) : ℂ :=
  if digit k (r n) % 2 = 1 then f n else 0

private lemma one_prefix {q W r d : ℕ} (hr : r ≤ W) (hD : W < 2^d)
    (b : ℕ → ℂ) (χ : DirichletCharacter ℂ q) :
    (∑ w ∈ Finset.Icc 1 r, b w * χ (w : ZMod q)) = ∑ k ∈ Finset.range d,
      if digit k r % 2 = 1 then primePoly (Finset.Icc 1 W)
        (cutCoef b (fun w => digit k (w-1)) (digit k r - 1)) χ else 0 := by
  classical
  have hfilter : (Finset.Icc 1 W).filter (fun w => w-1 < r) = Finset.Icc 1 r := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  calc
    _ = ∑ w ∈ Finset.Icc 1 W, (if w-1 < r then (1:ℂ) else 0) * (b w * χ (w : ZMod q)) := by
      rw [← hfilter, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro w _
      split_ifs <;> simp
    _ = ∑ w ∈ Finset.Icc 1 W, ∑ k ∈ Finset.range d,
        (if digit k r % 2 = 1 ∧ digit k (w-1) = digit k r - 1 then (1:ℂ) else 0) *
           (b w * χ (w : ZMod q)) := by
      apply Finset.sum_congr rfl
      intro w _
      rw [binary_prefix (w-1) r d (hr.trans_lt hD), Finset.sum_mul]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      by_cases hd : digit k r % 2 = 1
      · simp only [hd, true_and, ite_true, primePoly]
        apply Finset.sum_congr rfl
        intro w _
        simp only [cutCoef]
        split_ifs <;> simp
      · simp [hd]

private lemma moving_prefix {q M W d : ℕ} (hD : W < 2^d) (r : ℕ → ℕ)
    (hr : ∀ m ∈ Finset.Icc 1 M, r m ≤ W) (a b : ℕ → ℂ) (χ : DirichletCharacter ℂ q) :
    (∑ m ∈ Finset.Icc 1 M, a m * χ (m : ZMod q) *
        (∑ w ∈ Finset.Icc 1 (r m), b w * χ (w : ZMod q))) =
    ∑ k ∈ Finset.range d, ∑ j ∈ Finset.range (W+1),
      primePoly (Finset.Icc 1 M) (cutCoef (bitCoef k r a) (fun m => digit k (r m)-1) j) χ *
      primePoly (Finset.Icc 1 W) (cutCoef b (fun w => digit k (w-1)) j) χ := by
  let B (k j : ℕ) := primePoly (Finset.Icc 1 W) (cutCoef b (fun w => digit k (w-1)) j) χ
  let jA (k m : ℕ) := digit k (r m) - 1
  calc
    _ = ∑ m ∈ Finset.Icc 1 M, ∑ k ∈ Finset.range d,
        bitCoef k r a m * χ (m : ZMod q) * B k (jA k m) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [one_prefix (hr m hm) hD b χ, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      simp only [bitCoef, B, jA]
      split_ifs <;> simp
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      change _ = ∑ j ∈ Finset.range (W+1),
        (∑ m ∈ Finset.Icc 1 M, cutCoef (bitCoef k r a) (jA k) j m * χ (m : ZMod q)) * B k j
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm (s:=Finset.range (W+1))]
      apply Finset.sum_congr rfl
      intro m hm
      have hj : jA k m ∈ Finset.range (W+1) := by
        dsimp [jA, digit]
        have hh := Nat.div_le_self (r m) (2^k)
        have hw := hr m hm
        simp only [Finset.mem_range]
        omega
      rw [Finset.sum_eq_single_of_mem (jA k m) hj]
      · simp [cutCoef]
      · intro j _ hj'
        simp [cutCoef, Ne.symm hj']

theorem chenNorm_sum {ι : Type*} (q : ℕ) (I : Finset ι)
    (F : ι → DirichletCharacter ℂ q → ℂ) :
    chenPrimitiveNorm q (fun χ => ∑ i ∈ I, F i χ) ≤ ∑ i ∈ I, chenPrimitiveNorm q (F i) := by
  by_cases hq : 0 < q
  · let : NeZero q := ⟨hq.ne'⟩
    simp only [chenPrimitiveNorm, dite_eq_left hq, ← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [Finset.sum_comm (s:=I)]
    exact Finset.sum_le_sum fun χ _ => norm_sum_le _ _
  · simp [chenPrimitiveNorm, hq]

private lemma chenNorm_sub (q : ℕ) (F G : DirichletCharacter ℂ q → ℂ) :
    chenPrimitiveNorm q (fun χ => F χ - G χ) ≤ chenPrimitiveNorm q F + chenPrimitiveNorm q G := by
  by_cases hq : 0 < q
  · let : NeZero q := ⟨hq.ne'⟩
    simp only [chenPrimitiveNorm, dite_eq_left hq, ← mul_add, ← Finset.sum_add_distrib]
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun χ _ => norm_sub_le _ _) (by positivity)
  · simp [chenPrimitiveNorm, hq]

private lemma prefix_estimate (r₁ M W Q d : ℕ) (hr₁ : 0<r₁) (hD : W < 2^d) (r : ℕ → ℕ) (a b : ℕ → ℂ) {A B : ℝ}
    (hr : ∀ m ∈ Finset.Icc 1 M, r m ≤ W)
    (ha : (∑ m∈Finset.Icc 1 M, ‖a m‖^2)≤A) (hb : (∑ w∈Finset.Icc 1 W, ‖b w‖^2)≤B) :
    (∑ q ∈ Finset.Ioc Q (2*Q), chenPrimitiveNorm (r₁*q) (fun χ =>
      ∑ m ∈ Finset.Icc 1 M, a m * χ (m : ZMod (r₁*q)) *
        (∑ w ∈ Finset.Icc 1 (r m), b w * χ (w : ZMod (r₁*q))))) ≤
      d * (200 * Real.sqrt (((M:ℝ)+(r₁:ℝ)*(Q:ℝ)^2)*A) * Real.sqrt (((W:ℝ)+(r₁:ℝ)*(Q:ℝ)^2)*B)) := by
  let F (k j q : ℕ) (χ : DirichletCharacter ℂ q) :=
      primePoly (Finset.Icc 1 M) (cutCoef (bitCoef k r a) (fun m => digit k (r m)-1) j) χ *
      primePoly (Finset.Icc 1 W) (cutCoef b (fun w => digit k (w-1)) j) χ
  have heq q χ := @moving_prefix q M W d hD r hr a b χ
  calc
    _ ≤ ∑ q ∈ Finset.Ioc Q (2*Q), ∑ k ∈ Finset.range d, ∑ j ∈ Finset.range (W+1),
       chenPrimitiveNorm (r₁*q) (F k j (r₁*q)) := by
      apply Finset.sum_le_sum
      intro q _
      simp_rw [heq]
      apply (chenNorm_sum _ _ _).trans
      exact Finset.sum_le_sum fun k _ => chenNorm_sum _ _ _
    _ = ∑ k ∈ Finset.range d, ∑ j ∈ Finset.range (W+1), ∑ q ∈ Finset.Ioc Q (2*Q),
       chenPrimitiveNorm (r₁*q) (F k j (r₁*q)) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ ≤ ∑ _k ∈ Finset.range d,
       200 * Real.sqrt (((M:ℝ)+(r₁:ℝ)*(Q:ℝ)^2)*A) * Real.sqrt (((W:ℝ)+(r₁:ℝ)*(Q:ℝ)^2)*B) := by
      apply Finset.sum_le_sum
      intro k _
      apply level_estimate r₁ _ _ _ hr₁ _ _ _ _ _ _ hb
      apply le_trans _ ha
      apply Finset.sum_le_sum
      intro m _
      simp only [bitCoef,apply_ite norm,norm_zero,ite_pow,zero_pow (by decide : 2≠0)]
      split <;> first | rfl | positivity
    _ = _ := by simp


private lemma interval_sub_prefix {lo hi : ℕ} (hlo : 1 ≤ lo) (v : ℕ → ℂ) :
    ∑ w ∈ Finset.Icc lo hi, v w =
      (∑ w ∈ Finset.Icc 1 hi, v w) - ∑ w ∈ Finset.Icc 1 (min hi (lo-1)), v w := by
  have hs : Finset.Icc 1 (min hi (lo-1)) ⊆ Finset.Icc 1 hi := by
    intro w hw
    simp only [Finset.mem_Icc, le_min_iff] at hw ⊢
    exact ⟨hw.1, hw.2.1⟩
  have he : Finset.Icc 1 hi \ Finset.Icc 1 (min hi (lo-1)) = Finset.Icc lo hi := by
    ext w
    simp only [Finset.mem_sdiff, Finset.mem_Icc, le_min_iff]
    omega
  rw [← he, Finset.sum_sdiff_eq_sub hs]

private lemma digit_length_log {W : ℕ} (hW : 1 ≤ W) :
    ((Nat.log 2 W + 1 : ℕ):ℝ) ≤ 2*Real.log (2*(W:ℝ)) := by
  have hpow : (2:ℝ) ^ Nat.log 2 W ≤ (W:ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : W ≠ 0)
  have H := Real.log_le_log (by positivity) hpow
  rw [Real.log_pow] at H
  rw [Real.log_mul (by norm_num) (by positivity)]
  push_cast
  have ht : (1/2:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hn : 0 ≤ (Nat.log 2 W:ℝ) := by positivity
  nlinarith [mul_nonneg hn (sub_nonneg.mpr ht)]

/-- Primitive-character bilinear large sieve for an exact, independently moving
integer interval in each row. A reversed interval contributes zero. -/
theorem chen_interval_bilinear_large_sieve_multiple_of_energy (r₁ M W Q : ℕ) (hr₁ : 0<r₁) (a b : ℕ → ℂ) (lo hi : ℕ → ℕ) {EA EB : ℝ}
    (hW : 1 ≤ W) (ha : (∑ m∈Finset.Icc 1 M, ‖a m‖^2)≤EA)
    (hb : (∑ w∈Finset.Icc 1 W, ‖b w‖^2)≤EB)
    (hlo : ∀ m ∈ Finset.Icc 1 M, 1 ≤ lo m)
    (hhi : ∀ m ∈ Finset.Icc 1 M, hi m ≤ W) :
    (∑ q ∈ Finset.Ioc Q (2*Q), chenPrimitiveNorm (r₁*q) (fun χ =>
       ∑ m ∈ Finset.Icc 1 M, a m * χ (m : ZMod (r₁*q)) *
         (∑ w ∈ Finset.Icc (lo m) (hi m), b w * χ (w : ZMod (r₁*q))))) ≤
      1000 * Real.log (2*(W:ℝ)) * Real.sqrt (((M:ℝ)+(r₁:ℝ)*(Q:ℝ)^2)*EA) *
        Real.sqrt (((W:ℝ)+(r₁:ℝ)*(Q:ℝ)^2)*EB) := by
  let d := Nat.log 2 W + 1
  let l (m : ℕ) := min (hi m) (lo m - 1)
  let P (q : ℕ) (r : ℕ → ℕ) (χ : DirichletCharacter ℂ q) :=
    ∑ m ∈ Finset.Icc 1 M, a m * χ (m : ZMod q) *
        ∑ w ∈ Finset.Icc 1 (r m), b w * χ (w : ZMod q)
  let A := Real.sqrt (((M:ℝ)+(r₁:ℝ)*(Q:ℝ)^2)*EA)
  let B := Real.sqrt (((W:ℝ)+(r₁:ℝ)*(Q:ℝ)^2)*EB)
  have hd : W < 2^d := Nat.lt_pow_succ_log_self (by decide) _
  have hsplit (q : ℕ) (χ : DirichletCharacter ℂ q) :
      (∑ m ∈ Finset.Icc 1 M, a m * χ (m : ZMod q) *
        (∑ w ∈ Finset.Icc (lo m) (hi m), b w * χ (w : ZMod q))) =
       P q hi χ - P q l χ := by
    unfold P
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    rw [interval_sub_prefix (hlo m hm), mul_sub]
  calc
    _ ≤ ∑ q ∈ Finset.Ioc Q (2*Q), (chenPrimitiveNorm (r₁*q) (P (r₁*q) hi) + chenPrimitiveNorm (r₁*q) (P (r₁*q) l)) := by
      apply Finset.sum_le_sum
      intro q _
      simp_rw [hsplit]
      exact chenNorm_sub _ _ _
    _ ≤ (d:ℝ) * (200*A*B) + (d:ℝ) * (200*A*B) := by
      rw [Finset.sum_add_distrib]
      exact add_le_add (prefix_estimate r₁ M W Q d hr₁ hd hi a b hhi ha hb)
        (prefix_estimate r₁ M W Q d hr₁ hd l a b (fun m hm => (min_le_left _ _).trans (hhi m hm)) ha hb)
    _ = (400 * (d:ℝ)) * A * B := by ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      have hl := digit_length_log hW
      have hlog : 0 ≤ Real.log (2*(W:ℝ)) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 2*W))
      dsimp [d]
      linarith

theorem chen_interval_bilinear_large_sieve_multiple (r₁ M W Q : ℕ) (hr₁ : 0<r₁) (a b : ℕ → ℂ) (lo hi : ℕ → ℕ)
    (hW : 1 ≤ W) (ha : ∀ m ∈ Finset.Icc 1 M, ‖a m‖ ≤ 1)
    (hb : ∀ w ∈ Finset.Icc 1 W, ‖b w‖ ≤ 1)
    (hlo : ∀ m ∈ Finset.Icc 1 M, 1 ≤ lo m)
    (hhi : ∀ m ∈ Finset.Icc 1 M, hi m ≤ W) :
    (∑ q ∈ Finset.Ioc Q (2*Q), chenPrimitiveNorm (r₁*q) (fun χ =>
       ∑ m ∈ Finset.Icc 1 M, a m * χ (m : ZMod (r₁*q)) *
         (∑ w ∈ Finset.Icc (lo m) (hi m), b w * χ (w : ZMod (r₁*q))))) ≤
      1000 * Real.log (2*(W:ℝ)) * Real.sqrt (((M:ℝ)+(r₁:ℝ)*(Q:ℝ)^2)*M) *
        Real.sqrt (((W:ℝ)+(r₁:ℝ)*(Q:ℝ)^2)*W) := by
  apply chen_interval_bilinear_large_sieve_multiple_of_energy r₁ M W Q hr₁ a b lo hi hW _ _ hlo hhi
  · simpa using Finset.sum_le_sum (fun m hm => pow_le_one₀ (norm_nonneg _) (ha m hm) (n:=2))
  · simpa using Finset.sum_le_sum (fun w hw => pow_le_one₀ (norm_nonneg _) (hb w hw) (n:=2))

theorem chen_interval_bilinear_large_sieve_of_energy (M W Q : ℕ) (a b : ℕ → ℂ) (lo hi : ℕ → ℕ) {EA EB : ℝ}
    (hW : 1 ≤ W) (ha : (∑ m∈Finset.Icc 1 M, ‖a m‖^2)≤EA)
    (hb : (∑ w∈Finset.Icc 1 W, ‖b w‖^2)≤EB)
    (hlo : ∀ m ∈ Finset.Icc 1 M, 1 ≤ lo m)
    (hhi : ∀ m ∈ Finset.Icc 1 M, hi m ≤ W) :
    (∑ q ∈ Finset.Ioc Q (2*Q), chenPrimitiveNorm q (fun χ =>
       ∑ m ∈ Finset.Icc 1 M, a m * χ (m : ZMod q) *
         (∑ w ∈ Finset.Icc (lo m) (hi m), b w * χ (w : ZMod q)))) ≤
      1000 * Real.log (2*(W:ℝ)) * Real.sqrt (((M:ℝ)+(Q:ℝ)^2)*EA) *
        Real.sqrt (((W:ℝ)+(Q:ℝ)^2)*EB) := by
  convert chen_interval_bilinear_large_sieve_multiple_of_energy 1 M W Q (by decide)
    a b lo hi hW ha hb hlo hhi using 1
  · refine Finset.sum_congr rfl (fun q _ => ?_)
    exact congrArg (fun k => chenPrimitiveNorm k (fun χ =>
      ∑ m ∈ Finset.Icc 1 M, a m * χ (m : ZMod k) *
        ∑ w ∈ Finset.Icc (lo m) (hi m), b w * χ (w : ZMod k))) (Nat.one_mul q).symm
  · simp

theorem chen_interval_bilinear_large_sieve (M W Q : ℕ) (a b : ℕ → ℂ) (lo hi : ℕ → ℕ)
    (hW : 1 ≤ W) (ha : ∀ m ∈ Finset.Icc 1 M, ‖a m‖ ≤ 1)
    (hb : ∀ w ∈ Finset.Icc 1 W, ‖b w‖ ≤ 1)
    (hlo : ∀ m ∈ Finset.Icc 1 M, 1 ≤ lo m)
    (hhi : ∀ m ∈ Finset.Icc 1 M, hi m ≤ W) :
    (∑ q ∈ Finset.Ioc Q (2*Q), chenPrimitiveNorm q (fun χ =>
       ∑ m ∈ Finset.Icc 1 M, a m * χ (m : ZMod q) *
         (∑ w ∈ Finset.Icc (lo m) (hi m), b w * χ (w : ZMod q)))) ≤
      1000 * Real.log (2*(W:ℝ)) * Real.sqrt (((M:ℝ)+(Q:ℝ)^2)*M) *
        Real.sqrt (((W:ℝ)+(Q:ℝ)^2)*W) := by
  apply chen_interval_bilinear_large_sieve_of_energy M W Q a b lo hi hW _ _ hlo hhi
  · simpa using Finset.sum_le_sum (fun m hm => pow_le_one₀ (norm_nonneg _) (ha m hm) (n:=2))
  · simpa using Finset.sum_le_sum (fun w hw => pow_le_one₀ (norm_nonneg _) (hb w hw) (n:=2))

end FareyGoldbach
