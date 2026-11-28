import FareyGoldbach.PrimeAPSharp
import FareyGoldbach.SharpRankin

/-! # From sharp character sums to primes in a residue class -/

open Filter Finset
open scoped Topology Classical

namespace FareyGoldbach

private noncomputable abbrev primeErrorScale (X d : ℕ) : ℝ :=
  Real.sqrt X * Real.log (2 * (d : ℝ) * X) ^ 2

def SharpVonMangoldtTwistBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (X d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d), 2 ≤ X →
  ‖(∑ n ∈ Icc 1 X, (ArithmeticFunction.vonMangoldt n : ℂ) * χ n) -
    (if χ = 1 then (X : ℂ) else 0)‖ ≤ C * Real.sqrt X * Real.log (2 * (d : ℝ) * X) ^ 2

private theorem primesLE_eq_Icc_filter (X : ℕ) : X.primesLE = (Icc 1 X).filter Nat.Prime := by
  ext p
  simp only [Nat.mem_primesLE, mem_filter, mem_Icc]
  exact ⟨fun ⟨hp, h⟩ => ⟨⟨h.one_le, hp⟩, h⟩, fun h => ⟨h.1.2, h.2⟩⟩

private theorem primePower_twist_error {X d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d)
    (hX : 2 ≤ X) :
    ‖(∑ n ∈ Icc 1 X, (ArithmeticFunction.vonMangoldt n : ℂ) * χ n) -
      ∑ p ∈ X.primesLE, (Real.log p : ℂ) * χ p‖ ≤ 2 * primeErrorScale X d := by
  classical
  let f (n : ℕ) := (ArithmeticFunction.vonMangoldt n : ℂ) * χ n
  have hprime : (∑ p ∈ X.primesLE, (Real.log p : ℂ) * χ p) =
      ∑ p ∈ (Icc 1 X).filter Nat.Prime, f p := by
    rw [primesLE_eq_Icc_filter]
    exact sum_congr rfl fun p hp => by simp [f, ArithmeticFunction.vonMangoldt_apply_prime (mem_filter.mp hp).2]
  have hsplit := Finset.sum_filter_add_sum_filter_not (Icc 1 X) Nat.Prime f
  have hrem : (∑ n ∈ Icc 1 X, f n) - ∑ n ∈ (Icc 1 X).filter Nat.Prime, f n =
      ∑ n ∈ (Icc 1 X).filter (fun n => ¬n.Prime), f n := by
    rw [← hsplit]
    abel
  have hnorm (n : ℕ) : ‖f n‖ ≤ ArithmeticFunction.vonMangoldt n := by
    simpa [f, norm_mul, Real.norm_eq_abs, abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg)] using
      mul_le_mul_of_nonneg_left (χ.norm_le_one n) (ArithmeticFunction.vonMangoldt_nonneg (n := n))
  have heq : Icc 1 X = Ioc 0 X := by ext n; simp; omega
  have hpsi := Chebyshev.psi_sub_theta_eq_sum_not_prime (X : ℝ)
  rw [Nat.floor_natCast, ← heq] at hpsi
  have hXr : (2 : ℝ) ≤ X := by exact_mod_cast hX
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hx2 : (4 : ℝ) ≤ 2 * (d : ℝ) * X := by nlinarith
  have hlog : 1 ≤ Real.log (2 * (d : ℝ) * X) :=
    (Real.le_log_iff_exp_le (by positivity)).mpr (Real.exp_one_lt_three.le.trans (by linarith))
  have hlog' : Real.log X ≤ Real.log (2 * (d : ℝ) * X) := Real.log_le_log (by positivity) (by nlinarith)
  rw [hprime]
  change ‖(∑ n ∈ Icc 1 X, f n) - _‖ ≤ _
  rw [hrem]
  calc
    _ ≤ ∑ n ∈ (Icc 1 X).filter (fun n => ¬n.Prime), ‖f n‖ := norm_sum_le _ _
    _ ≤ _ := sum_le_sum fun n _ => hnorm n
    _ = _ := hpsi.symm
    _ ≤ _ := Chebyshev.psi_sub_theta_le (by linarith : (1 : ℝ) ≤ X)
    _ ≤ 2 * primeErrorScale X d := by
      unfold primeErrorScale
      have hs := Real.sqrt_nonneg (X : ℝ)
      have hlogs : Real.log X ≤ Real.log (2 * (d : ℝ) * X)^2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hlogs hs]

private theorem weighted_prime_twist (h : SharpVonMangoldtTwistBound) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d), 2 ≤ X →
    ‖(∑ p ∈ X.primesLE, (Real.log p : ℂ) * χ p) -
      (if χ = 1 then (X : ℂ) else 0)‖ ≤ C * primeErrorScale X d := by
  obtain ⟨C, hC, bound⟩ := h
  refine ⟨C + 2, by linarith, ?_⟩
  intro X d _ χ hX
  have h₁ := primePower_twist_error χ hX
  have h₂ := bound X d χ hX
  rw [norm_sub_rev] at h₁
  calc
    _ ≤ _ := norm_sub_le_norm_sub_add_norm_sub _ (∑ n ∈ Icc 1 X, (ArithmeticFunction.vonMangoldt n : ℂ) * χ n) _
    _ ≤ _ := add_le_add h₁ h₂
    _ = _ := by unfold primeErrorScale; ring

theorem abel_prime_bound {N : ℕ} (w : ℕ → ℝ) (g : ℕ → ℂ) (B : ℝ)
    (hw : ∀ n, 0 ≤ w n) (hm : Antitone w)
    (hs : ∀ j ≤ N, ‖∑ i ∈ range (j+1), g i‖ ≤ B) :
    ‖∑ i ∈ range (N+1), w i • g i‖ ≤ w 0 * B := by
  rw [Finset.sum_range_by_parts]
  simp only [Nat.add_sub_cancel]
  have hneg (i : ℕ) : |w (i+1)-w i| = w i-w (i+1) := by
    rw [abs_of_nonpos (sub_nonpos.mpr (hm (Nat.le_succ i)))]
    ring
  calc
    _ ≤ ‖w N • (∑ i ∈ range (N+1), g i)‖ +
        ‖∑ i ∈ range N, (w (i+1)-w i) • (∑ j ∈ range (i+1), g j)‖ := norm_sub_le .. 
    _ ≤ w N * B + ∑ i ∈ range N, (w i-w (i+1))*B := by
      apply add_le_add
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw N)]
        exact mul_le_mul_of_nonneg_left (hs N le_rfl) (hw N)
      · apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_smul, Real.norm_eq_abs, hneg]
        exact mul_le_mul_of_nonneg_left (hs i (Nat.le_of_lt (mem_range.mp hi)))
          (sub_nonneg.mpr (hm (Nat.le_succ i)))
    _ = _ := by
      rw [← Finset.sum_mul]
      rw [Finset.sum_range_sub']
      ring

private theorem scale_mono {X Y d e : ℕ} (hX : 2 ≤ X) (hXY : X ≤ Y)
    (hd : 0 < d) (hde : d ≤ e) : primeErrorScale X d ≤ primeErrorScale Y e := by
  have hlog : 0 ≤ Real.log (2 * (d : ℝ) * X) := Real.log_nonneg (by
    have : (1:ℝ) ≤ d := by exact_mod_cast hd
    have : (2:ℝ) ≤ X := by exact_mod_cast hX
    nlinarith)
  unfold primeErrorScale
  gcongr

private theorem one_char_level_one (n : ℕ) : (1 : DirichletCharacter ℂ 1) n = 1 := by
  rw [show (n : ZMod 1) = 1 from Subsingleton.elim _ _, map_one]

private theorem prime_weighted_centered (h : SharpVonMangoldtTwistBound) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d), 2 ≤ X →
    ‖∑ p ∈ X.primesLE, (Real.log p : ℂ) * (χ p - (if χ = 1 then 1 else 0))‖ ≤
      C * primeErrorScale X d := by
  classical
  obtain ⟨C,hC,hbound⟩ := weighted_prime_twist h
  refine ⟨2*C, by positivity, ?_⟩
  intro X d _ χ hX
  have hχ := hbound X d χ hX
  have hS : 0 ≤ primeErrorScale X d := by unfold primeErrorScale; positivity
  by_cases hc : χ = 1
  · simp only [hc, ite_true] at hχ ⊢
    have h₁ := hbound X 1 (1 : DirichletCharacter ℂ 1) hX
    simp only [one_char_level_one, mul_one, ite_true] at h₁
    have hmono := scale_mono hX (le_refl X) (by decide : 0 < 1)
      (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d))
    simp_rw [mul_sub, mul_one, sum_sub_distrib]
    have htri := norm_sub_le_norm_sub_add_norm_sub
      (∑ p ∈ X.primesLE, (Real.log p:ℂ)*(1:DirichletCharacter ℂ d) p)
      (X:ℂ) (∑ p ∈ X.primesLE, (Real.log p:ℂ))
    rw [norm_sub_rev (X : ℂ)] at htri
    exact htri.trans (by linarith [mul_le_mul_of_nonneg_left hmono hC.le])
  · simp only [hc, ite_false, sub_zero] at hχ ⊢
    linarith [mul_nonneg hC.le hS]

private theorem primesLE_range (X : ℕ) :
    (range (X+1)).filter Nat.Prime = X.primesLE := by
  ext n
  simp [Nat.mem_primesLE]

private theorem unweighted_prime_centered (h : SharpVonMangoldtTwistBound) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d), 2 ≤ X →
    ‖(∑ p ∈ X.primesLE, χ p) - (if χ = 1 then (Nat.primeCounting X:ℂ) else 0)‖ ≤
      C * primeErrorScale X d := by
  classical
  obtain ⟨C,hC,hbound⟩ := prime_weighted_centered h
  let w (n : ℕ) : ℝ := (Real.log (max 2 n : ℕ))⁻¹
  have hlog (n : ℕ) : 0 < Real.log (max 2 n : ℕ) := Real.log_pos (by
    exact_mod_cast (show 1 < max 2 n by omega))
  have hm : Antitone w := by
    intro n m hnm
    apply inv_anti₀ (hlog n)
    exact Real.log_le_log (by positivity) (by exact_mod_cast max_le_max_left 2 hnm)
  refine ⟨w 0 * C, mul_pos (inv_pos.mpr (hlog 0)) hC, ?_⟩
  intro X d _ χ hX
  let v (n : ℕ) : ℂ := χ n - (if χ = 1 then 1 else 0)
  let g (n : ℕ) : ℂ := if n.Prime then (Real.log n : ℂ)*v n else 0
  have hs (j : ℕ) (hj : j ≤ X) :
      ‖∑ i ∈ range (j+1), g i‖ ≤ C * primeErrorScale X d := by
    simp only [g, ← sum_filter, primesLE_range]
    by_cases hlarge : 2 ≤ j
    · exact (hbound j d χ hlarge).trans (mul_le_mul_of_nonneg_left
        (scale_mono hlarge hj (Nat.pos_of_ne_zero (NeZero.ne d)) le_rfl) hC.le)
    · have he : j.primesLE=∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro p hmem
        have h' := Nat.mem_primesLE.mp hmem
        have := h'.2.two_le
        omega
      rw [he, sum_empty, norm_zero]
      unfold primeErrorScale
      positivity
  have hw (n : ℕ) : 0 ≤ w n := (inv_pos.mpr (hlog n)).le
  have habel := abel_prime_bound w g (C * primeErrorScale X d) hw hm hs
  have hwg (n : ℕ) : w n • g n = if n.Prime then v n else 0 := by
    by_cases hp : n.Prime
    · simp only [g,hp,ite_true,w,max_eq_right hp.two_le,Complex.real_smul,Complex.ofReal_inv]
      have hn : (Real.log n : ℂ) ≠ 0 := by
        exact_mod_cast (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
      rw [← mul_assoc,inv_mul_cancel₀ hn,one_mul]
    · simp [g,hp]
  simp_rw [hwg] at habel
  rw [← sum_filter, primesLE_range] at habel
  simp only [v, sum_sub_distrib] at habel
  by_cases hc : χ=1 <;> simpa [hc,nsmul_eq_mul,Nat.primesLE_card_eq_primeCounting,mul_assoc] using habel

private theorem project_character_bound {d a : ℕ} [NeZero d] (ha : a.Coprime d)
    (s : Finset ℕ) (f : ℕ → ℂ) (z : ℂ) (B : ℝ)
    (h : ∀ χ : DirichletCharacter ℂ d,
      ‖(∑ n ∈ s, f n * χ n) - (if χ=1 then z else 0)‖ ≤ B) :
    ‖(∑ n ∈ s.filter (fun n => n%d=a%d), f n) - z/(d.totient:ℂ)‖ ≤ B := by
  classical
  let t : ℂ := d.totient
  let b : ZMod d := (a : ZMod d)⁻¹
  let U (χ : DirichletCharacter ℂ d) := (∑ n ∈ s, f n * χ n)
  have ht : 0 < (d.totient:ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne d)))
  have ht' : t ≠ 0 := by dsimp [t]; exact_mod_cast ht.ne'
  have ha' : IsUnit (a:ZMod d) := (ZMod.isUnit_iff_coprime a d).mpr ha
  have hb : IsUnit b := by
    have hu : IsUnit ((a:ℤ):ZMod d) := by exact_mod_cast ha'
    simpa only [b, Int.cast_natCast] using ZMod.isUnit_inv hu
  have hsum : (∑ χ : DirichletCharacter ℂ d, χ b * U χ) =
      t * (∑ n ∈ s.filter (fun n => n%d=a%d), f n) := by
    simp only [U, Finset.mul_sum]
    rw [Finset.sum_comm, Finset.sum_filter]
    refine sum_congr rfl fun n _ => ?_
    calc
      _ = f n * (∑ χ : DirichletCharacter ℂ d, χ b * χ n) := by
        rw [Finset.mul_sum]
        exact sum_congr rfl fun χ _ => by ring
      _ = _ := by
        rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ ha']
        by_cases hn : n%d=a%d
        · have he := (ZMod.natCast_eq_natCast_iff' a n d).2 hn.symm
          simp [hn,he,t,mul_comm]
        · have he : (a:ZMod d)≠n := fun he => hn ((ZMod.natCast_eq_natCast_iff' a n d).1 he).symm
          simp [hn,he]
  have hmain : (∑ χ : DirichletCharacter ℂ d, χ b * (if χ=1 then z else 0)) = z := by
    simp [mul_ite, MulChar.one_apply hb]
  have hdiff : (∑ χ : DirichletCharacter ℂ d, χ b * (U χ - (if χ=1 then z else 0))) =
      t * ((∑ n ∈ s.filter (fun n => n%d=a%d), f n) - z/t) := by
    simp only [mul_sub, sum_sub_distrib, hsum,hmain]
    field_simp
  have hcard : Fintype.card (DirichletCharacter ℂ d) = d.totient := by
    rw [← Nat.card_eq_fintype_card]
    exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ d
  have hnorm :
      ‖∑ χ : DirichletCharacter ℂ d, χ b * (U χ - (if χ=1 then z else 0))‖ ≤ (d.totient:ℝ)*B := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _χ : DirichletCharacter ℂ d, B := by
        refine sum_le_sum fun χ _ => ?_
        rw [norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one b)).trans (h χ)
      _ = _ := by simp [nsmul_eq_mul,hcard]
  rw [hdiff,norm_mul] at hnorm
  have htN : ‖t‖=(d.totient:ℝ) := by simp [t]
  rw [htN] at hnorm
  exact (mul_le_mul_iff_right₀ ht).mp hnorm

theorem sharpPsiAP_of_twistBound (h : SharpVonMangoldtTwistBound) :
    ∃ C : ℝ, 0<C ∧ ∀ {X d a : ℕ}, 2≤X → 0<d → a.Coprime d →
      |(∑ n ∈ (Icc 1 X).filter (fun n => n%d=a%d), ArithmeticFunction.vonMangoldt n) -
        (X:ℝ)/(d.totient:ℝ)| ≤ C*Real.sqrt X*Real.log (2*(d:ℝ)*X)^2 := by
  obtain ⟨C,hC,hb⟩ := h
  refine ⟨C,hC,?_⟩
  intro X d a hX hd ha
  let : NeZero d := ⟨hd.ne'⟩
  have H := project_character_bound ha (Icc 1 X) (fun n => (ArithmeticFunction.vonMangoldt n:ℂ))
    (X:ℂ) _ (fun χ => hb X d χ hX)
  rw [← Real.norm_eq_abs, ← Complex.norm_real]
  push_cast
  exact H

theorem primeAP_count_all_moduli_of_twistBound (h : SharpVonMangoldtTwistBound) :
    ∃ C : ℝ, 0<C ∧ ∀ {N d a : ℕ}, 2≤N → 0<d → a.Coprime d →
      |((N.primesLE.filter (fun p => p%d=a%d)).card:ℝ)-(Nat.primeCounting N:ℝ)/(d.totient:ℝ)| ≤
        C*Real.sqrt N*Real.log (2*(d:ℝ)*N)^2 := by
  obtain ⟨C,hC,hb⟩ := unweighted_prime_centered h
  refine ⟨C,hC,?_⟩
  intro N d a hN hd ha
  let : NeZero d := ⟨hd.ne'⟩
  have H := project_character_bound ha N.primesLE (fun _ => (1:ℂ)) (Nat.primeCounting N:ℂ)
    (C*primeErrorScale N d) (fun χ => by simpa using hb N d χ hN)
  simp only [sum_const,nsmul_eq_mul,mul_one] at H
  rw [← Real.norm_eq_abs, ← Complex.norm_real]
  push_cast
  simpa [primeErrorScale,mul_assoc] using H

theorem sharpThetaAP_of_twistBound (h : SharpVonMangoldtTwistBound) :
    ∃ C : ℝ, 0<C ∧ ∀ {X d a : ℕ}, 2≤X → 0<d → a.Coprime d →
      |(∑ p ∈ X.primesLE.filter (fun p => p%d=a%d), Real.log p) - (X:ℝ)/(d.totient:ℝ)| ≤
        C*Real.sqrt X*Real.log (2*(d:ℝ)*X)^2 := by
  obtain ⟨C,hC,hb⟩ := weighted_prime_twist h
  refine ⟨C,hC,?_⟩
  intro X d a hX hd ha
  let : NeZero d := ⟨hd.ne'⟩
  have H := project_character_bound ha X.primesLE (fun p => (Real.log p:ℂ)) (X:ℂ)
    (C*primeErrorScale X d) (fun χ => hb X d χ hX)
  rw [← Real.norm_eq_abs, ← Complex.norm_real]
  push_cast
  simpa [primeErrorScale,mul_assoc] using H

theorem nonprincipal_prime_twist_of_twistBound (h : SharpVonMangoldtTwistBound) :
    ∃ C : ℝ, 0<C ∧ ∀ (X d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d),
      χ≠1 → 2≤X → ‖∑ p ∈ X.primesLE, χ p‖ ≤ C*Real.sqrt X*Real.log (2*(d:ℝ)*X)^2 := by
  obtain ⟨C,hC,hb⟩ := unweighted_prime_centered h
  exact ⟨C,hC,fun X d _ χ hχ hX => by simpa [hχ,primeErrorScale,mul_assoc] using hb X d χ hX⟩

theorem primeAP_count_of_twistBound (h : SharpVonMangoldtTwistBound) :
    ∃ C : ℝ, 0<C ∧ ∀ {N d a : ℕ}, 2≤N → 0<d → d≤N → a.Coprime d →
      |((N.primesLE.filter (fun p => p%d=a%d)).card:ℝ)-(Nat.primeCounting N:ℝ)/(d.totient:ℝ)| ≤
        C*Real.sqrt N*Real.log (2*(N:ℝ))^2 := by
  obtain ⟨C,hC,hb⟩ := primeAP_count_all_moduli_of_twistBound h
  refine ⟨4*C,by positivity,?_⟩
  intro N d a hN hd hdN ha
  have hn : (2:ℝ)≤N := by exact_mod_cast hN
  have hdd : (1:ℝ)≤d := by exact_mod_cast hd
  have hdn : (d:ℝ)≤N := by exact_mod_cast hdN
  have hpos : 0≤Real.log (2*(d:ℝ)*N) := Real.log_nonneg (by nlinarith)
  have hlog : Real.log (2*(d:ℝ)*N) ≤ 2*Real.log (2*(N:ℝ)) := by
    rw [show 2*Real.log (2*(N:ℝ))=Real.log ((2*(N:ℝ))^2) by rw [Real.log_pow]; norm_num]
    exact Real.log_le_log (by positivity) (by nlinarith [mul_le_mul_of_nonneg_right hdn (Nat.cast_nonneg N : (0:ℝ)≤N)])
  have hs := (sq_le_sq₀ hpos (hpos.trans hlog)).mpr hlog
  have hprod := mul_le_mul_of_nonneg_left hs (mul_nonneg hC.le (Real.sqrt_nonneg (N:ℝ)))
  exact (hb hN hd ha).trans (by nlinarith only [hprod])

theorem primeCounting_ratio_of_twistBound (h : SharpVonMangoldtTwistBound) :
    Tendsto (fun N : ℕ => (Nat.primeCounting N:ℝ)/((N:ℝ)/Real.log (N:ℝ)))
      atTop (𝓝 1) := by
  obtain ⟨C,hC,hb⟩ := weighted_prime_twist h
  have htheta {N : ℕ} (hN : 2≤N) :
      |Chebyshev.theta (N:ℝ) - N| ≤ C*Real.sqrt N*Real.log (2*(N:ℝ))^2 := by
    have H := hb N 1 (1 : DirichletCharacter ℂ 1) hN
    rw [Chebyshev.theta_eq_sum_primesLE_log, ← Real.norm_eq_abs, ← Complex.norm_real]
    push_cast
    simpa [one_char_level_one,primeErrorScale,mul_assoc] using H
  have hnatTop := tendsto_natCast_atTop_atTop (R:=ℝ)
  have hx : Tendsto (fun n : ℕ => 2*(n:ℝ)) atTop atTop := hnatTop.const_mul_atTop (by norm_num)
  have hsmall : Tendsto (fun n : ℕ => Real.log (2*(n:ℝ))^2/Real.sqrt (2*(n:ℝ))) atTop (𝓝 0) := by
    have hh := (isLittleO_log_rpow_rpow_atTop (2:ℝ) (by norm_num : (0:ℝ)<1/2)).tendsto_div_nhds_zero.comp hx
    simpa only [Function.comp_def,Real.rpow_two,Real.sqrt_eq_rpow] using hh
  have hzero : Tendsto (fun n : ℕ => (Chebyshev.theta n - n)/(n:ℝ)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hu : Tendsto (fun n : ℕ => (C*Real.sqrt 2)*(Real.log (2*(n:ℝ))^2/Real.sqrt (2*(n:ℝ)))) atTop (𝓝 0) := by
      simpa using hsmall.const_mul (C*Real.sqrt 2)
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hu
    filter_upwards [eventually_ge_atTop (2:ℕ)] with n hn
    have hnr : 0<(n:ℝ) := Nat.cast_pos.mpr (by omega)
    have hs := Real.sqrt_pos.mpr hnr
    rw [Real.norm_eq_abs,abs_div,abs_of_pos hnr]
    apply (div_le_div_of_nonneg_right (htheta hn) hnr.le).trans
    apply le_of_eq
    rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
    have hs2 : 0 < Real.sqrt 2 := by positivity
    field_simp
    nlinarith [Real.sq_sqrt hnr.le]
  have hrem : Tendsto (fun n : ℕ => ((Nat.primeCounting n:ℝ)*Real.log n - Chebyshev.theta n)/(n:ℝ))
      atTop (𝓝 0) := by
    simpa [Function.comp_def] using Chebyshev.isLittleO_primeCounting_mul_log_sub_theta.tendsto_div_nhds_zero.comp hnatTop
  have hall := (hrem.add hzero).add (tendsto_const_nhds (x:=(1:ℝ)))
  simp only [zero_add] at hall
  apply hall.congr'
  filter_upwards [eventually_ge_atTop (2:ℕ)] with n hn
  have hnr : 0<(n:ℝ) := Nat.cast_pos.mpr (by omega)
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1<n by omega))
  field_simp
  ring

theorem sharpPsiAP_of_dirichletGRH (hGRH : DirichletGRH) :
    ∃ C : ℝ, 0<C ∧ ∀ {X d a : ℕ}, 2≤X → 0<d → a.Coprime d →
      |(∑ n ∈ (Icc 1 X).filter (fun n => n%d=a%d), ArithmeticFunction.vonMangoldt n) -
        (X:ℝ)/(d.totient:ℝ)| ≤ C*Real.sqrt X*Real.log (2*(d:ℝ)*X)^2 :=
  sharpPsiAP_of_twistBound (sharpVonMangoldtTwist_of_dirichletGRH hGRH)

theorem primeAP_count_all_moduli_of_dirichletGRH (hGRH : DirichletGRH) :
    ∃ C : ℝ, 0<C ∧ ∀ {N d a : ℕ}, 2≤N → 0<d → a.Coprime d →
      |((N.primesLE.filter (fun p => p%d=a%d)).card:ℝ)-(Nat.primeCounting N:ℝ)/(d.totient:ℝ)| ≤
        C*Real.sqrt N*Real.log (2*(d:ℝ)*N)^2 :=
  primeAP_count_all_moduli_of_twistBound (sharpVonMangoldtTwist_of_dirichletGRH hGRH)

theorem sharpThetaAP_of_dirichletGRH (hGRH : DirichletGRH) :
    ∃ C : ℝ, 0<C ∧ ∀ {X d a : ℕ}, 2≤X → 0<d → a.Coprime d →
      |(∑ p ∈ X.primesLE.filter (fun p => p%d=a%d), Real.log p) - (X:ℝ)/(d.totient:ℝ)| ≤
        C*Real.sqrt X*Real.log (2*(d:ℝ)*X)^2 :=
  sharpThetaAP_of_twistBound (sharpVonMangoldtTwist_of_dirichletGRH hGRH)

theorem nonprincipal_prime_twist_of_dirichletGRH (hGRH : DirichletGRH) :
    ∃ C : ℝ, 0<C ∧ ∀ (X d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d),
      χ≠1 → 2≤X → ‖∑ p ∈ X.primesLE, χ p‖ ≤ C*Real.sqrt X*Real.log (2*(d:ℝ)*X)^2 :=
  nonprincipal_prime_twist_of_twistBound (sharpVonMangoldtTwist_of_dirichletGRH hGRH)

theorem primeAP_count_of_dirichletGRH (hGRH : DirichletGRH) :
    ∃ C : ℝ, 0<C ∧ ∀ {N d a : ℕ}, 2≤N → 0<d → d≤N → a.Coprime d →
      |((N.primesLE.filter (fun p => p%d=a%d)).card:ℝ)-(Nat.primeCounting N:ℝ)/(d.totient:ℝ)| ≤
        C*Real.sqrt N*Real.log (2*(N:ℝ))^2 :=
  primeAP_count_of_twistBound (sharpVonMangoldtTwist_of_dirichletGRH hGRH)

theorem primeCounting_ratio_of_dirichletGRH (hGRH : DirichletGRH) :
    Tendsto (fun N : ℕ => (Nat.primeCounting N:ℝ)/((N:ℝ)/Real.log (N:ℝ)))
      atTop (𝓝 1) :=
  primeCounting_ratio_of_twistBound (sharpVonMangoldtTwist_of_dirichletGRH hGRH)

end FareyGoldbach
