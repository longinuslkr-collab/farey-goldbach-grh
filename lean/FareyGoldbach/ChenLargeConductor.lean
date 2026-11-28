import FareyGoldbach.ChenIntervalLargeSieve
import FareyGoldbach.ChenSwitchingScales

/-! # Dyadic conductor aggregation for switching intervals -/

open scoped Classical BigOperators

namespace FareyGoldbach

private lemma shell_roots {M W Q R D X α : ℝ}
    (hM₀ : 0 ≤ M) (hW₀ : 0 ≤ W) (hX : 0 < X) (hQ : 0 < Q) (hR : 0 < R)
    (hRQ : R ≤ 2*Q) (hQD : Q ≤ D) (hMW : M*W ≤ 2*X)
    (hM : M ≤ 2*X^α) (hW : W ≤ 2*X^α) :
    Real.sqrt ((M+Q^2)*M)*Real.sqrt ((W+Q^2)*W)/Q ≤
      8*(X/R+X^((1+α)/2)+D*Real.sqrt X) := by
  have hx₀ := hX.le
  have root_lin (u : ℝ) (hu : 0 ≤ u) :
      Real.sqrt ((u+Q^2)*u) ≤ u+Q*Real.sqrt u := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    nlinarith only [mul_nonneg (mul_nonneg hu hQ.le) (Real.sqrt_nonneg u),
      congrArg (fun t => Q^2*t) (Real.sq_sqrt hu)]
  have hsize (u : ℝ) (hu : u ≤ 2*X^α) :
      Real.sqrt u ≤ 2*X^(α/2) := by
    have he : X^(α/2)*X^(α/2)=X^α := by rw [← Real.rpow_add hX]; congr 1; ring
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    nlinarith only [hu, he, Real.rpow_nonneg hx₀ α]
  have hroot : Real.sqrt (M*W) ≤ 2*Real.sqrt X := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    nlinarith only [hMW, hx₀, Real.sq_sqrt hx₀]
  have hpow : Real.sqrt X*X^(α/2)=X^((1+α)/2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hX]
    congr 1
    ring
  have hmix (u : ℝ) (hu : u ≤ 2*X^α) :
      Real.sqrt (M*W)*Real.sqrt u ≤ 4*X^((1+α)/2) := by
    have hh := mul_le_mul hroot (hsize u hu) (Real.sqrt_nonneg _) (by positivity)
    nlinarith only [hh, hpow]
  have hfirst : M*W/Q ≤ 4*(X/R) := by
    rw [show 4*(X/R) = 4*X/R by ring, div_le_div_iff₀ hQ hR]
    have h := mul_le_mul hMW hRQ hR.le (by positivity)
    linarith only [h]
  have hlast : Q*Real.sqrt (M*W) ≤ 2*(D*Real.sqrt X) := by
    have hh := mul_le_mul hQD hroot (Real.sqrt_nonneg _) (hQ.le.trans hQD)
    linarith only [hh]
  have hcross : (M+Q*Real.sqrt M)*(W+Q*Real.sqrt W)/Q =
      M*W/Q + Real.sqrt (M*W)*Real.sqrt M + Real.sqrt (M*W)*Real.sqrt W +
        Q*Real.sqrt (M*W) := by
    rw [Real.sqrt_mul hM₀]
    field_simp [hQ.ne']
    ring_nf
    simp only [Real.sq_sqrt hM₀, Real.sq_sqrt hW₀]
    ring
  calc
    _ ≤ (M+Q*Real.sqrt M)*(W+Q*Real.sqrt W)/Q := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul (root_lin M hM₀) (root_lin W hW₀) (Real.sqrt_nonneg _) (by positivity)) hQ.le
    _ ≤ _ := by
      rw [hcross]
      have hD := hQ.le.trans hQD
      linarith only [hfirst, hmix M hM, hmix W hW, hlast, div_nonneg hx₀ hR.le,
        mul_nonneg hD (Real.sqrt_nonneg X)]

private lemma shell_roots_multiple {r M W Q R D X α : ℝ}
    (hr : 0<r) (hM₀ : 0≤M) (hW₀ : 0≤W) (hX : 0<X) (hQ : 0<Q) (hR : 0<R)
    (hRQ : R≤2*Q) (hQD : Q≤D) (hMW : M*W≤2*X) (hM : M≤2*X^α) (hW : W≤2*X^α) :
    Real.sqrt ((M+r*Q^2)*M)*Real.sqrt ((W+r*Q^2)*W)/Q ≤
      8*(X/R+Real.sqrt r*X^((1+α)/2)+r*D*Real.sqrt X) := by
  have hp : 0<Real.sqrt r := Real.sqrt_pos.mpr hr
  have h := shell_roots (Q:=Real.sqrt r*Q) (R:=Real.sqrt r*R) (D:=Real.sqrt r*D)
    hM₀ hW₀ hX (by positivity) (by positivity)
    (by simpa only [mul_assoc,mul_left_comm] using mul_le_mul_of_nonneg_left hRQ hp.le)
    (mul_le_mul_of_nonneg_left hQD hp.le) hMW hM hW
  have hs : (Real.sqrt r*Q)^2=r*Q^2 := by rw [mul_pow,Real.sq_sqrt hr.le]
  rw [hs] at h
  convert mul_le_mul_of_nonneg_left h hp.le using 1
  · field_simp
  · conv_lhs => rw [← Real.sq_sqrt hr.le]
    rw [Real.sqrt_sq hp.le]
    field_simp

/-- Global large-conductor estimate after an exact binary decomposition of each
moving summation interval and summation over dyadic conductor shells. -/
theorem chen_large_conductor_interval_multiple_energy (r₁ M W D R N : ℕ) (hr₁ : 0<r₁) (a b : ℕ → ℂ) (lo hi : ℕ → ℕ) {α A B : ℝ} (hA : 0≤A) (hB : 0≤B)
    (hN : 1 ≤ N) (hW : 1 ≤ W) (hWN : W ≤ N) (hDN : D ≤ N) (hR : 1 ≤ R)
    (hMW : (M:ℝ)*W ≤ 2*N) (hM : (M:ℝ) ≤ 2*(N:ℝ)^α)
    (hWpow : (W:ℝ) ≤ 2*(N:ℝ)^α)
    (ha : (∑ m∈Finset.Icc 1 M, ‖a m‖^2)≤(M:ℝ)*A^2) (hb : (∑ w∈Finset.Icc 1 W, ‖b w‖^2)≤(W:ℝ)*B^2)
    (hlo : ∀ m ∈ Finset.Icc 1 M, 1 ≤ lo m) (hhi : ∀ m ∈ Finset.Icc 1 M, hi m ≤ W) :
    (∑ q ∈ Finset.Ioc R D, chenPrimitiveNorm (r₁*q) (fun χ =>
       ∑ m ∈ Finset.Icc 1 M, a m * χ (m : ZMod (r₁*q)) *
         (∑ w ∈ Finset.Icc (lo m) (hi m), b w * χ (w : ZMod (r₁*q)))) / (q:ℝ)) ≤
      100000*(chenSwitchLog N)^2*(A*B)*((N:ℝ)/R+Real.sqrt (r₁:ℝ)*(N:ℝ)^((1+α)/2)+(r₁:ℝ)*(D:ℝ)*Real.sqrt N) := by
  let E (q : ℕ) := chenPrimitiveNorm (r₁*q) (fun χ =>
      ∑ m ∈ Finset.Icc 1 M, a m * χ (m : ZMod (r₁*q)) *
        (∑ w ∈ Finset.Icc (lo m) (hi m), b w * χ (w : ZMod (r₁*q))))
  let G := (N:ℝ)/R+Real.sqrt (r₁:ℝ)*(N:ℝ)^((1+α)/2)+(r₁:ℝ)*(D:ℝ)*Real.sqrt N
  let I := Finset.range (N.log2+1)
  let S (i : ℕ) := (Finset.Ioc R D).filter (fun q => chenShellIndex q = i)
  have hN' : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hR' : (0:ℝ)<R := Nat.cast_pos.mpr hR
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hL : 0 ≤ chenSwitchLog N := zero_le_one.trans (one_le_chenSwitchLog hN)
  have hlog : Real.log (2*(W:ℝ)) ≤ chenSwitchLog N := by
    have hw' : (0:ℝ)<W := Nat.cast_pos.mpr hW
    have h := Real.log_le_log (show 0 < 2*(W:ℝ) by positivity)
      (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hWN) (by norm_num : (0:ℝ)≤2))
    unfold chenSwitchLog
    linarith only [h]
  have hpartition : (∑ q ∈ Finset.Ioc R D, E q / q) = ∑ i ∈ I, ∑ q ∈ S i, E q / q := by
    simp only [S, Finset.sum_filter]
    rw [Finset.sum_comm (s:=I)]
    apply Finset.sum_congr rfl
    intro q hq
    obtain ⟨hl,hu⟩ := Finset.mem_Ioc.mp hq
    rw [Finset.sum_ite_eq]
    simp [I, chenShellIndex_mem_range (by omega : 2≤q) (hu.trans hDN)]
  have per (i : ℕ) : (∑ q ∈ S i, E q / q) ≤ 8000*chenSwitchLog N*(A*B)*G := by
    by_cases he : (S i).Nonempty
    · let Q := 2^i
      obtain ⟨q₀, h₀⟩ := he
      have hmem {q : ℕ} (h : q∈S i) : q∈Finset.Ioc Q (2*Q) := by
        obtain ⟨hq, hi'⟩ := Finset.mem_filter.mp h
        have H := chenShell_mem (show 2≤q by have := (Finset.mem_Ioc.mp hq).1; omega)
        simpa [hi', Q] using H
      obtain ⟨hqa,hqb⟩ := Finset.mem_Ioc.mp (hmem h₀)
      obtain ⟨hR₀,hD₀⟩ := Finset.mem_Ioc.mp (Finset.mem_filter.mp h₀).1
      have hQ' : (0:ℝ)<Q := by dsimp [Q]; positivity
      have hs := shell_roots_multiple (r:=(r₁:ℝ)) (M:=(M:ℝ)) (W:=(W:ℝ)) (Q:=(Q:ℝ)) (D:=(D:ℝ))
        (Nat.cast_pos.mpr hr₁) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hN' hQ' hR'
        (by exact_mod_cast (by omega : R ≤ 2*Q)) (by exact_mod_cast (by omega : Q ≤ D)) hMW hM hWpow
      have htotal := chen_interval_bilinear_large_sieve_multiple_of_energy r₁ M W Q hr₁ a b lo hi hW ha hb hlo hhi
      have hroot (m : ℕ) (C : ℝ) (hC : 0≤C) :
          Real.sqrt (((m:ℝ)+(r₁:ℝ)*(Q:ℝ)^2)*((m:ℝ)*C^2)) = Real.sqrt (((m:ℝ)+(r₁:ℝ)*(Q:ℝ)^2)*m)*C := by
        rw [←mul_assoc,Real.sqrt_mul (by positivity),Real.sqrt_sq hC]
      rw [hroot _ A hA,hroot _ B hB] at htotal
      change (∑ q ∈ Finset.Ioc Q (2*Q), E q) ≤ _ at htotal
      calc
        _ ≤ ∑ q ∈ S i, E q / Q := by
          apply Finset.sum_le_sum
          intro q hq
          exact div_le_div_of_nonneg_left (chenPrimitiveNorm_nonneg _ _) hQ'
            (Nat.cast_le.mpr (Finset.mem_Ioc.mp (hmem hq)).1.le)
        _ ≤ (∑ q ∈ Finset.Ioc Q (2*Q), E q)/(Q:ℝ) := by
          rw [Finset.sum_div]
          apply Finset.sum_le_sum_of_subset_of_nonneg (fun q h => hmem h)
          exact fun _ _ _ => div_nonneg (chenPrimitiveNorm_nonneg _ _) hQ'.le
        _ ≤ _ := div_le_div_of_nonneg_right htotal hQ'.le
        _ = (1000*Real.log (2*(W:ℝ)) *
            (Real.sqrt (((M:ℝ)+(r₁:ℝ)*(Q:ℝ)^2)*M)*Real.sqrt (((W:ℝ)+(r₁:ℝ)*(Q:ℝ)^2)*W)/Q))*(A*B) := by ring
        _ ≤ ((1000*chenSwitchLog N)*(8*G))*(A*B) :=
          mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_left hlog (by norm_num)) hs (by positivity) (by positivity)) (mul_nonneg hA hB)
        _ = _ := by ring
    · rw [Finset.not_nonempty_iff_eq_empty.mp he, Finset.sum_empty]
      positivity
  change (∑ q ∈ Finset.Ioc R D, E q / q) ≤ _
  rw [hpartition]
  calc
    _ ≤ ∑ _i ∈ I, 8000*chenSwitchLog N*(A*B)*G := Finset.sum_le_sum fun i _ => per i
    _ = (I.card:ℝ)*(8000*chenSwitchLog N*(A*B)*G) := by simp
    _ ≤ (3*chenSwitchLog N)*(8000*chenSwitchLog N*(A*B)*G) := by
      exact mul_le_mul_of_nonneg_right (chen_log2_range_card_le hN) (by positivity)
    _ ≤ _ := by
      change _ ≤ 100000*(chenSwitchLog N)^2*(A*B)*G
      nlinarith only [mul_nonneg (mul_nonneg (sq_nonneg (chenSwitchLog N)) (mul_nonneg hA hB)) hG]

theorem chen_large_conductor_interval_multiple_bound (r₁ M W D R N : ℕ) (hr₁ : 0<r₁) (a b : ℕ → ℂ) (lo hi : ℕ → ℕ)
    (hN : 1 ≤ N) (hW : 1 ≤ W) (hWN : W ≤ N) (hDN : D ≤ N) (hR : 1 ≤ R)
    (hMW : (M:ℝ)*W ≤ 2*N) (hM : (M:ℝ) ≤ 2*(N:ℝ)^(3/4:ℝ))
    (hWpow : (W:ℝ) ≤ 2*(N:ℝ)^(3/4:ℝ))
    (ha : ∀ m ∈ Finset.Icc 1 M, ‖a m‖ ≤ 1) (hb : ∀ w ∈ Finset.Icc 1 W, ‖b w‖ ≤ 1)
    (hlo : ∀ m ∈ Finset.Icc 1 M, 1 ≤ lo m) (hhi : ∀ m ∈ Finset.Icc 1 M, hi m ≤ W) :
    (∑ q ∈ Finset.Ioc R D, chenPrimitiveNorm (r₁*q) (fun χ =>
       ∑ m ∈ Finset.Icc 1 M, a m * χ (m : ZMod (r₁*q)) *
         (∑ w ∈ Finset.Icc (lo m) (hi m), b w * χ (w : ZMod (r₁*q)))) / (q:ℝ)) ≤
      100000*(chenSwitchLog N)^2*((N:ℝ)/R+Real.sqrt (r₁:ℝ)*(N:ℝ)^(7/8:ℝ)+(r₁:ℝ)*(D:ℝ)*Real.sqrt N) := by
  have h := chen_large_conductor_interval_multiple_energy r₁ M W D R N hr₁ a b lo hi
    (α:=3/4) (A:=1) (B:=1) zero_le_one zero_le_one hN hW hWN hDN hR hMW hM hWpow
    (by simpa using Finset.sum_le_sum (fun m hm => pow_le_one₀ (norm_nonneg _) (ha m hm) (n:=2)))
    (by simpa using Finset.sum_le_sum (fun w hw => pow_le_one₀ (norm_nonneg _) (hb w hw) (n:=2))) hlo hhi
  simpa only [one_mul,mul_one,show ((1:ℝ)+3/4)/2=7/8 by norm_num] using h

theorem chen_large_conductor_interval_energy (M W D R N : ℕ) (a b : ℕ → ℂ) (lo hi : ℕ → ℕ) {α A B : ℝ} (hA : 0≤A) (hB : 0≤B)
    (hN : 1 ≤ N) (hW : 1 ≤ W) (hWN : W ≤ N) (hDN : D ≤ N) (hR : 1 ≤ R)
    (hMW : (M:ℝ)*W ≤ 2*N) (hM : (M:ℝ) ≤ 2*(N:ℝ)^α)
    (hWpow : (W:ℝ) ≤ 2*(N:ℝ)^α)
    (ha : (∑ m∈Finset.Icc 1 M, ‖a m‖^2)≤(M:ℝ)*A^2) (hb : (∑ w∈Finset.Icc 1 W, ‖b w‖^2)≤(W:ℝ)*B^2)
    (hlo : ∀ m ∈ Finset.Icc 1 M, 1 ≤ lo m) (hhi : ∀ m ∈ Finset.Icc 1 M, hi m ≤ W) :
    (∑ q ∈ Finset.Ioc R D, chenPrimitiveNorm q (fun χ =>
       ∑ m ∈ Finset.Icc 1 M, a m * χ (m : ZMod q) *
         (∑ w ∈ Finset.Icc (lo m) (hi m), b w * χ (w : ZMod q))) / (q:ℝ)) ≤
      100000*(chenSwitchLog N)^2*(A*B)*((N:ℝ)/R+(N:ℝ)^((1+α)/2)+(D:ℝ)*Real.sqrt N) := by
  convert chen_large_conductor_interval_multiple_energy 1 M W D R N (by decide)
    a b lo hi hA hB hN hW hWN hDN hR hMW hM hWpow ha hb hlo hhi using 1
  · refine Finset.sum_congr rfl (fun q _ => ?_)
    exact congrArg (fun x => x/(q:ℝ)) (congrArg (fun k => chenPrimitiveNorm k (fun χ =>
      ∑ m ∈ Finset.Icc 1 M, a m * χ (m : ZMod k) *
        ∑ w ∈ Finset.Icc (lo m) (hi m), b w * χ (w : ZMod k))) (Nat.one_mul q).symm)
  · simp

theorem chen_large_conductor_interval_bound (M W D R N : ℕ) (a b : ℕ → ℂ) (lo hi : ℕ → ℕ)
    (hN : 1 ≤ N) (hW : 1 ≤ W) (hWN : W ≤ N) (hDN : D ≤ N) (hR : 1 ≤ R)
    (hMW : (M:ℝ)*W ≤ 2*N) (hM : (M:ℝ) ≤ 2*(N:ℝ)^(3/4:ℝ))
    (hWpow : (W:ℝ) ≤ 2*(N:ℝ)^(3/4:ℝ))
    (ha : ∀ m ∈ Finset.Icc 1 M, ‖a m‖ ≤ 1) (hb : ∀ w ∈ Finset.Icc 1 W, ‖b w‖ ≤ 1)
    (hlo : ∀ m ∈ Finset.Icc 1 M, 1 ≤ lo m) (hhi : ∀ m ∈ Finset.Icc 1 M, hi m ≤ W) :
    (∑ q ∈ Finset.Ioc R D, chenPrimitiveNorm q (fun χ =>
       ∑ m ∈ Finset.Icc 1 M, a m * χ (m : ZMod q) *
         (∑ w ∈ Finset.Icc (lo m) (hi m), b w * χ (w : ZMod q))) / (q:ℝ)) ≤
      100000*(chenSwitchLog N)^2*((N:ℝ)/R+(N:ℝ)^(7/8:ℝ)+(D:ℝ)*Real.sqrt N) := by
  have h := chen_large_conductor_interval_energy M W D R N a b lo hi
    (α:=3/4) (A:=1) (B:=1) zero_le_one zero_le_one hN hW hWN hDN hR hMW hM hWpow
    (by simpa using Finset.sum_le_sum (fun m hm => pow_le_one₀ (norm_nonneg _) (ha m hm) (n:=2)))
    (by simpa using Finset.sum_le_sum (fun w hw => pow_le_one₀ (norm_nonneg _) (hb w hw) (n:=2))) hlo hhi
  simpa only [one_mul,mul_one,show ((1:ℝ)+3/4)/2=7/8 by norm_num] using h

end FareyGoldbach
