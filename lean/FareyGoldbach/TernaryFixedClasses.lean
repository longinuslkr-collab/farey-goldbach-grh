import FareyGoldbach.TernaryCandidatePrimes
import FareyGoldbach.TernaryProgressions

/-! # Zero ternary exceptions for three prescribed reduced classes -/

open Filter
open scoped Topology

namespace FareyGoldbach

noncomputable def ternaryFixedParameter (X r : ℕ) : ℝ :=
  (r:ℝ)^3 * Real.log (2*(X:ℝ))^8 / (((r:ℝ)/r.totient)^8*(X:ℝ))

set_option maxHeartbeats 1000000 in
/-- An absolute upper bound on the fixed-class parameter forces every
admissible odd integer in the block to have the prescribed representation. -/
theorem ternary_fixed_block_of_dirichletGRH (hGRH : DirichletGRH) :
    ∃ ε : ℝ, 0<ε ∧ ∀ {X r : ℕ}, 16≤X → 0<r → r≤X → ternaryFixedParameter X r<ε →
      ∀ b₁ b₂ b₃ : ReducedClass r, ternaryGoodBlock X r b₁.1 b₂.1 b₃.1 := by
  obtain ⟨c,hc,hcandidate⟩ := ternary_candidate_prime_lower_of_dirichletGRH hGRH
  obtain ⟨C,hC,hbinary⟩ := target_of_dirichletGRH hGRH
  refine ⟨min (c^2/64) (1/(64*C)^2),lt_min (by positivity) (by positivity),?_⟩
  intro X r hX hr hrX hpar b₁ b₂ b₃
  let L := Real.log (2*(X:ℝ))
  let φ : ℝ := r.totient
  let κ := (r:ℝ)/φ
  let F := ternaryFixedParameter X r
  let D := dyadicBudget X r
  let W := (X:ℝ)/(64*φ*L)
  have hX₂ : 2≤X := by omega
  have hXp : (0:ℝ)<X := Nat.cast_pos.mpr (by omega)
  have hrp : (0:ℝ)<r := Nat.cast_pos.mpr hr
  have hr₁ : (1:ℝ)≤r := Nat.one_le_cast.mpr hr
  have hφ : 0<φ := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  have hκ : 0<κ := div_pos hrp hφ
  have hL : 0<L := zero_lt_one.trans_le (one_le_log_two_mul hX₂)
  have hκL : κ≤2*L := by
    refine (div_totient_le_two_log hr).trans (mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) ?_)
      (by norm_num))
    exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hrX) (by norm_num)
  have hκφ : κ*φ=(r:ℝ) := by dsimp [κ]; field_simp
  have hκ₆ : κ^6≤64*L^6 := by
    simpa only [mul_pow,show (2:ℝ)^6=64 by norm_num] using pow_le_pow_left₀ hκ.le hκL 6
  have hthin : (φ*L)^2 ≤ 64*(X:ℝ)*F := by
    have he : (φ*L)^2*κ^8 = (r:ℝ)^2*κ^6*L^2 := by
      calc _ = (κ*φ)^2*κ^6*L^2 := by ring
           _ = _ := by rw [hκφ]
    have hright : (64*(X:ℝ)*F)*κ^8 = 64*(r:ℝ)^3*L^8 := by
      dsimp [F,ternaryFixedParameter,κ,φ,L]; field_simp
    apply le_of_mul_le_mul_right _ (pow_pos hκ 8)
    rw [he,hright]
    calc (r:ℝ)^2*κ^6*L^2 ≤ (r:ℝ)^2*(64*L^6)*L^2 :=
         mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hκ₆ (sq_nonneg _)) (sq_nonneg _)
      _ = 64*(r:ℝ)^2*L^8 := by ring
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_right hr₁ (sq_nonneg (r:ℝ))
        have hh' : (r:ℝ)^2 ≤ (r:ℝ)^3 := by nlinarith only [hh]
        have hm := mul_le_mul_of_nonneg_right hh' (show 0≤64*L^8 by positivity)
        linarith only [hm]
  have hF₁ : F<c^2/64 := hpar.trans_le (min_le_left _ _)
  have hF₂ : F<1/(64*C)^2 := hpar.trans_le (min_le_right _ _)
  have hcand : φ≤c*Real.sqrt (X:ℝ)/L := by
    have hh := mul_lt_mul_of_pos_left hF₁ (show 0<64*(X:ℝ) by positivity)
    have hh' : (φ*L)^2≤(c*Real.sqrt (X:ℝ))^2 := by
      rw [mul_pow c,Real.sq_sqrt hXp.le]
      linarith only [hthin,hh]
    exact (le_div_iff₀ hL).2 ((sq_le_sq₀ (by positivity) (by positivity)).mp hh')
  have hprime : W≤((ternaryCandidatePrimes X r b₁.1).card:ℝ) :=
    hcandidate hX hr hrX hcand b₁.1 b₁.2
  let S := C*D*(64*φ*L)/(X:ℝ)
  have hS₀ : 0≤S := by dsimp [S,D,dyadicBudget]; positivity
  have hS : S^2=(64*C)^2*F := by
    dsimp [S,D,F,dyadicBudget,ternaryFixedParameter,L,φ]
    simp only [mul_pow,div_pow,Real.sq_sqrt (by positivity : 0≤(X:ℝ)*r)]
    field_simp
  have hSlt : S<1 := by
    have hp : S^2<1 := by
      rw [hS]
      calc _ < (64*C)^2*(1/(64*C)^2) := mul_lt_mul_of_pos_left hF₂ (by positivity)
           _ = 1 := by field_simp
    exact (sq_lt_sq₀ hS₀ (by norm_num : (0:ℝ)≤1)).mp (by simpa using hp)
  have hCD : C*D<W := by
    apply (lt_div_iff₀ (show 0<64*φ*L by positivity)).2
    simpa only [one_mul] using (div_lt_iff₀ hXp).mp hSlt
  by_contra hbad
  have he := ternaryCandidate_card_le_exceptions_of_badBlock hr b₁ b₂ b₃ hbad
  have he' : ((ternaryCandidatePrimes X r b₁.1).card:ℝ) ≤
      ((exceptions (shortProgressions hr b₂ b₃) X).card:ℝ) := Nat.cast_le.mpr he
  have hbin := hbinary (shortProgressions hr b₂ b₃) X (by omega) hrX
  have hbound : ((exceptions (shortProgressions hr b₂ b₃) X).card:ℝ)≤C*D :=
    hbin.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hC.le)
  exact (not_lt_of_ge ((hprime.trans he').trans hbound)) hCD

/-- The shrinking parameter guarantees zero exceptions eventually, uniformly
over choices of all three reduced classes at each index. -/
theorem ternary_fixed_classes_eventually_of_dirichletGRH (hGRH : DirichletGRH)
    (X r : ℕ→ℕ) (hr : ∀ j,0<r j) (hrX : ∀ j,r j≤X j) (hX : Tendsto X atTop atTop)
    (hparam : Tendsto (fun j => ternaryFixedParameter (X j) (r j)) atTop (𝓝 0)) :
    ∀ᶠ j in atTop, ∀ b₁ b₂ b₃ : ReducedClass (r j),
      ternaryGoodBlock (X j) (r j) b₁.1 b₂.1 b₃.1 := by
  obtain ⟨ε,hε,h⟩ := ternary_fixed_block_of_dirichletGRH hGRH
  have hlarge : ∀ᶠ j in atTop, 16≤X j := (tendsto_atTop.1 hX) 16
  have hsmall := hparam.eventually (gt_mem_nhds hε)
  filter_upwards [hlarge,hsmall] with j hj hs
  exact h hj (hr j) (hrX j) hs

end FareyGoldbach
