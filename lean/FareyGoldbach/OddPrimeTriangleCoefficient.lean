import FareyGoldbach.OddPrimeWindow
import FareyGoldbach.TriangularFrequencyKernel

/-! # The odd-prime convolution and its triangular Fourier coefficient -/

open MeasureTheory
open scoped Classical

namespace FareyGoldbach

private def primeWindowPairs (P : Progressions) (Y : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (Y/P.r+1)).product (Finset.range (Y/P.r+1))

private noncomputable def primeWindowPairWeight (P : Progressions) (Y : ℕ) (i : ℕ × ℕ) : ℝ :=
  oddPrimeWindowWeight P.r P.b₁ Y i.1 * oddPrimeWindowWeight P.r P.b₂ Y i.2

/-- The sum of the weights of pairs of odd primes at frequency (m). -/
noncomputable def oddPrimeConvWeight (P : Progressions) (Y m : ℕ) : ℝ :=
  ∑ i ∈ (primeWindowPairs P Y).filter (fun i => i.1+i.2=m), primeWindowPairWeight P Y i

theorem oddPrimeConvWeight_nonneg (P : Progressions) (Y m : ℕ) :
    0≤oddPrimeConvWeight P Y m :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (oddPrimeWindowWeight_nonneg ..) (oddPrimeWindowWeight_nonneg ..)

theorem even_and_rep_of_oddPrimeConvWeight_pos {P : Progressions} {Y m : ℕ}
    (h : 0<oddPrimeConvWeight P Y m) :
    Even (P.r*m+P.b₁+P.b₂) ∧ (primeRepresentations P (P.r*m+P.b₁+P.b₂)).Nonempty := by
  classical
  let S := (primeWindowPairs P Y).filter (fun i => i.1+i.2=m)
  have hex : ∃ i ∈ S, 0<primeWindowPairWeight P Y i := by
    by_contra! hn
    exact h.not_ge (Finset.sum_nonpos hn)
  obtain ⟨⟨i,j⟩,hij,hpos⟩ := hex
  have hsum : i+j=m := (Finset.mem_filter.mp hij).2
  change 0<oddPrimeWindowWeight P.r P.b₁ Y i * oddPrimeWindowWeight P.r P.b₂ Y j at hpos
  obtain ⟨hp,ho⟩ := oddPrimeWindowWeight_prime_odd (pos_of_mul_pos_left hpos (oddPrimeWindowWeight_nonneg ..))
  obtain ⟨hq,ho'⟩ := oddPrimeWindowWeight_prime_odd (pos_of_mul_pos_right hpos (oddPrimeWindowWeight_nonneg ..))
  have hadd : P.r*i+P.b₁+(P.r*j+P.b₂)=P.r*m+P.b₁+P.b₂ := by rw [←hsum,Nat.mul_add]; omega
  refine ⟨hadd ▸ ho.add_odd ho', ⟨(P.r*i+P.b₁,P.r*j+P.b₂),Finset.mem_filter.mpr ⟨?_,?_⟩⟩⟩
  · exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hp.two_le,by omega⟩,
      Finset.mem_Icc.mpr ⟨hq.two_le,by omega⟩⟩
  · exact ⟨hp,hq,hadd,by simp [Nat.add_mod,Nat.mod_eq_of_lt P.b₁_lt],
      by simp [Nat.add_mod,Nat.mod_eq_of_lt P.b₂_lt]⟩

/-- The triangularly weighted Fourier coefficient, for any real frequency center. -/
noncomputable def trianglePrimeCoefficient (P : Progressions) (Y : ℕ) (η x : ℝ) : ℂ :=
  ∫ t in -η..η, (triangleWindow η t : ℂ) *
    (oddPrimeWindowSum P.r P.b₁ Y t * oddPrimeWindowSum P.r P.b₂ Y t * e (-(x*t)))

theorem trianglePrimeCoefficient_eq_sum (P : Progressions) (Y : ℕ) {η : ℝ} (hη : 0<η) (x : ℝ) :
    trianglePrimeCoefficient P Y η x =
      ((∑ m ∈ Finset.range (2*(Y/P.r)+1), oddPrimeConvWeight P Y m * triangleFrequency η ((m:ℝ)-x) : ℝ):ℂ) := by
  classical
  let I := primeWindowPairs P Y
  let k (i : ℕ × ℕ) := i.1+i.2
  let W (i : ℕ × ℕ) := primeWindowPairWeight P Y i
  let G (u t : ℝ) := (triangleWindow η t:ℂ)*e (u*t)
  have hc (u : ℝ) : Continuous (G u) := (Complex.continuous_ofReal.comp (continuous_triangleWindow η)).mul
    (continuous_e_real.comp (continuous_const.mul continuous_id))
  have hpt (t : ℝ) : (triangleWindow η t:ℂ)*(oddPrimeWindowSum P.r P.b₁ Y t *
      oddPrimeWindowSum P.r P.b₂ Y t * e (-(x*t))) = ∑ i ∈ I, (W i:ℂ)*G ((k i:ℝ)-x) t := by
    dsimp only [I,primeWindowPairs,oddPrimeWindowSum]
    rw [Finset.product_eq_sprod,Finset.sum_product]
    simp only [Finset.mul_sum,Finset.sum_mul]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [W,G,k,primeWindowPairWeight,Nat.cast_add,Complex.ofReal_mul]
    rw [show ((i:ℝ)+(j:ℝ)-x)*t=t*i+t*j+ -(x*t) by ring,e_add,e_add]
    ring
  have hmap (i : ℕ × ℕ) (hi : i ∈ I) : k i ∈ Finset.range (2*(Y/P.r)+1) := by
    obtain ⟨h₁,h₂⟩ := Finset.mem_product.mp hi
    have hh₁ := Finset.mem_range.mp h₁
    have hh₂ := Finset.mem_range.mp h₂
    exact Finset.mem_range.mpr (by dsimp [k]; omega)
  calc
    trianglePrimeCoefficient P Y η x = ∫ t in -η..η, ∑ i ∈ I, (W i:ℂ)*G ((k i:ℝ)-x) t :=
      intervalIntegral.integral_congr fun t _ => hpt t
    _ = ∑ i ∈ I, ((W i * triangleFrequency η ((k i:ℝ)-x):ℝ):ℂ) := by
      rw [intervalIntegral.integral_finsetSum (s:=I) (f:=fun i t => (W i:ℂ)*G ((k i:ℝ)-x) t)
        (fun i _ => (continuous_const.mul (hc ((k i:ℝ)-x))).intervalIntegrable ..)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [intervalIntegral.integral_const_mul,show (∫ t in -η..η, G ((k i:ℝ)-x) t)=_ from
        triangleWindow_fourier hη ((k i:ℝ)-x),Complex.ofReal_mul]
    _ = _ := by
      rw [←Complex.ofReal_sum]
      apply congrArg Complex.ofReal
      rw [←Finset.sum_fiberwise_of_maps_to hmap]
      refine Finset.sum_congr rfl fun m _ => ?_
      dsimp only [oddPrimeConvWeight]
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i hi => by
        dsimp only [W,k]
        rw [(Finset.mem_filter.mp hi).2]

/-- A strict tail estimate locates a positive convolution coefficient in the desired window. -/
theorem exists_oddPrimeConvWeight_pos_of_tail_lt (P : Progressions) (Y : ℕ) {η : ℝ}
    (hη : 0<η) (x R : ℝ)
    (h : (∑ m ∈ (Finset.range (2*(Y/P.r)+1)).filter (fun m : ℕ => R≤|(m:ℝ)-x|),
      oddPrimeConvWeight P Y m * triangleFrequency η ((m:ℝ)-x)) < (trianglePrimeCoefficient P Y η x).re) :
    ∃ m : ℕ, |(m:ℝ)-x|<R ∧ 0<oddPrimeConvWeight P Y m := by
  classical
  by_contra! hn
  rw [trianglePrimeCoefficient_eq_sum P Y hη x,Complex.ofReal_re] at h
  apply h.ne
  refine Finset.sum_subset (Finset.filter_subset ..) fun m hm hmiss => ?_
  have hnear : |(m:ℝ)-x|<R := lt_of_not_ge (fun hf => hmiss (Finset.mem_filter.mpr ⟨hm,hf⟩))
  rw [le_antisymm (hn m hnear) (oddPrimeConvWeight_nonneg P Y m),zero_mul]

end FareyGoldbach
