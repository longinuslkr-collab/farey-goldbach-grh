import FareyGoldbach.LinearSieveFactors
import FareyGoldbach.LinearSieveWeights
import FareyGoldbach.RosserBuchstabMeasure

/-! # Exact changes of cutoff for the cubic Rosser weights

Beyond the cube cutoff no new largest prime can enter an upper Rosser
coefficient. For the lower coefficient, increasing the cutoff subtracts the
weighted upper coefficients at the intermediate primes. These identities
use the original finite packets rather than asymptotic surrogate functions.
-/

namespace FareyGoldbach

noncomputable def rosserPacketBelow (upper : Bool) (D m : ℕ) (P : Finset ℕ)
    (g : ℕ → ℝ) (z : ℕ) : ℝ := rosserPacket upper D m (P.filter (· < z)) g

private lemma packet_below_succ (upper : Bool) (D m : ℕ) (P : Finset ℕ)
    (g : ℕ → ℝ) (p : ℕ) :
    rosserPacketBelow upper D m P g (p+1) = rosserPacketBelow upper D m P g p -
      (if p ∈ P ∧ ¬(upper = true ∧ D ≤ m*p^3)
       then g p * rosserPacketBelow (!upper) D (m*p) P g p else 0) := by
  by_cases hp : p ∈ P
  · have he : P.filter (· < p+1) = insert p (P.filter (· < p)) := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_insert, Nat.lt_succ_iff, le_iff_lt_or_eq]
      aesop
    unfold rosserPacketBelow
    rw [he, rosserPacket_insert upper D m p _ g (fun q hq => (Finset.mem_filter.mp hq).2)]
    by_cases hcut : upper=true ∧ D≤m*p^3 <;> simp [hp,hcut]
  · have he : P.filter (· < p+1) = P.filter (· <p) := by
      ext q
      simp only [Finset.mem_filter, Nat.lt_succ_iff, le_iff_lt_or_eq]
      aesop
    simp only [rosserPacketBelow,he,hp,false_and,ite_false,sub_zero]

/-- Exact plateau of the upper main polynomial above the cubic stopping cutoff. -/
theorem rosser_upper_cube_transport (D m : ℕ) (P : Finset ℕ) (g : ℕ → ℝ)
    {w z : ℕ} (hwz : w ≤ z) (hD : D ≤ m*w^3) :
    rosserPacketBelow true D m P g z = rosserPacketBelow true D m P g w := by
  induction z, hwz using Nat.le_induction with
  | base => rfl
  | succ z hz ih =>
    have hstop := hD.trans (Nat.mul_le_mul_left m (Nat.pow_le_pow_left hz 3))
    rw [packet_below_succ,ih]
    simp [hstop]

/-- A main-coefficient bound at the cube cutoff transfers to every larger cutoff
at exactly the cost of the local Euler-product ratio. -/
theorem rosser_upper_cube_comparison (D m : ℕ) (P : Finset ℕ) (g : ℕ → ℝ)
    {w z : ℕ} (hwz : w ≤ z) (hD : D ≤ m*w^3)
    {A R : ℝ} (hA : 0 ≤ A) (hg : ∀ p ∈ P, g p < 1)
    (hbase : rosserPacketBelow true D m P g w ≤ A * buchstabProduct P g w)
    (hratio : buchstabProduct P g w / buchstabProduct P g z ≤ R) :
    rosserPacketBelow true D m P g z ≤ (A * R) * buchstabProduct P g z := by
  rw [rosser_upper_cube_transport D m P g hwz hD]
  exact hbase.trans ((mul_le_mul_of_nonneg_left ((div_le_iff₀ (buchstabProduct_pos P hg z)).mp hratio)
    hA).trans_eq (mul_assoc ..).symm)

/-- For the lower sieve every eligible largest prime is subtracted, with the
upper child evaluated on the strictly smaller sifting primes. -/
theorem rosser_lower_cutoff_transport (D m : ℕ) (P : Finset ℕ) (g : ℕ → ℝ)
    {w z : ℕ} (hwz : w ≤ z) :
    rosserPacketBelow false D m P g z = rosserPacketBelow false D m P g w -
      ∑ p ∈ Finset.Ico w z, if p ∈ P then g p * rosserPacketBelow true D (m*p) P g p else 0 := by
  induction z, hwz using Nat.le_induction with
  | base => simp
  | succ z hz ih =>
    rw [packet_below_succ,ih,Finset.sum_Ico_succ_top hz]
    simp only [Bool.false_eq_true, false_and,not_false_eq_true,and_true,Bool.not_false]
    ring

/-- The lower comparison with an upper test envelope. Normalization by the
Euler product leaves precisely the signed excess of the envelope over c. -/
theorem rosser_lower_cutoff_comparison (D m : ℕ) (P : Finset ℕ) (g U : ℕ → ℝ)
    {c : ℝ} {w z : ℕ} (hwz : w ≤ z) (hg : ∀ p ∈ P, 0 ≤ g p)
    (hbase : c * buchstabProduct P g w ≤ rosserPacketBelow false D m P g w)
    (hchild : ∀ p ∈ Finset.Ico w z, p ∈ P →
        rosserPacketBelow true D (m*p) P g p ≤ U p * buchstabProduct P g p) :
    c * buchstabProduct P g z -
      (∑ p ∈ Finset.Ico w z, (U p-c) * buchstabAtom P g p) ≤ rosserPacketBelow false D m P g z := by
  have hsum : (∑ p ∈ Finset.Ico w z,
      if p ∈ P then g p * rosserPacketBelow true D (m*p) P g p else 0) ≤
      ∑ p ∈ Finset.Ico w z, U p * buchstabAtom P g p := by
    apply Finset.sum_le_sum
    intro p hp
    by_cases h : p ∈ P
    · simp only [ite_eq_left h,buchstabAtom]
      calc _ ≤ g p * (U p * buchstabProduct P g p) :=
             mul_le_mul_of_nonneg_left (hchild p hp h) (hg p h)
           _ = _ := by ring
    · simp [h,buchstabAtom]
  rw [rosser_lower_cutoff_transport D m P g hwz]
  calc _ = c * buchstabProduct P g w -
        (∑ p ∈ Finset.Ico w z, U p * buchstabAtom P g p) := by
          simp_rw [sub_mul]
          rw [Finset.sum_sub_distrib,←Finset.mul_sum,buchstab_tail_mass P g hwz]
          ring
       _ ≤ _ := sub_le_sub hbase hsum

/-- The limiting comparison furnished by the lower transition from parameter four.
With u = log D / log p its kernel is (F(u−1)−f(4))/s. -/
theorem rosser_lower_transport_profile {s : ℝ} (hs : 2 ≤ s) (hs4 : s ≤ 4) :
    linearSieveLowerFactor 4 -
      (∫ u in s..4, linearSieveUpperFactor (u-1) - linearSieveLowerFactor 4) / s =
        linearSieveLowerFactor s := by
  let A := 2 * Real.exp Real.eulerMascheroniConstant
  let c := linearSieveLowerFactor 4
  let J (u : ℝ) := A * Real.log (u-1) - c*u
  have hd (u : ℝ) (hu : u ∈ Set.uIcc s 4) :
      HasDerivAt J (linearSieveUpperFactor (u-1) - c) u := by
    rw [Set.uIcc_of_le hs4] at hu
    have hn : u-1 ≠ 0 := by linarith [hu.1]
    have hid : HasDerivAt (fun v : ℝ => v) 1 u := hasDerivAt_id _
    have hlog := (hid.sub_const 1).log hn
    convert (hlog.const_mul A).sub (hid.const_mul c) using 1
    dsimp only [linearSieveUpperFactor,A]
    ring
  have hi : IntervalIntegrable (fun u => linearSieveUpperFactor (u-1) - c)
      MeasureTheory.volume s 4 := by
    apply ContinuousOn.intervalIntegrable
    unfold linearSieveUpperFactor
    apply ContinuousOn.sub _ continuousOn_const
    apply continuousOn_const.div (continuousOn_id.sub continuousOn_const)
    intro u hu
    rw [Set.uIcc_of_le hs4] at hu
    change u-1 ≠ 0
    linarith [hu.1]
  change c - (∫ u in s..4, linearSieveUpperFactor (u-1)-c)/s = _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
  dsimp only [J,c,A,linearSieveLowerFactor]
  field_simp [show s ≠ 0 by linarith]
  ring
end FareyGoldbach