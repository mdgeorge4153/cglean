import LeanCert.Core.IntervalDyadic

/-!
# Comparing intervals

`compare? x y` reports the order of two intervals when they are separated, and
`none` when they overlap. Overlap is exactly the case in which the intervals
carry no information about the order of the values inside them, which is what
`compare?_complete` records.

This is the decision a filtered representation makes before falling back on
exact arithmetic.
-/

namespace CGLean

open LeanCert.Core

/-! # Comparing intervals -/

/-- The common order of every member of `x` with every member of `y`, or `none`
when the intervals overlap. -/
def compare? (x y : IntervalDyadic) : Option Ordering :=
  if x.hi < y.lo then some .lt
  else if y.hi < x.lo then some .gt
  else if compare x.lo x.hi == .eq && compare x.hi y.lo == .eq && compare y.lo y.hi == .eq then some .eq
  else none

/-! # LeanCert helpers -/

@[simp] lemma dyadic_compare_eq_iff (d e : LeanCert.Core.Dyadic) :
    compare d e = .eq ↔ d.toRat = e.toRat := LeanCert.Core.Dyadic.compare_eq_iff d e

@[simp] lemma dyadic_lt_iff_toRat_lt (d e : LeanCert.Core.Dyadic) :
    d < e ↔ d.toRat < e.toRat := by
  simp [LT.lt, LeanCert.Core.Dyadic.lt, LeanCert.Core.Dyadic.compare_lt_iff]

/-! # Main results -/

@[simp] lemma compare?_eq_iff_coords_eq (x y : IntervalDyadic) : compare? x y = some .eq ↔
    x.lo.toRat = x.hi.toRat ∧ x.hi.toRat = y.lo.toRat ∧ y.lo.toRat = y.hi.toRat := by
  unfold compare?
  constructor <;> split_ifs with h1 h2 h3 <;> simp at * <;> aesop

@[simp] lemma compare?_lt_iff_lt (x y : IntervalDyadic) :
    compare? x y = some .lt ↔ x.hi.toRat < y.lo.toRat := by
  unfold compare?
  constructor <;> split_ifs with h1 h2 h3 <;> simp at * <;> linarith [x.le, y.le]

@[simp] lemma compare?_gt_iff_gt (x y : IntervalDyadic) :
    compare? x y = some .gt ↔ y.hi.toRat < x.lo.toRat := by
  unfold compare?
  constructor <;> split_ifs with h1 h2 h3 <;> simp at * <;> linarith [x.le, y.le]


/-- When `compare?` commits to an order, every pair of members realises it. -/
theorem compare_of_compare? {x y : IntervalDyadic} {o : Ordering}
    (h : compare? x y = some o) :
    ∀ a ∈ x, ∀ b ∈ y, compare a b = o := by
  intro a ⟨halo, hahi⟩ b ⟨hblo, hbhi⟩
  unfold compare? at h
  split_ifs at h with h1 h2 h3 <;> rw [Option.some.injEq] at h <;> subst h
  · apply compare_lt_iff_lt.mpr
    have : (x.hi.toRat < (y.lo.toRat : ℝ)) := by
      exact_mod_cast (dyadic_lt_iff_toRat_lt x.hi y.lo).mp h1
    linarith
  . apply compare_gt_iff_gt.mpr
    have : (y.hi.toRat < (x.lo.toRat : ℝ)) := by
      exact_mod_cast (dyadic_lt_iff_toRat_lt y.hi x.lo).mp h2
    linarith
  . apply compare_eq_iff_eq.mpr
    simp at h3
    obtain ⟨⟨he1, he2⟩, he3⟩ := h3
    rw [he1] at halo
    rw [←he3] at hbhi
    rw [←he2] at hblo hbhi
    linarith

/-- `compare?` returns `none` only when the intervals genuinely determine
nothing: there are members realising two different orders. This is not needed
for soundness, but it is what makes the filter worth having --- it says the
exact fallback is taken only when unavoidable. -/
theorem compare?_complete {x y : IntervalDyadic} (h : compare? x y = none) :
    ∃ x₁ ∈ x, ∃ y₁ ∈ y, ∃ x₂ ∈ x, ∃ y₂ ∈ y, compare x₁ y₁ ≠ compare x₂ y₂ := by
  refine ⟨x.lo.toRat, ⟨by simp [x.le], ?_⟩⟩
  refine ⟨y.hi.toRat, ⟨by simp [y.le], ?_⟩⟩
  refine ⟨x.hi.toRat, ⟨by simp [x.le], ?_⟩⟩
  refine ⟨y.lo.toRat, ⟨by simp [y.le], ?_⟩⟩

  have hxle : (x.lo.toRat : ℝ) ≤ (x.hi.toRat : ℝ) := by exact_mod_cast x.le
  have hyle : (y.lo.toRat : ℝ) ≤ (y.hi.toRat : ℝ) := by exact_mod_cast y.le

  unfold compare? at h; split_ifs at h with h1 h2 h3; simp at h3

  intro e; cases hab : compare (x.lo.toRat : ℝ) y.hi.toRat <;> rw [hab, eq_comm] at e
  . simp [compare_lt_iff_lt] at *; linarith
  . simp at *; apply h3 <;> linarith
  . simp [compare_gt_iff_gt] at *; linarith

/-! ## Rounding and constants -/

/-- Significant bits kept in each endpoint. Exact dyadic products double the
mantissa, so every arithmetic result is rounded back to this. -/
def precision : Nat := 64

/-- Round each endpoint of `I` outward to `precision` significant bits. -/
def trim (I : IntervalDyadic) : IntervalDyadic :=
  ⟨I.lo.normalizeDown precision, I.hi.normalizeUp precision, by
    calc (I.lo.normalizeDown precision).toRat
        ≤ I.lo.toRat := LeanCert.Core.Dyadic.toRat_normalizeDown_le _ _
      _ ≤ I.hi.toRat := I.le
      _ ≤ (I.hi.normalizeUp precision).toRat := LeanCert.Core.Dyadic.toRat_normalizeUp_ge _ _⟩

theorem mem_trim {x : ℝ} {I : IntervalDyadic} (hx : x ∈ I) : x ∈ trim I := by
  rw [IntervalDyadic.mem_def] at hx ⊢
  have hlo : ((I.lo.normalizeDown precision).toRat : ℝ) ≤ I.lo.toRat := by
    exact_mod_cast LeanCert.Core.Dyadic.toRat_normalizeDown_le _ _
  have hhi : (I.hi.toRat : ℝ) ≤ (I.hi.normalizeUp precision).toRat := by
    exact_mod_cast LeanCert.Core.Dyadic.toRat_normalizeUp_ge _ _
  exact ⟨hlo.trans hx.1, hx.2.trans hhi⟩

/-- The interval containing exactly the integer `i`. -/
def ofInt (i : ℤ) : IntervalDyadic := IntervalDyadic.singleton (LeanCert.Core.Dyadic.ofInt i)

theorem mem_ofInt (i : ℤ) : (i : ℝ) ∈ ofInt i := by
  simpa [ofInt, LeanCert.Core.Dyadic.toRat_ofInt] using
    IntervalDyadic.mem_singleton (LeanCert.Core.Dyadic.ofInt i)

/-- Absolute precision, as a binary exponent, for results that pass through
rational intervals. -/
def ratPrec : Int := -(precision : Int)

/-- An interval containing the rational `q`, exact when `q` is dyadic enough. -/
def ofRat (q : ℚ) : IntervalDyadic :=
  IntervalDyadic.ofIntervalRat (IntervalRat.singleton q) ratPrec

theorem mem_ofRat (q : ℚ) : (q : ℝ) ∈ ofRat q :=
  IntervalDyadic.mem_ofIntervalRat (IntervalRat.mem_singleton q) ratPrec (by simp [ratPrec])

/-! ## Reciprocals -/

/-- The reciprocal of `I`, or `none` when `I` contains zero.

The reciprocal is taken over rational endpoints and rounded back, at the
absolute precision `ratPrec`; LeanCert has no dyadic reciprocal. -/
def inv? (I : IntervalDyadic) : Option IntervalDyadic :=
  if h : IntervalRat.containsZero I.toIntervalRat then none
  else some (trim (IntervalDyadic.ofIntervalRat (IntervalRat.invNonzero ⟨_, h⟩) ratPrec))

theorem mem_inv? {x : ℝ} {I J : IntervalDyadic} (hx : x ∈ I) (h : inv? I = some J) :
    x⁻¹ ∈ J := by
  unfold inv? at h
  split_ifs at h with hz
  rw [Option.some.injEq] at h
  subst h
  have hxR : x ∈ I.toIntervalRat := IntervalDyadic.mem_toIntervalRat.mp hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [IntervalRat.mem_def] at hxR
    exact hz ⟨by exact_mod_cast hxR.1, by exact_mod_cast hxR.2⟩
  exact mem_trim (IntervalDyadic.mem_ofIntervalRat
    (IntervalRat.mem_invNonzero (I := ⟨_, hz⟩) hxR hx0) ratPrec (by simp [ratPrec]))

/-! ## Square roots

LeanCert's `IntervalDyadic.sqrt` returns `[0, max hi 1]`, which is sound but too
wide to separate anything. These bounds are within `2⁻ᵏ`, from `Nat.sqrt` of the
endpoints scaled by `4ᵏ`. -/

/-- A lower bound on `√q`, within `2⁻ᵏ`. -/
def sqrtLo (q : ℚ) (k : ℕ) : ℚ := (Nat.sqrt ⌊q * 4 ^ k⌋₊ : ℚ) / 2 ^ k

/-- An upper bound on `√q`, within `2⁻ᵏ`. -/
def sqrtHi (q : ℚ) (k : ℕ) : ℚ := (Nat.sqrt ⌈q * 4 ^ k⌉₊ + 1 : ℚ) / 2 ^ k

theorem sqrtLo_le (q : ℚ) (k : ℕ) : (sqrtLo q k : ℝ) ≤ Real.sqrt q := by
  unfold sqrtLo
  rcases lt_or_ge q 0 with hq | hq
  · have : ⌊q * 4 ^ k⌋₊ = 0 := Nat.floor_eq_zero.mpr (by
      have : q * 4 ^ k < 0 := mul_neg_of_neg_of_pos hq (by positivity)
      linarith)
    simp [this, Real.sqrt_nonneg]
  · push_cast
    rw [Real.le_sqrt (by positivity) (by exact_mod_cast hq), div_pow]
    have h1 : ((Nat.sqrt ⌊q * 4 ^ k⌋₊ : ℕ) : ℝ) ^ 2 ≤ (⌊q * 4 ^ k⌋₊ : ℝ) := by
      exact_mod_cast Nat.sqrt_le' _
    have h2 : (⌊q * 4 ^ k⌋₊ : ℝ) ≤ (q : ℝ) * 4 ^ k := by
      exact_mod_cast Nat.floor_le (by positivity)
    rw [div_le_iff₀ (by positivity), show ((2 : ℝ) ^ k) ^ 2 = 4 ^ k by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num]
    linarith

theorem le_sqrtHi (q : ℚ) (k : ℕ) : Real.sqrt q ≤ (sqrtHi q k : ℝ) := by
  unfold sqrtHi
  push_cast
  rw [Real.sqrt_le_left (by positivity), div_pow, le_div_iff₀ (by positivity),
    show ((2 : ℝ) ^ k) ^ 2 = 4 ^ k by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
  have h1 : (q : ℝ) * 4 ^ k ≤ (⌈q * 4 ^ k⌉₊ : ℝ) := by
    exact_mod_cast Nat.le_ceil _
  have h2 : (⌈q * 4 ^ k⌉₊ : ℝ) < ((Nat.sqrt ⌈q * 4 ^ k⌉₊ : ℕ) + 1 : ℝ) ^ 2 := by
    exact_mod_cast Nat.lt_succ_sqrt' _
  linarith

/-- An interval containing the square root of every member of `I`. -/
def sqrt (I : IntervalDyadic) : IntervalDyadic :=
  trim (IntervalDyadic.ofIntervalRat
    ⟨sqrtLo I.lo.toRat precision, sqrtHi I.hi.toRat precision, by
      have := (sqrtLo_le I.lo.toRat precision).trans <|
        (Real.sqrt_le_sqrt (by exact_mod_cast I.le)).trans (le_sqrtHi I.hi.toRat precision)
      exact_mod_cast this⟩ ratPrec)

theorem mem_sqrt {x : ℝ} {I : IntervalDyadic} (hx : x ∈ I) : Real.sqrt x ∈ sqrt I := by
  rw [IntervalDyadic.mem_def] at hx
  refine mem_trim (IntervalDyadic.mem_ofIntervalRat ?_ ratPrec (by simp [ratPrec]))
  rw [IntervalRat.mem_def]
  exact ⟨(sqrtLo_le _ _).trans (Real.sqrt_le_sqrt hx.1),
    (Real.sqrt_le_sqrt hx.2).trans (le_sqrtHi _ _)⟩

end CGLean
