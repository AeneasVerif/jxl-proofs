import Aeneas
import JxlProofs.Funs
import JxlProofs.Types
open Aeneas Aeneas.Std Result Error

namespace jxl

open entropy_coding.ans
open jxl.bit_reader

-- INVARIANTS OVER TYPES

@[simp]
def bit_reader.BitReader.invariant (self: bit_reader.BitReader) :=
  self.bits_in_buf < Usize.ofNat 64

@[simp]
def entropy_coding.ans.Bucket.invariant (self: Bucket): Bool :=
  self.dist.val < 2^LOG_SUM_PROBS.val ∧
  self.alias_dist_xor.val < 2^LOG_SUM_PROBS.val ∧
  self.alias_offset.val < self.dist

@[simp]
def entropy_coding.ans.AnsHistogram.invariant (self: AnsHistogram) :=
  self.log_bucket_size <= LOG_SUM_PROBS ∧
  self.buckets.len.val = 2^(LOG_SUM_PROBS.val - self.log_bucket_size.val) ∧
  self.buckets.val.all (fun b => b.invariant)

-- HELPERS

deriving instance Inhabited for AnsHistogram
deriving instance Inhabited for Bucket

def bucket_index (hist: AnsHistogram) (state: U32): Result Std.Usize :=
  do
    let r ← (state &&& U32.ofNat 0xfff) >>> hist.log_bucket_size
    -- avoids progress* being blocked because of an automatically-inserted
    -- coercion that is not recognized by the implementation of progress*
    Result.ok (Usize.ofNatCore r.val (by scalar_tac))

-- PROGRESS LEMMAS

@[simp,scalar_tac x.val * y.val]
theorem times_zero_or_1 (x y: U32) (h: y.val = 0 ∨ y.val = 1): x.val * y.val <= U32.max :=
  by
    cases h <;> scalar_tac

@[simp,scalar_tac x &&& y]
theorem and_lt1 (x y: U32): x &&& y <= x := by bv_tac 32

@[simp,scalar_tac x &&& y]
theorem and_lt2 (x y: U32): x &&& y <= y := by bv_tac 32

@[simp,scalar_tac x ||| y]
theorem or_lt1 (x y: U32): x <= x ||| y := by bv_tac 32

@[simp,scalar_tac x ||| y]
theorem or_lt2 (x y: U32): y <= x ||| y := by bv_tac 32

@[simp,scalar_tac x ||| y]
theorem or_lt2_usize (x y: Usize): y <= x ||| y := by
  let ⟨bv_x⟩ := x
  let ⟨bv_y⟩ := y
  cases System.Platform.numBits_eq <;>
  . rename_i h
    have : bv_y ≤ bv_x ||| bv_y := by
      -- We want to do something like `subst h` to rewrite the types knowing about the term
      -- equality. However, `subst` only takes type equalities, so this is basically a trick to do
      -- that without `subst`.
      revert bv_x bv_y
      unfold UScalarTy.numBits
      rw [h]
      intro bv_x bv_y
      simp at bv_x bv_y
      bv_tac
    -- Not sure I understand why `exact` is needed here.
    exact this

@[simp,scalar_tac x.len]
theorem len_is_len (x: alloc.vec.Vec a): x.len = x.deref.length := by rfl

-- SPECIFYING BITREADER

@[step]
theorem refill_slow_loop_does_not_panic (data0 : Slice Std.U8) (bit_buf0 : Std.U64) (bits_in_buf0 : Std.Usize) :
  BitReader.refill_slow_loop data0 bit_buf0 bits_in_buf0 ⦃ r => True ⦄ := by
    -- NOTE: the generated code does not seem to be able to reuse field names from the source code,
    -- but we can recover this information by looking at the types
    --   s = self.data
    --   i = self.bit_buf
    --   i1 = self.bits_in_buf
    apply loop.spec_decr_nat (measure := fun (data, bit_buf, bits_in_buf) => 56 - bits_in_buf) (inv := fun (data, bit_buf, bits_in_buf) => True) 
    . intros
      simp
      unfold BitReader.refill_slow_loop.body
      step*
      scalar_tac
    . scalar_tac

@[step]
theorem refill_slow_does_not_panic (self: BitReader): self.refill_slow ⦃ r => True ⦄ := by
  unfold BitReader.refill_slow
  step*

open byteorder.LittleEndian.Insts.ByteorderByteOrder

@[step]
theorem ofOption_spec (x: Option a) (e: Error) (h: x.isSome): ofOption x e ⦃ r => True ⦄ := by
  unfold ofOption
  grind

@[step]
theorem read_u64_spec (bytes: Slice Std.U8) (h: bytes.len ≥ Usize.ofNat 8): read_u64 bytes ⦃ r => True ⦄ := by
  unfold read_u64
  step* 
  <;> grind

theorem or_lt_pow2 (x y: U64) (h: x < 64#u64 ∧ y < 64#u64): x ||| y < 64#u64 := by
  bv_tac 64

/- Attempted shorter proof along the lines of this but couldn't figure out a way to conclude. -/

/-

+theorem elim_toNat (x: BitVec n) (y: Nat) (h: x.toNat < y) (h2: y < 2^n): x < BitVec.ofNat n y := by
+  rw [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h2]
+  exact h

then ... or_lt_pow2_usize ...
  let ⟨bv_x⟩ := x
  let ⟨bv_y⟩ := y
  cases System.Platform.numBits_eq <;>
  . rename_i h
    have : bv_x ||| bv_y < 64 := by
      rw [UScalar.lt_equiv] at hx hy
      simp only [UScalar.val,Usize.ofNat,UScalar.ofNat] at hx hy
      revert bv_x bv_y
      unfold UScalarTy.numBits
      simp
      rw [h]
      intros bv_x hx bv_y hy
      apply elim_toNat at hx
      apply elim_toNat at hy 
      simp at hx hy
      bv_tac
    sorry
-/

theorem or_lt_pow2_usize (x y: Usize) (h: x < 64#usize ∧ y < 64#usize): x ||| y < 64#usize := by
  -- FIXME: horrible Gemini-generated proof; needs improvement
  let ⟨bv_x⟩ := x
  let ⟨bv_y⟩ := y
  cases h_bits : System.Platform.numBits_eq
  . rename_i h_bits_val
    have h1 : bv_x.toNat < 64 := by
      simp [h_bits_val, UScalar.lt_equiv, UScalar.val] at h
      exact h.1
    have h2 : bv_y.toNat < 64 := by
      simp [h_bits_val, UScalar.lt_equiv, UScalar.val] at h
      exact h.2
    clear h
    have helper : ∀ (b1 b2 : BitVec 32), b1.toNat < 64 → b2.toNat < 64 → (b1 ||| b2).toNat < 64 := by
      intro b1 b2 hb1 hb2
      change b1 < BitVec.ofNat 32 64 at hb1
      change b2 < BitVec.ofNat 32 64 at hb2
      show (b1 ||| b2) < BitVec.ofNat 32 64
      bv_tac 32
    rw [UScalar.lt_equiv, UScalar.val_or]
    unfold UScalar.val
    simp [h_bits_val]
    rw [← BitVec.toNat_or]
    revert bv_x bv_y h1 h2
    unfold UScalarTy.numBits
    rw [h_bits_val]
    intro bv_x bv_y h1 h2
    apply helper <;> assumption
  . rename_i h_bits_val
    have h1 : bv_x.toNat < 64 := by
      simp [h_bits_val, UScalar.lt_equiv, UScalar.val] at h
      exact h.1
    have h2 : bv_y.toNat < 64 := by
      simp [h_bits_val, UScalar.lt_equiv, UScalar.val] at h
      exact h.2
    clear h
    have helper : ∀ (b1 b2 : BitVec 64), b1.toNat < 64 → b2.toNat < 64 → (b1 ||| b2).toNat < 64 := by
      intro b1 b2 hb1 hb2
      change b1 < BitVec.ofNat 64 64 at hb1
      change b2 < BitVec.ofNat 64 64 at hb2
      show (b1 ||| b2) < BitVec.ofNat 64 64
      bv_tac 64
    rw [UScalar.lt_equiv, UScalar.val_or]
    unfold UScalar.val
    simp [h_bits_val]
    rw [← BitVec.toNat_or]
    revert bv_x bv_y h1 h2
    unfold UScalarTy.numBits
    rw [h_bits_val]
    intro bv_x bv_y h1 h2
    apply helper <;> assumption

@[step]
theorem refill_does_not_panic (self: BitReader) (h: self.invariant): self.refill ⦃ r => True ⦄ := by
  unfold BitReader.refill
  step*
  simp at h
  . grind
  . simp at h
    grind
  . cases System.Platform.numBits_eq <;> grind
  . simp
    scalar_tac
  . have: Usize.ofNat 56 ≤ self.bits_in_buf ||| Usize.ofNat 56 := by apply or_lt2_usize
    grind
  . have : self.bits_in_buf ||| 56#usize < 64#usize := by apply or_lt_pow2_usize; grind
    grind

-- TODO: peek must:
-- 1. restore the invariant
-- 2. establish a predicate that says that it ensures that there is enough data for a
--    call to consume_optimistic to succeed, or that the invariant is destroyed and that then we are
--    at the end of the file

theorem shift_gt_1 (num: Usize) (h: num <= MAX_BITS_PER_CALL): (1#u64).val ≤ 1 <<< num.val % U64.size := by
  simp_all [global_simps]
  have h1 : 1 <<< num.val < 2^64 - 1 := by
    calc
      1 <<< num.val = 2^num.val := by
        grind
      _ <= 2^56 := by
        apply Nat.pow_le_pow_right
        <;> scalar_tac
      _ < 2^64 - 1 := by
        grind
  simp [U64.size,U64.numBits]
  grind [Nat.mod_eq_of_lt,Nat.pow_le_pow_right]

@[step]
theorem consum_optimistic_does_not_panic (self : BitReader) (num : Usize) (h: num <= MAX_BITS_PER_CALL): self.consume_optimistic num ⦃ r => True ⦄ := by
  unfold BitReader.consume_optimistic
  simp_all
  simp_all only [global_simps]
  simp [lift] -- WHY?!
  step*

@[step]
theorem peek_does_not_panic (self : BitReader) (num : Usize) (h: num <= MAX_BITS_PER_CALL): self.peek num ⦃ r => True ⦄ := by
  unfold BitReader.peek
  simp_all
  simp_all only [global_simps]
  step*
  . simp; scalar_tac
  . rw [i4_post1]; apply shift_gt_1; simp [global_simps]; assumption
  . rw [i4_post1]; apply shift_gt_1; simp [global_simps]; assumption

-- THEOREMZ

@[simp]
lemma ad_hoc (x: U32): x.val &&& 0xfff = x.val % 2^12 :=
  by
    have : 0xfff = 2^12 - 1 := by rfl
    rw [this, Nat.and_two_pow_sub_one_eq_mod]

@[step]
theorem bucket_index_is_in_bounds (hist: AnsHistogram) (inv: hist.invariant) (state: U32):
    bucket_index hist state ⦃ idx => idx < hist.buckets.len ⦄
:=
  by
    unfold bucket_index
    simp_all [global_simps]
    step*
    simp[*]
    have : (state.val % 4096) >>> hist.log_bucket_size.val < 2 ^ (12 - hist.log_bucket_size.val) := by
      rw [Nat.shiftRight_eq_div_pow]
      apply Nat.div_lt_of_lt_mul
      rw [← Nat.pow_add, Nat.add_sub_of_le] <;> scalar_tac
    assumption

theorem bucket_index_eq {a} (self: AnsHistogram) (i: U32) (f: Usize -> U32 -> Result a):
    (do
      let i1 ← lift (i &&& 4095#u32)
      let i2 ← i1 >>> self.log_bucket_size
      let i3 ← lift (UScalar.cast UScalarTy.Usize i2)
      f i3 i1) =
    (do
      let i3 ← bucket_index self i
      f i3 (i &&& 4095#u32))
  :=
  by
    simp [bucket_index,lift]
    intros v
    intros h
    congr
    scalar_tac

set_option maxRecDepth 200

set_option maxHeartbeats 4000000
theorem read_does_not_panic (self : entropy_coding.ans.AnsHistogram) (inv: self.invariant) (br : bit_reader.BitReader) (state : Std.U32) :
    self.read br state ⦃ r => True ⦄
:=
  by
    unfold entropy_coding.ans.AnsHistogram.read
    have inv2 := inv
    simp [-entropy_coding.ans.Bucket.invariant] at inv
    rcases inv with ⟨ inv0, inv1, inv2 ⟩
    simp_all only [global_simps]
    rw [bucket_index_eq]
    step*
    . have : (self.buckets.val).length.isPowerOfTwo := ⟨ _, inv1 ⟩
      scalar_tac
    . have : self.buckets.len = self.buckets.deref.length := rfl
      scalar_tac
    . have : i4.val < 2^16 := by simp_all; bv_tac 32
      have : pos.val < 2^12 := by simp_all; bv_tac 32
      scalar_tac
    . have : i10.val < 2^20 := by simp_all; bv_tac 32
      have : bucket.invariant := by
        rw [bucket_post]
        apply inv2; apply List.get_mem
      simp at this
      rcases this with ⟨ bi1, bi2, bi3 ⟩
      simp [global_simps] at bi1 bi2 bi3
      have : dist1.val < 2^12 := by
        simp [global_simps] at *
        bv_tac 32
      scalar_tac
    . have : i10.val < 2^20 := by simp_all; bv_tac 32
      have : bucket.invariant := by
        rw [bucket_post]
        apply inv2; apply List.get_mem
      simp at this
      rcases this with ⟨ bi1, bi2, bi3 ⟩
      simp [global_simps] at bi1 bi2 bi3
      have : dist1.val < 2^12 := by
        simp [global_simps] at *
        bv_tac 32
      have : bucket.alias_offset.val < 2^12 := by simp_all; bv_tac 32
      have : offset.val <= 2^12 - 1 := by
        have : map_to_alias.val = 0 ∨ map_to_alias.val = 1 := by scalar_tac
        cases this <;> scalar_tac
      scalar_tac
    . simp [global_simps]
    . simp [global_simps]
      scalar_tac
