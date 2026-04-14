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
  -- gemini-generated proof; can we do better?
  let ⟨bv_x⟩ := x
  let ⟨bv_y⟩ := y
  cases h_bits : System.Platform.numBits_eq
  . rename_i h
    rw [UScalar.le_equiv, UScalar.val_or]
    unfold UScalar.val
    rw [← BitVec.toNat_or]
    have : bv_y ≤ bv_x ||| bv_y := by
      revert bv_x bv_y
      unfold UScalarTy.numBits
      rw [h]
      intro bv_x bv_y
      simp at bv_x bv_y
      bv_tac
    exact this
  . rename_i h
    rw [UScalar.le_equiv, UScalar.val_or]
    unfold UScalar.val
    rw [← BitVec.toNat_or]
    have : bv_y ≤ bv_x ||| bv_y := by
      revert bv_x bv_y
      unfold UScalarTy.numBits
      rw [h]
      intro bv_x bv_y
      simp at bv_x bv_y
      bv_tac
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

theorem or_lt_pow2_usize (x y: Usize) (h: x < 64#usize ∧ y < 64#usize): x ||| y < 64#usize := by
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
  <;> try scalar_tac
  . simp at h
    grind
  . cases System.Platform.numBits_eq <;> grind
  . simp
    scalar_tac
  . have: Usize.ofNat 56 ≤ self.bits_in_buf ||| Usize.ofNat 56 := by apply or_lt2_usize
    grind
  . have : self.bits_in_buf ||| 56#usize < 64#usize := by
      apply or_lt_pow2_usize
      constructor
      . assumption
      . simp
    scalar_tac

-- TODO: peek must:
-- 1. restore the invariant
-- 2. establish a predicate that says that it ensures that there is enough data for a
--    call to consume_optimistic to succeed, or that the invariant is destroyed and that then we are
--    at the end of the file

@[step]
theorem peek_does_not_panic (self : BitReader) (num : Usize) (h: num <= MAX_BITS_PER_CALL): self.peek num ⦃ r => True ⦄ := by
  unfold BitReader.peek
  simp_all
  simp_all only [global_simps]
  step*
  <;> try scalar_tac
  . simp; scalar_tac
  . sorry
  . sorry

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
    simp_all
    simp_all only [global_simps]
    step*
    simp[*]
    have : (state.val % 4096) >>> hist.log_bucket_size.val < 2 ^ (12 - hist.log_bucket_size.val) :=
      calc
        (state.val % 4096) >>> hist.log_bucket_size.val < 2 ^ 12 >>> hist.log_bucket_size.val := 
          by
            simp only [Nat.shiftRight_eq_div_pow]
            have : 2 ^ hist.log_bucket_size.val ∣ 2^12 := by simp_scalar
            simp_scalar [Nat.lt_div_iff_mul_lt_of_dvd, Nat.div_mul_le_self]
            apply (Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _))
            scalar_tac
        _ = 2 ^ (12 - hist.log_bucket_size.val) := 
          by
            simp only [Nat.shiftRight_eq_div_pow]
            apply Nat.pow_div <;> scalar_tac
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
    simp at inv
    rcases inv with ⟨ inv0, inv1, inv2 ⟩
    simp_all only [global_simps]
    rw [bucket_index_eq]
    step*
    . have : self.buckets.val.length.isPowerOfTwo := ⟨ _, by assumption ⟩
      scalar_tac
    . have : self.buckets.len = self.buckets.deref.length := rfl
      scalar_tac
    /- <;> try -/ 
    /-   have : map_to_alias.val = 0 ∨ map_to_alias.val = 1 := by scalar_tac -/
    /-   cases this <;> scalar_tac -/
    . have : i4.val < 2^16 := by simp_all; bv_tac 32
      have : pos.val < 2^12 := by simp_all; bv_tac 32
      scalar_tac
    . have : i10.val < 2^20 := by simp_all; bv_tac 32
      have h : bucket = self.buckets.val[i3.val] := by
        simp_all[alloc.vec.Vec.deref]
        grind
      have : bucket.invariant := by
        have := inv2 bucket
        simp [h] at this
        simp [global_simps,h,this]
      simp at this
      split_conjs at this
      have : dist1.val < 2^12 := by
        simp [global_simps] at *
        bv_tac 32
      scalar_tac
    . have : i10.val < 2^20 := by simp_all; bv_tac 32
      have h : bucket = self.buckets.val[i3.val] := by
        simp_all[alloc.vec.Vec.deref]
        grind
      have : bucket.invariant := by
        have := inv2 bucket
        simp [h] at this
        simp [global_simps,h,this]
      simp at this
      rcases this with ⟨ bi1, bi2, bi3 ⟩
      simp [global_simps] at bi1 bi2 bi3
      have : dist1.val < 2^12 := by
        simp [global_simps] at *
        bv_tac 32
      have : bucket.alias_offset.val < 2^12 := by simp_all; bv_tac 32
      have : offset.val <= 2^12 - 1 := by
        calc
          offset.val <= i4.val := by
            -- FIXME: why is this not triggering automatically? I thought we had a pattern
            have : map_to_alias.val = 0 ∨ map_to_alias.val = 1 := by scalar_tac
            cases this <;> scalar_tac
          _ <= bucket.alias_offset := by
            scalar_tac
          _ <= 2^12 - 1 := by
            simp_all; bv_tac 32
      scalar_tac
    . simp [global_simps]
    . sorry
