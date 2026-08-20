import Aeneas
import JxlProofs.Funs
import JxlProofs.Types
open Aeneas Aeneas.Std Result Error

namespace jxl

open entropy_coding.ans
open jxl.bit_reader

-- INVARIANTS OVER TYPES

@[simp,grind]
def bit_reader.BitReader.invariant (self: bit_reader.BitReader) :=
  self.bits_in_buf < Usize.ofNat 64

@[simp,grind]
def entropy_coding.ans.Bucket.invariant (self: Bucket): Bool :=
  self.dist.val < 2^LOG_SUM_PROBS.val ∧
  self.alias_dist_xor.val < 2^LOG_SUM_PROBS.val ∧
  self.alias_offset.val < self.dist

@[simp,grind]
def entropy_coding.ans.AnsHistogram.invariant (self: AnsHistogram) :=
  self.log_bucket_size <= LOG_SUM_PROBS ∧
  self.buckets.len.val = 2^(LOG_SUM_PROBS.val - self.log_bucket_size.val) ∧
  self.buckets.val.all (fun b => b.invariant)

-- HELPERS

deriving instance Inhabited for AnsHistogram
deriving instance Inhabited for Bucket

-- PROGRESS LEMMAS

@[simp,scalar_tac x.val * y.val]
theorem times_zero_or_1 (x y: U32) (h: y.val = 0 ∨ y.val = 1): x.val * y.val <= U32.max :=
  by
    cases h <;> scalar_tac

grind_pattern [agrind] times_zero_or_1 => x.val * y.val where gen < 1

@[simp,scalar_tac x &&& y]
theorem and_lt1 (x y: U32): x &&& y <= x := by bv_tac 32

grind_pattern [agrind] and_lt1 => x &&& y

@[simp,scalar_tac x &&& y]
theorem and_lt2 (x y: U32): x &&& y <= y := by bv_tac 32

grind_pattern [agrind] and_lt2 => x &&& y

@[simp,scalar_tac x ||| y]
theorem or_lt1 (x y: U32): x <= x ||| y := by bv_tac 32

grind_pattern [agrind] or_lt1 => x ||| y

@[simp,scalar_tac x ||| y]
theorem or_lt2 (x y: U32): y <= x ||| y := by bv_tac 32

grind_pattern [agrind] or_lt2 => x ||| y

theorem case_usize (P : {n : Nat} → BitVec n → BitVec n → Prop)
  (h32 : ∀ (x y : BitVec 32), P x y)
  (h64 : ∀ (x y : BitVec 64), P x y) :
  ∀ (x y : Usize), P x.bv y.bv := by
  intro x y
  rcases System.Platform.numBits_eq with h | h
  · exact (Eq.ndrec (motive := fun n => ∀ (a b : BitVec n), P a b) h32 h.symm) x.bv y.bv
  · exact (Eq.ndrec (motive := fun n => ∀ (a b : BitVec n), P a b) h64 h.symm) x.bv y.bv

@[simp,scalar_tac x ||| y]
theorem or_lt2_usize (x y : Usize) : y ≤ x ||| y := by
  bvify System.Platform.numBits
  apply case_usize (fun x y => y ≤ x ||| y) <;> intros <;> bv_tac

theorem or_lt_pow2_usize (x y : Usize) (h : x < 64#usize ∧ y < 64#usize) :
    x ||| y < 64#usize := by
  bvify System.Platform.numBits
  apply case_usize (fun x y => x < 64 ∧ y < 64 → x ||| y < 64) <;> intros <;> bv_tac

grind_pattern [agrind] or_lt2_usize => x ||| y

@[simp,scalar_tac x.len]
theorem len_is_len (x: alloc.vec.Vec a): x.len = x.deref.length := by rfl

grind_pattern [agrind] len_is_len => x.len
grind_pattern [agrind] len_is_len => x.deref.length

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

@[step]
theorem refill_does_not_panic (self: BitReader) (h: self.invariant): self.refill ⦃ r => True ⦄ := by
  unfold BitReader.refill
  step*
  <;> try grind
  . cases System.Platform.numBits_eq <;> grind
  . simp; scalar_tac
  . scalar_tac
  . have : self.bits_in_buf ||| 56#usize < 64#usize := by apply or_lt_pow2_usize; grind
    grind

-- TODO: peek must:
-- 1. restore the invariant
-- 2. establish a predicate that says that it ensures that there is enough data for a
--    call to consume_optimistic to succeed, or that the invariant is destroyed and that then we are
--    at the end of the file

attribute [scalar_tac_simps,grind =,bvify] MAX_BITS_PER_CALL LOG_SUM_PROBS

theorem shift_gt_1 (num: Usize) (h: num <= MAX_BITS_PER_CALL): (1#u64).val ≤ 1 <<< num.val % U64.size := by
  have h1 : 1 <<< num.val < 2^64 - 1 := by
    calc
      1 <<< num.val = 2^num.val := by
        grind
      _ <= 2^56 := by
        simp_scalar
      _ < 2^64 - 1 := by
        grind
  simp [U64.size,U64.numBits]
  grind [Nat.mod_eq_of_lt,Nat.pow_le_pow_right]

@[step]
theorem consum_optimistic_does_not_panic (self : BitReader) (num : Usize) (h: num <= MAX_BITS_PER_CALL): self.consume_optimistic num ⦃ r => True ⦄ := by
  unfold BitReader.consume_optimistic
  simp [lift] -- TODO: upgrade Aeneas to get rid of this
  step*

@[step]
theorem peek_does_not_panic (self : BitReader) (num : Usize) (h: num <= MAX_BITS_PER_CALL): self.peek num ⦃ r => True ⦄ := by
  unfold BitReader.peek
  step; split <;> step*
  . grind
  all_goals rw [i4_post1]; apply shift_gt_1; scalar_tac

-- THEOREMZ

@[simp]
lemma ad_hoc (x: U32): x.val &&& 0xfff = x.val % 2^12 :=
  by
    have : 0xfff = 2^12 - 1 := by rfl
    rw [this, Nat.and_two_pow_sub_one_eq_mod]

-- def bucket_index (hist: AnsHistogram) (state: U32): Result Std.Usize :=
--   do
--     let r ← (state &&& U32.ofNat 0xfff) >>> hist.log_bucket_size
--     -- avoids progress* being blocked because of an automatically-inserted
--     -- coercion that is not recognized by the implementation of progress*
--     .ok (Usize.ofNatCore r.val (by scalar_tac))

#decompose AnsHistogram.read read_eq
  letRange 0 3 => bucket_index

#print bucket_index

@[step]
theorem bucket_index_is_in_bounds (hist: AnsHistogram) (inv: hist.invariant) (state: U32):
    bucket_index hist state ⦃ (_, idx) => idx < hist.buckets.len ⦄
:=
  by
    unfold bucket_index
    simp_all [global_simps]
    step*
    -- simp[*]
    have : (state.val % 4096) >>> hist.log_bucket_size.val < 2 ^ (12 - hist.log_bucket_size.val) := by
      rw [Nat.shiftRight_eq_div_pow]
      apply Nat.div_lt_of_lt_mul
      rw [← Nat.pow_add, Nat.add_sub_of_le] <;> scalar_tac
    simp [this]
    assumption

set_option maxRecDepth 200

set_option maxHeartbeats 4000000
theorem read_does_not_panic (self : entropy_coding.ans.AnsHistogram) (inv: self.invariant) (br : bit_reader.BitReader) (state : Std.U32) :
    self.read br state ⦃ r => True ⦄
:=
  by
    rw [read_eq]
    have inv2 := inv
    simp [-entropy_coding.ans.Bucket.invariant] at inv
    rcases inv with ⟨ inv0, inv1, inv2 ⟩
    iterate 4 step
    . have : (self.buckets.val).length.isPowerOfTwo := ⟨ _, inv1 ⟩
      grind
    split <;> step* <;> try grind
    . have : i4.val < 2^16 := by bv_tac 32
      have : pos.val < 2^12 := by bv_tac 32
      grind
    all_goals
      have : i10.val < 2^20 := by bv_tac 32
      have : bucket.invariant := by
        rw [bucket_post]
        apply inv2; apply List.get_mem
      simp at this
      rcases this with ⟨ bi1, bi2, bi3 ⟩
      have : dist1.val < 2^12 := by bv_tac 32
    . grind
    . have : bucket.alias_offset.val < 2^12 := by bv_tac 32
      have : offset.val <= 2^12 - 1 := by
        have : map_to_alias.val = 0 ∨ map_to_alias.val = 1 := by scalar_tac
        cases this <;> scalar_tac
      have : pos.val < 2^12 := by bv_tac 32
      scalar_tac
