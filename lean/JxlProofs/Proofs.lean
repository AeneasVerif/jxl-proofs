import Aeneas
import JxlProofs.Funs
import JxlProofs.Types
open Aeneas Aeneas.Std Result Error

namespace jxl

open entropy_coding.ans

-- TYPES

@[simp]
def entropy_coding.ans.Bucket.invariant (self: Bucket): Bool :=
  self.dist.val < 2^LOG_SUM_PROBS.val ∧
  self.alias_dist_xor.val < 2^LOG_SUM_PROBS.val

@[simp]
def entropy_coding.ans.AnsHistogram.invariant (self: AnsHistogram) :=
  self.log_bucket_size <= LOG_SUM_PROBS ∧
  self.buckets.len.val = 2^(LOG_SUM_PROBS.val - self.log_bucket_size.val) ∧
  self.buckets.val.all (fun b => b.invariant)

-- HELPERS

def bucket_index (hist: AnsHistogram) (state: U32): Result Std.Usize :=
  do
    let r ← (state &&& U32.ofNat 0xfff) >>> hist.log_bucket_size
    -- avoids progress* being blocked because of an automatically-inserted
    -- coercion that is not recognized by the implementation of progress*
    Result.ok (Usize.ofNatCore r.val (by scalar_tac))

@[simp]
lemma ad_hoc (x: U32): x.val &&& 0xfff = x.val % 2^12 :=
  by
    have : 0xfff = 2^12 - 1 := by rfl
    rw [this, Nat.and_two_pow_sub_one_eq_mod]

-- THEOREMZ

@[progress]
theorem bucket_index_is_in_bounds (hist: AnsHistogram) (inv: hist.invariant) (state: U32):
    bucket_index hist state ⦃ idx => idx < hist.buckets.len ⦄
:=
  by
    unfold bucket_index
    simp_all
    simp_all only [global_simps]
    progress*
    simp[*]
    have : (state.val % 4096) >>> hist.log_bucket_size.val < 2 ^ (12 - hist.log_bucket_size.val) :=
      calc
        (state.val % 4096) >>> hist.log_bucket_size.val < 2 ^ 12 >>> hist.log_bucket_size.val := 
          by
            simp only [Nat.shiftRight_eq_div_pow]
            have : state.val % 4096 < 4096 := by scalar_tac
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
      let i1 ← toResult (i &&& 4095#u32)
      let i2 ← i1 >>> self.log_bucket_size
      let i3 ← toResult (UScalar.cast UScalarTy.Usize i2)
      f i3 i1) =
    (do
      let i3 ← bucket_index self i
      f i3 (i &&& 4095#u32))
  :=
  by
    simp [bucket_index,toResult]
    intros v
    intros h
    congr
    scalar_tac

/- attribute [bv_tac_simps,simp] LOG_SUM_PROBS -/

@[simp,scalar_tac x.val * y.val]
theorem times_zero_or_1 (x y: U32) (h: y.val = 0 ∨ y.val = 1): x.val * y.val <= U32.max :=
  by
    cases h <;> scalar_tac

set_option maxHeartbeats 1000000
theorem read_does_not_panic (self : entropy_coding.ans.AnsHistogram) (inv: self.invariant) (br : bit_reader.BitReader) (state : Std.U32) :
    self.read br state ⦃ r => True ⦄
:=
  by
    unfold entropy_coding.ans.AnsHistogram.read
    simp at inv
    rcases inv with ⟨ inv0, inv1, inv2 ⟩
    simp_all only [global_simps]
    rw [bucket_index_eq]
    progress*
    <;> try 
      have : map_to_alias.val = 0 ∨ map_to_alias.val = 1 := by scalar_tac
      cases this <;> scalar_tac
    . simp_all [global_simps]
    . have : self.buckets.val.length.isPowerOfTwo := ⟨ _, by assumption ⟩
      scalar_tac
    . have : self.buckets.len = self.buckets.deref.length := rfl
      scalar_tac
    . have : i4.val < 2^16 := by bv_tac 32
      have : pos.val < 4096 := by bv_tac 32
      scalar_tac
    . have : i10.val < 2^20 := by bv_tac 32
      have h : bucket = self.buckets.val[i3.val] := by
        simp_all[alloc.vec.Vec.deref]
        sorry
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
    . sorry
    . sorry -- need to specify br.peek
