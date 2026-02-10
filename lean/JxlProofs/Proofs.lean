import Aeneas
import JxlProofs.Funs
import JxlProofs.Types
open Aeneas Aeneas.Std Result Error

namespace jxl

open entropy_coding.ans

@[simp]
def entropy_coding.ans.AnsHistogram.invariant (self: AnsHistogram) :=
  self.log_bucket_size <= LOG_SUM_PROBS ∧
  self.buckets.len.val = 2^(LOG_SUM_PROBS.val - self.log_bucket_size.val)

def bucket_index (hist: AnsHistogram) (state: U32): Result Std.Usize :=
  do
    let r ← (state &&& U32.ofNat 0xfff) >>> hist.log_bucket_size
    -- avoids progress* being blocked because of an automatically-inserted
    -- coercion that is not recognized by the implementation of progress*
    Result.ok (Usize.ofNatCore r.val (by scalar_tac))

@[simp]
lemma ad_hoc (x: U32): x.val &&& 0xfff = x.val % 2^12 :=
  by
    sorry

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

theorem read_does_not_panic (self : entropy_coding.ans.AnsHistogram) (br : bit_reader.BitReader) (state : Std.U32) :
    self.read br state ⦃ r => True ⦄
:=
  by
    unfold entropy_coding.ans.AnsHistogram.read
    progress*
    sorry
