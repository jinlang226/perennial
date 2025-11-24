From New.proof Require Import proof_prelude.
From New.generatedproof Require Import unicode.utf8.

Module utf8.
Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

(* Specification for RuneStart: checks if a byte is the start of a UTF-8 sequence *)
Lemma wp_RuneStart (b : w8) :
  {{{
    True
  }}}
    utf8.RuneStartⁱᵐᵖˡ #b
  {{{
    (result : bool), RET #result;
    True
  }}}.
Proof.
  wp_start. 
  unfold utf8.RuneStartⁱᵐᵖˡ.
  wp_pures.
  wp_bind.
  wp_alloc b_ptr as "Hb".
  wp_pures.
  wp_bind.
  wp_load.
  wp_pures.
  iApply "HΦ".
  done.
Qed.  


(* Specification for ValidRune: checks if a rune can be legally encoded as UTF-8 *)
Lemma wp_ValidRunegd
 (r : w32) :
  {{{
    True
  }}}
    utf8.ValidRuneⁱᵐᵖˡ #r
  {{{
    (result : bool), RET #result;
    True
  }}}.
Proof.
  wp_start. 
  unfold utf8.ValidRuneⁱᵐᵖˡ.
  wp_pures.
  wp_bind.
  wp_alloc r_ptr as "Hr".
  wp_pures.
  wp_bind.
  wp_load. 
  
Admitted.

End proof.
End utf8.
