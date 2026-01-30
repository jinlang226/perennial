From New.proof Require Import proof_prelude.
From New.generatedproof Require Import unicode.utf8.

Module utf8.
Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

(* Set Printing Coercions. *)
(* disable z of nat *)
(* Disable Coercion Z.of_nat. *)
(* Specification for DecodeRune: unpacks the first UTF-8 encoding in a byte slice *)
Remove Printing Coercion Z.of_nat.
(* https://rocq-prover.org/doc/master/refman/addendum/implicit-coercions.html#rocq:cmd.Coercion *)

Lemma wp_DecodeRune (s : slice.t) (bs : list w8) :
  {{{
    own_slice s (DfracOwn 1) bs
  }}}
    utf8.DecodeRuneⁱᵐᵖˡ #s
  {{{
    (r : w32) (size : w64), RET (#r, #size);
    own_slice s (DfracOwn 1) bs ∗
    ⌜(* Empty slice case *)
     (bs = [] ∧ uint.Z size = 0 ∧ uint.Z r = uint.Z (W32 utf8.RuneError)) ∨
     (* Invalid encoding case *)
     (bs ≠ [] ∧ uint.Z size = 1 ∧ uint.Z r = uint.Z (W32 utf8.RuneError)) ∨
     (* Valid encoding case *)
     (bs ≠ [] ∧ 1 ≤ uint.Z size ≤ 4 ∧
      0 ≤ uint.Z r ≤ uint.Z (W32 utf8.MaxRune))⌝
  }}}.
Proof.
  wp_start.
  unfold utf8.DecodeRuneⁱᵐᵖˡ.
  wp_pures.
  wp_bind.
  wp_alloc s_ptr as "Hs".
  wp_pures.
  wp_bind.
  wp_alloc r_ptr as "Hr".
  wp_pures.
  wp_bind.
  wp_alloc p_ptr as "Hp".
  wp_pures.
  wp_bind.
  wp_alloc n_ptr as "Hn".
  wp_pures.
  wp_bind.
  wp_load.
  wp_pures.
  wp_bind.
  wp_store.
  wp_pures.
  wp_bind.
  wp_load.
  wp_pures.
  destruct bs as [|b0 bs'].
  { (* Empty slice case *)
    wp_pures.
    wp_if_destruct.
    {
      wp_pures.
      iApply "HΦ".
      iFrame "Hpre".
      iPureIntro.
      left.
      done.
    }
    {
      iDestruct (own_slice_len with "Hpre") as %(Hlen & Hnonneg).
      simpl in Hlen.
      word.
      (* exfalso.
      apply n.
      clear n. *)
      (* assert (sint.Z s.(slice.len_f) = 0%Z) as Hz by word.
      rewrite Hz.
      word. *)
    }
  }
Admitted.

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
Lemma wp_ValidRune
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
  wp_pures.
  wp_if_destruct.
  { (* first condition true *)
    wp_pures.
    wp_bind.
    wp_pures.
    wp_if_destruct.
    { (* nested condition true *)
      wp_pures.
      iApply ("HΦ" $! true). done.
    }
    { (* nested condition false *)
      wp_pures.
      wp_if_destruct.
      {
        (* second nested condition true *)
        wp_pures.
        wp_if_destruct.
        { (* third nested condition true *)
          wp_pures.
          iApply ("HΦ" $! true). done.
        }
        { (* third nested condition false *)
          wp_pures.
          iApply ("HΦ" $! false). done.
        }
      }
      { (* second nested condition false *)
        wp_pures.
        iApply ("HΦ" $! false). done.
      }
    }
  }
  {
    (* first condition false *)
    wp_pures.
    wp_bind.
    wp_if_destruct.
    { (* second condition true *)
      wp_pures.
      wp_if_destruct.
      { (* nested condition true *)
        wp_pures.
        iApply ("HΦ" $! true). done.
      }
      { (* nested condition false *)
        wp_pures.
        iApply ("HΦ" $! false). done.
      }
    }
    { (* second condition false *)
      wp_pures.
      iApply ("HΦ" $! false). done.
    }
  }
Qed.

End proof.
End utf8.
