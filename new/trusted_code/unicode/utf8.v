From New.golang Require Import defn.

Section code.
Context `{ffi_syntax}.

Axiom FullRuneⁱᵐᵖˡ : val.
Axiom FullRuneInStringⁱᵐᵖˡ : val.
Axiom DecodeRuneⁱᵐᵖˡ : val.
Axiom DecodeRuneInStringⁱᵐᵖˡ : val.
Axiom DecodeLastRuneⁱᵐᵖˡ : val.
Axiom DecodeLastRuneInStringⁱᵐᵖˡ : val.
Axiom RuneLenⁱᵐᵖˡ : val.
Axiom EncodeRuneⁱᵐᵖˡ : val.
Axiom RuneCountⁱᵐᵖˡ : val.
Axiom RuneCountInStringⁱᵐᵖˡ : val.
Axiom Validⁱᵐᵖˡ : val.
Axiom ValidStringⁱᵐᵖˡ : val.

End code.
