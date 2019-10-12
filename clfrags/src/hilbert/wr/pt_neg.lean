import core.connectives

import hilbert.wr.pt
import hilbert.wr.proofs.pt

namespace clfrags
    namespace hilbert
        namespace wr
            namespace pt_neg
                axiom n₁ : Π {a b : Prop}, a → neg a → b
                axiom ptn₁ : Π {a b c : Prop}, neg (pt a b c) → pt (neg a) b c
                axiom ptn₂ : Π {a b c : Prop}, pt (neg a) b c → neg (pt a b c)
                --axiom ptn₃ : Π {a b c : Prop}, neg (pt a b c) → pt a (neg b) c 
                axiom ptn₃ : Π {a b c : Prop}, pt (neg a) b c → pt a (neg b) c 
            end pt_neg
        end wr
    end hilbert
end clfrags
