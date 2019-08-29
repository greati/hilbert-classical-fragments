import hilbert.wr.ka_bot
import hilbert.wr.proofs.ka

namespace clfrags
    namespace hilbert
        namespace wr
            namespace ka_bot

                theorem  kab₁_or {a b c d e : Prop} (h₁ : ka d e (ka b a bot)) : ka d e (ka b a c) :=
                    have h₂ : ka d e (ka d a bot), from ka.ka₇ h₁,
                    have h₃ : ka d (ka d e a) bot, from ka.ka₄ h₂,
                    have h₄ : ka d (ka d e a) c, from kab₁ h₃,
                    have h₅ : ka d e b, from ka.ka₆ h₁,
                    have h₆ : ka d e (ka d a c), from ka.ka₄' h₄,
                    show ka d e (ka b a c), from ka.ka₅ h₅ h₆

                theorem  b₁ {a : Prop} (h₁ : bot) : a :=
                    have h₂ : ka bot bot bot, from ka.ka₁ h₁ h₁,
                    have h₃ : ka bot bot a, from kab₁ h₂,
                    have h₄ : ka bot a bot, from ka.ka₃ h₃,
                    have h₅ : ka bot a a, from kab₁ h₄,
                    show a, from ka.ka₂ h₅

            end ka_bot
        end wr
    end hilbert
end clfrags

