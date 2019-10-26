import hilbert.wr.ka_bot
import hilbert.wr.proofs.ka

namespace clfrags
    namespace hilbert
        namespace wr
            namespace ka_bot

                theorem  kab₁_ka {a b c d e : Prop} (h₁ : ka d e (ka a b bot)) : ka d e (ka a b c) :=
                    have h₂ : ka d e (ka d b bot), from ka.ka₇ h₁,
                    have h₃ : ka d (ka d e b) bot, from ka.ka₄ h₂,
                    have h₄ : ka d (ka d e b) c, from kab₁ h₃,
                    have h₅ : ka d e a, from ka.ka₆ h₁,
                    have h₆ : ka d e (ka d b c), from ka.ka₄' h₄,
                    show ka d e (ka a b c), from ka.ka₅ h₅ h₆

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

