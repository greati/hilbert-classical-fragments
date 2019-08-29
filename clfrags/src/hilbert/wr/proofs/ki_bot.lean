import hilbert.wr.ki_bot
import hilbert.wr.proofs.ki

namespace clfrags
    namespace hilbert
        namespace wr
            namespace ki_bot

                theorem  kib₁_or {a b c d e : Prop} (h₁ : ki d e (ki b a bot)) : ki d e (ki b a c) :=
                    have h₂ : ki d e (ki d a bot), from ki.ki₉ h₁,
                    have h₃ : ki d (ki e e a) bot, from ki.ki₅ h₂,
                    have h₄ : ki d (ki e e a) c, from kib₁ h₃,
                    have h₅ : ki d e (ki d a c), from ki.ki₆ h₄,
                    have h₆ : ki d e b, from ki.ki₈ h₁,
                    show ki d e (ki b a c), from ki.ki₇ h₆ h₅

                theorem  b₁ {a : Prop} (h₁ : bot) : a :=
                    have h₂ : ki bot bot bot, from ki.ki₁₀ h₁ h₁,
                    have h₃ : ki bot bot a, from kib₁ h₂,
                    show a, from ki.ki₁ h₁ h₃

            end ki_bot
        end wr
    end hilbert
end clfrags

