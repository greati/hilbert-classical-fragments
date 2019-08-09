import hilbert.wr.or
import hilbert.wr.or_bot

namespace clfrags
    namespace hilbert
        namespace wr
            namespace or_bot
                theorem  db₁_or {a b : Prop} (h₁ : or b (or a bot)) : or b a :=
                    have h₂ : or (or b a) bot, from or.d₄ h₁,
                    show or b a, from db₁ h₂

                theorem  b₁ {a : Prop} (h₁ : bot) : a :=
                    have h₂ : or bot a, from or.d₁ h₁,
                    have h₃ : or a bot, from or.d₃ h₂,
                    show a, from db₁ h₃
            end or_bot
        end wr
    end hilbert
end clfrags

