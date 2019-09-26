import hilbert.wr.ad

namespace clfrags
    namespace hilbert
        namespace wr
            namespace ad

                theorem ad₂₆ {a b c : Prop} (h₁ : a) (h₂ : b) : ad a b c :=
                    have h₃ : ad (ad a b c) b a, from ad₂ h₂,
                    show ad a b c, from ad₁ h₁ h₃

                theorem ad'₄ {a b c : Prop} (h₁ : a) : ad c a (ad c a (ad b a c)) :=
                    have h₂ : ad a a a, from ad₂₆ h₁ h₁,
                    have h₃ : ad (ad c a (ad c a (ad b a c))) a a, from ad₄ h₂,
                    show ad c a (ad c a (ad b a c)), from ad₁ h₁ h₃

            end ad
        end wr
    end hilbert
end clfrags
