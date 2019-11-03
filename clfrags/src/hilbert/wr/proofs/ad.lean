import hilbert.wr.ad

namespace clfrags
    namespace hilbert
        namespace wr
            namespace ad
                
                theorem ad₂₆ {a b c : Prop} (h₁ : a) (h₂ : b) : ad a b c :=
                    have h₃ : ad (ad a b c) b a, from ad₂ h₂,
                    show ad a b c, from ad₁ h₁ h₃
                
                theorem ad₄' {a b c : Prop} (h₁ : a) : ad c a (ad c a (ad b a c)) :=
                    have h₂ : ad a a a, from ad₂₆ h₁ h₁,
                    have h₃ : ad (ad c a (ad c a (ad b a c))) a a, from ad₄ h₂,
                    show ad c a (ad c a (ad b a c)), from ad₁ h₁ h₃

                theorem ad₂₇ {a b c d e : Prop} (h₁ : ad (ad a b c) d e) : ad (ad a d e) b c :=
                    have h₂ : (ad a d e) or (ad a b c), from ad₁₀ h₁,
                    have h₃ : (ad a b c) or (ad a d e), from ad₁₃ h₂,
                    show ad (ad a d e) b c, from ad₁₁ h₃
            
                theorem ad₆' {a b : Prop} (h₁ : a) : a or b := ad₆ h₁

                --theorem ad₂' {a b c d e : Prop} (h₁ : ad a d e) : 
                --    ((ad c a c) or (ad c a b)) or ((ad a d e) or (ad c a b)) :=
                --    sorry

                theorem ad₈' {a b c d e f : Prop} (h₁ : ad (ad c a b) e f) : ad (ad (c or d) a b) e f := 
                    have h₂ : (ad (ad c a b) e f) → ((ad c e f) or (ad c a b)), from ad₁₀,
                    have h₃ : (ad c e f) → (ad (ad (c or d) a b) e f), from sorry,
                    have h₄ : (ad c a b) → (ad (ad (c or d) a b) e f), from sorry,
                    have h₅ : ((ad c e f) or (ad c a b)) → (ad (ad (c or d) a b) e f), from δ_or₁ h₃ h₄,
                    show ad (ad (c or d) a b) e f, from (T₁ h₂ h₅) h₁
                
                theorem ad₁_ad {a b c d e : Prop} (h₁ : ad c d e) (h₂ : ad (ad a b c) d e) :
                    ad a d e := 
                    have h₃ : (ad (ad a b c) d e) → ((ad a d e) or (ad a b c)), from ad₁₀,
                    have h₄ : ad a d e → ad a d e, from R,
                    have h₅ : ad c d e → ad a b c → ad a d e, from ad₉,
                    have h₆ : ad c d e → ad a d e → ad a d e, from M₂ h₄,
                    have h₇ : ad c d e → ((ad a d e) or (ad a b c)) → ad a d e, from δ_or₂ h₆ h₅,
                    have h₈ : ad c d e → (ad (ad a b c) d e) → ((ad a d e) or (ad a b c)), from M₂ h₃,
                    show ad a d e, from (T₂ h₈ h₇) h₁ h₂

        
            end ad
        end wr
    end hilbert
end clfrags
